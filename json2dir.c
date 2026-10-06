/* json2dir: create the directory tree a JSON document describes, in the current directory.
 * Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
 *
 * Written in GNU C on purpose: nested functions, statement expressions, cleanup attributes,
 * __auto_type, typeof, case ranges, range designated initializers, labels as values, flexible
 * array members and __builtin_expect. It does not compile with -pedantic-errors.
 *
 * The nested functions never have their address taken, so GCC needs no trampolines and the
 * stack stays non-executable.
 *
 * Build: gcc -std=gnu17 -O2 -Wall -o out/json2dir json2dir.c
 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

static void die(const char *fmt, ...) __attribute__((noreturn, format(printf, 1, 2)));
static void die(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    fputs("json2dir: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
    exit(1);
}

/* A system call that returns -1 on failure: die with errno, otherwise yield the result. */
#define SYS(expr, ...) ({                                                    \
    __auto_type _r = (expr);                                                 \
    if (unlikely(_r == (typeof(_r))-1)) {                                    \
        int _e = errno;                                                      \
        fprintf(stderr, "json2dir: ");                                       \
        fprintf(stderr, __VA_ARGS__);                                        \
        die(": %s", strerror(_e));                                           \
    }                                                                        \
    _r; })

#define XALLOC(p, n) ({                                                      \
    typeof(p) _p = realloc((p), (n));                                        \
    if (unlikely(!_p)) die("out of memory");                                 \
    _p; })

static void closep(int *fd) { if (*fd >= 0) close(*fd); }
static void freep(void *p) { free(*(void **)p); }
#define AUTOCLOSE __attribute__((cleanup(closep)))
#define AUTOFREE __attribute__((cleanup(freep)))

/* ---- data model ---- */

/* A decoded JSON string: exact bytes plus a trailing NUL for use as a C path. */
struct jstr {
    size_t len;
    char data[];               /* flexible array member */
};

enum kind { K_FILE, K_SCRIPT, K_LINK, K_DIR };

struct member;

struct node {
    enum kind kind;
    struct jstr *str;          /* file content, script content or link target */
    size_t n, cap;             /* members of a directory */
    struct member *members;
};

struct member {
    struct jstr *name;
    struct node *val;
};

/* ---- input ---- */

static char *read_all(int fd, size_t *len)
{
    char *buf = NULL;
    size_t n = 0, cap = 0;
    for (;;) {
        if (n == cap) {
            cap = cap ? cap * 2 : 65536;
            buf = XALLOC(buf, cap + 1);
        }
        ssize_t r = read(fd, buf + n, cap - n);
        if (r == 0) break;
        if (r < 0) {
            if (errno == EINTR) continue;
            die("cannot read standard input: %s", strerror(errno));
        }
        n += (size_t)r;
    }
    *len = n;
    return buf;
}

/* RFC 3629 strict UTF-8: no overlongs, no surrogates, nothing above U+10FFFF. */
static void check_utf8(const unsigned char *s, size_t len)
{
    for (size_t i = 0; i < len;) {
        unsigned char c = s[i];
        int more;
        unsigned char lo = 0x80, hi = 0xBF;
        switch (c) {
        case 0x00 ... 0x7F: i++; continue;
        case 0xC2 ... 0xDF: more = 1; break;
        case 0xE0:          more = 2; lo = 0xA0; break;
        case 0xE1 ... 0xEC: more = 2; break;
        case 0xED:          more = 2; hi = 0x9F; break;
        case 0xEE ... 0xEF: more = 2; break;
        case 0xF0:          more = 3; lo = 0x90; break;
        case 0xF1 ... 0xF3: more = 3; break;
        case 0xF4:          more = 3; hi = 0x8F; break;
        default: die("input is not valid UTF-8 (byte offset %zu)", i);
        }
        if (unlikely(i + (size_t)more >= len))
            die("input is not valid UTF-8 (truncated sequence at byte offset %zu)", i);
        for (int k = 1; k <= more; k++) {
            unsigned char b = s[i + k];
            if (k == 1 ? (b < lo || b > hi) : (b < 0x80 || b > 0xBF))
                die("input is not valid UTF-8 (byte offset %zu)", i);
        }
        i += more + 1;
    }
}

/* ---- parser ---- */

static struct node *parse(const char *buf, size_t len)
{
    size_t pos = 0;
    int depth = 0;

    /* Nested functions closing over buf, len, pos and depth. */
    __attribute__((noreturn)) void bad(const char *what)
    {
        die("input is not valid JSON: %s at byte offset %zu", what, pos);
    }

    void ws(void)
    {
        while (pos < len && (buf[pos] == ' ' || buf[pos] == '\t' || buf[pos] == '\n' || buf[pos] == '\r'))
            pos++;
    }

    int peek(void) { return pos < len ? (unsigned char)buf[pos] : -1; }

    void expect(char c)
    {
        if (peek() != (unsigned char)c) {
            char msg[32];
            snprintf(msg, sizeof msg, "expected '%c'", c);
            bad(msg);
        }
        pos++;
    }

    unsigned hex4(void)
    {
        unsigned v = 0;
        for (int i = 0; i < 4; i++) {
            int c = peek();
            pos++;
            switch (c) {
            case '0' ... '9': v = v * 16 + (unsigned)(c - '0'); break;
            case 'a' ... 'f': v = v * 16 + (unsigned)(c - 'a' + 10); break;
            case 'A' ... 'F': v = v * 16 + (unsigned)(c - 'A' + 10); break;
            default: pos--; bad("bad \\u escape");
            }
        }
        return v;
    }

    struct jstr *string(void)
    {
        expect('"');
        /* The decoded string is never longer than its source text. */
        size_t start = pos;
        size_t end = start;
        while (end < len && buf[end] != '"') end += buf[end] == '\\' ? 2 : 1;
        struct jstr *s = XALLOC((struct jstr *)NULL, sizeof *s + (end - start) + 1);
        char *o = s->data;
        for (;;) {
            int c = peek();
            if (unlikely(c < 0)) bad("unterminated string");
            pos++;
            if (c == '"') break;
            if (unlikely(c < 0x20)) { pos--; bad("control character in string"); }
            if (likely(c != '\\')) { *o++ = (char)c; continue; }
            c = peek();
            pos++;
            switch (c) {
            case '"': case '\\': case '/': *o++ = (char)c; break;
            case 'b': *o++ = '\b'; break;
            case 'f': *o++ = '\f'; break;
            case 'n': *o++ = '\n'; break;
            case 'r': *o++ = '\r'; break;
            case 't': *o++ = '\t'; break;
            case 'u': {
                uint32_t cp = hex4();
                switch (cp) {
                case 0xDC00 ... 0xDFFF: bad("unpaired low surrogate");
                case 0xD800 ... 0xDBFF: {
                    if (peek() != '\\' || pos + 1 >= len || buf[pos + 1] != 'u') bad("unpaired high surrogate");
                    pos += 2;
                    uint32_t lo = hex4();
                    switch (lo) {
                    case 0xDC00 ... 0xDFFF: break;
                    default: bad("unpaired high surrogate");
                    }
                    cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                    break;
                }
                default: break;
                }
                if (cp < 0x80) {
                    *o++ = (char)cp;
                } else if (cp < 0x800) {
                    *o++ = (char)(0xC0 | cp >> 6);
                    *o++ = (char)(0x80 | (cp & 0x3F));
                } else if (cp < 0x10000) {
                    *o++ = (char)(0xE0 | cp >> 12);
                    *o++ = (char)(0x80 | (cp >> 6 & 0x3F));
                    *o++ = (char)(0x80 | (cp & 0x3F));
                } else {
                    *o++ = (char)(0xF0 | cp >> 18);
                    *o++ = (char)(0x80 | (cp >> 12 & 0x3F));
                    *o++ = (char)(0x80 | (cp >> 6 & 0x3F));
                    *o++ = (char)(0x80 | (cp & 0x3F));
                }
                break;
            }
            default: pos--; bad("bad escape");
            }
        }
        s->len = (size_t)(o - s->data);
        *o = 0;
        return s;
    }

    auto struct node *value(void);

    void check_name(const struct jstr *n)
    {
        if (n->len == 0 || (n->len == 1 && n->data[0] == '.') || (n->len == 2 && !memcmp(n->data, "..", 2))
            || memchr(n->data, '/', n->len) || memchr(n->data, 0, n->len))
            die("invalid name \"%s\"", n->data);
    }

    void add_member(struct node *d, struct jstr *name, struct node *v)
    {
        /* Duplicate names: the last occurrence wins (RFC J2D-1 §4.2). */
        for (size_t i = 0; i < d->n; i++)
            if (d->members[i].name->len == name->len && !memcmp(d->members[i].name->data, name->data, name->len)) {
                d->members[i].val = v;
                free(name);
                return;
            }
        if (d->n == d->cap) {
            d->cap = d->cap ? d->cap * 2 : 8;
            d->members = XALLOC(d->members, d->cap * sizeof *d->members);
        }
        d->members[d->n++] = (struct member){ name, v };
    }

    struct node *object(void)
    {
        if (++depth > 1000) bad("nesting too deep");
        expect('{');
        struct node *d = XALLOC((struct node *)NULL, sizeof *d);
        *d = (struct node){ .kind = K_DIR };
        ws();
        if (peek() == '}') { pos++; depth--; return d; }
        for (;;) {
            ws();
            if (peek() != '"') bad("expected a member name");
            struct jstr *name = string();
            check_name(name);
            ws();
            expect(':');
            ws();
            add_member(d, name, value());
            ws();
            if (peek() == ',') { pos++; continue; }
            expect('}');
            depth--;
            return d;
        }
    }

    struct node *array(void)
    {
        expect('[');
        ws();
        if (peek() != '"') bad("an array must be [\"link\", target] or [\"script\", content]");
        struct jstr *k AUTOFREE = string();
        ws();
        expect(',');
        ws();
        if (peek() != '"') bad("an array must be [\"link\", target] or [\"script\", content]");
        struct jstr *payload = string();
        ws();
        expect(']');
        struct node *n = XALLOC((struct node *)NULL, sizeof *n);
        *n = (struct node){ .str = payload };
        if (k->len == 4 && !memcmp(k->data, "link", 4)) {
            if (memchr(payload->data, 0, payload->len)) die("a link target cannot contain NUL");
            n->kind = K_LINK;
        } else if (k->len == 6 && !memcmp(k->data, "script", 6)) {
            n->kind = K_SCRIPT;
        } else {
            die("unknown array kind \"%s\"", k->data);
        }
        return n;
    }

    /* Value dispatch through a table of label addresses (computed goto). */
    struct node *value(void)
    {
        static const void *const dispatch[257] = {
            [0 ... 256] = &&other,
            ['"'] = &&str, ['{'] = &&obj, ['['] = &&arr,
            ['-'] = &&scalar, ['0' ... '9'] = &&scalar,
            ['t'] = &&scalar, ['f'] = &&scalar, ['n'] = &&scalar,
        };
        int c = peek();
        goto *dispatch[c < 0 ? 256 : c];
    str: {
            struct node *n = XALLOC((struct node *)NULL, sizeof *n);
            *n = (struct node){ .kind = K_FILE, .str = string() };
            return n;
        }
    obj:
        return object();
    arr:
        return array();
    scalar:
        die("numbers, booleans and null are not allowed (byte offset %zu)", pos);
    other:
        bad("expected a value");
    }

    if (len >= 3 && !memcmp(buf, "\xEF\xBB\xBF", 3)) pos = 3;   /* optional BOM */
    ws();
    if (peek() != '{') {
        if (peek() < 0) bad("empty input");
        (void)value();
        die("the root of the document must be an object");
    }
    struct node *root = object();
    ws();
    if (pos != len) bad("trailing data");
    return root;
}

/* ---- file system ---- */

static void write_file(int dfd, const char *path, const struct jstr *name, const struct jstr *content, bool exec)
{
    int fd AUTOCLOSE = SYS(openat(dfd, name->data, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0666),
                           "%s/%s: cannot create", path, name->data);
    for (size_t off = 0; off < content->len;) {
        ssize_t w = write(fd, content->data + off, content->len - off);
        if (w < 0 && errno == EINTR) continue;
        SYS(w, "%s/%s: cannot write", path, name->data);
        off += (size_t)w;
    }
    if (exec) {
        struct stat st;
        SYS(fstat(fd, &st), "%s/%s: cannot stat", path, name->data);
        SYS(fchmod(fd, (st.st_mode & 07777) | 0111), "%s/%s: cannot chmod", path, name->data);
    }
}

static void apply(int dfd, const char *path, struct node *dir)
{
    /* Insertion sort by UTF-8 bytes (a nested function: no comparator pointer, no trampoline). */
    void sort(void)
    {
        for (size_t i = 1; i < dir->n; i++) {
            __auto_type m = dir->members[i];
            size_t j = i;
            while (j > 0) {
                __auto_type a = dir->members[j - 1].name;
                size_t l = a->len < m.name->len ? a->len : m.name->len;
                int c = memcmp(a->data, m.name->data, l);
                if (c < 0 || (c == 0 && a->len <= m.name->len)) break;
                dir->members[j] = dir->members[j - 1];
                j--;
            }
            dir->members[j] = m;
        }
    }
    sort();

    for (size_t i = 0; i < dir->n; i++) {
        const struct jstr *name = dir->members[i].name;
        struct node *v = dir->members[i].val;
        struct stat st;
        bool exists = fstatat(dfd, name->data, &st, AT_SYMLINK_NOFOLLOW) == 0;
        if (!exists && errno != ENOENT) die("%s/%s: cannot stat: %s", path, name->data, strerror(errno));
        bool isdir = exists && S_ISDIR(st.st_mode);

        if (v->kind == K_DIR) {
            if (exists && !isdir) SYS(unlinkat(dfd, name->data, 0), "%s/%s: cannot remove", path, name->data);
            if (!isdir) SYS(mkdirat(dfd, name->data, 0777), "%s/%s: cannot create directory", path, name->data);
            int sub AUTOCLOSE = SYS(openat(dfd, name->data, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC),
                                    "%s/%s: cannot open directory", path, name->data);
            size_t plen = strlen(path) + 1 + name->len + 1;
            char *sub_path AUTOFREE = XALLOC((char *)NULL, plen);
            snprintf(sub_path, plen, "%s/%s", path, name->data);
            apply(sub, sub_path, v);
            continue;
        }

        if (isdir) die("%s/%s: a directory is in the way", path, name->data);
        if (exists) SYS(unlinkat(dfd, name->data, 0), "%s/%s: cannot remove", path, name->data);
        switch (v->kind) {
        case K_FILE:   write_file(dfd, path, name, v->str, false); break;
        case K_SCRIPT: write_file(dfd, path, name, v->str, true); break;
        case K_LINK:
            SYS(symlinkat(v->str->data, dfd, name->data), "%s/%s: cannot create symlink", path, name->data);
            break;
        default: __builtin_unreachable();
        }
    }
}

int main(int argc, char **argv)
{
    (void)argv;
    if (argc > 1) {
        fputs("usage: json2dir < document.json\n", stderr);
        return 2;
    }
    size_t len;
    char *buf AUTOFREE = read_all(0, &len);
    check_utf8((const unsigned char *)buf, len);
    struct node *root = parse(buf, len);   /* parses and validates everything before any write */
    apply(AT_FDCWD, ".", root);
    return 0;
}
