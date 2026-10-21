/* read.c — text into term records (read.h).
 *
 * The reader is an input boundary: it builds the same records the machine
 * runs, by the constructors of term.h, and decides nothing. Syntax is one
 * s-expression per CCHM former:
 *
 *   x                         a variable or a definition in scope
 *   (U n)                     universe
 *   (Pi (x A) B)  (Pi m n (x A) B)        Π, optionally with its two levels
 *   (Sigma (x A) B)  (Sigma m n (x A) B)  Σ
 *   (lam (x A) b)  (lam m (x A) b)        λ, optionally with its domain level
 *   (f a b ...)               application
 *   (pair a b) (fst p) (snd p)
 *   (Path (i) A a b)          PathP, A under i
 *   (plam (i) t)              path abstraction
 *   (papp (i) A a b p r)      path application, with the path's type
 *   (comp n (i) A phi u a0)   composition; A and u under i
 *   (Glue n A phi T e) (glue n A phi T e t a) (unglue n A phi T e v)
 *   (sys (phi t) ...)         system
 *
 *   intervals: 0 1 i (not r) (and r s) (or r s)
 *   faces:     true false (= r 0) (= r 1) (/\ phi psi) (\/ phi psi)
 *
 *   program items: (def name A t) a definition (its body may mention name),
 *                  (axiom name A) an opaque constant.
 */
#include "read.h"
#include "eval.h"
#include <ctype.h>

/* ---------------- s-expressions ---------------- */
typedef struct Sx { bool list; const char *atom; size_t alen; struct Sx **kids; size_t n; } Sx;
typedef struct { const char *p; const char *err; } Rd;

static void skip(Rd *r) {
    for (;;) {
        while (isspace((unsigned char)*r->p)) r->p++;
        if (*r->p == ';') { while (*r->p && *r->p != '\n') r->p++; continue; }
        return;
    }
}
static Sx *sx_new(void) { Sx *s = calloc(1, sizeof *s); require(s, "out of memory"); return s; }
static Sx *parse(Rd *r) {
    skip(r);
    if (!*r->p) { r->err = "unexpected end of input"; return NULL; }
    if (*r->p == ')') { r->err = "unexpected ')'"; return NULL; }
    Sx *s = sx_new();
    if (*r->p == '(') {
        r->p++; s->list = true;
        for (;;) {
            skip(r);
            if (*r->p == ')') { r->p++; return s; }
            Sx *k = parse(r); if (!k) return NULL;
            s->kids = realloc(s->kids, (s->n + 1) * sizeof *s->kids); require(s->kids, "out of memory");
            s->kids[s->n++] = k;
        }
    }
    s->atom = r->p;
    while (*r->p && !isspace((unsigned char)*r->p) && *r->p != '(' && *r->p != ')' && *r->p != ';') r->p++;
    s->alen = (size_t)(r->p - s->atom);
    return s;
}
static void sx_free(Sx *s) { if (!s) return; for (size_t i = 0; i < s->n; i++) sx_free(s->kids[i]); free(s->kids); free(s); }
static bool is(const Sx *s, const char *a) { return s && !s->list && s->alen == strlen(a) && !memcmp(s->atom, a, s->alen); }
static bool head(const Sx *s, const char *a) { return s && s->list && s->n && is(s->kids[0], a); }

/* ---------------- scope ---------------- */
typedef enum { B_TERM, B_DIM, B_GLOBAL } BKind;
typedef struct Bind { const char *name; size_t len; BKind kind; uint64_t id; const struct Bind *next; } Bind;
struct Reader { Bind *globals; const char *err; char msg[256]; };

static jmp_buf *tl_fail;
static Reader *tl_rd;
static _Noreturn void fail(const Sx *at, const char *what) {
    if (at && !at->list) snprintf(tl_rd->msg, sizeof tl_rd->msg, "%s at '%.*s'", what, (int)at->alen, at->atom);
    else snprintf(tl_rd->msg, sizeof tl_rd->msg, "%s", what);
    longjmp(*tl_fail, 1);
}
static const Bind *lookup(const Bind *env, const Sx *s) {
    for (const Bind *b = env; b; b = b->next) if (b->len == s->alen && !memcmp(b->name, s->atom, s->alen)) return b;
    for (const Bind *b = tl_rd->globals; b; b = b->next) if (b->len == s->alen && !memcmp(b->name, s->atom, s->alen)) return b;
    return NULL;
}
static uint64_t number(const Sx *s) {
    if (!s || s->list || !s->alen) fail(s, "a number");
    uint64_t v = 0;
    for (size_t i = 0; i < s->alen; i++) { if (!isdigit((unsigned char)s->atom[i])) fail(s, "a number"); v = v * 10 + (uint64_t)(s->atom[i] - '0'); }
    return v;
}
static void want(const Sx *s, size_t n, const char *form) { if (!s->list || s->n != n) fail(s->n ? s->kids[0] : s, form); }

/* ---------------- intervals and faces ---------------- */
static IntervalId interval(const Sx *s, const Bind *env) {
    if (is(s, "0")) return iv_zero();
    if (is(s, "1")) return iv_one();
    if (!s->list) {
        const Bind *b = lookup(env, s);
        if (!b || b->kind != B_DIM) fail(s, "a dimension");
        return iv_var(b->id);
    }
    if (head(s, "not")) { want(s, 2, "(not r)"); return iv_negate(interval(s->kids[1], env)); }
    if (head(s, "and")) { want(s, 3, "(and r s)"); return iv_meet(interval(s->kids[1], env), interval(s->kids[2], env)); }
    if (head(s, "or")) { want(s, 3, "(or r s)"); return iv_join(interval(s->kids[1], env), interval(s->kids[2], env)); }
    fail(s->n ? s->kids[0] : s, "an interval");
    return 0;
}
static FaceId face(const Sx *s, const Bind *env) {
    if (is(s, "true")) return fc_true();
    if (is(s, "false")) return fc_false();
    if (head(s, "=")) {
        want(s, 3, "(= r 0|1)");
        int eps = is(s->kids[2], "1") ? 1 : is(s->kids[2], "0") ? 0 : -1;
        if (eps < 0) fail(s->kids[2], "an endpoint 0 or 1");
        return family_call(F_FCEND, interval(s->kids[1], env), (uint64_t)eps);
    }
    if (head(s, "/\\")) { want(s, 3, "(/\\ phi psi)"); return fc_meet(face(s->kids[1], env), face(s->kids[2], env)); }
    if (head(s, "\\/")) { want(s, 3, "(\\/ phi psi)"); return fc_join(face(s->kids[1], env), face(s->kids[2], env)); }
    fail(s->n ? s->kids[0] : s, "a face");
    return 0;
}

/* ---------------- terms ---------------- */
static RefId term(const Sx *s, const Bind *env);
static Bind bind_term(const Bind *env, const Sx *name, RefId type, TermVarId *out) {
    if (name->list) fail(name, "a variable name");
    *out = declare_term(type, fc_true());
    return (Bind){ name->atom, name->alen, B_TERM, *out, env };
}
static Bind bind_dim(const Bind *env, const Sx *binder, DimVarId *out) {
    if (!binder->list || binder->n != 1 || binder->kids[0]->list) fail(binder, "a dimension binder (i)");
    *out = declare_dim();
    return (Bind){ binder->kids[0]->atom, binder->kids[0]->alen, B_DIM, *out, env };
}
/* (x A) */
static void binder(const Sx *b, const Bind *env, const Sx **name, RefId *type) {
    if (!b->list || b->n != 2) fail(b, "a binder (x A)");
    *name = b->kids[0]; *type = term(b->kids[1], env);
}
static RefId term_binder_form(Tag tag, const Sx *s, const Bind *env) {
    /* (F (x A) B) or (F m n (x A) B); λ: (lam m (x A) b) */
    size_t at = 1; uint64_t m = LEVEL_NONE, n = LEVEL_NONE;
    if (s->n == 5 && tag != T_LAM) { m = number(s->kids[1]); n = number(s->kids[2]); at = 3; }
    else if (s->n == 4 && tag == T_LAM) { m = number(s->kids[1]); at = 2; }
    else if (s->n != 3) fail(s->kids[0], "a binder form");
    const Sx *name; RefId A; binder(s->kids[at], env, &name, &A);
    TermVarId x; Bind inner = bind_term(env, name, A, &x);
    RefId body = term(s->kids[at + 1], &inner);
    return MK(tag, 0, levels_pack(m, tag == T_LAM ? LEVEL_NONE : n), x, A, body);
}
/* the former a cmatch tests: var, a term former's name, iv or face */
static uint64_t former(const Sx *s) {
    static const struct { const char *name; uint64_t tag; } F[] = {
        { "var", 0 }, { "U", T_UNIVERSE }, { "Pi", T_PI }, { "Sigma", T_SIGMA }, { "lam", T_LAM }, { "app", T_APP },
        { "pair", T_PAIR }, { "fst", T_FST }, { "snd", T_SND }, { "Path", T_PATH }, { "plam", T_PLAM }, { "papp", T_PAPP },
        { "Glue", T_GLUE_TYPE }, { "glue", T_GLUE_INTRO }, { "unglue", T_UNGLUE }, { "comp", T_COMP }, { "sys", T_SYSTEM },
        { "global", T_GLOBAL }, { "Code", T_CODE }, { "quote", T_QUOTE }, { "qiv", T_QIV }, { "qfc", T_QFC },
        { "cmatch", T_CMATCH }, { "cinst", T_CINST }, { "ceq", T_CEQ }, { "cent", T_CENT }, { "cfcend", T_CFCEND },
        { "cunfold", T_CUNFOLD },
        { "iv", T_QIV }, { "face", T_QFC } };
    if (s->list) fail(s, "a former name");
    for (size_t q = 0; q < sizeof F / sizeof F[0]; q++)
        if (strlen(F[q].name) == s->alen && !memcmp(F[q].name, s->atom, s->alen)) return F[q].tag;
    fail(s, "a former name");
}
static RefId term(const Sx *s, const Bind *env) {
    if (!s->list) {
        const Bind *b = lookup(env, s);
        if (!b) fail(s, "an unbound name");
        if (b->kind == B_TERM) return ref_var(b->id);
        if (b->kind == B_GLOBAL) return global_ref(b->id);
        fail(s, "a dimension where a term is expected");
    }
    if (!s->n) fail(s, "an empty form");
    if (head(s, "U")) { want(s, 2, "(U n)"); return mk_universe(number(s->kids[1])); }
    if (head(s, "Pi")) return term_binder_form(T_PI, s, env);
    if (head(s, "Sigma")) return term_binder_form(T_SIGMA, s, env);
    if (head(s, "lam")) return term_binder_form(T_LAM, s, env);
    if (head(s, "pair")) { want(s, 3, "(pair a b)"); return mk_pair(term(s->kids[1], env), term(s->kids[2], env)); }
    if (head(s, "fst")) { want(s, 2, "(fst p)"); return mk_fst(term(s->kids[1], env)); }
    if (head(s, "snd")) { want(s, 2, "(snd p)"); return mk_snd(term(s->kids[1], env)); }
    if (head(s, "Path")) {
        want(s, 5, "(Path (i) A a b)");
        DimVarId i; Bind inner = bind_dim(env, s->kids[1], &i);
        return mk_path(i, term(s->kids[2], &inner), term(s->kids[3], env), term(s->kids[4], env));
    }
    if (head(s, "plam")) { want(s, 3, "(plam (i) t)"); DimVarId i; Bind inner = bind_dim(env, s->kids[1], &i); return mk_plam(i, term(s->kids[2], &inner)); }
    if (head(s, "papp")) {
        want(s, 7, "(papp (i) A a b p r)");
        DimVarId i; Bind inner = bind_dim(env, s->kids[1], &i);
        return mk_papp(i, term(s->kids[2], &inner), term(s->kids[3], env), term(s->kids[4], env), term(s->kids[5], env), interval(s->kids[6], env));
    }
    if (head(s, "comp")) {
        want(s, 7, "(comp n (i) A phi u a0)");
        uint64_t n = number(s->kids[1]);
        DimVarId i; Bind inner = bind_dim(env, s->kids[2], &i);
        return mk_comp_lv(n, i, term(s->kids[3], &inner), face(s->kids[4], env), term(s->kids[5], &inner), term(s->kids[6], env));
    }
    if (head(s, "Glue")) {
        want(s, 6, "(Glue n A phi T e)");
        return mk_glue_type_lv(number(s->kids[1]), term(s->kids[2], env), face(s->kids[3], env), term(s->kids[4], env), term(s->kids[5], env));
    }
    if (head(s, "glue")) {
        want(s, 8, "(glue n A phi T e t a)");
        return mk_glue_intro_lv(number(s->kids[1]), term(s->kids[2], env), face(s->kids[3], env), term(s->kids[4], env), term(s->kids[5], env), term(s->kids[6], env), term(s->kids[7], env));
    }
    if (head(s, "unglue")) {
        want(s, 7, "(unglue n A phi T e v)");
        return mk_unglue_lv(number(s->kids[1]), term(s->kids[2], env), face(s->kids[3], env), term(s->kids[4], env), term(s->kids[5], env), term(s->kids[6], env));
    }
    if (head(s, "sys")) {
        size_t n = s->n - 1;
        FaceId *fs = calloc(n ? n : 1, sizeof *fs); RefId *ts = calloc(n ? n : 1, sizeof *ts); require(fs && ts, "out of memory");
        for (size_t q = 0; q < n; q++) {
            const Sx *br = s->kids[1 + q];
            if (!br->list || br->n != 2) { free(fs); free(ts); fail(br, "a branch (phi t)"); }
            fs[q] = face(br->kids[0], env); ts[q] = term(br->kids[1], env);
        }
        RefId r = mk_system(n, fs, ts); free(fs); free(ts); return r;
    }
    /* codes (code.c) */
    if (head(s, "Code")) { want(s, 1, "(Code)"); return mk_tag(T_CODE, 0, LEVELS_NONE, 0, NULL, 0); }
    if (head(s, "quote")) { want(s, 2, "(quote t)"); return MK(T_QUOTE, 0, LEVELS_NONE, 0, term(s->kids[1], env)); }
    if (head(s, "qiv")) { want(s, 2, "(qiv r)"); return MK(T_QIV, 0, LEVELS_NONE, 0, interval(s->kids[1], env)); }
    if (head(s, "qfc")) { want(s, 2, "(qfc phi)"); return MK(T_QFC, 0, LEVELS_NONE, 0, face(s->kids[1], env)); }
    if (head(s, "cmatch")) {
        want(s, 5, "(cmatch former c h d)");
        return MK(T_CMATCH, former(s->kids[1]), LEVELS_NONE, 0, term(s->kids[2], env), term(s->kids[3], env), term(s->kids[4], env));
    }
    if (head(s, "cinst")) { want(s, 4, "(cinst k c a)"); return MK(T_CINST, number(s->kids[1]), LEVELS_NONE, 0, term(s->kids[2], env), term(s->kids[3], env)); }
    if (head(s, "ceq") || head(s, "cent")) {
        want(s, 5, "(ceq a b t f)");
        return MK(head(s, "ceq") ? T_CEQ : T_CENT, 0, LEVELS_NONE, 0, term(s->kids[1], env), term(s->kids[2], env), term(s->kids[3], env), term(s->kids[4], env));
    }
    if (head(s, "cfcend")) {
        want(s, 3, "(cfcend eps r)");
        uint64_t eps = number(s->kids[1]); if (eps > 1) fail(s->kids[1], "an endpoint 0 or 1");
        return MK(T_CFCEND, eps, LEVELS_NONE, 0, term(s->kids[2], env));
    }
    if (head(s, "cunfold")) { want(s, 4, "(cunfold c h d)"); return MK(T_CUNFOLD, 0, LEVELS_NONE, 0, term(s->kids[1], env), term(s->kids[2], env), term(s->kids[3], env)); }
    /* application, left to right */
    RefId f = term(s->kids[0], env);
    for (size_t q = 1; q < s->n; q++) f = mk_app(f, term(s->kids[q], env));
    return f;
}

/* ---------------- entry points ---------------- */
Reader *reader_new(void) { Reader *r = calloc(1, sizeof *r); require(r, "out of memory"); return r; }
void reader_free(Reader *r) {
    for (Bind *b = r->globals, *n; b; b = n) { n = (Bind *)b->next; free((char *)b->name); free(b); }
    free(r);
}
const char *reader_error(const Reader *r) { return r->msg[0] ? r->msg : NULL; }
static char *dup_name(const Sx *name) { char *nm = malloc(name->alen + 1); require(nm, "out of memory"); memcpy(nm, name->atom, name->alen); nm[name->alen] = 0; return nm; }
static void add_global(Reader *r, char *nm, size_t len, SymbolId s) {
    Bind *b = malloc(sizeof *b); require(b, "out of memory");
    *b = (Bind){ nm, len, B_GLOBAL, s, r->globals }; r->globals = b;
}
static bool guarded(Reader *r, Rd *rd, Sx **sx) {
    r->msg[0] = 0; *sx = parse(rd);
    if (!*sx) { snprintf(r->msg, sizeof r->msg, "%s", rd->err); return false; }
    return true;
}
bool reader_program(Reader *r, const char *src) {
    Rd rd = { src, NULL };
    for (;;) {
        skip(&rd);
        if (!*rd.p) return true;
        Sx *s; if (!guarded(r, &rd, &s)) return false;
        jmp_buf jb; jmp_buf *saved = tl_fail; Reader *savedr = tl_rd; tl_fail = &jb; tl_rd = r;
        volatile bool ok = true;
        if (setjmp(jb)) ok = false;
        else if (head(s, "def")) {
            want(s, 4, "(def name A t)");
            if (s->kids[1]->list) fail(s->kids[1], "a definition name");
            char *nm = dup_name(s->kids[1]);
            SymbolId sym = define_global(nm, set_make(NULL, 0), set_make(NULL, 0), term(s->kids[2], NULL));
            add_global(r, nm, s->kids[1]->alen, sym);
            set_global_body(sym, term(s->kids[3], NULL));
        } else if (head(s, "axiom")) {
            want(s, 3, "(axiom name A)");
            if (s->kids[1]->list) fail(s->kids[1], "an axiom name");
            char *nm = dup_name(s->kids[1]);
            add_global(r, nm, s->kids[1]->alen, define_global(nm, set_make(NULL, 0), set_make(NULL, 0), term(s->kids[2], NULL)));
        } else fail(s->n ? s->kids[0] : s, "a program item (def or axiom)");
        tl_fail = saved; tl_rd = savedr;
        sx_free(s);
        if (!ok) return false;
    }
}
RefId reader_term(Reader *r, const char *src) {
    Rd rd = { src, NULL };
    Sx *s; if (!guarded(r, &rd, &s)) return 0;
    jmp_buf jb; jmp_buf *saved = tl_fail; Reader *savedr = tl_rd; tl_fail = &jb; tl_rd = r;
    RefId t = 0;
    if (!setjmp(jb)) t = term(s, NULL);
    tl_fail = saved; tl_rd = savedr;
    sx_free(s);
    return t;
}
RefId reader_global(const Reader *r, const char *name) {
    for (const Bind *b = r->globals; b; b = b->next) if (b->len == strlen(name) && !memcmp(b->name, name, b->len)) return global_ref(b->id);
    return 0;
}
