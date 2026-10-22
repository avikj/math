/* lang.c — reading terms, compiling them to binder records, definitions,
 * reading values back, and the driver. */
#include "core.h"
#include <string.h>
#include <ctype.h>
#include <pthread.h>

/* grow an array to hold at least n elements */
#define GROW(arr, cap, n) do { if ((size_t)(n) > (size_t)(cap)) { size_t nc_ = (cap) ? (size_t)(cap) * 2 : 16; while (nc_ < (size_t)(n)) nc_ *= 2; (arr) = realloc((arr), nc_ * sizeof *(arr)); (cap) = nc_; } } while (0)

static void die(const char *m, const char *x) { fprintf(stderr, "error: %s%s%s\n", m, x ? " " : "", x ? x : ""); exit(1); }

/* ---------------- s-expressions ---------------- */
typedef struct Node { int list; char *s; int n; struct Node **it; } Node;
static Node *nsym(const char *s) { Node *x = calloc(1, sizeof(Node)); x->s = strdup(s); return x; }
static Node *nlist(int n) { Node *x = calloc(1, sizeof(Node)); x->list = 1; x->n = n; x->it = calloc((size_t)n + 1, sizeof(Node *)); return x; }
static Node *nl2(const char *h, Node *a) { Node *x = nlist(2); x->it[0] = nsym(h); x->it[1] = a; return x; }
static Node *nl3(const char *h, Node *a, Node *b) { Node *x = nlist(3); x->it[0] = nsym(h); x->it[1] = a; x->it[2] = b; return x; }
static Node *nl4(const char *h, Node *a, Node *b, Node *c) { Node *x = nlist(4); x->it[0] = nsym(h); x->it[1] = a; x->it[2] = b; x->it[3] = c; return x; }

static const char *src;
static void skip(void) {
    for (;;) {
        while (*src && isspace((unsigned char)*src)) src++;
        if (*src == ';') { while (*src && *src != '\n') src++; continue; }
        return;
    }
}
static Node *read_node(void) {
    skip();
    if (!*src) return NULL;
    if (*src == ')') die("unexpected )", NULL);
    if (*src == '(') {
        src++;
        Node **items = NULL; size_t cap = 0; int n = 0;
        for (;;) {
            skip();
            if (!*src) die("unclosed (", NULL);
            if (*src == ')') { src++; break; }
            GROW(items, cap, (size_t)n + 1);
            items[n++] = read_node();
        }
        Node *x = nlist(n);
        if (n) memcpy(x->it, items, (size_t)n * sizeof(Node *));
        free(items);
        return x;
    }
    const char *b = src;
    while (*src && !isspace((unsigned char)*src) && *src != '(' && *src != ')' && *src != ';') src++;
    size_t len = (size_t)(src - b);
    char *buf = malloc(len + 1);
    memcpy(buf, b, len); buf[len] = 0;
    Node *x = nsym(buf);
    free(buf);
    return x;
}
static bool is(Node *x, const char *s) { return x && !x->list && strcmp(x->s, s) == 0; }
static void print_node(FILE *o, Node *x) {
    if (!x->list) { fputs(x->s, o); return; }
    fputc('(', o);
    for (int i = 0; i < x->n; i++) { if (i) fputc(' ', o); print_node(o, x->it[i]); }
    fputc(')', o);
}
static bool node_eq(Node *a, Node *b) {
    if (a->list != b->list) return false;
    if (!a->list) return strcmp(a->s, b->s) == 0;
    if (a->n != b->n) return false;
    for (int i = 0; i < a->n; i++) if (!node_eq(a->it[i], b->it[i])) return false;
    return true;
}

/* ---------------- desugaring to the core forms ---------------- */
static const char *KW[] = { "lam", "thunk", "delay", "force", "case", "if", "the", "code", "plam", "forall", "let", "app", "pair", "fst", "snd", "Pi", "Sigma", "U",
    "PathP", "@", "~", "/\\", "\\/", "=", "&", "|", "faceof", "sys", "sys0", "sys+", "sysmap", "comp", "Glue", "glue",
    "unglue", NULL };
static bool keyword(const char *s) { for (int i = 0; KW[i]; i++) if (!strcmp(KW[i], s)) return true; return false; }
static Node *param_name(Node *p) { return p->list ? p->it[0] : p; }

/* data types (Scott encoding): a constructor C_i of a type with N
 * constructors, applied to its fields, is λh1..hN. h_i fields. A case gives
 * one handler per constructor; each branch is a thunk, forced only once
 * selected, so an unselected branch computes nothing. */
typedef struct { char *name; int type, index, arity; } Con;
static Con *CONS; static size_t capcons; static int ncons;
static int *TYPE_N; static size_t captypes; static int ntypes;
static Con *con_lookup(const char *s) { for (int i = ncons - 1; i >= 0; i--) if (!strcmp(CONS[i].name, s)) return &CONS[i]; return NULL; }

static Node *ds(Node *t);
static Node *to_code(Node *t);
static Node *ds_lam(Node **ps, int np, Node *body, const char *b) {
    if (np == 0) return ds(body);
    return nl3(b, param_name(ps[0]), ds_lam(ps + 1, np - 1, body, b));
}
static void arity(Node *t, int n) { if (t->n != n + 1) { print_node(stderr, t); die("wrong number of operands in", t->it[0]->s); } }
static Node *ds(Node *t) {
    if (!t->list) return t;
    if (t->n == 0) die("empty list", NULL);
    Node *h = t->it[0];
    if (!h->list && keyword(h->s)) {
        const char *k = h->s;
        if (!strcmp(k, "delay")) { arity(t, 1); return nl2("thunk", ds(t->it[1])); }
        if (!strcmp(k, "force")) { arity(t, 1); return nl2("force", ds(t->it[1])); }
        if (!strcmp(k, "if")) {
            arity(t, 3);
            return nl2("force", nl3("app", nl3("app", ds(t->it[1]), nl2("thunk", ds(t->it[2]))), nl2("thunk", ds(t->it[3]))));
        }
        if (!strcmp(k, "case")) {
            if (t->n < 3) die("(case e branch...)", NULL);
            int type = -1; Node *dflt = NULL;
            for (int i = 2; i < t->n; i++) {
                Node *br = t->it[i];
                if (!br->list || br->n != 2) die("malformed case branch", NULL);
                if (!br->it[0]->list && is(br->it[0], "_")) { dflt = br->it[1]; continue; }
                if (!br->it[0]->list || br->it[0]->n < 1) die("case branch pattern must be (C x...)", NULL);
                Con *c = con_lookup(br->it[0]->it[0]->s);
                if (!c) die("unknown constructor", br->it[0]->it[0]->s);
                if (type >= 0 && c->type != type) die("constructors of different types in one case:", c->name);
                type = c->type;
                if (br->it[0]->n - 1 != c->arity) die("wrong number of fields for", c->name);
            }
            if (type < 0) die("case needs at least one constructor branch", NULL);
            int N = TYPE_N[type];
            Node *e = ds(t->it[1]);
            for (int ci = 0; ci < N; ci++) {
                Con *c = NULL;
                for (int j = 0; j < ncons; j++) if (CONS[j].type == type && CONS[j].index == ci) c = &CONS[j];
                Node *pat = NULL, *body = NULL;
                for (int i = 2; i < t->n; i++) {
                    Node *br = t->it[i];
                    if (br->it[0]->list && !strcmp(br->it[0]->it[0]->s, c->name)) { pat = br->it[0]; body = br->it[1]; }
                }
                if (!body) { if (!dflt) die("case misses constructor", c->name); body = dflt; }
                Node *hnd = nl2("thunk", ds(body));
                for (int f = c->arity; f >= 1; f--) {
                    Node *x = pat ? pat->it[f] : NULL;
                    char nm[32];
                    if (!x) { snprintf(nm, sizeof nm, "%%_%d", f); x = nsym(nm); }
                    hnd = nl3("lam", x, hnd);
                }
                e = nl3("app", e, hnd);
            }
            return nl2("force", e);
        }
        if (!strcmp(k, "lam") || !strcmp(k, "plam")) { if (t->n < 3) die("binder without body", NULL); return ds_lam(t->it + 1, t->n - 2, t->it[t->n - 1], k); }
        if (!strcmp(k, "forall")) { arity(t, 2); return nl3("forall", t->it[1], ds(t->it[2])); }
        if (!strcmp(k, "let")) { arity(t, 3); return nl4("let", t->it[1], ds(t->it[2]), ds(t->it[3])); }
        if (!strcmp(k, "Pi") || !strcmp(k, "Sigma")) {
            Node *x, *A, *B;
            if (t->n == 4) { x = t->it[1]; A = t->it[2]; B = t->it[3]; }
            else if (t->n == 3 && t->it[1]->list && t->it[1]->n == 2) { x = t->it[1]->it[0]; A = t->it[1]->it[1]; B = t->it[2]; }
            else die("malformed", k);
            return nl3(k, ds(A), nl3("lam", x, ds(B)));
        }
        if (!strcmp(k, "sys")) {
            Node *r = nlist(1); r->it[0] = nsym("sys0");
            for (int i = t->n - 1; i >= 1; i--) {
                Node *br = t->it[i];
                if (!br->list || br->n != 2) die("malformed system branch", NULL);
                r = nl4("sys+", ds(br->it[0]), nl2("thunk", ds(br->it[1])), r);
            }
            return r;
        }
        if (!strcmp(k, "sys+")) { arity(t, 3); return nl4("sys+", ds(t->it[1]), nl2("thunk", ds(t->it[2])), ds(t->it[3])); }
        if (!strcmp(k, "U")) { if (t->n > 2) die("(U [level])", NULL); return t; }   /* the level is kept for codes */
        if (!strcmp(k, "the")) { arity(t, 2); return nl3("the", ds(t->it[1]), ds(t->it[2])); }
        if (!strcmp(k, "code")) { arity(t, 1); return to_code(ds(t->it[1])); }
        if (!strcmp(k, "/\\") || !strcmp(k, "\\/") || !strcmp(k, "&") || !strcmp(k, "|")) {
            if (t->n < 3) die("too few operands for", k);
            Node *r = ds(t->it[1]);
            for (int i = 2; i < t->n; i++) r = nl3(k, r, ds(t->it[i]));
            return r;
        }
        static const struct { const char *k; int n; } AR[] = { { "pair", 2 }, { "fst", 1 }, { "snd", 1 }, { "PathP", 3 },
            { "~", 1 }, { "=", 2 }, { "faceof", 1 }, { "sysmap", 2 }, { "comp", 3 }, { "Glue", 2 }, { "glue", 2 },
            { "unglue", 2 }, { "app", 2 }, { NULL, 0 } };
        if (!strcmp(k, "@")) { if (t->n != 3 && t->n != 5) die("@ takes a path, an interval and optionally both endpoints", NULL); }
        else for (int i = 0; AR[i].k; i++) if (!strcmp(AR[i].k, k)) arity(t, AR[i].n);
        Node *r = nlist(t->n); r->it[0] = h;
        for (int i = 1; i < t->n; i++) r->it[i] = (!strcmp(k, "=") && i == 2) ? t->it[i] : ds(t->it[i]);
        return r;
    }
    Node *f = ds(h);
    for (int i = 1; i < t->n; i++) f = nl3("app", f, ds(t->it[i]));
    return f;
}

/* ---------------- codes of source terms ----------------
 * (code t) writes the code of a source term as data: constructor
 * applications of lib/code.ctt, variables as de Bruijn indices over one
 * context of term and dimension variables, checked definitions as signature
 * indices. This is reading source text, not inspecting a value. */
static const char **cscope; static size_t capcscope; static int ncscope;
static char **CHECKED; static size_t capchecked; static int nchecked;
static Node *numeral(int n) { Node *x = nsym("nz"); for (int i = 0; i < n; i++) x = nl3("app", nsym("ns"), x); return x; }
static Node *capp1(const char *c, Node *a) { return nl3("app", nsym(c), a); }
static Node *capp2(const char *c, Node *a, Node *b) { return nl3("app", nl3("app", nsym(c), a), b); }
static Node *capp3(const char *c, Node *a, Node *b, Node *d) { return nl3("app", capp2(c, a, b), d); }
static Node *code_bound(const char *x, Node *body) {
    GROW(cscope, capcscope, (size_t)ncscope + 1);
    cscope[ncscope++] = x;
    Node *r = to_code(body);
    ncscope--;
    return r;
}
static Node *to_code(Node *t) {
    if (!t->list) {
        const char *s = t->s;
        if (!strcmp(s, "0")) return nsym("ci0");
        if (!strcmp(s, "1")) return nsym("ci1");
        if (!strcmp(s, "tt")) return nsym("cftt");
        if (!strcmp(s, "ff")) return nsym("cfff");
        if (!strcmp(s, "U")) return capp1("cuniv", nsym("nz"));
        for (int i = ncscope - 1; i >= 0; i--) if (!strcmp(cscope[i], s)) return capp1("cvar", numeral(ncscope - 1 - i));
        for (int i = 0; i < nchecked; i++) if (!strcmp(CHECKED[i], s)) return capp1("cglob", numeral(i));
        die("code: not a bound variable or checked definition:", s);
    }
    const char *h = t->it[0]->s;
    if (!strcmp(h, "lam")) return capp1("clam", code_bound(t->it[1]->s, t->it[2]));
    if (!strcmp(h, "plam")) return capp1("cplam", code_bound(t->it[1]->s, t->it[2]));
    if (!strcmp(h, "forall")) return capp1("cforall", code_bound(t->it[1]->s, t->it[2]));
    if (!strcmp(h, "let")) return capp2("clet", to_code(t->it[2]), code_bound(t->it[1]->s, t->it[3]));
    if (!strcmp(h, "app")) return capp2("capp", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "pair")) return capp2("cpair", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "fst")) return capp1("cfst", to_code(t->it[1]));
    if (!strcmp(h, "snd")) return capp1("csnd", to_code(t->it[1]));
    if (!strcmp(h, "Pi") || !strcmp(h, "Sigma")) {
        Node *B = t->it[2];   /* (lam x body) */
        return capp2(!strcmp(h, "Pi") ? "cpi" : "csigma", to_code(t->it[1]), code_bound(B->it[1]->s, B->it[2]));
    }
    if (!strcmp(h, "U")) return capp1("cuniv", numeral(t->n == 2 ? atoi(t->it[1]->s) : 0));
    if (!strcmp(h, "PathP")) return capp3("cpathp", to_code(t->it[1]), to_code(t->it[2]), to_code(t->it[3]));
    if (!strcmp(h, "@")) return capp2("cpapp", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "~")) return capp1("cneg", to_code(t->it[1]));
    if (!strcmp(h, "/\\")) return capp2("cmeet", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "\\/")) return capp2("cjoin", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "=")) return capp1(is(t->it[2], "0") ? "ceq0" : "ceq1", to_code(t->it[1]));
    if (!strcmp(h, "&")) return capp2("cfand", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "|")) return capp2("cfor", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "sys0")) return nsym("csys0");
    if (!strcmp(h, "sys+")) return capp3("csysc", to_code(t->it[1]), to_code(t->it[2]->it[1]), to_code(t->it[3]));
    if (!strcmp(h, "comp")) return capp3("ccomp", to_code(t->it[1]), to_code(t->it[2]), to_code(t->it[3]));
    if (!strcmp(h, "Glue")) return capp2("cgluet", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "glue")) return capp2("cglue", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "unglue")) return capp2("cunglue", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "the")) return capp2("cann", to_code(t->it[2]), to_code(t->it[1]));
    die("code: no code for form", h);
    return NULL;
}

/* ---------------- definitions ---------------- */
enum { G_DEF, G_AXIOM, G_INPUT };
typedef struct {
    char *name; int kind;
    Syn *body; int nslots; int *uses;
    Cell *res;                       /* holds the definition's value; a use copies it */
    long tyg;                        /* an axiom's type: the global holding it, or -1 */
    Cell **park_o, **park_v; int npark, parkcap;
} Global;
static Global *G; static long nG, capG;
static char **fresh_names; static long nfresh, capfresh;
#define FRESH_BASE (1L << 40)

long global_lookup(const char *name) { for (long i = nG - 1; i >= 0; i--) if (!strcmp(G[i].name, name)) return i; return -1; }
const char *name_of(long id) { return id >= FRESH_BASE ? fresh_names[id - FRESH_BASE] : G[id].name; }
static long fresh_var(const char *pfx, long k) {
    if (nfresh == capfresh) { capfresh = capfresh ? capfresh * 2 : 64; fresh_names = realloc(fresh_names, (size_t)capfresh * sizeof(char *)); }
    char b[32]; snprintf(b, sizeof b, "%s%ld", pfx, k);
    fresh_names[nfresh] = strdup(b);
    return FRESH_BASE + nfresh++;
}
static long add_global(const char *name, int kind) {
    if (nG == capG) { capG = capG ? capG * 2 : 64; G = realloc(G, (size_t)capG * sizeof(Global)); }
    memset(&G[nG], 0, sizeof(Global));
    G[nG].name = strdup(name); G[nG].kind = kind; G[nG].tyg = -1;
    G[nG].res = cell(O_ROOT, 1);
    return nG++;
}
Port global_copy(long g) {
    Cell *r = G[g].res;
    if (!r->port[0]) return 0;
    Cell *d = cell(O_DUP, 3);
    link(r->port[0], P(d, 0));
    link(P(d, 1), P(r, 0));
    return P(d, 2);
}
Cell *global_res(long g) { return G[g].res; }
static pthread_mutex_t park_mu = PTHREAD_MUTEX_INITIALIZER;
void global_park(long g, Cell *op, Cell *glob) {
    pthread_mutex_lock(&park_mu);
    Global *x = &G[g];
    if (x->npark == x->parkcap) {
        x->parkcap = x->parkcap ? x->parkcap * 2 : 8;
        x->park_o = realloc(x->park_o, (size_t)x->parkcap * sizeof(Cell *));
        x->park_v = realloc(x->park_v, (size_t)x->parkcap * sizeof(Cell *));
    }
    x->park_o[x->npark] = op; x->park_v[x->npark] = glob; x->npark++;
    pthread_mutex_unlock(&park_mu);
}

/* ---------------- identities on running computations ----------------
 * (identity L R p [n]): p g1..gn is a path L g1..gn = R g1..gn, at the
 * identity's own dimension i (fixed when declared). Following it is
 * transport along that path: an application of L to its n arguments
 * becomes the line (p g @ i) with its endpoints annotated, L g at 0 and
 * R g at 1. The line is a neutral path application, so nothing waits on
 * the evidence p: by the endpoint rule the 1-end is R g, the answer, and the
 * 0-end is L g, what was posed; only the witness (the interior) needs p.
 * All three are deferred: each is built when it is eliminated. The 0-end is
 * L's own run and does not follow L's identities again; the 1-end does, so
 * identities chain (and a declared cycle has no normal form).
 *
 * Applications of L collect their n arguments first (a curried application
 * is a value V_SITEF until saturated). */
typedef struct { long L, R, p; int n; Dim dim; } Ident;
static Ident *ID; static int nID, capID;
static int identities_on = 1;    /* off only while a defect reading runs the declaration without them */

static int arity_of(long L) { for (int i = 0; i < nID; i++) if (ID[i].L == L) return ID[i].n; return 0; }
static int pick(long L) { for (int i = 0; i < nID; i++) if (ID[i].L == L && ID[i].R != L) return i; return -1; }
static Port global_cell(long g) { Cell *c = cell(V_GLOBAL, 1); c->a = (uint64_t)g; return P(c, 0); }
static Port app_chain(Port f, const Port *args, int n, uint32_t x) {
    for (int k = 0; k < n; k++) { Cell *a = cell(O_APP, 3); a->x = x; link(f, P(a, 0)); link(args[k], P(a, 1)); f = P(a, 2); }
    return f;
}
static void split_n(Port prov, int m, Port *out) {
    for (int k = 0; k < m - 1; k++) { Cell *d = cell(O_DUP, 3); link(prov, P(d, 0)); out[k] = P(d, 1); prov = P(d, 2); }
    out[m - 1] = prov;
}
static Port defer_cell(long g, const Port *args, int n, uint32_t x) {
    Cell *d = cell(V_DEFER, n + 1); d->a = (uint64_t)g; d->x = x;
    for (int k = 0; k < n; k++) link(args[k], P(d, k + 1));
    return P(d, 0);
}
/* the application a deferred cell stands for, under its substitution */
static Port defer_build(Cell *v) {
    Port r = app_chain(global_cell((long)v->a), &v->port[1], v->n - 1, v->x);
    if (v->p) { Cell *c = cell(O_SUBST, 2); c->p = subst_retain(v->p); link(r, P(c, 0)); r = P(c, 1); }
    return r;
}
void defer_force(Cell *o, Cell *v) { link(defer_build(v), P(o, 0)); cell_free(v); }
/* identity id applied to all n arguments, at consumer */
static void follow(int id, const Port *args, int n, Port consumer) {
    Port *c = malloc((size_t)3 * n * sizeof(Port));
    for (int k = 0; k < n; k++) { Port three[3]; split_n(args[k], 3, three); c[k] = three[0]; c[n + k] = three[1]; c[2 * n + k] = three[2]; }
    Cell *l = cell(V_NPAPP, 5); l->x = 1; l->p = iv_atom(ID[id].dim);
    link(defer_cell(ID[id].p, c, n, X_SITED), P(l, 1));
    link(defer_cell(ID[id].L, c + n, n, X_SITED), P(l, 2));
    link(defer_cell(ID[id].R, c + 2 * n, n, 0), P(l, 3));
    Cell *u = cell(V_UNK, 1); link(P(u, 0), P(l, 4));
    link(P(l, 0), consumer);
    free(c);
}
bool site_open(Cell *o, Cell *v) {
    if (!identities_on || (o->x & X_SITED)) return false;
    long L = (long)v->a;
    int id = pick(L);
    if (id < 0) return false;
    int n = arity_of(L);
    if (n <= 1) { Port a = o->port[1]; follow(id, &a, 1, o->port[2]); }
    else {
        /* the first argument of a curried application: collect */
        Cell *sf = cell(V_SITEF, 2); sf->a = (uint64_t)L; sf->x = 1;
        link(o->port[1], P(sf, 1));
        link(P(sf, 0), o->port[2]);
    }
    cell_free(o); cell_free(v);
    return true;
}
void site_apply(Cell *o, Cell *v) {
    long L = (long)v->a;
    int k = (int)v->x, n = arity_of(L);
    Port arg = o->port[1], consumer = o->port[2];
    if (k + 1 < n) {
        Cell *sf = cell(V_SITEF, k + 2); sf->a = v->a; sf->x = (uint32_t)(k + 1);
        for (int j = 0; j < k; j++) link(v->port[1 + j], P(sf, 1 + j));
        link(arg, P(sf, 1 + k));
        link(P(sf, 0), consumer);
    } else {
        Port *args = malloc((size_t)n * sizeof(Port));
        for (int j = 0; j < k; j++) args[j] = v->port[1 + j];
        args[k] = arg;
        follow(pick(L), args, n, consumer);
        free(args);
    }
    cell_free(o); cell_free(v);
}
/* a copy of the value held by an observation cell */
static Port held_copy(Cell *r) {
    if (!r->port[0]) return 0;
    Cell *d = cell(O_DUP, 3);
    link(r->port[0], P(d, 0)); link(P(d, 1), P(r, 0));
    return P(d, 2);
}
/* the answer: every identity followed taken to its 1-end */
/* every identity's dimension sent to r (owned result; NULL when none) */
static Subst *identity_subst(const Dnf *r) {
    Subst *s = NULL;
    for (int i = 0; i < nID; i++) if (ID[i].dim) {
        Subst *t = s ? subst_with(s, ID[i].dim, r) : subst_single(ID[i].dim, r);
        subst_release(s); s = t;
    }
    return s;
}
static Subst *answer_subst(void) { Dnf *one = dnf_one(); Subst *s = identity_subst(one); dnf_release(one); return s; }
/* the empty substitution re-dispatches every neutral: a witness read after
 * its evidence arrived is read in normal form */
static Port reactivate(Port prov) { Cell *c = cell(O_SUBST, 2); c->p = subst_id(); link(prov, P(c, 0)); return P(c, 1); }
static Port as_answer(Port prov) {
    Subst *s = answer_subst();
    if (!s || !prov) return prov;
    Cell *c = cell(O_SUBST, 2); c->p = s;
    link(prov, P(c, 0));
    return P(c, 1);
}

/* ---------------- compiling: binder levels and lifting ---------------- */
typedef struct { const char *name; int level, slot; } Bind;
typedef struct {
    int is_thunk, scope_start, nslots, ucap;
    int *uses;
    int nenv, ecap;
    Node **env_nodes; int *env_slots; Syn **env_syns;
} Level;
static Bind *binds; static size_t capbinds; static int nbinds;
static Level *levels; static size_t caplevels; static int nlevels;
static const char **shadow; static size_t capshadow; static int nshadow;

static Syn *syn(int tag, int n) { Syn *s = calloc(1, sizeof(Syn)); s->tag = tag; s->n = n; s->k = calloc((size_t)n + 1, sizeof(Syn *)); return s; }
static Bind *lookup(const char *name) { for (int i = nbinds - 1; i >= 0; i--) if (!strcmp(binds[i].name, name)) return &binds[i]; return NULL; }
static void push_bind(const char *name, int level, int slot) { GROW(binds, capbinds, (size_t)nbinds + 1); binds[nbinds++] = (Bind){ name, level, slot }; }
static int new_slot(void) {
    Level *L = &levels[nlevels - 1];
    if (L->nslots == L->ucap) { L->ucap = L->ucap ? L->ucap * 2 : 8; L->uses = realloc(L->uses, (size_t)L->ucap * sizeof(int)); }
    L->uses[L->nslots] = 0;
    return L->nslots++;
}
static Syn *var_syn(int slot) { levels[nlevels - 1].uses[slot]++; Syn *s = syn(S_VAR, 0); s->slot = slot; return s; }
static bool constant_sym(const char *s) { return !strcmp(s, "0") || !strcmp(s, "1") || !strcmp(s, "tt") || !strcmp(s, "ff") || !strcmp(s, "U"); }

/* the outermost binder level a term refers to (-1: none) */
static int maxlev(Node *t) {
    if (!t->list) {
        if (constant_sym(t->s)) return -1;
        for (int i = nshadow - 1; i >= 0; i--) if (!strcmp(shadow[i], t->s)) return -1;
        Bind *b = lookup(t->s);
        return b ? b->level : -1;
    }
    const char *h = t->it[0]->s;
    int r = -1;
    if (!strcmp(h, "lam") || !strcmp(h, "plam") || !strcmp(h, "forall")) {
        GROW(shadow, capshadow, (size_t)nshadow + 1);
        shadow[nshadow++] = t->it[1]->s; r = maxlev(t->it[2]); nshadow--; return r;
    }
    if (!strcmp(h, "let")) {
        r = maxlev(t->it[2]);
        GROW(shadow, capshadow, (size_t)nshadow + 1);
        shadow[nshadow++] = t->it[1]->s; int r2 = maxlev(t->it[3]); nshadow--;
        return r > r2 ? r : r2;
    }
    for (int i = 1; i < t->n; i++) { int m = maxlev(t->it[i]); if (m > r) r = m; }
    return r;
}

static Syn *compile(Node *t);
/* a maximal subterm free of the current level becomes a port of its cell,
 * computed once in the enclosing level */
static int lift(Node *t) {
    int li = nlevels - 1;
    Level *L = &levels[li];
    for (int k = 0; k < L->nenv; k++) if (node_eq(L->env_nodes[k], t)) { return L->env_slots[k]; }
    int sb = L->scope_start, nb = nbinds, nsaved = nb - sb;
    Bind *saved = malloc((size_t)(nsaved + 1) * sizeof(Bind));
    memcpy(saved, binds + sb, (size_t)nsaved * sizeof(Bind));
    Level savedL = *L;
    nbinds = sb; nlevels = li;
    Syn *s = compile(t);
    levels[li] = savedL; nlevels = li + 1;
    memcpy(binds + sb, saved, (size_t)nsaved * sizeof(Bind)); nbinds = nb;
    free(saved);
    L = &levels[li];
    int slot = new_slot();
    if (L->nenv == L->ecap) {
        L->ecap = L->ecap ? L->ecap * 2 : 8;
        L->env_nodes = realloc(L->env_nodes, (size_t)L->ecap * sizeof(Node *));
        L->env_slots = realloc(L->env_slots, (size_t)L->ecap * sizeof(int));
        L->env_syns = realloc(L->env_syns, (size_t)L->ecap * sizeof(Syn *));
    }
    L->env_nodes[L->nenv] = t; L->env_slots[L->nenv] = slot; L->env_syns[L->nenv] = s; L->nenv++;
    return slot;
}
static Syn *compile_record(Node *param, Node *body, bool thunk) {
    GROW(levels, caplevels, (size_t)nlevels + 1);
    int li = nlevels++;
    levels[li] = (Level){ .is_thunk = thunk, .scope_start = nbinds };
    if (!thunk) push_bind(param->s, li, new_slot());
    Syn *b = compile(body);
    nbinds = levels[li].scope_start;
    Level L = levels[li];
    nlevels--;
    Record *r = calloc(1, sizeof(Record));
    r->nparam = thunk ? 0 : 1; r->nslots = L.nslots; r->nenv = L.nenv; r->env_slot = L.env_slots; r->uses = L.uses; r->body = b;
    Syn *s = syn(S_LAM, L.nenv);
    s->rec = r;
    for (int k = 0; k < L.nenv; k++) s->k[k] = L.env_syns[k];
    return s;
}
static Syn *compile_bound(int tag, Node *name, Node *body) {
    int slot = new_slot();
    push_bind(name->s, nlevels - 1, slot);
    Syn *s = syn(tag, 1); s->slot = slot; s->k[0] = compile(body);
    nbinds--;
    return s;
}
static Syn *compile_n(int tag, Node *t, int from, int n) {
    Syn *s = syn(tag, n);
    for (int i = 0; i < n; i++) s->k[i] = compile(t->it[from + i]);
    return s;
}
static Syn *compile(Node *t) {
    int li = nlevels - 1;
    if (li >= 1) {
        int m = maxlev(t);
        if (m >= 0 && m < li && (!levels[li].is_thunk || !t->list)) return var_syn(lift(t));
    }
    if (!t->list) {
        const char *s = t->s;
        if (!strcmp(s, "0")) return syn(S_IV0, 0);
        if (!strcmp(s, "1")) return syn(S_IV1, 0);
        if (!strcmp(s, "tt")) return syn(S_FTT, 0);
        if (!strcmp(s, "ff")) return syn(S_FFF, 0);
        if (!strcmp(s, "U")) return syn(S_U, 0);
        Bind *b = lookup(s);
        if (b) {
            if (b->level != li) die("internal: unlifted outer variable", s);
            return var_syn(b->slot);
        }
        long g = global_lookup(s);
        if (g < 0) die("unbound name", s);
        Syn *r = syn(G[g].kind == G_AXIOM ? S_AXIOM : S_GLOBAL, 0); r->id = g; r->slot = (int)G[g].tyg;
        return r;
    }
    const char *h = t->it[0]->s;
    if (!strcmp(h, "lam")) return compile_record(t->it[1], t->it[2], false);
    if (!strcmp(h, "thunk")) return compile_record(NULL, t->it[1], true);
    if (!strcmp(h, "force")) return compile_n(S_FORCE, t, 1, 1);
    if (!strcmp(h, "the")) return compile(t->it[2]);
    if (!strcmp(h, "plam")) return compile_bound(S_PLAM, t->it[1], t->it[2]);
    if (!strcmp(h, "forall")) return compile_bound(S_FORALL, t->it[1], t->it[2]);
    if (!strcmp(h, "let")) {
        Syn *v = compile(t->it[2]);
        Syn *s = compile_bound(S_LET, t->it[1], t->it[3]);
        s->k[1] = s->k[0]; s->k[0] = v; s->n = 2;
        return s;
    }
    if (!strcmp(h, "app")) return compile_n(S_APP, t, 1, 2);
    if (!strcmp(h, "pair")) return compile_n(S_PAIR, t, 1, 2);
    if (!strcmp(h, "fst")) return compile_n(S_FST, t, 1, 1);
    if (!strcmp(h, "snd")) return compile_n(S_SND, t, 1, 1);
    if (!strcmp(h, "Pi")) return compile_n(S_PI, t, 1, 2);
    if (!strcmp(h, "Sigma")) return compile_n(S_SIGMA, t, 1, 2);
    if (!strcmp(h, "U")) return syn(S_U, 0);
    if (!strcmp(h, "PathP")) return compile_n(S_PATHP, t, 1, 3);
    if (!strcmp(h, "@")) { Syn *s = compile_n(S_PAPP, t, 1, t->n - 1); s->x = t->n == 5; return s; }
    if (!strcmp(h, "~")) return compile_n(S_NEG, t, 1, 1);
    if (!strcmp(h, "/\\")) { Syn *s = compile_n(S_BIN, t, 1, 2); s->x = B_MEET; return s; }
    if (!strcmp(h, "\\/")) { Syn *s = compile_n(S_BIN, t, 1, 2); s->x = B_JOIN; return s; }
    if (!strcmp(h, "&")) { Syn *s = compile_n(S_BIN, t, 1, 2); s->x = B_FAND; return s; }
    if (!strcmp(h, "|")) { Syn *s = compile_n(S_BIN, t, 1, 2); s->x = B_FOR; return s; }
    if (!strcmp(h, "=")) {
        Syn *s = compile_n(S_FEQ, t, 1, 1);
        if (is(t->it[2], "0")) s->x = 0; else if (is(t->it[2], "1")) s->x = 1; else die("(= r e) needs e = 0 or 1", NULL);
        return s;
    }
    if (!strcmp(h, "faceof")) return compile_n(S_FACEOF, t, 1, 1);
    if (!strcmp(h, "sys0")) return syn(S_SYS0, 0);
    if (!strcmp(h, "sys+")) return compile_n(S_SYSCONS, t, 1, 3);
    if (!strcmp(h, "sysmap")) return compile_n(S_SYSMAP, t, 1, 2);
    if (!strcmp(h, "comp")) return compile_n(S_COMP, t, 1, 3);
    if (!strcmp(h, "Glue")) return compile_n(S_GLUE, t, 1, 2);
    if (!strcmp(h, "glue")) return compile_n(S_GLUEV, t, 1, 2);
    if (!strcmp(h, "unglue")) return compile_n(S_UNGLUE, t, 1, 2);
    die("unknown form", h);
    return NULL;
}
/* compile a closed top-level term into a frame of its own */
static Syn *compile_top(Node *t, int *nslots, int **uses) {
    nbinds = 0; nlevels = 1;
    GROW(levels, caplevels, 1);
    levels[0] = (Level){ 0 };
    Syn *s = compile(ds(t));
    *nslots = levels[0].nslots; *uses = levels[0].uses;
    if (!*uses) *uses = calloc(1, sizeof(int));
    nlevels = 0;
    return s;
}
static Port build_top(Node *t) { int ns; int *u; Syn *s = compile_top(t, &ns, &u); return top_build(s, ns, u); }

/* ---------------- reading back ---------------- */
typedef struct { Dim d; char name[16]; } DimShow;
static bool saw_identity;         /* readback named an identity's dimension */
static DimShow *dshow; static size_t capdshow; static int ndshow, dcount; static long vcount;
static char dimbuf[8][24]; static int dimbuf_i;
static const char *dim_name(Dim d) {
    for (int i = ndshow - 1; i >= 0; i--) if (dshow[i].d == d) return dshow[i].name;
    for (int i = 0; i < nID; i++) if (ID[i].dim == d) { saw_identity = true; char *b = dimbuf[dimbuf_i++ & 7]; snprintf(b, 24, "i:%s", name_of(ID[i].p)); return b; }
    char *b = dimbuf[dimbuf_i++ & 7]; snprintf(b, 24, "#%u", d); return b;
}
static Cell *observe(Port prov) {
    Cell *r = cell(O_ROOT, 1);
    link(prov, P(r, 0));
    if (!net_observe(r, -1)) return NULL;
    return PC(r->port[0]);
}
static long *unfolding; static size_t capunfold; static int nunfold;
static void rb(FILE *o, Port prov);
static Port apply_fresh(Port f, long *name) {
    *name = fresh_var("x", vcount++);
    Cell *v = cell(V_NVAR, 2); v->a = (uint64_t)*name;
    Cell *u = cell(V_UNK, 1); link(P(u, 0), P(v, 1));
    Cell *a = cell(O_APP, 3);
    link(f, P(a, 0)); link(P(v, 0), P(a, 1));
    return P(a, 2);
}
/* Reading a value back runs on an explicit stack of tasks, so the depth of a
 * value is bounded by memory, not by the native stack. */
/* a field is read from its cell when its turn comes: until then its wire may
 * still be rewritten by the reduction of the fields before it */
enum { TK_PORT, TK_FIELD, TK_STR, TK_BINDER, TK_POPDIM, TK_POPUNFOLD };
typedef struct { int kind; Port p; char *s; } Task;
static Task *tasks; static size_t captasks; static long ntasks;
static void push_task(int kind, Port p, char *s) { GROW(tasks, captasks, (size_t)ntasks + 1); tasks[ntasks++] = (Task){ kind, p, s }; }
static void push_str(const char *s) { push_task(TK_STR, 0, strdup(s)); }
static void push_port(Port p) { push_task(TK_PORT, p, NULL); }
static void push_field(Cell *c, int k) { push_task(TK_FIELD, P(c, k), NULL); }
static void push_binder(Cell *c, int k) { push_task(TK_BINDER, P(c, k), NULL); }
/* "(h f1 f2 ... )" over ports from..to-1 */
static void push_fields_to(FILE *o, const char *h, Cell *c, int from, int to) {
    fprintf(o, "(%s", h);
    push_str(")");
    for (int k = to - 1; k >= from; k--) { push_field(c, k); push_str(" "); }
}
static void push_fields(FILE *o, const char *h, Cell *c, int from) { push_fields_to(o, h, c, from, c->n); }
static char *dnf_string(const Dnf *d, bool face) {
    char *buf; size_t len; FILE *m = open_memstream(&buf, &len);
    dnf_print(m, d, face, dim_name); fclose(m);
    return buf;
}
static void rb_one(FILE *o, Port prov) {
    Cell *c = observe(prov);
    if (!c) { fputs("<pending>", o); return; }
    long nm;
    switch (c->kind) {
    case V_LAM: case V_SITEF: {
        Port b = apply_fresh(P(c, 0), &nm);
        fprintf(o, "(lam %s ", name_of(nm));
        push_str(")"); push_port(b);
        return;
    }
    case V_PI: case V_SIGMA:
        fprintf(o, "(%s ", c->kind == V_PI ? "Pi" : "Sigma");
        push_binder(c, 2); push_field(c, 1);
        return;
    case V_PAIR: push_fields(o, "pair", c, 1); return;
    case V_U: fputs("U", o); return;
    case V_PATHP: push_fields(o, "PathP", c, 1); return;
    case V_PLAM: {
        GROW(dshow, capdshow, (size_t)ndshow + 1);
        DimShow *d = &dshow[ndshow++]; d->d = (Dim)c->a; snprintf(d->name, sizeof d->name, "i%d", dcount++);
        fprintf(o, "(plam %s ", d->name);
        push_task(TK_POPDIM, 0, NULL); push_str(")"); push_field(c, 1);
        return;
    }
    case V_IV: dnf_print(o, c->p, false, dim_name); return;
    case V_FACE: dnf_print(o, c->p, true, dim_name); return;
    case V_SYS: {
        Dnf *cl = c->p;
        fputs("(sys", o);
        push_str(")");
        for (int k = c->n - 1; k >= 1; k--) {
            char *buf; size_t len; FILE *m = open_memstream(&buf, &len);
            fputs(" (", m); clause_print(m, cl->c[k - 1], dim_name); fputc(' ', m); fclose(m);
            push_str(")"); push_field(c, k); push_task(TK_STR, 0, buf);
        }
        return;
    }
    case V_GLUE: push_fields(o, "Glue", c, 1); return;
    case V_GLUEV: push_fields(o, "glue", c, 1); return;
    case V_NVAR: fputs(name_of((long)c->a), o); return;
    case V_NAPP:
        fputc('(', o);
        push_str(")"); push_field(c, 2); push_str(" "); push_field(c, 1);
        return;
    case V_NFST: push_fields_to(o, "fst", c, 1, 2); return;
    case V_NSND: push_fields_to(o, "snd", c, 1, 2); return;
    case V_NPAPP: {
        fputs("(@ ", o);
        push_str(")");
        if (c->x) { push_field(c, 3); push_str(" "); push_field(c, 2); push_str(" "); }
        char *r = dnf_string(c->p, false);
        push_task(TK_STR, 0, r); push_str(" "); push_field(c, 1);
        return;
    }
    case V_NCOMP: push_fields_to(o, "comp", c, 1, 4); return;
    case V_NUNGLUE: push_fields_to(o, "unglue", c, 1, 3); return;
    case V_DEFER: push_port(defer_build(c)); return;
    case V_UNK: fputs("?", o); return;
    case V_GLOBAL: {
        /* a definition reads back as its value; within its own value it is its name */
        long g = (long)c->a;
        for (int i = 0; i < nunfold; i++) if (unfolding[i] == g) { fputs(name_of(g), o); return; }
        Port v = global_copy(g);
        if (!v) { fputs(name_of(g), o); return; }
        GROW(unfolding, capunfold, (size_t)nunfold + 1);
        unfolding[nunfold++] = g;
        push_task(TK_POPUNFOLD, 0, NULL); push_port(v);
        return;
    }
    }
    fputs("<?>", o);
}
static void rb(FILE *o, Port prov) {
    long base = ntasks;
    push_port(prov);
    while (ntasks > base) {
        Task t = tasks[--ntasks];
        switch (t.kind) {
        case TK_STR: fputs(t.s, o); free(t.s); break;
        case TK_POPDIM: ndshow--; break;
        case TK_POPUNFOLD: nunfold--; break;
        case TK_FIELD: rb_one(o, PC(t.p)->port[PI(t.p)]); break;
        case TK_BINDER: {
            long nm;
            Port b = apply_fresh(PC(t.p)->port[PI(t.p)], &nm);
            fprintf(o, " %s ", name_of(nm));
            push_str(")"); push_port(b);
            break;
        }
        case TK_PORT: rb_one(o, t.p); break;
        }
    }
}
static char *read_port(Port prov) {
    char *buf; size_t len;
    FILE *o = open_memstream(&buf, &len);
    ndshow = 0; dcount = 0; vcount = 0;
    rb(o, prov);
    fclose(o);
    return buf;
}
/* does a value mention an identity's dimension? (read back a copy) */
static bool mentions_identity(Cell *holder) {
    saw_identity = false;
    free(read_port(held_copy(holder)));
    return saw_identity;
}
/* (the T t): t observed at its declared type T. When T itself moved along
 * identities' lines, the answer (at the lines' 1-end) is transported back
 * along T to T at the 0-end, so it inhabits the declaration. */
static Port typed_answer(Node *T, Node *t) {
    Cell *hT = cell(O_ROOT, 1);
    link(build_top(T), P(hT, 0));
    /* held at once: an unattached output port is rewritten by the rules */
    Cell *ht = cell(O_ROOT, 1);
    link(build_top(t), P(ht, 0));
    Subst *as = answer_subst();
    bool moved = as && mentions_identity(hT);
    subst_release(as);
    if (!moved) return as_answer(held_copy(ht));
    Port v = held_copy(ht);
    Dim j = fresh_dim();
    Dnf *aj = iv_atom(j), *nj = iv_neg(aj);
    Subst *back = identity_subst(nj);
    dnf_release(aj); dnf_release(nj);
    Cell *sb = cell(O_SUBST, 2); sb->p = back; link(held_copy(hT), P(sb, 0));
    Cell *mk = cell(O_MKPLAM, 2); mk->a = j; link(P(sb, 1), P(mk, 0));
    Cell *cp = cell(O_COMP, 4);
    Cell *s0 = cell(V_SYS, 1); s0->p = NULL;
    link(P(s0, 0), P(cp, 0)); link(P(mk, 1), P(cp, 1)); link(as_answer(v), P(cp, 2));
    return P(cp, 3);
}
/* A reading is taken over the complete normalization of what was posed
 * (5.13 concerns a normal form): pending pairs are reduced before and after,
 * so the counts do not depend on the schedule. */
static char *readback(Node *t, long *steps, long *erased) {
    bool reading = steps || erased;
    if (reading) net_drain();
    long s0 = stat_steps, e0 = stat_kind[O_ERA];
    Port v = (t->list && t->n == 3 && is(t->it[0], "the")) ? typed_answer(t->it[1], t->it[2]) : as_answer(build_top(t));
    char *buf = read_port(v);
    if (reading) net_drain();
    if (steps) *steps = stat_steps - s0;
    if (erased) *erased = stat_kind[O_ERA] - e0;
    return buf;
}

/* ---------------- the driver ---------------- */
static int failures, passes;
static void toplevel(Node *f);
static char **watch_name; static Cell **watch_root; static size_t capwn, capwr; static int nwatch;
static void toplevel(Node *f) {
    if (!f->list || f->n == 0 || f->it[0]->list) die("top-level form expected", NULL);
    const char *h = f->it[0]->s;
    if (!strcmp(h, "def")) {
        if (f->n != 3) die("(def name term)", NULL);
        /* a name declared earlier (forward reference, mutual recursion) is filled */
        long g = global_lookup(f->it[1]->s);
        bool fill_decl = g >= 0 && G[g].kind == G_INPUT && !G[g].res->port[0];
        if (fill_decl) G[g].kind = G_DEF; else g = add_global(f->it[1]->s, G_DEF);
        int ns; int *u;
        Syn *s = compile_top(f->it[2], &ns, &u);
        G[g].body = s; G[g].nslots = ns; G[g].uses = u;
        link(top_build(s, ns, u), P(G[g].res, 0));
        if (fill_decl) { for (int i = 0; i < G[g].npark; i++) net_push(G[g].park_o[i], G[g].park_v[i]); G[g].npark = 0; }
    } else if (!strcmp(h, "checked") || !strcmp(h, "check") || !strcmp(h, "check-fail")) {
        /* the checker (lib/check.ctt), a term, run on the codes of T and t
         * against the signature of the definitions checked so far */
        bool define = !strcmp(h, "checked"), expect = strcmp(h, "check-fail") != 0;
        int at = define ? 2 : 1;
        if (f->n != at + 2) die(define ? "(checked name T t)" : "(check T t)", NULL);
        Node *T = f->it[at], *t = f->it[at + 1];
        char sig[32]; snprintf(sig, sizeof sig, "%%sig%d", nchecked);
        Node *sign = nchecked ? nsym(sig) : nsym("lnil");
        Node *cT = to_code(ds(T)), *ct = to_code(ds(t));
        Node *q = nl4("chk-def", sign, cT, ct);
        long steps;
        char *r = readback(q, &steps, NULL), *tr = readback(nsym("true"), NULL, NULL);
        bool ok = !strcmp(r, tr) == expect;
        if (ok) passes++; else failures++;
        printf("%s: %s ", ok ? "ok" : "FAIL", expect ? "checks" : "rejected");
        if (define) printf("%s", f->it[1]->s); else print_node(stdout, t);
        printf("   [%ld steps]\n", steps);
        free(r); free(tr);
        if (define && ok) {
            Node *d = nlist(3); d->it[0] = nsym("def"); d->it[1] = f->it[1]; d->it[2] = t;
            toplevel(d);
            char sig2[32]; snprintf(sig2, sizeof sig2, "%%sig%d", nchecked + 1);
            Node *sd = nlist(3); sd->it[0] = nsym("def"); sd->it[1] = nsym(sig2); sd->it[2] = nl4("sig-add", sign, cT, ct);
            GROW(CHECKED, capchecked, (size_t)nchecked + 1);
            CHECKED[nchecked++] = strdup(f->it[1]->s);
            toplevel(sd);
        }
    } else if (!strcmp(h, "declare")) {
        for (int i = 1; i < f->n; i++) add_global(f->it[i]->s, G_INPUT);
    } else if (!strcmp(h, "data")) {
        /* (data T (C f...) ...): constructors as definitions */
        if (f->n < 3) die("(data T (C f...) ...)", NULL);
        int type = ntypes++;
        GROW(TYPE_N, captypes, (size_t)ntypes);
        int N = f->n - 2;
        TYPE_N[type] = N;
        for (int i = 0; i < N; i++) {
            Node *cd = f->it[i + 2];
            if (!cd->list || cd->n < 1) die("constructor must be (C f...)", NULL);
            GROW(CONS, capcons, (size_t)ncons + 1);
            CONS[ncons++] = (Con){ strdup(cd->it[0]->s), type, i, cd->n - 1 };
        }
        for (int i = 0; i < N; i++) {
            Node *cd = f->it[i + 2];
            int ar = cd->n - 1;
            Node *app = NULL;
            char nm[32];
            snprintf(nm, sizeof nm, "%%h%d", i); app = nsym(nm);
            for (int k = 1; k <= ar; k++) app = nl3("app", app, cd->it[k]);
            Node *body = app;
            for (int j = N - 1; j >= 0; j--) { snprintf(nm, sizeof nm, "%%h%d", j); body = nl3("lam", nsym(nm), body); }
            for (int k = ar; k >= 1; k--) body = nl3("lam", cd->it[k], body);
            Node *def = nlist(3); def->it[0] = nsym("def"); def->it[1] = cd->it[0]; def->it[2] = body;
            toplevel(def);
        }
    } else if (!strcmp(h, "axiom")) {
        /* name, or (name T): a constant of type T; its neutral carries T */
        for (int i = 1; i < f->n; i++) {
            Node *e = f->it[i];
            if (!e->list) { add_global(e->s, G_AXIOM); continue; }
            if (e->n != 2 || e->it[0]->list) die("(axiom name... (name T)...)", NULL);
            char *tn = malloc(strlen(e->it[0]->s) + 8); sprintf(tn, "%%type-%s", e->it[0]->s);
            Node *d = nlist(3); d->it[0] = nsym("def"); d->it[1] = nsym(tn); d->it[2] = e->it[1];
            toplevel(d);
            long tg = global_lookup(tn);
            long g = add_global(e->it[0]->s, G_AXIOM);
            G[g].tyg = tg;
            free(tn);
        }
    } else if (!strcmp(h, "input")) {
        for (int i = 1; i < f->n; i++) add_global(f->it[i]->s, G_INPUT);
    } else if (!strcmp(h, "supply")) {
        if (f->n != 3) die("(supply name term)", NULL);
        long g = global_lookup(f->it[1]->s);
        if (g < 0 || G[g].kind != G_INPUT || G[g].res->port[0]) die("not an unsupplied input:", f->it[1]->s);
        link(build_top(f->it[2]), P(G[g].res, 0));
        for (int i = 0; i < G[g].npark; i++) net_push(G[g].park_o[i], G[g].park_v[i]);
        G[g].npark = 0;
    } else if (!strcmp(h, "identity")) {
        if (f->n != 4 && f->n != 5) die("(identity L R p [n])", NULL);
        long L = global_lookup(f->it[1]->s), R = global_lookup(f->it[2]->s), pp = global_lookup(f->it[3]->s);
        if (L < 0 || R < 0 || pp < 0) die("identity names must be definitions or inputs", NULL);
        int n = 0;
        if (f->n == 5) n = atoi(f->it[4]->s);
        else for (Syn *b = G[L].body; b && b->tag == S_LAM && b->rec->nparam == 1; b = b->rec->body) n++;
        if (n < 1) n = 1;
        for (int i = 0; i < nID; i++) if (ID[i].L == L && ID[i].n != n) die("identities of one definition take the same number of arguments:", f->it[1]->s);
        if (nID == capID) { capID = capID ? capID * 2 : 8; ID = realloc(ID, (size_t)capID * sizeof(Ident)); }
        ID[nID] = (Ident){ L, R, pp, n, fresh_dim() };
        nID++;
    } else if (!strcmp(h, "watch")) {
        if (f->n != 3) die("(watch name term)", NULL);
        GROW(watch_name, capwn, (size_t)nwatch + 1); GROW(watch_root, capwr, (size_t)nwatch + 1);
        watch_name[nwatch] = strdup(f->it[1]->s);
        watch_root[nwatch] = cell(O_ROOT, 1);
        link(build_top(f->it[2]), P(watch_root[nwatch], 0));
        nwatch++;
    } else if (!strcmp(h, "same-watch")) {
        if (f->n != 3 && f->n != 4) die("(same-watch name term [0|1])", NULL);
        int at0 = f->n == 4 && is(f->it[3], "0");
        int w = -1;
        for (int i = 0; i < nwatch; i++) if (!strcmp(watch_name[i], f->it[1]->s)) w = i;
        if (w < 0) die("no such watch", f->it[1]->s);
        char *buf; size_t len;
        FILE *o = open_memstream(&buf, &len);
        ndshow = 0; dcount = 0; vcount = 0;
        /* the watch keeps its value; read at the identities' 1-end (the answer)
         * or their 0-end (what was posed) */
        Port hv = held_copy(watch_root[w]);
        if (at0) {
            Dnf *zero = dnf_zero();
            Subst *z = identity_subst(zero);
            dnf_release(zero);
            if (z) { Cell *c = cell(O_SUBST, 2); c->p = z; link(hv, P(c, 0)); hv = P(c, 1); }
        } else hv = as_answer(hv);
        rb(o, hv);
        fclose(o);
        char *b = readback(f->it[2], NULL, NULL);
        if (strcmp(buf, b)) { failures++; printf("FAIL: watch %s\n  left:  %s\n  right: %s\n", f->it[1]->s, buf, b); }
        else { passes++; printf("ok: watch %s\n", f->it[1]->s); }
        free(buf); free(b);
    } else if (!strcmp(h, "witness") || !strcmp(h, "witness-watch")) {
        /* the value itself: a line (or cube) in the identities' dimensions,
         * from what was posed (0) to the answer (1) */
        Port v;
        if (!strcmp(h, "witness")) v = build_top(f->it[1]);
        else {
            int w = -1;
            for (int i = 0; i < nwatch; i++) if (!strcmp(watch_name[i], f->it[1]->s)) w = i;
            if (w < 0) die("no such watch", f->it[1]->s);
            v = held_copy(watch_root[w]);
        }
        char *r = read_port(reactivate(v));
        print_node(stdout, f->it[1]); printf("\n  witness: %s\n", r);
        free(r);
    } else if (!strcmp(h, "defect")) {
        /* the same declaration from the same (warm) state without and with its
         * identities: the difference in length and in effect */
        identities_on = 0;
        free(readback(f->it[1], NULL, NULL));
        long s0, e0, s1, e1;
        char *a0 = readback(f->it[1], &s0, &e0);
        identities_on = 1;
        char *a1 = readback(f->it[1], &s1, &e1);
        print_node(stdout, f->it[1]);
        printf("\n  without identities: %s   [%ld steps, %ld erasures]\n  with identities:    %s   [%ld steps, %ld erasures]\n  defect: %+ld steps, %+ld erasures\n",
               a0, s0, e0, a1, s1, e1, s1 - s0, e1 - e0);
        free(a0); free(a1);
    } else if (!strcmp(h, "show")) {
        long steps, erased;
        char *r = readback(f->it[1], &steps, &erased);
        /* length: every interaction; effect: the interactions that forget (erasures) */
        print_node(stdout, f->it[1]); printf("\n  = %s   [%ld steps, %ld erasures]\n", r, steps, erased);
        free(r);
    } else if (!strcmp(h, "same")) {
        if (f->n != 3) die("(same t u)", NULL);
        char *a = readback(f->it[1], NULL, NULL), *b = readback(f->it[2], NULL, NULL);
        if (strcmp(a, b)) {
            failures++;
            printf("FAIL: "); print_node(stdout, f->it[1]); printf("\n  left:  %s\n  right: %s\n", a, b);
        } else { passes++; printf("ok: "); print_node(stdout, f->it[1]); printf("\n"); }
        free(a); free(b);
    } else die("unknown top-level form", h);
}
static char *slurp(const char *path) {
    FILE *f = fopen(path, "rb"); if (!f) die("cannot open", path);
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    char *b = malloc((size_t)n + 1); size_t got = fread(b, 1, (size_t)n, f); b[got] = 0; fclose(f);
    return b;
}
int main(int argc, char **argv) {
    const char *w = getenv("CUBICAL_WORKERS");
    net_start(w ? atoi(w) : 0);
    for (int i = 1; i < argc; i++) {
        char *text = slurp(argv[i]);
        src = text;
        Node *f;
        while ((f = read_node())) toplevel(f);
    }
    /* steps performed so far: a reading only when the workload has normalized (show, defect) */
    printf("%d passed, %d failed; %ld interaction steps performed; %ld cells live; %ld payloads live\n", passes, failures, stat_steps, stat_cells, stat_payloads);
    return failures ? 1 : 0;
}
