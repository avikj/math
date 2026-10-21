/* lang.c — reading terms, compiling them to binder records, definitions,
 * reading values back, and the driver. */
#include "core.h"
#include <string.h>
#include <ctype.h>
#include <pthread.h>

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
        Node *items[256]; int n = 0;
        for (;;) {
            skip();
            if (!*src) die("unclosed (", NULL);
            if (*src == ')') { src++; break; }
            if (n == 256) die("list too long", NULL);
            items[n++] = read_node();
        }
        Node *x = nlist(n);
        memcpy(x->it, items, (size_t)n * sizeof(Node *));
        return x;
    }
    const char *b = src;
    while (*src && !isspace((unsigned char)*src) && *src != '(' && *src != ')' && *src != ';') src++;
    char buf[256]; size_t len = (size_t)(src - b); if (len > 255) len = 255;
    memcpy(buf, b, len); buf[len] = 0;
    return nsym(buf);
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
static const char *KW[] = { "lam", "thunk", "plam", "forall", "let", "app", "pair", "fst", "snd", "Pi", "Sigma", "U",
    "PathP", "@", "~", "/\\", "\\/", "=", "&", "|", "faceof", "sys", "sys0", "sys+", "sysmap", "comp", "Glue", "glue",
    "unglue", NULL };
static bool keyword(const char *s) { for (int i = 0; KW[i]; i++) if (!strcmp(KW[i], s)) return true; return false; }
static Node *param_name(Node *p) { return p->list ? p->it[0] : p; }

static Node *ds(Node *t);
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
        if (!strcmp(k, "U")) { Node *r = nlist(1); r->it[0] = nsym("U"); return r; }
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

/* ---------------- definitions ---------------- */
enum { G_DEF, G_AXIOM, G_INPUT };
typedef struct {
    char *name; int kind;
    Syn *body; int nslots; int *uses;
    Cell *res;                       /* holds the definition's value; a use copies it */
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
    G[nG].name = strdup(name); G[nG].kind = kind;
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

/* ---------------- compiling: binder levels and lifting ---------------- */
typedef struct { const char *name; int level, slot; } Bind;
typedef struct {
    int is_thunk, scope_start, nslots, ucap;
    int *uses;
    int nenv, ecap;
    Node **env_nodes; int *env_slots; Syn **env_syns;
} Level;
#define MAXB 8192
#define MAXL 1024
static Bind binds[MAXB]; static int nbinds;
static Level levels[MAXL]; static int nlevels;
static const char *shadow[MAXB]; static int nshadow;

static Syn *syn(int tag, int n) { Syn *s = calloc(1, sizeof(Syn)); s->tag = tag; s->n = n; s->k = calloc((size_t)n + 1, sizeof(Syn *)); return s; }
static Bind *lookup(const char *name) { for (int i = nbinds - 1; i >= 0; i--) if (!strcmp(binds[i].name, name)) return &binds[i]; return NULL; }
static void push_bind(const char *name, int level, int slot) { if (nbinds == MAXB) die("too many binders", NULL); binds[nbinds++] = (Bind){ name, level, slot }; }
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
        shadow[nshadow++] = t->it[1]->s; r = maxlev(t->it[2]); nshadow--; return r;
    }
    if (!strcmp(h, "let")) {
        r = maxlev(t->it[2]);
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
    if (nlevels == MAXL) die("binders nested too deeply", NULL);
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
        Syn *r = syn(G[g].kind == G_AXIOM ? S_AXIOM : S_GLOBAL, 0); r->id = g;
        return r;
    }
    const char *h = t->it[0]->s;
    if (!strcmp(h, "lam")) return compile_record(t->it[1], t->it[2], false);
    if (!strcmp(h, "thunk")) return compile_record(NULL, t->it[1], true);
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
    levels[0] = (Level){ 0 };
    Syn *s = compile(ds(t));
    *nslots = levels[0].nslots; *uses = levels[0].uses;
    if (!*uses) *uses = calloc(1, sizeof(int));
    nlevels = 0;
    return s;
}
static Port build_top(Node *t) { int ns; int *u; Syn *s = compile_top(t, &ns, &u); return top_build(s, ns, u); }

/* ---------------- reading back ---------------- */
#define RUN_LIMIT 50000000L
typedef struct { Dim d; char name[16]; } DimShow;
static DimShow dshow[4096]; static int ndshow, dcount; static long vcount;
static char dimbuf[8][24]; static int dimbuf_i;
static const char *dim_name(Dim d) {
    for (int i = ndshow - 1; i >= 0; i--) if (dshow[i].d == d) return dshow[i].name;
    char *b = dimbuf[dimbuf_i++ & 7]; snprintf(b, 24, "#%u", d); return b;
}
static Cell *observe(Port prov) {
    Cell *r = cell(O_ROOT, 1);
    link(prov, P(r, 0));
    if (!net_observe(r, RUN_LIMIT)) return NULL;
    return PC(r->port[0]);
}
static long unfolding[256]; static int nunfold;
static void rb(FILE *o, Port prov);
static Port apply_fresh(Port f, long *name) {
    *name = fresh_var("x", vcount++);
    Cell *v = cell(V_NVAR, 1); v->a = (uint64_t)*name;
    Cell *a = cell(O_APP, 3);
    link(f, P(a, 0)); link(P(v, 0), P(a, 1));
    return P(a, 2);
}
static void rb_fields(FILE *o, const char *h, Cell *c, int from) {
    fprintf(o, "(%s", h);
    for (int k = from; k < c->n; k++) { fputc(' ', o); rb(o, c->port[k]); }
    fputc(')', o);
}
static void rb(FILE *o, Port prov) {
    Cell *c = observe(prov);
    if (!c) { fputs("<pending>", o); return; }
    long nm;
    switch (c->kind) {
    case V_LAM: {
        Port b = apply_fresh(P(c, 0), &nm);
        fprintf(o, "(lam %s ", name_of(nm)); rb(o, b); fputc(')', o); return;
    }
    case V_PI: case V_SIGMA: {
        Port B = c->port[2];
        fprintf(o, "(%s ", c->kind == V_PI ? "Pi" : "Sigma");
        rb(o, c->port[1]);
        Port b = apply_fresh(B, &nm);
        fprintf(o, " %s ", name_of(nm)); rb(o, b); fputc(')', o); return;
    }
    case V_PAIR: rb_fields(o, "pair", c, 1); return;
    case V_U: fputs("U", o); return;
    case V_PATHP: rb_fields(o, "PathP", c, 1); return;
    case V_PLAM: {
        DimShow *d = &dshow[ndshow++]; d->d = (Dim)c->a; snprintf(d->name, sizeof d->name, "i%d", dcount++);
        fprintf(o, "(plam %s ", d->name); rb(o, c->port[1]); fputc(')', o);
        ndshow--; return;
    }
    case V_IV: dnf_print(o, c->p, false, dim_name); return;
    case V_FACE: dnf_print(o, c->p, true, dim_name); return;
    case V_SYS: {
        Clause **cl = c->p;
        fputs("(sys", o);
        for (int k = 1; k < c->n; k++) { fputs(" (", o); clause_print(o, cl[k - 1], dim_name); fputc(' ', o); rb(o, c->port[k]); fputc(')', o); }
        fputc(')', o); return;
    }
    case V_GLUE: rb_fields(o, "Glue", c, 1); return;
    case V_GLUEV: rb_fields(o, "glue", c, 1); return;
    case V_NVAR: fputs(name_of((long)c->a), o); return;
    case V_NAPP: fputc('(', o); rb(o, c->port[1]); fputc(' ', o); rb(o, c->port[2]); fputc(')', o); return;
    case V_NFST: rb_fields(o, "fst", c, 1); return;
    case V_NSND: rb_fields(o, "snd", c, 1); return;
    case V_NPAPP: fputs("(@ ", o); rb(o, c->port[1]); fputc(' ', o); dnf_print(o, c->p, false, dim_name); fputc(')', o); return;
    case V_NCOMP: rb_fields(o, "comp", c, 1); return;
    case V_NUNGLUE: rb_fields(o, "unglue", c, 1); return;
    case V_GLOBAL: {
        /* a definition reads back as its value; within its own value it is its name */
        long g = (long)c->a;
        for (int i = 0; i < nunfold; i++) if (unfolding[i] == g) { fputs(name_of(g), o); return; }
        Port v = global_copy(g);
        if (!v || nunfold == 256) { fputs(name_of(g), o); return; }
        unfolding[nunfold++] = g;
        rb(o, v);
        nunfold--;
        return;
    }
    }
    fputs("<?>", o);
}
static char *readback(Node *t, long *steps, long *erased) {
    char *buf; size_t len;
    FILE *o = open_memstream(&buf, &len);
    ndshow = 0; dcount = 0; vcount = 0;
    long s0 = stat_steps, e0 = stat_kind[O_ERA];
    rb(o, build_top(t));
    fclose(o);
    if (steps) *steps = stat_steps - s0;
    if (erased) *erased = stat_kind[O_ERA] - e0;
    return buf;
}

/* ---------------- the driver ---------------- */
static int failures, passes;
static void toplevel(Node *f) {
    if (!f->list || f->n == 0 || f->it[0]->list) die("top-level form expected", NULL);
    const char *h = f->it[0]->s;
    if (!strcmp(h, "def")) {
        if (f->n != 3) die("(def name term)", NULL);
        long g = add_global(f->it[1]->s, G_DEF);
        int ns; int *u;
        Syn *s = compile_top(f->it[2], &ns, &u);
        G[g].body = s; G[g].nslots = ns; G[g].uses = u;
        link(top_build(s, ns, u), P(G[g].res, 0));
    } else if (!strcmp(h, "axiom")) {
        for (int i = 1; i < f->n; i++) add_global(f->it[i]->s, G_AXIOM);
    } else if (!strcmp(h, "input")) {
        for (int i = 1; i < f->n; i++) add_global(f->it[i]->s, G_INPUT);
    } else if (!strcmp(h, "supply")) {
        if (f->n != 3) die("(supply name term)", NULL);
        long g = global_lookup(f->it[1]->s);
        if (g < 0 || G[g].kind != G_INPUT || G[g].res->port[0]) die("not an unsupplied input:", f->it[1]->s);
        link(build_top(f->it[2]), P(G[g].res, 0));
        for (int i = 0; i < G[g].npark; i++) net_push(G[g].park_o[i], G[g].park_v[i]);
        G[g].npark = 0;
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
    printf("%d passed, %d failed; %ld interaction steps; %ld cells live\n", passes, failures, stat_steps, stat_cells);
    return failures ? 1 : 0;
}
