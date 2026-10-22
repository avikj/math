#include <signal.h>
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
static const char *KW[] = { "%raw", "%welimP", "lam", "thunk", "delay", "force", "case", "elim", "if", "rec", "the", "code", "%data", "%con", "hcompD", "%transD", "%case", "%branches", "plam", "forall", "let", "app", "pair", "fst", "snd", "Pi", "Sigma", "U",
    "PathP", "@", "~", "/\\", "\\/", "=", "&", "|", "faceof", "sys", "sys0", "sys+", "sysmap", "comp", "Glue", "glue",
    "unglue", "%view", "%var", "%dim", "%ieq", "%feq", "%clauses", "%restrict", "%gval", "%gty", "%dtab", "%dent", "%abs", "%branch", "%clos", "%box", "%wsucc", "%weq", "%wlt", "%wadd", "%wmax", "%wsub", "%welim", NULL };
static bool keyword(const char *s) { for (int i = 0; KW[i]; i++) if (!strcmp(KW[i], s)) return true; return false; }
static Node *param_name(Node *p) { return p->list ? p->it[0] : p; }

/* data types: higher inductive types (Coquand–Huber–Mörtberg), declared by
 * (data ...) below; constructors are values, eliminated by %case */
ConInfo *CON; static size_t capcon; static int ncon;
DataInfo *DATA; static size_t capdata; static int ndata;
long case_hcomp_global = -1;
static int con_lookup(const char *s) { for (int i = ncon - 1; i >= 0; i--) if (!strcmp(CON[i].name, s)) return i; return -1; }
int con_index(const char *name) { return con_lookup(name); }
static int data_lookup(const char *s) { for (int i = ndata - 1; i >= 0; i--) if (!strcmp(DATA[i].name, s)) return i; return -1; }

static Node *ds(Node *t);
static Node *to_code(Node *t);
/* induction hypotheses: within a branch, (rec x) is the elimination of the
 * recursive field x by the same branches and motive; innermost branch first */
static const char **rs_field, **rs_ih; static size_t caprsf, caprsi; static int nrs, nih;
long global_lookup(const char *name);
static bool constant_sym(const char *s);
/* the local variables free in a desugared term, in order of first occurrence: symbols not
 * bound within it, not global, not constants, not keywords */
typedef struct { const char **v; int n, cap; } Names;
static bool names_has(const Names *s, const char *x) { for (int i = 0; i < s->n; i++) if (!strcmp(s->v[i], x)) return true; return false; }
static void names_add(Names *s, const char *x) { if (names_has(s, x)) return; if (s->n == s->cap) { s->cap = s->cap ? s->cap * 2 : 8; s->v = realloc(s->v, (size_t)s->cap * sizeof(char *)); } s->v[s->n++] = x; }
static void free_vars(Node *t, Names *bound, Names *out) {
    if (!t->list) {
        const char *x = t->s;
        if (names_has(bound, x) || constant_sym(x) || keyword(x) || global_lookup(x) >= 0) return;
        if ((x[0] >= '0' && x[0] <= '9') || x[0] == '-') return;
        names_add(out, x);
        return;
    }
    if (t->n == 0) return;
    Node *h = t->it[0];
    if (!h->list) {
        const char *k = h->s;
        if ((!strcmp(k, "lam") || !strcmp(k, "plam") || !strcmp(k, "forall")) && t->n == 3) {
            int save = bound->n; names_add(bound, param_name(t->it[1])->s);
            bool added = bound->n > save;
            free_vars(t->it[2], bound, out);
            if (added) bound->n = save;
            return;
        }
        if (!strcmp(k, "let") && t->n == 4) {
            free_vars(t->it[2], bound, out);
            int save = bound->n; names_add(bound, t->it[1]->s);
            bool added = bound->n > save;
            free_vars(t->it[3], bound, out);
            if (added) bound->n = save;
            return;
        }
        int from = 1;
        if (!strcmp(k, "%con") || !strcmp(k, "%data") || !strcmp(k, "%transD")) from = 2;
        if (!strcmp(k, "%branches")) from = 4;
        if (!strcmp(k, "=")) { free_vars(t->it[1], bound, out); return; }
        for (int i = from; i < t->n; i++) free_vars(t->it[i], bound, out);
        return;
    }
    for (int i = 0; i < t->n; i++) free_vars(t->it[i], bound, out);
}
/* does t refer to the free name x (not rebound inside)? */
static bool mentions_name(Node *t, const char *x) {
    if (!t->list) return !strcmp(t->s, x);
    if (t->n == 0) return false;
    if (!t->it[0]->list) {
        const char *k = t->it[0]->s;
        if ((!strcmp(k, "lam") || !strcmp(k, "plam") || !strcmp(k, "forall")) && t->n >= 3) {
            for (int i = 1; i < t->n - 1; i++) if (!strcmp(param_name(t->it[i])->s, x)) return false;
            return mentions_name(t->it[t->n - 1], x);
        }
        if (!strcmp(k, "let") && t->n == 4) return mentions_name(t->it[2], x) || (strcmp(t->it[1]->s, x) && mentions_name(t->it[3], x));
    }
    for (int i = 0; i < t->n; i++) if (mentions_name(t->it[i], x)) return true;
    return false;
}
static bool mentions_rec(Node *t, Node **names, int n) {
    if (!t->list) return false;
    if (t->n == 2 && is(t->it[0], "rec") && !t->it[1]->list)
        for (int i = 0; i < n; i++) if (names[i] && !strcmp(names[i]->s, t->it[1]->s)) return true;
    for (int i = 0; i < t->n; i++) if (mentions_rec(t->it[i], names, n)) return true;
    return false;
}
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
        /* a term already desugared (an annotated code) */
        if (!strcmp(k, "%raw")) { arity(t, 1); return t->it[1]; }
        if (!strcmp(k, "force")) { arity(t, 1); return nl2("force", ds(t->it[1])); }
        if (!strcmp(k, "rec")) {
            arity(t, 1);
            if (!t->it[1]->list) for (int i = nrs - 1; i >= 0; i--) if (!strcmp(rs_field[i], t->it[1]->s)) return nl2("force", nsym(rs_ih[i]));
            die("rec of a name that is not a recursive field of its branch:", t->it[1]->list ? "(...)" : t->it[1]->s);
        }
        if (!strcmp(k, "if")) {
            /* elimination of Bool */
            arity(t, 3);
            Node *c = nlist(4); c->it[0] = nsym("case"); c->it[1] = t->it[1];
            Node *bt = nlist(2); bt->it[0] = nlist(1); bt->it[0]->it[0] = nsym("true"); bt->it[1] = t->it[2];
            Node *bf = nlist(2); bf->it[0] = nlist(1); bf->it[0]->it[0] = nsym("false"); bf->it[1] = t->it[3];
            c->it[2] = bt; c->it[3] = bf;
            return ds(c);
        }
        if (!strcmp(k, "case") || !strcmp(k, "elim")) {
            /* (case e branch...) and (elim P e branch...): one branch per constructor,
             * a λ over its fields and dimensions returning a thunk of the body */
            bool el = !strcmp(k, "elim");
            int first = el ? 3 : 2;
            if (t->n < first + 1) die(el ? "(elim P e branch...)" : "(case e branch...)", NULL);
            int d = -1; Node *dflt = NULL; Node *dname = NULL;
            if (t->n == first + 1 && !t->it[first]->list && data_lookup(t->it[first]->s) >= 0 && DATA[data_lookup(t->it[first]->s)].ncons == 0) {
                /* a type with no constructors: (case e D), (elim P e D), no branches */
                int d0 = data_lookup(t->it[first]->s);
                Node *B = nlist(4); B->it[0] = nsym("%branches"); B->it[1] = nsym(DATA[d0].name); B->it[2] = nsym("0"); B->it[3] = nsym("0");
                Node *env = nl3("lam", nsym("%g"), nsym("%g"));
                if (el) { Node *r = nlist(5); r->it[0] = nsym("%case"); r->it[1] = B; r->it[2] = ds(t->it[1]); r->it[3] = env; r->it[4] = ds(t->it[2]); return r; }
                return nl4("%case", B, env, ds(t->it[1]));
            }
            for (int i = first; i < t->n; i++) {
                Node *br = t->it[i];
                if (!br->list || br->n != 2) die("malformed case branch", NULL);
                if (!br->it[0]->list) {
                    /* a default branch: (_ body), or (x body) with x the scrutinee, rebuilt from the
                     * fields of whichever constructor it is */
                    dflt = br->it[1]; dname = is(br->it[0], "_") ? NULL : br->it[0];
                    continue;
                }
                if (!br->it[0]->list || br->it[0]->n < 1) die("case branch pattern must be (C x...)", NULL);
                int c = con_lookup(br->it[0]->it[0]->s);
                if (c < 0) die("unknown constructor", br->it[0]->it[0]->s);
                if (d >= 0 && CON[c].data != d) die("constructors of different types in one case:", CON[c].name);
                d = CON[c].data;
                if (br->it[0]->n - 1 != CON[c].nfields + CON[c].ndims) die("wrong number of fields and dimensions for", CON[c].name);
            }
            if (d < 0) die("case needs at least one constructor branch", NULL);
            int N = DATA[d].ncons;
            Node *B = nlist(N + 4); B->it[0] = nsym("%branches"); B->it[1] = nsym(DATA[d].name);
            uint64_t mask = 0;
            Node **hb = calloc((size_t)N + 1, sizeof(Node *));
            Names fv = { 0 };
            for (int ci = 0; ci < N; ci++) {
                ConInfo *c = &CON[DATA[d].cons[ci]];
                Node *pat = NULL, *body = NULL;
                for (int i = first; i < t->n; i++) {
                    Node *br = t->it[i];
                    if (br->it[0]->list && !strcmp(br->it[0]->it[0]->s, c->name)) { pat = br->it[0]; body = br->it[1]; }
                }
                /* within branch (C x...) the scrutinee is (C x...): a branch mentioning the
                 * scrutinee's name rebuilds it from its fields instead of a copy of it */
                Node *scr = t->it[first - 1];
                if (body && !scr->list && !dname && mentions_name(body, scr->s)) {
                    bool shadow = false;
                    for (int q = 1; pat && q < pat->n; q++) if (!pat->it[q]->list && !strcmp(pat->it[q]->s, scr->s)) shadow = true;
                    if (!shadow) {
                        static int nsc;
                        int na = c->nfields + c->ndims;
                        if (!pat) { pat = nlist(na + 1); pat->it[0] = nsym(c->name); for (int q = 0; q < na; q++) { char nm[32]; snprintf(nm, sizeof nm, "%%sc%d", nsc++); pat->it[q + 1] = nsym(nm); } }
                        Node *rebuilt = nsym(c->name);
                        Node *np2 = nlist(na + 1); np2->it[0] = pat->it[0];
                        Node *pre = NULL;
                        for (int q = 0; q < na; q++) {
                            Node *x = pat->it[q + 1];
                            if (!x->list && !strcmp(x->s, "_")) { char nm[32]; snprintf(nm, sizeof nm, "%%sc%d", nsc++); x = nsym(nm); }
                            np2->it[q + 1] = x; rebuilt = nl3("app", rebuilt, x);
                        }
                        (void)pre;
                        pat = np2;
                        Node *lb = nlist(4); lb->it[0] = nsym("let"); lb->it[1] = scr; lb->it[2] = rebuilt; lb->it[3] = body; body = lb;
                    }
                }
                if (!body) {
                    if (!dflt) die("case misses constructor", c->name);
                    body = dflt;
                    if (dname) {
                        static int ndf;
                        int na = c->nfields + c->ndims;
                        pat = nlist(na + 1); pat->it[0] = nsym(c->name);
                        Node *rebuilt = nsym(c->name);
                        for (int q = 0; q < na; q++) { char nm[32]; snprintf(nm, sizeof nm, "%%df%d", ndf++); pat->it[q + 1] = nsym(nm); rebuilt = nl3("app", rebuilt, nsym(nm)); }
                        body = nlist(4); body->it[0] = nsym("let"); body->it[1] = dname; body->it[2] = rebuilt; body->it[3] = dflt;
                    }
                }
                /* a branch takes the induction hypotheses of its recursive fields when its body
                 * uses one: λ fields, hypotheses, dimensions, of a thunk of the body, so nothing
                 * in an unselected branch, and no recursive call lifted out of it, is computed */
                Node *rn[64]; int nr = 0;
                if (pat) for (int f = 0; f < c->nfields; f++) if (c->recmask >> f & 1) rn[nr++] = pat->it[f + 1];
                bool ih = nr && mentions_rec(body, rn, nr);
                char ihn[64][24];
                int save = nrs;
                if (ih) {
                    mask |= 1ull << ci;
                    for (int q = 0; q < nr; q++) {
                        snprintf(ihn[q], sizeof ihn[q], "%%ih%d", nih++);
                        GROW(rs_field, caprsf, (size_t)nrs + 1); GROW(rs_ih, caprsi, (size_t)nrs + 1);
                        rs_field[nrs] = rn[q]->s; rs_ih[nrs] = ihn[q]; nrs++;
                    }
                }
                Node *hnd = nl2("thunk", ds(body));
                nrs = save;
                for (int f = c->nfields + c->ndims; f > c->nfields; f--) {
                    Node *x = pat ? pat->it[f] : NULL;
                    char nm[32];
                    if (!x) { snprintf(nm, sizeof nm, "%%_%d", f); x = nsym(nm); }
                    hnd = nl3("lam", x, hnd);
                }
                if (ih) for (int q = nr - 1; q >= 0; q--) hnd = nl3("lam", nsym(ihn[q]), hnd);
                for (int f = c->nfields; f >= 1; f--) {
                    Node *x = pat ? pat->it[f] : NULL;
                    char nm[32];
                    if (!x) { snprintf(nm, sizeof nm, "%%_%d", f); x = nsym(nm); }
                    hnd = nl3("lam", x, hnd);
                }
                Names bound = { 0 };
                free_vars(hnd, &bound, &fv);
                free(bound.v);
                hb[ci] = hnd;
            }
            /* the variables the branches share are not captured by each branch (copied into
             * every one, all but one then erased) but supplied once to the selected one: each
             * branch is λ shared..., and the environment λ g. g shared... applies it */
            for (int ci = 0; ci < N; ci++) {
                Node *hnd = hb[ci];
                for (int q = fv.n - 1; q >= 0; q--) hnd = nl3("lam", nsym(fv.v[q]), hnd);
                B->it[ci + 4] = hnd;
            }
            { char mb[24]; snprintf(mb, sizeof mb, "%llu", (unsigned long long)mask); B->it[2] = nsym(mb);
              snprintf(mb, sizeof mb, "%d", fv.n); B->it[3] = nsym(mb); }
            Node *env = nsym("%g");
            for (int q = 0; q < fv.n; q++) env = nl3("app", env, nsym(fv.v[q]));
            env = nl3("lam", nsym("%g"), env);
            free(hb); free(fv.v);
            if (el) { Node *r = nlist(5); r->it[0] = nsym("%case"); r->it[1] = B; r->it[2] = ds(t->it[1]); r->it[3] = env; r->it[4] = ds(t->it[2]); return r; }
            return nl4("%case", B, env, ds(t->it[1]));
        }
        if (!strcmp(k, "lam") || !strcmp(k, "plam")) { if (t->n < 3) die("binder without body", NULL); return ds_lam(t->it + 1, t->n - 2, t->it[t->n - 1], k); }
        if (!strcmp(k, "forall")) { arity(t, 2); return nl3("forall", t->it[1], ds(t->it[2])); }
        if (!strcmp(k, "let")) { arity(t, 3); return nl4("let", t->it[1], ds(t->it[2]), ds(t->it[3])); }
        if ((!strcmp(k, "Pi") || !strcmp(k, "Sigma")) && t->n == 3 && t->it[1]->list && t->it[1]->n >= 1 && t->it[1]->it[0]->list) {
            /* a telescope: (Pi ((x A) (y B) ...) C) */
            Node *tel = t->it[1], *r = t->it[2];
            for (int q = tel->n - 1; q >= 0; q--) {
                Node *b = tel->it[q];
                if (!b->list || b->n != 2 || b->it[0]->list) die("malformed telescope in", k);
                Node *n = nlist(4); n->it[0] = nsym(k); n->it[1] = b->it[0]; n->it[2] = b->it[1]; n->it[3] = r; r = n;
            }
            return ds(r);
        }
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
        if (!strcmp(k, "U")) {
            /* the level is kept for codes: a numeral, or a level expression */
            if (t->n > 2) die("(U [level])", NULL);
            if (t->n == 2 && !(t->it[1]->s && t->it[1]->s[0] >= '0' && t->it[1]->s[0] <= '9')) return nl2("U", ds(t->it[1]));
            return t;
        }
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
            { "unglue", 2 }, { "app", 2 }, { "hcompD", 2 }, { NULL, 0 } };
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
static int *CHKDATA; static size_t capchkdata; static int nchkdata;   /* checked data types, in signature order */
static int checked_index(const char *s) { for (int i = nchecked - 1; i >= 0; i--) if (!strcmp(CHECKED[i], s)) return i; return -1; }
/* inputs that are the evidence of a checked identity: their supply is checked */
typedef struct { long g; int iL, iR, n; } ChkId;
static ChkId *CHKID; static size_t capchkid; static int nchkid;
static int chk_index(int d) { for (int i = 0; i < nchkdata; i++) if (CHKDATA[i] == d) return i; return -1; }
int data_checked_index(int d) { return chk_index(d); }
/* the checker's tables: entry i of each is a global, so a lookup is a reference */
static long *TABLE[TB_N]; static size_t TABCAP[TB_N]; static long TABN[TB_N];
static void table_set(int t, long i, long g) {
    if ((size_t)i >= TABCAP[t]) { size_t nc = TABCAP[t] ? TABCAP[t] * 2 : 64; while (nc <= (size_t)i) nc *= 2; TABLE[t] = realloc(TABLE[t], nc * sizeof(long)); TABCAP[t] = nc; }
    TABLE[t][i] = g; if (i >= TABN[t]) TABN[t] = i + 1;
}
long table_global(int t, long i) { return t >= 0 && t < TB_N && i >= 0 && i < TABN[t] ? TABLE[t][i] : -1; }
static Node *word(long n) { char b[32]; snprintf(b, sizeof b, "#%ld", n); return nsym(b); }
static Node *capp1(const char *c, Node *a) { return nl3("app", nsym(c), a); }
static Node *capp2(const char *c, Node *a, Node *b) { return nl3("app", nl3("app", nsym(c), a), b); }
static Node *capp3(const char *c, Node *a, Node *b, Node *d) { return nl3("app", capp2(c, a, b), d); }
static Node *capp4(const char *c, Node *a, Node *b, Node *d, Node *e) { return nl3("app", capp3(c, a, b, d), e); }
/* a list of codes as data */
static Node *code_list(Node **xs, int n) { Node *l = nsym("lnil"); for (int i = n - 1; i >= 0; i--) l = capp2("lcons", xs[i], l); return l; }
static bool bound_name(const char *s) { for (int i = ncscope - 1; i >= 0; i--) if (!strcmp(cscope[i], s)) return true; return false; }
static int checked_data_of(const char *s, const char *what) {
    int d = data_lookup(s), di = d < 0 ? -1 : chk_index(d);
    if (di < 0) die(what, s);
    return di;
}
/* a branch of an elimination: λ fields, hypotheses (one per recursive field), dimensions,
 * of a thunk of the body. A branch not using its hypotheses has no binders for them in
 * the machine; its code binds them anyway, unused. */
static Node *code_branch(Node *b, ConInfo *c, bool ih, int i) {
    int nf = c->nfields, nr = c->nrec, ar = nf + nr + c->ndims;
    if (i == ar) {
        if (!b->list || b->n != 2 || !is(b->it[0], "thunk")) die("code: malformed branch", NULL);
        return to_code(b->it[1]);
    }
    bool hyp = i >= nf && i < nf + nr;
    GROW(cscope, capcscope, (size_t)ncscope + 1);
    Node *r;
    if (hyp && !ih) {
        cscope[ncscope++] = "%unused-ih";
        r = code_branch(b, c, ih, i + 1);
    } else {
        if (!b->list || b->n != 3 || !is(b->it[0], "lam")) die("code: malformed branch", NULL);
        cscope[ncscope++] = b->it[1]->s;
        r = code_branch(b->it[2], c, ih, i + 1);
    }
    ncscope--;
    return capp1(i < nf + nr ? "clam" : "cdlam", r);
}
static Node *code_bound(const char *x, Node *body) {
    GROW(cscope, capcscope, (size_t)ncscope + 1);
    cscope[ncscope++] = x;
    Node *r = to_code(body);
    ncscope--;
    return r;
}
static Node *to_code(Node *t) {
    /* universe levels: Level, lzero, (lsuc l), (lmax a b) */
    if (is(t, "Level") && !bound_name("Level")) return nsym("clevel");
    if (is(t, "lzero") && !bound_name("lzero")) return nsym("clzero");
    if (t->list && t->n == 3 && is(t->it[0], "app")) {
        Node *f = t->it[1];
        if (is(f, "lsuc") && !bound_name("lsuc")) return capp1("clsuc", to_code(t->it[2]));
        if (f->list && f->n == 3 && is(f->it[0], "app") && is(f->it[1], "lmax") && !bound_name("lmax"))
            return capp2("clmax", to_code(f->it[2]), to_code(t->it[2]));
    }
    /* a data type at its parameters, a constructor at its fields and dimensions */
    {
        Node *h = t; int na = 0;
        while (h->list && h->n == 3 && is(h->it[0], "app")) { h = h->it[1]; na++; }
        if (!h->list && !bound_name(h->s)) {
            int c = con_lookup(h->s), d = data_lookup(h->s);
            if (c >= 0 && na < CON[c].nfields && !CON[c].ndims) {
                /* a constructor short of fields, as a function of the rest */
                static int neta;
                int rest = CON[c].nfields - na;
                Node *body = t; Node **xs = calloc((size_t)rest + 1, sizeof(Node *));
                for (int q = 0; q < rest; q++) { char nm[32]; snprintf(nm, sizeof nm, "%%eta%d", neta++); xs[q] = nsym(nm); body = nl3("app", body, xs[q]); }
                for (int q = rest - 1; q >= 0; q--) body = nl3("lam", xs[q], body);
                free(xs);
                return to_code(body);
            }
            if (c >= 0 && CON[c].nfields + CON[c].ndims == na) {
                int di = checked_data_of(DATA[CON[c].data].name, "code: data type not checked:");
                Node **a = calloc((size_t)na + 1, sizeof(Node *));
                Node *x = t;
                for (int k = na - 1; k >= 0; k--) { a[k] = to_code(x->it[2]); x = x->it[1]; }
                Node *r = capp4("ccon", word(di), word(CON[c].index), code_list(a, CON[c].nfields), code_list(a + CON[c].nfields, CON[c].ndims));
                free(a);
                return r;
            }
            if (d >= 0 && DATA[d].nparams == na && global_lookup(h->s) >= 0) {
                int di = checked_data_of(h->s, "code: data type not checked:");
                Node **a = calloc((size_t)na + 1, sizeof(Node *));
                Node *x = t;
                for (int k = na - 1; k >= 0; k--) { a[k] = to_code(x->it[2]); x = x->it[1]; }
                Node *r = capp2("cdata", word(di), code_list(a, na));
                free(a);
                return r;
            }
        }
    }
    if (!t->list) {
        const char *s = t->s;
        if (!strcmp(s, "0")) return nsym("ci0");
        if (!strcmp(s, "1")) return nsym("ci1");
        if (!strcmp(s, "tt")) return nsym("cftt");
        if (!strcmp(s, "ff")) return nsym("cfff");
        if (!strcmp(s, "U")) return capp1("cuniv", nsym("clzero"));
        for (int i = ncscope - 1; i >= 0; i--) if (!strcmp(cscope[i], s)) return capp1("cvar", word(ncscope - 1 - i));
        for (int i = 0; i < nchecked; i++) if (!strcmp(CHECKED[i], s)) return capp1("cglob", word(i));
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
    if (!strcmp(h, "U")) {
        if (t->n == 2 && !t->it[1]->list && t->it[1]->s[0] >= '0' && t->it[1]->s[0] <= '9') {
            Node *l = nsym("clzero");
            for (int q = atoi(t->it[1]->s); q > 0; q--) l = capp1("clsuc", l);
            return capp1("cuniv", l);
        }
        return capp1("cuniv", t->n == 2 ? to_code(t->it[1]) : nsym("clzero"));
    }
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
    if (!strcmp(h, "hcompD")) return capp2("chcomp", to_code(t->it[1]), to_code(t->it[2]));
    if (!strcmp(h, "force")) return capp1("cforce", to_code(t->it[1]));
    if (!strcmp(h, "%case")) {
        /* (%case (%branches D b...) [P] x) */
        Node *B = t->it[1];
        if (!B->list || B->n < 4 || !is(B->it[0], "%branches")) die("code: elimination without its branches", NULL);
        int d = data_lookup(B->it[1]->s), di = checked_data_of(B->it[1]->s, "code: data type not checked:");
        int N = B->n - 4, m = atoi(B->it[3]->s);
        uint64_t mask = strtoull(B->it[2]->s, NULL, 10);
        Node **bs = calloc((size_t)N + 1, sizeof(Node *));
        for (int i = 0; i < N; i++) {
            /* the shared variables a branch binds first are the variables of the same names
             * where the elimination stands */
            Node *b = B->it[i + 4];
            for (int q = 0; q < m; q++) { if (!b->list || b->n != 3 || !is(b->it[0], "lam")) die("code: malformed branch", NULL); b = b->it[2]; }
            bs[i] = code_branch(b, &CON[DATA[d].cons[i]], mask >> i & 1, 0);
        }
        Node *bl = code_list(bs, N);
        free(bs);
        if (t->n == 5) return capp4("celim", word(di), to_code(t->it[2]), bl, to_code(t->it[4]));
        return capp3("ccase", word(di), bl, to_code(t->it[3]));
    }
    die("code: no code for form", h);
    return NULL;
}

/* ---------------- annotated codes ----------------
 * The checker's input (lib/check.ctt `Tm`): the code of a term whose every node carries the
 * term's value, computed by the machine from the compiled subterm, and whose binders are
 * functions: a term binder λ x xT. (code of the body), a dimension binder λ i. (code of the
 * body). Instantiating a binder is applying it; a variable's node is (tv x xT), its value and
 * type. Each node's value is built from its parts' values (let-bound, so each is computed
 * once); a binder's value is the compiled binder itself. A system's branches are thunks, so a
 * branch is computed under its face. Checked definitions are (tg n (%gval n)); indices are words. */
typedef struct { Node **x, **e; int n, cap; } Chain;
typedef struct { const char *name; Node *ty; } AScope;   /* ty NULL: a dimension */
static AScope *asc; static size_t capasc; static int nasc;
static long nann;
static Node *afresh(const char *p) { char b[32]; snprintf(b, sizeof b, "%%%s%ld", p, nann++); return nsym(b); }
static Node *bind_in(Chain *c, const char *p, Node *e) {
    if (!e->list) return e;
    if (c->n == c->cap) { c->cap = c->cap ? c->cap * 2 : 16; c->x = realloc(c->x, (size_t)c->cap * sizeof(Node *)); c->e = realloc(c->e, (size_t)c->cap * sizeof(Node *)); }
    Node *x = afresh(p); c->x[c->n] = x; c->e[c->n] = e; c->n++;
    return x;
}
static Node *chain_close(Chain *c, Node *body) {
    for (int i = c->n - 1; i >= 0; i--) body = nl4("let", c->x[i], c->e[i], body);
    free(c->x); free(c->e); c->x = c->e = NULL; c->n = c->cap = 0;
    return body;
}
static AScope *ascope(const char *s) { for (int i = nasc - 1; i >= 0; i--) if (!strcmp(asc[i].name, s)) return &asc[i]; return NULL; }
static void apush(const char *s, Node *ty) { GROW(asc, capasc, (size_t)nasc + 1); asc[nasc++] = (AScope){ s, ty }; }
/* a source subterm as the expression of its value: checked definitions by their own values */
static Node *vsrc(Node *t, Names *bound) {
    if (!t->list) {
        if (names_has(bound, t->s) || ascope(t->s)) return t;
        int i = checked_index(t->s);
        return i >= 0 ? nl2("%gval", word(i)) : t;
    }
    if (t->n == 0) return t;
    Node *r = nlist(t->n);
    const char *h = t->it[0]->list ? NULL : t->it[0]->s;
    if (h && (!strcmp(h, "lam") || !strcmp(h, "plam") || !strcmp(h, "forall")) && t->n == 3) {
        int save = bound->n; names_add(bound, t->it[1]->s);
        r->it[0] = t->it[0]; r->it[1] = t->it[1]; r->it[2] = vsrc(t->it[2], bound);
        bound->n = save; return r;
    }
    if (h && !strcmp(h, "let") && t->n == 4) {
        r->it[0] = t->it[0]; r->it[1] = t->it[1]; r->it[2] = vsrc(t->it[2], bound);
        int save = bound->n; names_add(bound, t->it[1]->s);
        r->it[3] = vsrc(t->it[3], bound); bound->n = save; return r;
    }
    if (h && !strcmp(h, "%branches")) {
        for (int i = 0; i < 4; i++) r->it[i] = t->it[i];
        for (int i = 4; i < t->n; i++) r->it[i] = vsrc(t->it[i], bound);
        return r;
    }
    if (h && keyword(h)) { r->it[0] = t->it[0]; for (int i = 1; i < t->n; i++) r->it[i] = (!strcmp(h, "=") && i == 2) ? t->it[i] : vsrc(t->it[i], bound); return r; }
    for (int i = 0; i < t->n; i++) r->it[i] = vsrc(t->it[i], bound);
    return r;
}
static Node *vsrc0(Node *t) { Names b = { 0 }; Node *r = vsrc(t, &b); free(b.v); return r; }
typedef struct { Node *node, *val; } NV;
static NV ann(Node *t, Chain *C);
/* a node: its constructor applied to its parts' nodes, then its value */
static NV anode(Chain *C, const char *con, Node **parts, int n, Node *val) {
    NV r; r.val = bind_in(C, "av", val);
    Node *x = nsym(con);
    for (int i = 0; i < n; i++) x = nl3("app", x, parts[i]);
    r.node = bind_in(C, "an", nl3("app", x, r.val));
    return r;
}
static Node *alist(Node **xs, int n) { Node *l = nsym("lnil"); for (int i = n - 1; i >= 0; i--) l = capp2("lcons", xs[i], l); return l; }
/* the code of t in a scope of its own (a binder's body) */
static Node *aclosed(Node *t) { Chain c = { 0 }; NV r = ann(t, &c); return chain_close(&c, r.node); }
static Node *abinder(Node *x, Node *body, bool dim) {
    Node *ty = dim ? NULL : afresh("at");
    apush(x->s, ty);
    Node *b = aclosed(body);
    nasc--;
    return dim ? nl3("lam", x, b) : nl3("lam", x, nl3("lam", ty, b));
}
static Node *abranch(Node *b, ConInfo *c, bool ih, int i) {
    int nf = c->nfields, nr = c->nrec, ar = nf + nr + c->ndims;
    if (i == ar) {
        if (!b->list || b->n != 2 || !is(b->it[0], "thunk")) die("code: malformed branch", NULL);
        return nl3("app", nsym("be"), aclosed(b->it[1]));
    }
    bool hyp = i >= nf && i < nf + nr, dim = i >= nf + nr;
    Node *x, *body;
    if (hyp && !ih) { x = afresh("au"); body = b; }
    else {
        if (!b->list || b->n != 3 || !is(b->it[0], "lam")) die("code: malformed branch", NULL);
        x = b->it[1]; body = b->it[2];
    }
    Node *ty = dim ? NULL : afresh("at");
    apush(x->s, ty);
    Node *r = abranch(body, c, ih, i + 1);
    nasc--;
    return nl3("app", nsym(dim ? "bi" : "bx"), dim ? nl3("lam", x, r) : nl3("lam", x, nl3("lam", ty, r)));
}
static NV aconst(const char *node, const char *val) { NV r = { nsym(node), nsym(val) }; return r; }
static NV ann(Node *t, Chain *C) {
    Node *p[8];
    if (is(t, "Level") && !ascope("Level")) return aconst("tlevel", "Level");
    if (is(t, "lzero") && !ascope("lzero")) return aconst("tlzero", "lzero");
    if (t->list && t->n == 3 && is(t->it[0], "app")) {
        Node *f = t->it[1];
        if (is(f, "lsuc") && !ascope("lsuc")) { NV a = ann(t->it[2], C); p[0] = a.node; return anode(C, "tlsuc", p, 1, nl3("app", nsym("lsuc"), a.val)); }
        if (f->list && f->n == 3 && is(f->it[0], "app") && is(f->it[1], "lmax") && !ascope("lmax")) {
            NV a = ann(f->it[2], C), b = ann(t->it[2], C); p[0] = a.node; p[1] = b.node;
            return anode(C, "tlmax", p, 2, nl3("app", nl3("app", nsym("lmax"), a.val), b.val));
        }
    }
    {
        Node *h = t; int na = 0;
        while (h->list && h->n == 3 && is(h->it[0], "app")) { h = h->it[1]; na++; }
        if (!h->list && !ascope(h->s)) {
            int c = con_lookup(h->s), d = data_lookup(h->s);
            if (c >= 0 && na < CON[c].nfields && !CON[c].ndims) {
                static int neta;
                int rest = CON[c].nfields - na;
                Node *body = t; Node **xs = calloc((size_t)rest + 1, sizeof(Node *));
                for (int q = 0; q < rest; q++) { char nm[32]; snprintf(nm, sizeof nm, "%%aeta%d", neta++); xs[q] = nsym(nm); body = nl3("app", body, xs[q]); }
                for (int q = rest - 1; q >= 0; q--) body = nl3("lam", xs[q], body);
                free(xs);
                return ann(body, C);
            }
            bool con = c >= 0 && CON[c].nfields + CON[c].ndims == na;
            if (con || (d >= 0 && DATA[d].nparams == na && global_lookup(h->s) >= 0)) {
                int di = checked_data_of(con ? DATA[CON[c].data].name : h->s, "code: data type not checked:");
                Node **a = calloc((size_t)na + 1, sizeof(Node *)), **v = calloc((size_t)na + 1, sizeof(Node *));
                Node *x = t;
                for (int k = na - 1; k >= 0; k--) { NV r = ann(x->it[2], C); a[k] = r.node; v[k] = r.val; x = x->it[1]; }
                Node *val = h;
                for (int k = 0; k < na; k++) val = nl3("app", val, v[k]);
                NV r;
                if (con) { p[0] = word(di); p[1] = word(CON[c].index); p[2] = alist(a, CON[c].nfields); p[3] = alist(a + CON[c].nfields, CON[c].ndims); r = anode(C, "tcon", p, 4, val); }
                else { p[0] = word(di); p[1] = alist(a, na); r = anode(C, "tdata", p, 2, val); }
                free(a); free(v);
                return r;
            }
        }
    }
    if (!t->list) {
        const char *s = t->s;
        if (!strcmp(s, "0")) return aconst("tc0", "0");
        if (!strcmp(s, "1")) return aconst("tc1", "1");
        if (!strcmp(s, "tt")) return aconst("ttt", "tt");
        if (!strcmp(s, "ff")) return aconst("tff", "ff");
        if (!strcmp(s, "U")) { p[0] = nsym("tlzero"); return anode(C, "tuniv", p, 1, nsym("U")); }
        if (!strcmp(s, "Word")) return aconst("tword", "Word");
        if (s[0] == '#' && s[1] >= '0' && s[1] <= '9') { NV r; r.val = t; r.node = nl3("app", nsym("tlit"), t); return r; }
        AScope *a = ascope(s);
        if (a) { NV r; r.val = t; r.node = a->ty ? nl3("app", nl3("app", nsym("tv"), t), a->ty) : nl3("app", nsym("ti"), t); return r; }
        int i = checked_index(s);
        if (i >= 0) { p[0] = word(i); return anode(C, "tg", p, 1, nl2("%gval", word(i))); }
        die("code: not a bound variable or checked definition:", s);
    }
    const char *h = t->it[0]->s;
    if (!strcmp(h, "lam") || !strcmp(h, "plam") || !strcmp(h, "forall")) {
        p[0] = abinder(t->it[1], t->it[2], strcmp(h, "lam") != 0);
        return anode(C, !strcmp(h, "lam") ? "tlam" : !strcmp(h, "plam") ? "tplam" : "tforall", p, 1, vsrc0(t));
    }
    if (!strcmp(h, "let")) {
        NV a = ann(t->it[2], C);
        p[0] = a.node; p[1] = abinder(t->it[1], t->it[3], false);
        Names b = { 0 }; names_add(&b, t->it[1]->s);
        Node *val = nl4("let", t->it[1], a.val, vsrc(t->it[3], &b)); free(b.v);
        return anode(C, "tlet", p, 2, val);
    }
    if (!strcmp(h, "Pi") || !strcmp(h, "Sigma")) {
        Node *B = t->it[2];
        NV a = ann(t->it[1], C);
        p[0] = a.node; p[1] = abinder(B->it[1], B->it[2], false);
        return anode(C, !strcmp(h, "Pi") ? "tpi" : "tsigma", p, 2, nl3(h, a.val, vsrc0(B)));
    }
    if (!strcmp(h, "U")) {
        NV l;
        if (t->n == 2 && !t->it[1]->list && t->it[1]->s[0] >= '0' && t->it[1]->s[0] <= '9') {
            l = aconst("tlzero", "lzero");
            for (int q = atoi(t->it[1]->s); q > 0; q--) { p[0] = l.node; l = anode(C, "tlsuc", p, 1, nl3("app", nsym("lsuc"), l.val)); }
        } else if (t->n == 2) l = ann(t->it[1], C);
        else l = aconst("tlzero", "lzero");
        p[0] = l.node;
        return anode(C, "tuniv", p, 1, nl2("U", l.val));
    }
    if (!strcmp(h, "sys0") || !strcmp(h, "sys+")) {
        Node *bs[256]; int nb = 0;
        for (Node *x = t; x->list && is(x->it[0], "sys+"); x = x->it[3]) {
            if (nb == 256) die("code: more than 256 system branches", NULL);
            NV f = ann(x->it[1], C);
            bs[nb++] = nl3("pair", f.node, nl2("thunk", aclosed(x->it[2]->it[1])));
        }
        p[0] = alist(bs, nb);
        return anode(C, "tsys", p, 1, vsrc0(t));
    }
    if (!strcmp(h, "%case")) {
        Node *B = t->it[1];
        if (!B->list || B->n < 4 || !is(B->it[0], "%branches")) die("code: elimination without its branches", NULL);
        int d = data_lookup(B->it[1]->s), di = checked_data_of(B->it[1]->s, "code: data type not checked:");
        int N = B->n - 4, m = atoi(B->it[3]->s);
        uint64_t mask = strtoull(B->it[2]->s, NULL, 10);
        bool el = t->n == 5;
        NV P = { 0 };
        if (el) P = ann(t->it[2], C);
        NV x = ann(t->it[el ? 4 : 3], C);
        Node **bs = calloc((size_t)N + 1, sizeof(Node *));
        for (int i = 0; i < N; i++) {
            Node *b = B->it[i + 4];
            for (int q = 0; q < m; q++) { if (!b->list || b->n != 3 || !is(b->it[0], "lam")) die("code: malformed branch", NULL); b = b->it[2]; }
            bs[i] = abranch(b, &CON[DATA[d].cons[i]], mask >> i & 1, 0);
        }
        /* the elimination as a function of its scrutinee */
        Node *sv = afresh("as");
        Node *cs = nlist(t->n); cs->it[0] = t->it[0]; cs->it[1] = vsrc0(B);
        if (el) { cs->it[2] = P.val; cs->it[3] = vsrc0(t->it[3]); cs->it[4] = sv; }
        else { cs->it[2] = vsrc0(t->it[2]); cs->it[3] = sv; }
        Node *F = bind_in(C, "af", nl3("lam", sv, cs));
        int k = 0;
        p[k++] = word(di);
        if (el) p[k++] = P.node;
        p[k++] = alist(bs, N); p[k++] = x.node; p[k++] = F;
        free(bs);
        return anode(C, el ? "telim" : "tcase", p, k, nl3("app", F, x.val));
    }
    static const struct { const char *h, *con; int n; } F[] = {
        { "app", "tapp", 2 }, { "pair", "tpair", 2 }, { "fst", "tfst", 1 }, { "snd", "tsnd", 1 },
        { "PathP", "tpathp", 3 }, { "@", "tpapp", 2 }, { "~", "tneg", 1 }, { "/\\", "tmeet", 2 }, { "\\/", "tjoin", 2 },
        { "&", "tfand", 2 }, { "|", "tfor", 2 }, { "comp", "tcomp", 3 }, { "Glue", "tgluet", 2 }, { "glue", "tglue", 2 },
        { "unglue", "tunglue", 2 }, { "hcompD", "thcomp", 2 }, { "force", "tforce", 1 }, { NULL, NULL, 0 } };
    {
        static const char *WO[] = { "%weq", "%wlt", "%wadd", "%wmax", "%wsub", NULL };
        for (int q = 0; WO[q]; q++) if (!strcmp(h, WO[q])) {
            NV a = ann(t->it[1], C), b = ann(t->it[2], C);
            p[0] = word(q); p[1] = a.node; p[2] = b.node;
            Node *v = nl3(h, a.val, b.val);
            return anode(C, "twop", p, 3, v);
        }
        if (!strcmp(h, "%wsucc")) { NV a = ann(t->it[1], C); p[0] = a.node; return anode(C, "twsucc", p, 1, nl2(h, a.val)); }
        if (!strcmp(h, "%welimP")) {
            Node *v = nlist(5); v->it[0] = t->it[0];
            for (int i = 0; i < 4; i++) { NV r = ann(t->it[i + 1], C); p[i] = r.node; v->it[i + 1] = r.val; }
            return anode(C, "twelim", p, 4, v);
        }
    }
    if (!strcmp(h, "=")) {
        NV r = ann(t->it[1], C); p[0] = r.node;
        return anode(C, is(t->it[2], "0") ? "teq0" : "teq1", p, 1, nl3("=", r.val, t->it[2]));
    }
    if (!strcmp(h, "the")) {
        NV T = ann(t->it[1], C), a = ann(t->it[2], C); p[0] = a.node; p[1] = T.node;
        return anode(C, "tann", p, 2, a.val);
    }
    for (int q = 0; F[q].h; q++) if (!strcmp(h, F[q].h)) {
        Node *v = nlist(F[q].n + 1); v->it[0] = t->it[0];
        for (int i = 0; i < F[q].n; i++) { NV r = ann(t->it[i + 1], C); p[i] = r.node; v->it[i + 1] = r.val; }
        return anode(C, F[q].con, p, F[q].n, v);
    }
    die("code: no code for form", h);
    return (NV){ 0 };
}
/* a data declaration as a telescope (lib/check.ctt `Tel`): its parameters, then the list of its
 * constructors, each its fields, its dimensions, then its boundary */
static Node *atel_ctor(Node *cd, ConInfo *c, int i, int k) {
    if (k < c->nfields) {
        Node *fl = cd->it[i];
        if (!fl->list) die("a checked data type needs its fields' types:", c->name);
        Chain C = { 0 }; NV A = ann(ds(fl->it[1]), &C);
        Node *ty = afresh("at");
        apush(fl->it[0]->s, ty);
        Node *rest = atel_ctor(cd, c, i + 1, k + 1);
        nasc--;
        return chain_close(&C, capp2("tx", A.node, nl3("lam", fl->it[0], nl3("lam", ty, rest))));
    }
    if (!c->ndims) { Node *s0 = nlist(1); s0->it[0] = nsym("sys"); return capp1("tz", aclosed(ds(s0))); }
    Node *dl = cd->it[i++];
    int base = nasc;
    for (int q = 1; q < dl->n; q++) apush(dl->it[q]->s, NULL);
    Node *sy = nlist(cd->n - i + 1); sy->it[0] = nsym("sys");
    for (int q = i; q < cd->n; q++) sy->it[q - i + 1] = cd->it[q];
    Node *r = capp1("tz", aclosed(ds(sy)));
    nasc = base;
    for (int q = dl->n - 1; q >= 1; q--) r = capp1("ty", nl3("lam", dl->it[q], r));
    return r;
}
static Node *atel_params(Node *dd, int d, int k) {
    Node *hd = dd->it[1];
    if (k < DATA[d].nparams) {
        Node *p = hd->it[k + 1];
        if (!p->list || p->n != 2) die("a checked data type needs its parameters' types:", DATA[d].name);
        Chain C = { 0 }; NV A = ann(ds(p->it[1]), &C);
        Node *ty = afresh("at");
        apush(p->it[0]->s, ty);
        Node *rest = atel_params(dd, d, k + 1);
        nasc--;
        return chain_close(&C, capp2("tx", A.node, nl3("lam", p->it[0], nl3("lam", ty, rest))));
    }
    Node **cs = calloc((size_t)DATA[d].ncons + 1, sizeof(Node *));
    for (int ci = 0; ci < DATA[d].ncons; ci++) cs[ci] = atel_ctor(dd->it[ci + 2], &CON[DATA[d].cons[ci]], 1, 0);
    Node *r = capp1("tz", alist(cs, DATA[d].ncons));
    free(cs);
    return r;
}

static void toplevel(Node *f);
static size_t name_hash(const char *s);
/* ---------------- definitions ---------------- */
enum { G_DEF, G_AXIOM, G_INPUT };
typedef struct {
    char *name; int kind;
    Syn *body; int nslots; int *uses;
    Record *nary;                    /* the body taking all its parameters at once, or NULL */
    Cell *res;                       /* holds the definition's value; a use copies it */
    long tyg;                        /* an axiom's type: the global holding it, or -1 */
    Cell **park_o, **park_v; int npark, parkcap;
} Global;
static Global *G; static long nG, capG;
static char **fresh_names; static long nfresh, capfresh;
#define FRESH_BASE (1L << 40)

/* names to the latest global of that name: open addressing, doubled when half full */
static long *GH; static size_t capGH;
static size_t name_hash(const char *s) { size_t h = 1469598103934665603ull; for (; *s; s++) h = (h ^ (unsigned char)*s) * 1099511628211ull; return h; }
static void gh_put(const char *name, long g) {
    if ((size_t)nG * 2 >= capGH) {
        size_t nc = capGH ? capGH * 2 : 1024;
        long *nh = malloc(nc * sizeof(long));
        for (size_t i = 0; i < nc; i++) nh[i] = -1;
        for (size_t i = 0; i < capGH; i++) if (GH[i] >= 0) {
            size_t j = name_hash(G[GH[i]].name) & (nc - 1);
            while (nh[j] >= 0) j = (j + 1) & (nc - 1);
            nh[j] = GH[i];
        }
        free(GH); GH = nh; capGH = nc;
    }
    size_t j = name_hash(name) & (capGH - 1);
    while (GH[j] >= 0 && strcmp(G[GH[j]].name, name)) j = (j + 1) & (capGH - 1);
    GH[j] = g;
}
long global_lookup(const char *name) {
    if (!capGH) return -1;
    size_t j = name_hash(name) & (capGH - 1);
    while (GH[j] >= 0) { if (!strcmp(G[GH[j]].name, name)) return GH[j]; j = (j + 1) & (capGH - 1); }
    return -1;
}
const char *name_of(long id) {
    if ((uint64_t)id & LVL_TAG) { static __thread char b[8][32]; static __thread int bi; char *r = b[bi++ & 7]; snprintf(r, 32, "v%llu", (unsigned long long)((uint64_t)id & ~LVL_TAG)); return r; }
    return id >= FRESH_BASE ? fresh_names[id - FRESH_BASE] : G[id].name;
}
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
    nG++;
    gh_put(name, nG - 1);
    return nG - 1;
}
Port global_copy(long g) {
    Cell *r = G[g].res;
    if (!r->port[0]) return 0;
    /* a definition whose value is a closed λ or a constant constructor is built from its
     * syntax: unfolding it is the one interaction that meets it */
    Syn *b = G[g].kind == G_DEF ? G[g].body : NULL;
    if (b && b->tag == S_LAM && b->n == 0) { Cell *c = cell(V_LAM, 1); c->p = b->rec; return P(c, 0); }
    if (b && b->tag == S_CON && b->n == 0) return con_build((int)b->id, NULL, NULL);
    if (b && b->tag == S_DATA && b->n == 0) { Cell *c = cell(V_DATA, 1); c->a = (uint64_t)b->id; return P(c, 0); }
    extern Port lazy_copy(Cell *root);
    return lazy_copy(r);
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
bool global_sited(long g) { return identities_on && pick(g) >= 0; }
Record *global_nary(long g) { return g >= 0 && g < nG && G[g].kind == G_DEF ? G[g].nary : NULL; }
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
static bool constant_sym(const char *s);
static void push_bind(const char *name, int level, int slot) {
    if (constant_sym(name)) die("a constant cannot be bound:", name);
    if (keyword(name)) die("a keyword cannot be bound:", name);
    GROW(binds, capbinds, (size_t)nbinds + 1); binds[nbinds++] = (Bind){ name, level, slot }; }
static int new_slot(void) {
    Level *L = &levels[nlevels - 1];
    if (L->nslots == L->ucap) { L->ucap = L->ucap ? L->ucap * 2 : 8; L->uses = realloc(L->uses, (size_t)L->ucap * sizeof(int)); }
    L->uses[L->nslots] = 0;
    return L->nslots++;
}
static Syn *var_syn(int slot) { levels[nlevels - 1].uses[slot]++; Syn *s = syn(S_VAR, 0); s->slot = slot; return s; }
static bool constant_sym(const char *s) { return !strcmp(s, "0") || !strcmp(s, "1") || !strcmp(s, "tt") || !strcmp(s, "ff") || !strcmp(s, "U") || !strcmp(s, "Word"); }

/* the outermost binder level a term refers to (-1: none) */
/* (only whether it is below the current level matters: the walk stops at the first variable of
 * the current level or deeper) */
static int ml_cut = 1 << 30;
static int maxlev(Node *t) {
    if (!t->list) {
        if (constant_sym(t->s)) return -1;
        for (int i = nshadow - 1; i >= 0; i--) if (!strcmp(shadow[i], t->s)) return -1;
        Bind *b = lookup(t->s);
        return b ? b->level : -1;
    }
    const char *h = t->it[0]->list ? "" : t->it[0]->s;
    int r = -1;
    /* a fresh variable or dimension is made each time its level runs: never lifted */
    if (!strcmp(h, "%var") || !strcmp(h, "%dim")) return 1 << 30;
    if (!strcmp(h, "lam") || !strcmp(h, "plam") || !strcmp(h, "forall")) {
        GROW(shadow, capshadow, (size_t)nshadow + 1);
        shadow[nshadow++] = t->it[1]->s; r = maxlev(t->it[2]); nshadow--; return r;
    }
    if (!strcmp(h, "let")) {
        r = maxlev(t->it[2]);
        if (r >= ml_cut) return r;
        GROW(shadow, capshadow, (size_t)nshadow + 1);
        shadow[nshadow++] = t->it[1]->s; int r2 = maxlev(t->it[3]); nshadow--;
        return r > r2 ? r : r2;
    }
    for (int i = 1; i < t->n; i++) { int m = maxlev(t->it[i]); if (m > r) r = m; if (r >= ml_cut) return r; }
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
long *prof_count, *prof_dup; const char **prof_name; int prof_n, prof_on; static int prof_cur; long prof_dupk[64], prof_erak[64], prof_con[4096], prof_glob[65536];
static size_t capprofc, capprofn, capprofd;
static void prof_enter(const char *name) {
    GROW(prof_count, capprofc, (size_t)prof_n + 1); GROW(prof_name, capprofn, (size_t)prof_n + 1); GROW(prof_dup, capprofd, (size_t)prof_n + 1);
    prof_count[prof_n] = 0; prof_dup[prof_n] = 0; prof_name[prof_n] = strdup(name); prof_cur = prof_n++;
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
    r->where = prof_cur;
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
/* the variables of the enclosing scopes a term refers to, in order of first occurrence */
static void local_free(Node *t, Names *bound, Names *out) {
    if (!t->list) {
        if (!names_has(bound, t->s) && lookup(t->s)) names_add(out, t->s);
        return;
    }
    if (t->n == 0) return;
    if (t->it[0]->list) { for (int i = 0; i < t->n; i++) local_free(t->it[i], bound, out); return; }
    const char *h = t->it[0]->s;
    if ((!strcmp(h, "lam") || !strcmp(h, "plam") || !strcmp(h, "forall")) && t->n == 3) {
        int save = bound->n; names_add(bound, param_name(t->it[1])->s);
        local_free(t->it[2], bound, out); bound->n = save; return;
    }
    if (!strcmp(h, "let") && t->n == 4) {
        local_free(t->it[2], bound, out);
        int save = bound->n; names_add(bound, t->it[1]->s);
        local_free(t->it[3], bound, out); bound->n = save; return;
    }
    if (!strcmp(h, "the") && t->n == 3) { local_free(t->it[2], bound, out); return; }
    int from = 1;
    if (!strcmp(h, "%branches")) from = 4;
    else if (!strcmp(h, "%con") || !strcmp(h, "%data") || !strcmp(h, "%transD")) from = 2;
    for (int i = from; i < t->n; i++) local_free(t->it[i], bound, out);
}
/* a branch: a record whose parameters (slots 0..np-1) are the constructor's fields, hypotheses
 * and dimensions and whose environment is the case's shared variables. Nothing is lifted out of
 * it: it is built only when selected */
static Record *compile_branch(const Names *env, Node **pn, int np, Node *body) {
    GROW(levels, caplevels, (size_t)nlevels + 1);
    int li = nlevels++;
    levels[li] = (Level){ .is_thunk = 1, .scope_start = nbinds };
    int *es = calloc((size_t)env->n + 1, sizeof(int));
    for (int q = 0; q < np; q++) new_slot();
    for (int e = 0; e < env->n; e++) { es[e] = new_slot(); push_bind(env->v[e], li, es[e]); }
    for (int q = 0; q < np; q++) push_bind(pn[q]->s, li, q);
    Syn *b = compile(body);
    nbinds = levels[li].scope_start;
    Level L = levels[li];
    nlevels--;
    if (L.nenv) die("internal: a case branch lifted a term", NULL);
    Record *r = calloc(1, sizeof(Record));
    r->nparam = np; r->nslots = L.nslots; r->nenv = env->n; r->env_slot = es;
    r->uses = L.uses ? L.uses : calloc(1, sizeof(int)); r->body = b; r->where = prof_cur;
    return r;
}
/* (%case (%branches D mask m b...) [P] E x): one cell. Its table holds one record per
 * constructor; its ports the scrutinee, the motive and the variables the branches share, each
 * once. A constructor meeting it builds the selected branch: one interaction. A handler is
 * λ shared(m)... λ fields, hypotheses, dimensions. (thunk body), or any term, then applied */
static Syn *compile_case(Node *t) {
    bool el = t->n == 5;
    Node *B = t->it[1];
    if (!B->list || B->n < 4 || !is(B->it[0], "%branches")) die("%case without its branches", NULL);
    int d = data_lookup(B->it[1]->s);
    if (d < 0) die("%branches: unknown data type", B->it[1]->s);
    uint64_t mask = strtoull(B->it[2]->s, NULL, 10);
    int m = atoi(B->it[3]->s), N = DATA[d].ncons;
    if (B->n - 4 != N) die("%branches: one branch per constructor of", DATA[d].name);
    Node **body = calloc((size_t)N + 1, sizeof(Node *)), ***pn = calloc((size_t)N + 1, sizeof(Node **));
    int *np = calloc((size_t)N + 1, sizeof(int));
    Names env = { 0 };
    for (int c = 0; c < N; c++) {
        ConInfo *ci = &CON[DATA[d].cons[c]];
        Node *h = B->it[4 + c];
        for (int q = 0; q < m; q++) {
            if (!h->list || h->n != 3 || !is(h->it[0], "lam")) die("%branches: a branch binds the shared variables first", NULL);
            h = h->it[2];
        }
        int n = ci->nfields + ((mask >> c & 1) && ci->nrec ? ci->nrec : 0) + ci->ndims;
        np[c] = n; pn[c] = calloc((size_t)n + 1, sizeof(Node *));
        int got = 0;
        while (got < n && h->list && h->n == 3 && is(h->it[0], "lam")) { pn[c][got++] = param_name(h->it[1]); h = h->it[2]; }
        if (got < n) {
            for (int q = got; q < n; q++) { char nm[32]; snprintf(nm, sizeof nm, "%%p%d", q); pn[c][q] = nsym(nm); h = nl3("app", h, nsym(nm)); }
            h = nl2("force", h);
        } else if (h->list && h->n == 2 && is(h->it[0], "thunk")) h = h->it[1];
        else h = nl2("force", h);
        body[c] = h;
        Names bound = { 0 };
        for (int q = 0; q < n; q++) names_add(&bound, pn[c][q]->s);
        local_free(h, &bound, &env);
        free(bound.v);
    }
    CaseTab *tb = calloc(1, sizeof(CaseTab));
    tb->d = d; tb->nenv = env.n; tb->mask = mask; tb->br = calloc((size_t)N + 1, sizeof(Record *));
    for (int c = 0; c < N; c++) tb->br[c] = compile_branch(&env, pn[c], np[c], body[c]);
    Syn *s = syn(S_CASE, 2 + env.n);
    s->tab = tb; s->x = el;
    s->k[0] = compile(t->it[el ? 4 : 3]);
    s->k[1] = el ? compile(t->it[2]) : NULL;
    for (int e = 0; e < env.n; e++) s->k[2 + e] = compile(nsym(env.v[e]));
    free(body); free(np);
    return s;
}
static Syn *compile(Node *t) {
    int li = nlevels - 1;
    if (li >= 1) {
        ml_cut = li;
        int m = maxlev(t);
        ml_cut = 1 << 30;
        if (m >= 0 && m < li && (!levels[li].is_thunk || !t->list)) return var_syn(lift(t));
    }
    if (!t->list) {
        const char *s = t->s;
        if (!strcmp(s, "0")) return syn(S_IV0, 0);
        if (!strcmp(s, "1")) return syn(S_IV1, 0);
        if (!strcmp(s, "tt")) return syn(S_FTT, 0);
        if (!strcmp(s, "ff")) return syn(S_FFF, 0);
        if (!strcmp(s, "U")) return syn(S_U, 0);
        if (!strcmp(s, "Word")) return syn(S_WORDTY, 0);
        Bind *b = lookup(s);
        if (b) {
            if (b->level != li) die("internal: unlifted outer variable", s);
            return var_syn(b->slot);
        }
        { int c = con_lookup(s); if (c >= 0 && CON[c].nfields + CON[c].ndims == 0) { Syn *r = syn(S_CON, 0); r->id = c; return r; } }
        if (s[0] == '#' && s[1] >= '0' && s[1] <= '9') {
            Syn *r = syn(S_WORD, 0); WN w = wn_parse(s + 1);
            r->id = (long)w.s; r->big = w.b;
            return r;
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
    if (!strcmp(h, "app")) {
        /* a constructor applied to all its fields and dimensions is the constructor */
        Node *hd = t; int na = 0;
        while (hd->list && hd->n == 3 && is(hd->it[0], "app")) { hd = hd->it[1]; na++; }
        int c = !hd->list && !lookup(hd->s) ? con_lookup(hd->s) : -1;
        if (c >= 0 && na == CON[c].nfields + CON[c].ndims) {
            Syn *r = syn(S_CON, na); r->id = c;
            Node *a = t;
            for (int q = na - 1; q >= 0; q--) { r->k[q] = compile(a->it[2]); a = a->it[1]; }
            return r;
        }
        /* a definition applied to arguments: one call cell (its body built at once when the
         * arguments cover its parameters) */
        long g = !hd->list && !lookup(hd->s) && c < 0 && !constant_sym(hd->s) ? global_lookup(hd->s) : -1;
        if (g >= 0 && G[g].kind != G_AXIOM && na >= 1) {
            Syn *r = syn(S_CALL, na); r->id = g;
            Node *a = t;
            for (int q = na - 1; q >= 0; q--) { r->k[q] = compile(a->it[2]); a = a->it[1]; }
            return r;
        }
        return compile_n(S_APP, t, 1, 2);
    }
    if (!strcmp(h, "pair")) return compile_n(S_PAIR, t, 1, 2);
    if (!strcmp(h, "fst")) return compile_n(S_FST, t, 1, 1);
    if (!strcmp(h, "snd")) return compile_n(S_SND, t, 1, 1);
    if (!strcmp(h, "Pi")) return compile_n(S_PI, t, 1, 2);
    if (!strcmp(h, "Sigma")) return compile_n(S_SIGMA, t, 1, 2);
    if (!strcmp(h, "U")) {
        if (t->n == 1) return syn(S_U, 0);
        Node *l = t->it[1];
        if (!l->list && l->s[0] >= '0' && l->s[0] <= '9') { Node *z = nsym("lzero"); for (int q = atoi(l->s); q > 0; q--) z = nl3("app", nsym("lsuc"), z); l = z; }
        Syn *s = syn(S_U, 1); s->k[0] = compile(l); return s;
    }
    {
        static const struct { const char *name; int kind, n; } PR[] = { { "%view", O_VIEW, 1 }, { "%ieq", O_IEQ, 2 }, { "%feq", O_FEQL, 2 }, { "%clauses", O_CLAUSES, 1 },
            { "%restrict", O_RESTRICT, 2 }, { "%abs", O_ABS, 2 }, { "%branch", O_BRANCH, 3 }, { "%clos", O_CLOS, 2 }, { "%wsucc", O_WSUCC, 1 }, { "%weq", O_WEQ, 2 }, { "%wlt", O_WLT, 2 },
            { "%wadd", O_WADD, 2 }, { "%wmax", O_WMAX, 2 }, { "%wsub", O_WSUB, 2 }, { "%welim", O_WELIM, 3 }, { NULL, 0, 0 } };
        if (!strcmp(h, "%welimP")) {
            /* (%welimP P w z s): the elimination of a word with its motive, which is for the
             * checker: the machine runs (%welim w z s) */
            if (t->n != 5) die("(%welimP P w z s)", NULL);
            Syn *s = compile_n(S_PRIM, t, 2, 3); s->x = O_WELIM; return s;
        }
        if (!strcmp(h, "%var") || !strcmp(h, "%dim")) {
            /* (%var T), (%dim): a fresh variable of type T, a fresh dimension; the first port
             * only triggers the cell */
            bool v = !strcmp(h, "%var");
            if (t->n != (v ? 2 : 1)) die(v ? "(%var T)" : "(%dim)", NULL);
            Syn *s = syn(S_PRIM, v ? 2 : 1); s->x = v ? O_MKVAR : O_MKDIM;
            s->k[0] = syn(S_FTT, 0);
            if (v) s->k[1] = compile(t->it[1]);
            return s;
        }
        for (int q = 0; PR[q].name; q++) if (!strcmp(h, PR[q].name)) {
            if (t->n != PR[q].n + 1) die("wrong number of operands in", h);
            Syn *s = compile_n(S_PRIM, t, 1, PR[q].n); s->x = (uint32_t)PR[q].kind; return s;
        }
        if (!strcmp(h, "%box")) { if (t->n != 2) die("(%box v)", NULL); Syn *s = syn(S_BOX, 1); s->k[0] = compile(t->it[1]); return s; }
        static const char *TBN[TB_N] = { "%gval", "%gty", "%dtab", "%dent" };
        for (int q = 0; q < TB_N; q++) if (!strcmp(h, TBN[q])) {
            if (t->n != 2) die("wrong number of operands in", h);
            Syn *s = syn(S_GLOBTAB, 1); s->x = (uint32_t)q; s->k[0] = compile(t->it[1]); return s;
        }
    }
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
    if (!strcmp(h, "%data")) {
        int d = data_lookup(t->it[1]->s);
        if (d < 0 || t->n - 2 != DATA[d].nparams) die("bad %data", t->it[1]->s);
        Syn *s = compile_n(S_DATA, t, 2, t->n - 2); s->id = d; return s;
    }
    if (!strcmp(h, "%con")) {
        int c = con_lookup(t->it[1]->s);
        if (c < 0 || t->n - 2 != CON[c].nfields + CON[c].ndims) die("bad %con", t->it[1]->s);
        Syn *s = compile_n(S_CON, t, 2, t->n - 2); s->id = c; return s;
    }
    if (!strcmp(h, "hcompD")) return compile_n(S_HCOMPD, t, 1, 2);
    if (!strcmp(h, "%transD")) {
        int d = data_lookup(t->it[1]->s);
        if (d < 0 || t->n - 2 != DATA[d].nparams + 2) die("bad %transD", t->it[1]->s);
        Syn *s = compile_n(S_TRANSD, t, 2, t->n - 2); s->id = d; return s;
    }
    if (!strcmp(h, "%case")) {
        if (t->n != 4 && t->n != 5) die("bad %case", NULL);
        return compile_case(t);
    }
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
    char *b = dimbuf[dimbuf_i++ & 7]; snprintf(b, 24, "#%llu", (unsigned long long)d); return b;
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
    case V_U: {
        Cell *lc = PC(c->port[1]);
        if (lc && lc->kind == V_CON && !strcmp(CON[lc->a].name, "lzero")) { fputs("U", o); return; }
        fputs("(U ", o); push_str(")"); push_field(c, 1); return;
    }
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
    case V_DATA: if (c->n == 1) fputs(DATA[c->a].name, o); else push_fields(o, DATA[c->a].name, c, 1); return;
    case V_CON: if (c->n == 1) fputs(CON[c->a].name, o); else push_fields(o, CON[c->a].name, c, 1); return;
    case V_HCOMP: push_fields(o, "hcompD", c, 1); return;
    case V_CASEF: fputs("%casef", o); return;
    case V_WORD: { WN w = { c->a, c->p }; fputc('#', o); wn_print(o, &w); return; }
    case V_WTY: fputs("Word", o); return;
    case V_WPLUS: {
        /* k successors of x: (%wsucc x), or (%wadd x #k) */
        WN w = { c->a, c->p };
        if (!c->p && c->a == 1) { fputs("(%wsucc ", o); push_str(")"); push_field(c, 1); return; }
        char *buf; size_t len; FILE *m = open_memstream(&buf, &len); fputs(" #", m); wn_print(m, &w); fputc(')', m); fclose(m);
        fputs("(%wadd ", o); push_task(TK_STR, 0, buf); push_field(c, 1);
        return;
    }
    case V_NWOP: {
        static const char *nm[] = { "%weq", "%wlt", "%wadd", "%wmax", "%wsub" };
        push_fields_to(o, nm[c->x - O_WEQ], c, 1, 3);
        return;
    }
    case V_NWELIM: push_fields_to(o, "%welim", c, 1, 4); return;
    case V_WSUSP: { extern Port wsusp_force(Cell *c); push_port(wsusp_force(c)); return; }
    case V_REF: { extern Port ref_copy(Cell *c); push_port(ref_copy(c)); return; }
    case V_SUSP:
        /* an unforced induction hypothesis */
        fputs("(rec ", o);
        push_str(")"); push_field(c, 1);
        return;
    case V_NCASE: {
        /* (case x ((C v...) body)...), or (elim P x ...): each branch built on fresh variables */
        CaseTab *tb = c->p;
        int ne = tb->nenv, N = DATA[tb->d].ncons;
        Port ec[ne + 1][N + 1];
        for (int e = 0; e < ne; e++) port_split(c->port[2 + (c->x ? 1 : 0) + e], N, ec[e]);
        fputs(c->x ? "(elim " : "(case ", o);
        push_str(")");
        for (int k = N - 1; k >= 0; k--) {
            ConInfo *ci = &CON[DATA[tb->d].cons[k]];
            int nf = ci->nfields, nd = ci->ndims, nr = (tb->mask >> k & 1) ? ci->nrec : 0, np = nf + nr + nd;
            Port prm[np + 1], env[ne + 1];
            char pat[1024]; int at = snprintf(pat, sizeof pat, " ((%s", ci->name);
            for (int j = 0; j < np; j++) {
                if (j >= nf + nr) {
                    Dim dd = fresh_dim();
                    Cell *iv = cell(V_IV, 1); iv->p = iv_atom(dd); prm[j] = P(iv, 0);
                    at += snprintf(pat + at, sizeof pat - (size_t)at, " %s", dim_name(dd));
                } else {
                    long nm = fresh_var(j < nf ? "x" : "ih", vcount++);
                    Cell *v = cell(V_NVAR, 2); v->a = (uint64_t)nm;
                    Cell *u = cell(V_UNK, 1); link(P(u, 0), P(v, 1));
                    prm[j] = P(v, 0);
                    if (j < nf) at += snprintf(pat + at, sizeof pat - (size_t)at, " %s", name_of(nm));
                }
                if (at >= (int)sizeof pat) at = (int)sizeof pat - 1;
            }
            snprintf(pat + at, sizeof pat - (size_t)at, ") ");
            for (int e = 0; e < ne; e++) env[e] = ec[e][k];
            push_str(")"); push_port(record_build_n(tb->br[k], prm, env)); push_str(pat);
        }
        push_field(c, 1);
        if (c->x) { push_str(" "); push_field(c, 2); }
        return;
    }
    case V_NTRANS:
        /* (%transD D ψ lines... x) */
        fprintf(o, "(%%transD %s", DATA[c->a].name);
        push_str(")"); push_field(c, 1); push_str(" ");
        for (int k = c->n - 2; k >= 2; k--) { push_field(c, k); push_str(" "); }
        push_task(TK_STR, 0, dnf_string(c->p, true)); push_str(" ");
        return;
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
/* top-level forms written by the system (a data declaration's definitions) */
static void emit(const char *text) {
    if (getenv("CUBICAL_SHOW_EMIT")) fprintf(stderr, "%s\n", text);
    const char *saved = src;
    src = text;
    Node *f;
    while ((f = read_node())) toplevel(f);
    src = saved;
}
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
        prof_enter(f->it[1]->s);
        Syn *s = compile_top(f->it[2], &ns, &u);
        G[g].body = s; G[g].nslots = ns; G[g].uses = u;
        {
            /* the body with all its parameters at once */
            Node *b = ds(f->it[2]); int np = 0;
            Node *pn[256];
            while (b->list && b->n == 3 && is(b->it[0], "lam") && np < 256) { pn[np++] = param_name(b->it[1]); b = b->it[2]; }
            if (np >= 1) {
                nbinds = 0; nlevels = 1; GROW(levels, caplevels, 1); levels[0] = (Level){ 0 };
                Names none = { 0 };
                G[g].nary = compile_branch(&none, pn, np, b);
                nlevels = 0;
            }
        }
        prof_cur = 0;
        link(top_build(s, ns, u), P(G[g].res, 0));
        if (!strcmp(G[g].name, "%case-hcomp")) case_hcomp_global = g;
        if (fill_decl) { for (int i = 0; i < G[g].npark; i++) net_push(G[g].park_o[i], G[g].park_v[i]); G[g].npark = 0; }
    } else if (!strcmp(h, "checked") || !strcmp(h, "check") || !strcmp(h, "check-fail")) {
        /* the checker (lib/check.ctt), a term, run on the codes of T and t
         * against the signature of the definitions checked so far */
        bool define = !strcmp(h, "checked"), expect = strcmp(h, "check-fail") != 0;
        int at = define ? 2 : 1;
        if (f->n != at + 2) die(define ? "(checked name T t)" : "(check T t)", NULL);
        Node *T = f->it[at], *t = f->it[at + 1];
        Node *cT = nl2("%raw", aclosed(ds(T))), *ct = nl2("%raw", aclosed(ds(t)));
        Node *q = nl3("chk-def", cT, ct);
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
            /* the checker's tables: the definition and its type, each a global, so a lookup
             * is a reference */
            char ty[32]; snprintf(ty, sizeof ty, "%%sty%d", nchecked);
            Node *td = nlist(3); td->it[0] = nsym("def"); td->it[1] = nsym(ty); td->it[2] = nl2("sig-type", cT);
            toplevel(td);
            table_set(TB_VAL, nchecked, global_lookup(f->it[1]->s));
            table_set(TB_TY, nchecked, global_lookup(ty));
            GROW(CHECKED, capchecked, (size_t)nchecked + 1);
            CHECKED[nchecked++] = strdup(f->it[1]->s);
        }
    } else if (!strcmp(h, "checked-identity") || !strcmp(h, "checked-identity-fail")) {
        /* (checked-identity L R p [n]): L and R checked definitions of one type, p a checked
         * definition of type Π g. L g = R g, or an input whose supply is checked at that type */
        bool expect = !strcmp(h, "checked-identity");
        if (f->n != 4 && f->n != 5) die("(checked-identity L R p [n])", NULL);
        int iL = checked_index(f->it[1]->s), iR = checked_index(f->it[2]->s), ip = checked_index(f->it[3]->s);
        if (iL < 0 || iR < 0) die("checked-identity: L and R must be checked definitions", NULL);
        long gL = global_lookup(f->it[1]->s), gp = global_lookup(f->it[3]->s);
        int n = 0;
        if (f->n == 5) n = atoi(f->it[4]->s);
        else for (Syn *b = G[gL].body; b && b->tag == S_LAM && b->rec->nparam == 1; b = b->rec->body) n++;
        if (n < 1) n = 1;
        bool input = ip < 0 && gp >= 0 && G[gp].kind == G_INPUT && !G[gp].res->port[0];
        if (ip < 0 && !input) die("checked-identity: the evidence must be a checked definition or an unsupplied input:", f->it[3]->s);
        Node *q = nlist(input ? 4 : 5);
        q->it[0] = nsym(input ? "id-type-ok" : "chk-identity-def");
        q->it[1] = word(iL); q->it[2] = word(iR); q->it[3] = word(n);
        if (!input) q->it[4] = word(ip);
        long steps;
        char *r = readback(q, &steps, NULL), *tr = readback(nsym("true"), NULL, NULL);
        bool accepted = !strcmp(r, tr), ok = accepted == expect;
        if (ok) passes++; else failures++;
        printf("%s: %s identity %s = %s by %s   [%ld steps]\n", ok ? "ok" : "FAIL", expect ? "checks" : "rejected", f->it[1]->s, f->it[2]->s, f->it[3]->s, steps);
        free(r); free(tr);
        if (accepted && expect) {
            if (input) { GROW(CHKID, capchkid, (size_t)nchkid + 1); CHKID[nchkid++] = (ChkId){ gp, iL, iR, n }; }
            char nb[16]; snprintf(nb, sizeof nb, "%d", n);
            Node *d = nlist(5); d->it[0] = nsym("identity"); d->it[1] = f->it[1]; d->it[2] = f->it[2]; d->it[3] = f->it[3]; d->it[4] = nsym(nb);
            toplevel(d);
        }
    } else if (!strcmp(h, "identity-from") || !strcmp(h, "checked-identity-from") || !strcmp(h, "checked-identity-from-fail")) {
        /* (identity-from L e [n]): the identity a term produces, e = (R, p) with
         * p : Π g. L g = R g; the optimizer as a term (5.26). The checked forms check e's
         * type against Σ (R : T_L). Π g. PathP (λ_. B) (L g) (R g) first. */
        bool chk = strcmp(h, "identity-from") != 0, expect = strcmp(h, "checked-identity-from-fail") != 0;
        if (f->n != 3 && f->n != 4) die("(identity-from L e [n])", NULL);
        long gL = global_lookup(f->it[1]->s), ge = global_lookup(f->it[2]->s);
        if (gL < 0 || ge < 0) die("identity-from: L and e must be definitions", NULL);
        int n = 0;
        if (f->n == 4) n = atoi(f->it[3]->s);
        else for (Syn *b = G[gL].body; b && b->tag == S_LAM && b->rec->nparam == 1; b = b->rec->body) n++;
        if (n < 1) n = 1;
        if (chk) {
            int iL = checked_index(f->it[1]->s), ie = checked_index(f->it[2]->s);
            if (iL < 0 || ie < 0) die("checked-identity-from: L and e must be checked definitions", NULL);
            Node *q = nlist(4); q->it[0] = nsym("chk-optimizer"); q->it[1] = word(iL); q->it[2] = word(n); q->it[3] = word(ie);
            long steps;
            char *r = readback(q, &steps, NULL), *tr = readback(nsym("true"), NULL, NULL);
            bool accepted = !strcmp(r, tr), ok = accepted == expect;
            if (ok) passes++; else failures++;
            printf("%s: %s identity of %s from %s   [%ld steps]\n", ok ? "ok" : "FAIL", expect ? "checks" : "rejected", f->it[1]->s, f->it[2]->s, steps);
            free(r); free(tr);
            if (!accepted || !expect) return;
        }
        static int nopt;
        char rn[48], pn[48], nb[16];
        snprintf(rn, sizeof rn, "%%opt-R%d", nopt); snprintf(pn, sizeof pn, "%%opt-p%d", nopt); snprintf(nb, sizeof nb, "%d", n);
        nopt++;
        Node *d = nlist(3); d->it[0] = nsym("def"); d->it[1] = nsym(rn); d->it[2] = nl2("fst", f->it[2]); toplevel(d);
        d = nlist(3); d->it[0] = nsym("def"); d->it[1] = nsym(pn); d->it[2] = nl2("snd", f->it[2]); toplevel(d);
        Node *id = nlist(5); id->it[0] = nsym("identity"); id->it[1] = f->it[1]; id->it[2] = nsym(rn); id->it[3] = nsym(pn); id->it[4] = nsym(nb);
        toplevel(id);
    } else if (!strcmp(h, "checked-data") || !strcmp(h, "checked-data-fail") || !strcmp(h, "check-data")) {
        bool expect = strcmp(h, "checked-data-fail") != 0;
        /* (checked-data (data ...)): declare the data type and check it with the
         * checker: parameter and field types are types, fields strictly positive,
         * boundaries elements of the type made of earlier constructors.
         * (check-data D): check a data type already declared (the prelude's) */
        Node *dd; int d;
        if (!strcmp(h, "check-data")) {
            if (f->n != 2 || f->it[1]->list) die("(check-data D)", NULL);
            d = data_lookup(f->it[1]->s);
            if (d < 0) die("check-data: no such data type:", f->it[1]->s);
            if (chk_index(d) >= 0) die("check-data: already checked:", f->it[1]->s);
            dd = DATA[d].decl;
        } else {
            if (f->n != 2 || !f->it[1]->list || !is(f->it[1]->it[0], "data")) die("(checked-data[-fail] (data ...))", NULL);
            dd = f->it[1];
            toplevel(dd);
            d = ndata - 1;
        }
        GROW(CHKDATA, capchkdata, (size_t)nchkdata + 1);
        CHKDATA[nchkdata++] = d;
        Node *ent = nl2("%raw", capp2("dent", atel_params(dd, d, 0), nsym("lzero")));
        int di = nchkdata - 1;
        /* the tables while it is checked: its declaration at level lzero, and the machine's data
         * type, constructors, elimination and case for the evaluator */
        char den[32], dtn[32]; snprintf(den, sizeof den, "%%dentp%d", di); snprintf(dtn, sizeof dtn, "%%dtab%d", di);
        Node *pd = nlist(3); pd->it[0] = nsym("def"); pd->it[1] = nsym(den); pd->it[2] = ent;
        toplevel(pd);
        Node **cs = calloc((size_t)DATA[d].ncons + 1, sizeof(Node *));
        for (int ci = 0; ci < DATA[d].ncons; ci++) cs[ci] = nsym(CON[DATA[d].cons[ci]].name);
        char en[256], cn[256]; snprintf(en, sizeof en, "%%elim-%s", DATA[d].name); snprintf(cn, sizeof cn, "%%case-%s", DATA[d].name);
        Node *td = nlist(3); td->it[0] = nsym("def"); td->it[1] = nsym(dtn);
        td->it[2] = capp4("dtab", nsym(DATA[d].name), code_list(cs, DATA[d].ncons), nsym(en), nsym(cn));
        free(cs);
        toplevel(td);
        table_set(TB_DENT, di, global_lookup(den));
        table_set(TB_DTAB, di, global_lookup(dtn));
        long steps;
        char *r = readback(nl3("chk-data", word(di), ent), &steps, NULL), *tr = readback(nsym("true"), NULL, NULL);
        bool accepted = !strcmp(r, tr), ok = accepted == expect;
        if (ok) passes++; else failures++;
        printf("%s: %s data %s   [%ld steps]\n", ok ? "ok" : "FAIL", expect ? "checks" : "rejected", DATA[d].name, steps);
        free(r); free(tr);
        if (!accepted) { nchkdata--; return; }
        char dent[32]; snprintf(dent, sizeof dent, "%%dent%d", di);
        Node *ed = nlist(3); ed->it[0] = nsym("def"); ed->it[1] = nsym(dent); ed->it[2] = nl3("data-entry", word(di), ent);
        toplevel(ed);
        table_set(TB_DENT, di, global_lookup(dent));
    } else if (!strcmp(h, "declare")) {
        /* a name already declared and not yet given is declared once */
        for (int i = 1; i < f->n; i++) {
            long g = global_lookup(f->it[i]->s);
            if (g >= 0 && G[g].kind == G_INPUT && !G[g].res->port[0]) continue;
            add_global(f->it[i]->s, G_INPUT);
        }
    } else if (!strcmp(h, "data")) {
        /* (data D ctor...) or (data (D z...) ctor...); ctor = (c field... [(dims i...) (φ e)...]),
         * field = x or (x A). Generates the type former D, the constructors, each path
         * constructor's boundary %bdy-c, and from CHM's equations the composition
         * %comp-D = hcomp after transport, transport on each constructor %trans-c
         * and on hcomp %trans-hcomp-D. */
        if (f->n < 2) die("(data D ctor...)", NULL);
        if (f->n - 2 > 64) die("more than 64 constructors in", f->it[1]->list ? f->it[1]->it[0]->s : f->it[1]->s);
        Node *hd = f->it[1];
        const char *D = hd->list ? hd->it[0]->s : hd->s;
        int np = hd->list ? hd->n - 1 : 0, nc = f->n - 2;
        const char **pn = calloc((size_t)np + 1, sizeof(char *));
        for (int k = 0; k < np; k++) pn[k] = param_name(hd->it[k + 1])->s;
        GROW(DATA, capdata, (size_t)ndata + 1);
        int d = ndata++;
        DATA[d] = (DataInfo){ strdup(D), np, nc, calloc((size_t)nc + 1, sizeof(int)), -1, -1, f };
        typedef struct { Node *cd; int nf, nd, nb; Node **fn, **ft, **dn, **bf, **be; } CD;
        CD *cs = calloc((size_t)nc + 1, sizeof(CD));
        for (int ci = 0; ci < nc; ci++) {
            Node *cd = f->it[ci + 2];
            if (!cd->list || cd->n < 1 || cd->it[0]->list) die("constructor must be (C field...)", NULL);
            CD *x = &cs[ci]; x->cd = cd;
            x->fn = calloc((size_t)cd->n, sizeof(Node *)); x->ft = calloc((size_t)cd->n, sizeof(Node *));
            x->dn = calloc((size_t)cd->n, sizeof(Node *)); x->bf = calloc((size_t)cd->n, sizeof(Node *)); x->be = calloc((size_t)cd->n, sizeof(Node *));
            int i = 1;
            for (; i < cd->n; i++) {
                Node *it = cd->it[i];
                if (it->list && it->n >= 1 && is(it->it[0], "dims")) break;
                if (it->list) { if (it->n != 2 || it->it[0]->list) die("field must be x or (x A) in", cd->it[0]->s); x->fn[x->nf] = it->it[0]; x->ft[x->nf] = it->it[1]; }
                else x->fn[x->nf] = it;
                x->nf++;
            }
            if (i < cd->n) {
                Node *dl = cd->it[i++];
                for (int k = 1; k < dl->n; k++) x->dn[x->nd++] = dl->it[k];
                for (; i < cd->n; i++) {
                    Node *br = cd->it[i];
                    if (!br->list || br->n != 2) die("boundary must be (φ e) in", cd->it[0]->s);
                    x->bf[x->nb] = br->it[0]; x->be[x->nb] = br->it[1]; x->nb++;
                }
            }
            if (x->nb && !x->nd) die("a boundary needs dimensions in", cd->it[0]->s);
            GROW(CON, capcon, (size_t)ncon + 1);
            DATA[d].cons[ci] = ncon;
            /* a field of type D itself is recursive: its branch may take its induction hypothesis */
            uint64_t rm = 0; int nr = 0;
            for (int k = 0; k < x->nf; k++) {
                Node *A = x->ft[k];
                if (A && ((!A->list && !strcmp(A->s, D)) || (A->list && A->n >= 1 && !A->it[0]->list && !strcmp(A->it[0]->s, D)))) { rm |= 1ull << k; nr++; }
            }
            if (x->nf > 64) die("more than 64 fields in", cd->it[0]->s);
            CON[ncon++] = (ConInfo){ strdup(cd->it[0]->s), d, ci, x->nf, x->nd, -1, -1, nr, rm };
        }
        char *buf; size_t len; FILE *m;
#define OPEN() (m = open_memstream(&buf, &len))
#define EMIT() do { fclose(m); emit(buf); free(buf); } while (0)
#define PN(x) print_node(m, (x))
        /* the type former */
        OPEN();
        if (np) { fprintf(m, "(def %s (lam", D); for (int k = 0; k < np; k++) fprintf(m, " %s", pn[k]); fprintf(m, " (%%data %s", D); for (int k = 0; k < np; k++) fprintf(m, " %s", pn[k]); fprintf(m, ")))"); }
        else fprintf(m, "(def %s (%%data %s))", D, D);
        EMIT();
        for (int ci = 0; ci < nc; ci++) {
            CD *x = &cs[ci]; int c = DATA[d].cons[ci]; const char *cn = CON[c].name;
            /* fields then dimensions, as written */
            char *args; size_t alen; FILE *am = open_memstream(&args, &alen);
            for (int k = 0; k < x->nf; k++) { fputc(' ', am); print_node(am, x->fn[k]); }
            for (int k = 0; k < x->nd; k++) { fputc(' ', am); print_node(am, x->dn[k]); }
            fclose(am);
            if (x->nb) {
                OPEN(); fprintf(m, "(def %%bdy-%s (lam%s (sys", cn, args);
                for (int k = 0; k < x->nb; k++) { fputs(" (", m); PN(x->bf[k]); fputc(' ', m); PN(x->be[k]); fputc(')', m); }
                fprintf(m, ")))"); EMIT();
                char nm[256]; snprintf(nm, sizeof nm, "%%bdy-%s", cn);
                CON[c].bdy = global_lookup(nm);
            }
            OPEN();
            if (x->nf + x->nd) fprintf(m, "(def %s (lam%s (%%con %s%s)))", cn, args, cn, args);
            else fprintf(m, "(def %s (%%con %s))", cn, cn);
            EMIT();
            free(args);
        }
        /* the eliminators as functions (used by the evaluator over codes, whose branches
         * take every recursive field's hypothesis) */
        uint64_t allih = 0;
        for (int ci = 0; ci < nc; ci++) if (CON[DATA[d].cons[ci]].nrec) allih |= 1ull << ci;
        OPEN();
        fprintf(m, "(def %%elim-%s (lam %%P", D);
        for (int k = 0; k < nc; k++) fprintf(m, " %%b%d", k);
        fprintf(m, " %%x (%%case (%%branches %s %llu 0", D, (unsigned long long)allih);
        for (int k = 0; k < nc; k++) fprintf(m, " %%b%d", k);
        fprintf(m, ") %%P (lam %%g %%g) %%x)))");
        EMIT();
        OPEN();
        fprintf(m, "(def %%case-%s (lam", D);
        for (int k = 0; k < nc; k++) fprintf(m, " %%b%d", k);
        fprintf(m, " %%x (%%case (%%branches %s %llu 0", D, (unsigned long long)allih);
        for (int k = 0; k < nc; k++) fprintf(m, " %%b%d", k);
        fprintf(m, ") (lam %%g %%g) %%x)))");
        EMIT();
        /* composition: hcomp after transport (CHM); a closed type transports as the identity */
        OPEN();
        if (!np) fprintf(m, "(def %%comp-%s (lam %%u %%a0 (hcompD %%u %%a0)))", D);
        else {
            fprintf(m, "(def %%comp-%s (lam", D);
            for (int k = 0; k < np; k++) fprintf(m, " %%z%d", k);
            fprintf(m, " %%u %%a0 (hcompD (sysmap (lam %%w (plam %%i (%%transD %s (= %%i 1)", D);
            for (int k = 0; k < np; k++) fprintf(m, " (plam %%j (@ %%z%d (\\/ %%i %%j)))", k);
            fprintf(m, " (@ %%w %%i)))) %%u) (%%transD %s ff", D);
            for (int k = 0; k < np; k++) fprintf(m, " %%z%d", k);
            fprintf(m, " %%a0))))");
        }
        EMIT();
        { char nm[256]; snprintf(nm, sizeof nm, "%%comp-%s", D); DATA[d].comp = global_lookup(nm); }
        /* transport on hcomp: into its tube and cap */
        OPEN();
        fprintf(m, "(def %%trans-hcomp-%s (lam", D);
        for (int k = 0; k < np; k++) fprintf(m, " %%z%d", k);
        if (!np) fprintf(m, " %%psi %%u %%u0 (hcompD %%u %%u0)))");
        else {
            fprintf(m, " %%psi %%u %%u0 (hcompD (sysmap (lam %%w (plam %%j (%%transD %s %%psi", D);
            for (int k = 0; k < np; k++) fprintf(m, " %%z%d", k);
            fprintf(m, " (@ %%w %%j)))) %%u) (%%transD %s %%psi", D);
            for (int k = 0; k < np; k++) fprintf(m, " %%z%d", k);
            fprintf(m, " %%u0))))");
        }
        EMIT();
        { char nm[256]; snprintf(nm, sizeof nm, "%%trans-hcomp-%s", D); DATA[d].transh = global_lookup(nm); }
        /* transport on each constructor */
        for (int ci = 0; ci < nc; ci++) {
            CD *x = &cs[ci]; int c = DATA[d].cons[ci]; const char *cn = CON[c].name;
            OPEN();
            fprintf(m, "(def %%trans-%s (lam", cn);
            for (int k = 0; k < np; k++) fprintf(m, " %%z%d", k);
            fprintf(m, " %%psi");
            for (int k = 0; k < x->nf; k++) { fputc(' ', m); PN(x->fn[k]); }
            for (int k = 0; k < x->nd; k++) { fputc(' ', m); PN(x->dn[k]); }
            fputc(' ', m);
            if (!np) {
                /* a closed type: the identity */
                if (x->nf + x->nd) { fprintf(m, "(%s", cn); for (int k = 0; k < x->nf; k++) { fputc(' ', m); PN(x->fn[k]); } for (int k = 0; k < x->nd; k++) { fputc(' ', m); PN(x->dn[k]); } fputc(')', m); }
                else fputs(cn, m);
                fputs("))", m);
            } else {
                /* θ_m = transFill^i of field m along its type, with the parameters and the earlier
                 * fields at i ∧ j; a field of type D itself is transported by D's transport */
                for (int k = 0; k < x->nf; k++) {
                    if (!x->ft[k]) die("a parameterized data type needs its fields' types:", cn);
                    Node *A = x->ft[k];
                    bool rec = (!A->list && !strcmp(A->s, D)) || (A->list && A->n >= 1 && !A->it[0]->list && !strcmp(A->it[0]->s, D));
                    fprintf(m, "(let %%t%d (plam %%i ", k);
                    if (rec) {
                        fprintf(m, "(%%transD %s (| %%psi (= %%i 0))", D);
                        for (int q = 0; q < np; q++) fprintf(m, " (plam %%j (@ %%z%d (/\\ %%i %%j)))", q);
                        fputc(' ', m); PN(x->fn[k]); fputc(')', m);
                    } else {
                        fprintf(m, "(comp (plam %%j");
                        for (int q = 0; q < np; q++) fprintf(m, " (let %s (@ %%z%d (/\\ %%i %%j))", pn[q], q);
                        for (int q = 0; q < k; q++) { fputs(" (let ", m); PN(x->fn[q]); fprintf(m, " (@ %%t%d (/\\ %%i %%j))", q); }
                        fputc(' ', m); PN(A);
                        for (int q = 0; q < np + k; q++) fputc(')', m);
                        fprintf(m, ") (sys ((| %%psi (= %%i 0)) (plam %%j "); PN(x->fn[k]); fputs("))) ", m); PN(x->fn[k]); fputc(')', m);
                    }
                    fputs(") ", m);
                }
                /* the constructor on the transported fields */
                char *head; size_t hlen; FILE *hm = open_memstream(&head, &hlen);
                if (x->nf + x->nd) { fprintf(hm, "(%s", cn); for (int k = 0; k < x->nf; k++) fprintf(hm, " (@ %%t%d 1)", k); for (int k = 0; k < x->nd; k++) { fputc(' ', hm); print_node(hm, x->dn[k]); } fputc(')', hm); }
                else fputs(cn, hm);
                fclose(hm);
                if (!x->nb) fputs(head, m);
                else {
                    /* a path constructor: corrected at its boundary by the squeezed boundary,
                     * hcomp^i [φ(r) ↦ α(1-i), ψ ↦ c v r] (c (trans v) r) */
                    fputs("(hcompD (sys+ ", m);
                    if (x->nb > 1) fputs("(|", m);
                    for (int k = 0; k < x->nb; k++) { fputc(' ', m); PN(x->bf[k]); }
                    if (x->nb > 1) fputc(')', m);
                    fprintf(m, " (plam %%i (%%transD %s (| %%psi (= (~ %%i) 1))", D);
                    for (int q = 0; q < np; q++) fprintf(m, " (plam %%j (@ %%z%d (\\/ (~ %%i) %%j)))", q);
                    fputc(' ', m);
                    for (int k = 0; k < x->nf; k++) { fputs("(let ", m); PN(x->fn[k]); fprintf(m, " (@ %%t%d (~ %%i)) ", k); }
                    fputs("(sys", m);
                    for (int k = 0; k < x->nb; k++) { fputs(" (", m); PN(x->bf[k]); fputc(' ', m); PN(x->be[k]); fputc(')', m); }
                    fputc(')', m);
                    for (int k = 0; k < x->nf; k++) fputc(')', m);
                    fprintf(m, ")) (sys (%%psi (plam %%i (%s", cn);
                    for (int k = 0; k < x->nf; k++) { fputc(' ', m); PN(x->fn[k]); }
                    for (int k = 0; k < x->nd; k++) { fputc(' ', m); PN(x->dn[k]); }
                    fprintf(m, "))))) %s)", head);
                }
                free(head);
                for (int k = 0; k < x->nf; k++) fputc(')', m);
                fputs("))", m);
            }
            EMIT();
            char nm[256]; snprintf(nm, sizeof nm, "%%trans-%s", cn);
            CON[c].trans = global_lookup(nm);
        }
#undef OPEN
#undef EMIT
#undef PN
        for (int ci = 0; ci < nc; ci++) { free(cs[ci].fn); free(cs[ci].ft); free(cs[ci].dn); free(cs[ci].bf); free(cs[ci].be); }
        free(cs); free(pn);
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
    } else if (!strcmp(h, "supply") || !strcmp(h, "supply-fail")) {
        if (f->n != 3) die("(supply name term)", NULL);
        long g = global_lookup(f->it[1]->s);
        if (g < 0 || G[g].kind != G_INPUT || G[g].res->port[0]) die("not an unsupplied input:", f->it[1]->s);
        bool expect = !strcmp(h, "supply");
        for (int i = 0; i < nchkid; i++) if (CHKID[i].g == g) {
            /* the evidence of a checked identity: checked at the identity's type first */
            Node *q = nlist(5); q->it[0] = nsym("chk-identity");
            q->it[1] = word(CHKID[i].iL); q->it[2] = word(CHKID[i].iR); q->it[3] = word(CHKID[i].n); q->it[4] = nl2("%raw", aclosed(ds(f->it[2])));
            long steps;
            char *r = readback(q, &steps, NULL), *tr = readback(nsym("true"), NULL, NULL);
            bool accepted = !strcmp(r, tr), ok = accepted == expect;
            if (ok) passes++; else failures++;
            printf("%s: %s evidence %s   [%ld steps]\n", ok ? "ok" : "FAIL", expect ? "checks" : "rejected", f->it[1]->s, steps);
            free(r); free(tr);
            if (!accepted) return;
            break;
        }
        if (!expect) die("supply-fail of an input that is not a checked identity's evidence:", f->it[1]->s);
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
static void prof_print(void);
static void prof_signal(int sig) { (void)sig; fflush(stdout); prof_print(); _Exit(3); }
int main(int argc, char **argv) {
    const char *w = getenv("CUBICAL_WORKERS");
    prof_on = getenv("CUBICAL_PROFILE") != NULL;
    if (prof_on) signal(SIGTERM, prof_signal);
    prof_enter("(top level)");
    net_start(w ? atoi(w) : 0);
    for (int i = 1; i < argc; i++) {
        char *text = slurp(argv[i]);
        src = text;
        Node *f;
        while ((f = read_node())) toplevel(f);
    }
    /* steps performed so far: a reading only when the workload has normalized (show, defect) */
    printf("%d passed, %d failed; %ld interaction steps performed; %ld cells live; %ld payloads live\n", passes, failures, stat_steps, stat_cells, stat_payloads);
    prof_print();
    return failures ? 1 : 0;
}
static void prof_print(void) {
    if (prof_on) {
        /* the definitions whose λs and thunks were entered most */
        int *ix = malloc((size_t)prof_n * sizeof(int)), *ix2 = malloc((size_t)prof_n * sizeof(int));
        for (int i = 0; i < prof_n; i++) ix[i] = i;
        for (int i = 0; i < prof_n; i++) for (int j = i + 1; j < prof_n; j++) if (prof_count[ix[j]] > prof_count[ix[i]]) { int t = ix[i]; ix[i] = ix[j]; ix[j] = t; }
        for (int i = 0; i < prof_n && i < 40; i++) fprintf(stderr, "%12ld  %s\n", prof_count[ix[i]], prof_name[ix[i]]);
        for (int k = 0; k < K_END; k++) if (stat_kind[k]) fprintf(stderr, "kind %3d: %ld\n", k, stat_kind[k]);
        for (int k = 0; k < 64; k++) if (prof_dupk[k] || prof_erak[k]) fprintf(stderr, "value kind %3d: dup %ld era %ld\n", k, prof_dupk[k], prof_erak[k]);
        for (int i = 0; i < prof_n; i++) ix2[i] = i;
        for (int i = 0; i < prof_n; i++) for (int j = i + 1; j < prof_n; j++) if (prof_dup[ix2[j]] > prof_dup[ix2[i]]) { int t = ix2[i]; ix2[i] = ix2[j]; ix2[j] = t; }
        for (int i = 0; i < prof_n && i < 25; i++) fprintf(stderr, "dup %12ld  %s\n", prof_dup[ix2[i]], prof_name[ix2[i]]);
        free(ix2);
        {
            extern long prof_odup[65536], prof_oera[65536], prof_rdup[256], prof_rera[256];
            for (int w = 0; w < 2; w++) {
                long *rec = w ? prof_oera : prof_odup, *rul = w ? prof_rera : prof_rdup;
                int *o = malloc(65536 * sizeof(int)); int no = 0;
                for (int i = 0; i < 65536; i++) if (rec[i]) o[no++] = i;
                for (int i = 0; i < no; i++) for (int j = i + 1; j < no; j++) if (rec[o[j]] > rec[o[i]]) { int t = o[i]; o[i] = o[j]; o[j] = t; }
                for (int i = 0; i < no && i < 25; i++) fprintf(stderr, "%s from %10ld  %s\n", w ? "era" : "dup", rec[o[i]], o[i] == 0 ? "(top or unknown)" : (o[i] - 1 < prof_n ? prof_name[o[i] - 1] : "?"));
                for (int k = 0; k < 256; k++) if (rul[k] > 100000) fprintf(stderr, "%s from %10ld  rule kind %d\n", w ? "era" : "dup", rul[k], k);
                free(o);
            }
        }
        for (int c = 0; c < ncon && c < 4096; c++) if (prof_con[c] > 50000) fprintf(stderr, "con dup %10ld %s\n", prof_con[c], CON[c].name);
        for (long g = 0; g < 65536; g++) if (prof_glob[g] > 50000) fprintf(stderr, "glob dup %10ld %s\n", prof_glob[g], name_of(g));
        free(ix);
    }
}
