/* net.c — cells, wiring, the interaction rules, and building a net from
 * compiled syntax. */
#include "core.h"
#include <string.h>
#include <pthread.h>
#include <sched.h>

long stat_steps, stat_kind[K_END], stat_cells;
#define ADD(x, v) __atomic_fetch_add(&(x), (v), __ATOMIC_RELAXED)

/* ---------------- type-stable cells ----------------
 * A cell's memory is never returned: a thread holding a stale pointer can
 * still take the lock word, and revalidation then finds the wire changed.
 * Freed cells go to the freeing thread's list after its locks are released. */
#define MAXFREE 4096
typedef struct { Cell *op, *v; } Redex;
typedef struct { Cell *free[MAXFREE + 1]; Cell *defer; Redex *made; size_t nmade, capmade; } Local;
static __thread Local *L;
static Local *local(void) { if (!L) L = calloc(1, sizeof(Local)); return L; }

Cell *cell(int kind, int n) {
    Local *l = local();
    Cell *c;
    if (n <= MAXFREE && l->free[n]) { c = l->free[n]; l->free[n] = (Cell *)(uintptr_t)c->a; }
    else {
        c = malloc(sizeof(Cell) + (size_t)n * sizeof(Port));
        if (!c) { fputs("out of memory\n", stderr); exit(2); }
        __atomic_store_n(&c->lk, 0, __ATOMIC_RELAXED);
    }
    memset(c->port, 0, (size_t)n * sizeof(Port));
    c->kind = (uint16_t)kind; c->n = (uint16_t)n; c->x = 0; c->ty = 0; c->a = 0; c->p = NULL;
    ADD(stat_cells, 1);
    return c;
}
/* the payload a cell owns */
static bool owns_dnf(int k) { return k == O_PEND || k == V_IV || k == V_FACE || k == V_SYS || k == V_NPAPP || k == O_PAPPP || k == O_BIN2 || k == O_SYSCONS2 || k == V_NTRANS || k == O_TRANSD2 || k == O_IEQB || k == O_FEQLB; }
static bool owns_subst(int k) { return k == O_SUBST || k == V_DEFER; }
static void payload_retain(Cell *c) { if (owns_dnf(c->kind)) dnf_retain(c->p); else if (owns_subst(c->kind)) subst_retain(c->p); }
static void payload_release(Cell *c) {
    if (owns_dnf(c->kind)) dnf_release(c->p); else if (owns_subst(c->kind)) subst_release(c->p);
    c->p = NULL;
}
void cell_free(Cell *c) { payload_release(c); Local *l = local(); c->a = (uint64_t)(uintptr_t)l->defer; l->defer = c; ADD(stat_cells, -1); }
static void flush_frees(void) {
    Local *l = local();
    while (l->defer) {
        Cell *c = l->defer; l->defer = (Cell *)(uintptr_t)c->a;
        if (c->n <= MAXFREE) { c->a = (uint64_t)(uintptr_t)l->free[c->n]; l->free[c->n] = c; }
    }
}
static Cell *clone(const Cell *v) { Cell *c = cell(v->kind, v->n); c->x = v->x; c->ty = v->ty; c->a = v->a; c->p = v->p; payload_retain(c); return c; }

/* a wire is published with release and read with acquire, so a cell is
 * initialized before any thread reaching it through a wire touches it */
static inline Port rd(Cell *c, int k) { return __atomic_load_n(&c->port[k], __ATOMIC_ACQUIRE); }
static void lock(Cell *c) {
    while (__atomic_exchange_n(&c->lk, 1, __ATOMIC_ACQUIRE))
        while (__atomic_load_n(&c->lk, __ATOMIC_RELAXED)) __builtin_ia32_pause();
}
static void unlock(Cell *c) { __atomic_store_n(&c->lk, 0, __ATOMIC_RELEASE); }

/* ---------------- active pairs: per-worker queues ---------------- */
typedef struct { pthread_mutex_t mu; Redex *q; size_t head, len, cap; } Queue;
static Queue *Q; static int NQ;
static __thread int myq;
static long pending;                       /* queued or being rewritten */
static void queues_init(int n) {
    NQ = n; Q = calloc((size_t)n, sizeof(Queue));
    for (int i = 0; i < n; i++) pthread_mutex_init(&Q[i].mu, NULL);
}
void net_push(Cell *op, Cell *v) {
    if (!Q) queues_init(1);
    Queue *q = &Q[myq];
    pthread_mutex_lock(&q->mu);
    if (q->len == q->cap) {
        if (q->head > 0) { memmove(q->q, q->q + q->head, (q->len - q->head) * sizeof(Redex)); q->len -= q->head; q->head = 0; }
        if (q->len == q->cap) { q->cap = q->cap ? q->cap * 2 : 1024; q->q = realloc(q->q, q->cap * sizeof(Redex)); }
    }
    q->q[q->len++] = (Redex){ op, v };
    ADD(pending, 1);
    pthread_mutex_unlock(&q->mu);
}
static bool pop_from(Queue *q, Redex *r) {
    bool got = false;
    pthread_mutex_lock(&q->mu);
    if (q->head < q->len) { *r = q->q[q->head++]; if (q->head == q->len) q->head = q->len = 0; got = true; }
    pthread_mutex_unlock(&q->mu);
    return got;
}
static bool pop(Redex *r) {
    if (!Q) queues_init(1);
    if (pop_from(&Q[myq], r)) return true;
    for (int k = 1; k < NQ; k++) if (pop_from(&Q[(myq + k) % NQ], r)) return true;
    return false;
}

void link(Port a, Port b) {
    if (a) __atomic_store_n(&PC(a)->port[PI(a)], b, __ATOMIC_RELEASE);
    if (b) __atomic_store_n(&PC(b)->port[PI(b)], a, __ATOMIC_RELEASE);
    if (a && b && PI(a) == 0 && PI(b) == 0) {
        Cell *x = PC(a), *y = PC(b);
        Cell *op = NULL, *val = NULL;
        if (is_value(x->kind) && !is_value(y->kind)) { op = y; val = x; }
        else if (is_value(y->kind) && !is_value(x->kind)) { op = x; val = y; }
        if (op && op->kind != O_ROOT) {
            /* held until the replacement creating it is complete */
            Local *l = local();
            if (l->nmade == l->capmade) { l->capmade = l->capmade ? l->capmade * 2 : 64; l->made = realloc(l->made, l->capmade * sizeof(Redex)); }
            l->made[l->nmade++] = (Redex){ op, val };
        }
    }
}
/* publish the active pairs this thread has made */
static void publish(void) {
    Local *l = local();
    for (size_t i = 0; i < l->nmade; i++) net_push(l->made[i].op, l->made[i].v);
    l->nmade = 0;
}
/* move whatever is wired to c's port k onto port `to` */
static void mv(Cell *c, int k, Port to) { link(c->port[k], to); }
static Port out_of(Cell *o) { return o->port[o->n - 1]; }

/* ---------------- small constructors ---------------- */
static void era(Port prov) { Cell *e = cell(O_ERA, 1); link(prov, P(e, 0)); }
static Port sub(Port prov, Subst *s) { Cell *c = cell(O_SUBST, 2); c->p = subst_retain(s); link(prov, P(c, 0)); return P(c, 1); }  /* borrows s */
static Port mkplam_of(Port prov, Dim i) { Cell *m = cell(O_MKPLAM, 2); m->a = i; link(prov, P(m, 0)); return P(m, 1); }
static Port iv_cell(Dnf *r) { Cell *c = cell(V_IV, 1); c->p = r; return P(c, 0); }  /* takes r */
/* m providers sharing one value (a chain of duplicators) */
static void split(Port prov, int m, Port *out) {
    if (m == 0) { era(prov); return; }
    for (int k = 0; k < m - 1; k++) { Cell *d = cell(O_DUP, 3); link(prov, P(d, 0)); out[k] = P(d, 1); prov = P(d, 2); }
    out[m - 1] = prov;
}
void port_split(Port prov, int m, Port *out) { split(prov, m, out); }
static void split_restrict(Port prov, const Dnf *cl, int m, Port *out) {
    split(prov, m, out);
    for (int k = 0; k < m; k++) { Subst *t = subst_of_clause(cl->c[k]); out[k] = sub(out[k], t); subst_release(t); }
}

/* ---------------- types of neutrals ----------------
 * A neutral carries its type on its last port. Eliminating a neutral of
 * known type computes the result's type from it (CCHM: the endpoints of a
 * path are part of its type, so t 0 = u0 for t : Path A u0 u1 even when t
 * is neutral). The type is known when the neutral's head was declared with
 * one (ty = 1); otherwise it is V_UNK. */
static Port unk(void) { return P(cell(V_UNK, 1), 0); }
static bool is_neutral(int k) { return k >= V_NVAR && k <= V_NTRANS; }
static Port tpart(Port T, int k) { Cell *c = cell(O_TPART, 2); c->a = (uint64_t)k; link(T, P(c, 0)); return P(c, 1); }
static Port app2(Port f, Port x) { Cell *a = cell(O_APP, 3); link(f, P(a, 0)); link(x, P(a, 1)); return P(a, 2); }
static Port ntype_of(Port neu) { Cell *c = cell(O_NTYPE, 2); link(neu, P(c, 0)); return P(c, 1); }
static Port papp_at(Port line, Dnf *r) { Cell *a = cell(O_PAPPR, 3); link(iv_cell(r), P(a, 0)); link(line, P(a, 1)); return P(a, 2); }  /* takes r */
static void split2(Port prov, Port *a, Port *b) { Cell *d = cell(O_DUP, 3); link(prov, P(d, 0)); *a = P(d, 1); *b = P(d, 2); }

Port apply_gid(long g, const Port *args, int n) {
    Cell *gc = cell(V_GLOBAL, 1); gc->a = (uint64_t)g;
    Port f = P(gc, 0);
    for (int k = 0; k < n; k++) { Cell *a = cell(O_APP, 3); link(f, P(a, 0)); link(args[k], P(a, 1)); f = P(a, 2); }
    return f;
}
static Port apply_global(const char *name, Port *args, int n) {
    long g = global_lookup(name);
    if (g < 0) { fprintf(stderr, "missing library definition %s\n", name); exit(2); }
    return apply_gid(g, args, n);
}
static Port face_cell(Dnf *f) { Cell *c = cell(V_FACE, 1); c->p = f; return P(c, 0); }  /* takes f */

/* a constructor applied to its fields and dimensions: c v r is its boundary
 * e(v, r) where the boundary's face holds at r (judgmentally), and otherwise
 * a constructor value. Built again after every substitution. */
Port con_build(int c, const Port *f, const Port *d) {
    ConInfo *k = &CON[c];
    int nf = k->nfields, nd = k->ndims, n = nf + nd;
    if (k->bdy < 0) {
        Cell *v = cell(V_CON, n + 1); v->a = (uint64_t)c;
        for (int j = 0; j < nf; j++) link(f[j], P(v, 1 + j));
        for (int j = 0; j < nd; j++) link(d[j], P(v, 1 + nf + j));
        return P(v, 0);
    }
    Port *a = malloc((size_t)(2 * n + 1) * sizeof(Port));
    for (int j = 0; j < n; j++) split2(j < nf ? f[j] : d[j - nf], &a[j], &a[n + j]);
    Port S = apply_gid(k->bdy, a, n), s1, s2;
    split2(S, &s1, &s2);
    Cell *fo = cell(O_FACEOF, 2); link(s1, P(fo, 0));
    Cell *ck = cell(O_CONCHK, n + 3); ck->a = (uint64_t)c;
    link(P(fo, 1), P(ck, 0)); link(s2, P(ck, 1));
    for (int j = 0; j < n; j++) link(a[n + j], P(ck, 2 + j));
    free(a);
    return P(ck, n + 2);
}

/* ---------------- structural rules ---------------- */
static void rule_dup(Cell *o, Cell *v) {
    Port o1 = o->port[1], o2 = o->port[2];
    if (prof_on) {
        ADD(prof_dupk[v->kind & 63], 1);
        if (v->kind == V_LAM) ADD(prof_dup[((Record *)v->p)->where], 1);
        if (v->kind == V_CON && v->a < 4096) ADD(prof_con[v->a], 1);
        if (v->kind == V_GLOBAL && v->a < 65536) ADD(prof_glob[v->a], 1);
    }
    Cell *c1 = clone(v), *c2 = clone(v);
    for (int k = 1; k < v->n; k++) {
        Cell *d = cell(O_DUP, 3);
        link(v->port[k], P(d, 0)); link(P(d, 1), P(c1, k)); link(P(d, 2), P(c2, k));
    }
    link(P(c1, 0), o1); link(P(c2, 0), o2);
    cell_free(o); cell_free(v);
}
static void rule_era(Cell *o, Cell *v) {
    if (prof_on) ADD(prof_erak[v->kind & 63], 1);
    for (int k = 1; k < v->n; k++) era(v->port[k]);
    cell_free(o); cell_free(v);
}

/* substitution of dimensions */
static void rule_subst(Cell *o, Cell *v) {
    Subst *s = o->p;
    Port out = o->port[1];
    switch (v->kind) {
    case V_GLOBAL: case V_UNK:
        link(P(v, 0), out); cell_free(o); return;
    case V_NVAR:
        link(sub(v->port[1], s), P(v, 1));
        link(P(v, 0), out); cell_free(o); return;
    case V_DEFER: {
        /* (g args)[p][s] = (g args)[p;s]: the substitution waits for the value */
        Subst *t = v->p ? subst_compose(v->p, s) : subst_retain(s);
        subst_release(v->p); v->p = t;
        link(P(v, 0), out); cell_free(o); return;
    }
    case V_IV: { Dnf *n2 = iv_subst(v->p, s); dnf_release(v->p); v->p = n2; link(P(v, 0), out); cell_free(o); return; }
    case V_FACE: { Dnf *n2 = face_subst(v->p, s); dnf_release(v->p); v->p = n2; link(P(v, 0), out); cell_free(o); return; }
    case V_PLAM: {
        Dim j = (Dim)v->a, j2 = j;
        Subst *t = subst_without(s, j);
        if (subst_range_mentions(t, j)) {
            j2 = fresh_dim();
            Dnf *at = iv_atom(j2); Subst *t2 = subst_with(t, j, at);
            dnf_release(at); subst_release(t); t = t2;
        }
        link(mkplam_of(sub(v->port[1], t), j2), out);
        subst_release(t);
        cell_free(o); cell_free(v); return;
    }
    case V_SYS: {
        int nb = v->n - 1;
        Dnf *cl = v->p;
        Dnf **f = malloc((size_t)(nb + 1) * sizeof(Dnf *));
        int total = 0;
        for (int k = 0; k < nb; k++) { Dnf *fc = face_of_clause(cl->c[k]); f[k] = face_subst(fc, s); dnf_release(fc); total += (int)f[k]->n; }
        for (int k = 0; k < nb; k++) if (dnf_is_one(f[k])) {
            /* the substitution entails this branch's clause: the system is that value */
            link(sub(v->port[k + 1], s), out);
            for (int m = 0; m < nb; m++) if (m != k) era(v->port[m + 1]);
            for (int m = 0; m < nb; m++) dnf_release(f[m]);
            free(f); cell_free(o); cell_free(v); return;
        }
        Cell *ns = cell(V_SYS, total + 1);
        Clause **ncl = malloc((size_t)(total + 1) * sizeof(Clause *));
        int idx = 0;
        for (int k = 0; k < nb; k++) {
            int m = (int)f[k]->n;
            Port *cp = malloc((size_t)(m + 1) * sizeof(Port));
            split(v->port[k + 1], m, cp);
            for (int q = 0; q < m; q++) {
                ncl[idx] = f[k]->c[q];
                Subst *t = subst_then_clause(s, f[k]->c[q]);
                link(sub(cp[q], t), P(ns, idx + 1));
                subst_release(t);
                idx++;
            }
            free(cp);
        }
        ns->p = clause_list(ncl, (uint32_t)total);
        free(ncl);
        link(P(ns, 0), out);
        for (int m = 0; m < nb; m++) dnf_release(f[m]);
        free(f); cell_free(o); cell_free(v); return;
    }
    /* neutrals and reducible constructors become their operations again */
    case V_NAPP: { Cell *a = cell(O_APP, 3); link(sub(v->port[1], s), P(a, 0)); link(sub(v->port[2], s), P(a, 1)); link(P(a, 2), out); era(v->port[3]); break; }
    case V_NFST: case V_NSND: { Cell *a = cell(v->kind == V_NFST ? O_FST : O_SND, 2); link(sub(v->port[1], s), P(a, 0)); link(P(a, 1), out); era(v->port[2]); break; }
    case V_NPAPP: {
        Cell *a = cell(O_PAPPR, v->x ? 5 : 3); a->x = v->x;
        link(iv_cell(iv_subst(v->p, s)), P(a, 0));
        link(sub(v->port[1], s), P(a, 1));
        if (v->x) { link(sub(v->port[2], s), P(a, 2)); link(sub(v->port[3], s), P(a, 3)); }
        link(P(a, a->n - 1), out);
        era(v->port[v->n - 1]);
        break;
    }
    case V_NCOMP: { Cell *a = cell(O_COMP, 4); link(sub(v->port[2], s), P(a, 0)); link(sub(v->port[1], s), P(a, 1)); link(sub(v->port[3], s), P(a, 2)); link(P(a, 3), out); era(v->port[4]); break; }
    case V_NUNGLUE: { Cell *a = cell(O_UNGLUE, 3); link(sub(v->port[1], s), P(a, 0)); link(sub(v->port[2], s), P(a, 1)); link(P(a, 2), out); era(v->port[3]); break; }
    case V_CON: {
        ConInfo *k = &CON[v->a];
        int n = k->nfields + k->ndims;
        Port *a = malloc((size_t)(n + 1) * sizeof(Port));
        for (int j = 0; j < n; j++) a[j] = sub(v->port[1 + j], s);
        link(con_build((int)v->a, a, a + k->nfields), out);
        free(a);
        break;
    }
    case V_HCOMP: { Cell *a = cell(O_HCOMP, 3); link(sub(v->port[1], s), P(a, 0)); link(sub(v->port[2], s), P(a, 1)); link(P(a, 2), out); break; }
    case V_NCASE: {
        /* 1=scrutinee 2=motive 3..=environment, type → 0=scrutinee 1=motive 2..=environment out */
        Cell *a = cell(O_CASE, v->n - 1); a->x = v->x; a->p = v->p;
        for (int k = 1; k < v->n - 1; k++) link(sub(v->port[k], s), P(a, k - 1));
        link(P(a, a->n - 1), out);
        era(v->port[v->n - 1]);
        break;
    }
    case V_NTRANS: {
        int np = v->n - 3;
        Cell *a = cell(O_TRANSD1, np + 3); a->a = v->a;
        link(face_cell(face_subst(v->p, s)), P(a, 0));
        for (int j = 0; j < np; j++) link(sub(v->port[2 + j], s), P(a, 1 + j));
        link(sub(v->port[1], s), P(a, np + 1));
        link(P(a, np + 2), out);
        era(v->port[v->n - 1]);
        break;
    }
    case V_GLUE: { Cell *a = cell(O_MKGLUE, 3); link(sub(v->port[2], s), P(a, 0)); link(sub(v->port[1], s), P(a, 1)); link(P(a, 2), out); break; }
    case V_GLUEV: { Cell *a = cell(O_MKGLUEV, 3); link(sub(v->port[1], s), P(a, 0)); link(sub(v->port[2], s), P(a, 1)); link(P(a, 2), out); break; }
    default: {
        /* constructors: λ (its environment), pair, Π, Σ, PathP */
        Cell *c = clone(v);
        for (int k = 1; k < v->n; k++) link(sub(v->port[k], s), P(c, k));
        link(P(c, 0), out);
        break;
    }
    }
    cell_free(o); cell_free(v);
}

/* a value is put under a dimension binder; a system whose clauses avoid the
 * dimension is a system of lines */
static void rule_mkplam(Cell *o, Cell *v) {
    Dim i = (Dim)o->a;
    Port out = o->port[1];
    if (v->kind == V_SYS) {
        Dnf *cl = v->p;
        int nb = v->n - 1;
        bool avoid = true;
        for (int k = 0; k < nb; k++) if (clause_mentions(cl->c[k], i)) avoid = false;
        if (avoid) {
            Cell *ns = cell(V_SYS, nb + 1); ns->p = dnf_retain(cl);
            for (int k = 0; k < nb; k++) link(mkplam_of(v->port[k + 1], i), P(ns, k + 1));
            link(P(ns, 0), out);
            cell_free(o); cell_free(v); return;
        }
    }
    Cell *pl = cell(V_PLAM, 2); pl->a = i;
    link(P(v, 0), P(pl, 1));
    link(P(pl, 0), out);
    cell_free(o);
}

/* an eliminator meets a system: it acts branchwise, every other operand
 * restricted to the branch's clause */
static void distribute(Cell *o, Cell *v) {
    int nb = v->n - 1;
    Dnf *cl = v->p;
    Cell *ns = cell(V_SYS, nb + 1); ns->p = dnf_retain(cl);
    Port ex[o->n]; int ne = 0;
    switch (o->kind) {
    case O_APP: case O_UNGLUE2: case O_SYSMAP: ex[ne++] = o->port[1]; break;
    case O_PAPPP: if (o->x) { ex[ne++] = o->port[1]; ex[ne++] = o->port[2]; } break;
    case O_COMPA: ex[ne++] = o->port[1]; ex[ne++] = o->port[2]; break;
    case O_CASE: for (int k = 1; k < o->n - 1; k++) ex[ne++] = o->port[k]; break;
    case O_TRANSD2: for (int k = 1; k < o->n - 1; k++) ex[ne++] = o->port[k]; break;
    default: break;
    }
    Port out = out_of(o);
    Port *cp[o->n];
    for (int e = 0; e < ne; e++) { cp[e] = malloc((size_t)(nb + 1) * sizeof(Port)); split_restrict(ex[e], cl, nb, cp[e]); }
    for (int b = 0; b < nb; b++) {
        Port val = v->port[b + 1], res = P(ns, b + 1);
        Cell *c;
        switch (o->kind) {
        case O_APP: c = cell(O_APP, 3); link(val, P(c, 0)); link(cp[0][b], P(c, 1)); link(P(c, 2), res); break;
        case O_SYSMAP: c = cell(O_APP, 3); link(cp[0][b], P(c, 0)); link(val, P(c, 1)); link(P(c, 2), res); break;
        case O_FST: case O_SND: case O_FORCE: case O_TPART: c = cell(o->kind, 2); c->a = o->a; link(val, P(c, 0)); link(P(c, 1), res); break;
        case O_FACEOF: c = cell(O_FACEOF, 2); link(val, P(c, 0)); link(P(c, 1), res); break;
        case O_PAPPP:
            c = cell(O_PAPPR, o->x ? 5 : 3); c->x = o->x;
            { Subst *t = subst_of_clause(cl->c[b]); link(iv_cell(iv_subst(o->p, t)), P(c, 0)); subst_release(t); }
            link(val, P(c, 1));
            if (o->x) { link(cp[0][b], P(c, 2)); link(cp[1][b], P(c, 3)); }
            link(P(c, c->n - 1), res);
            break;
        case O_UNGLUE2: c = cell(O_UNGLUE, 3); link(cp[0][b], P(c, 0)); link(val, P(c, 1)); link(P(c, 2), res); break;
        case O_COMPA: c = cell(O_COMP, 4); link(cp[0][b], P(c, 0)); link(val, P(c, 1)); link(cp[1][b], P(c, 2)); link(P(c, 3), res); break;
        case O_CASE:
            c = cell(O_CASE, o->n); c->x = o->x; c->p = o->p;
            link(val, P(c, 0));
            for (int e = 0; e < ne; e++) link(cp[e][b], P(c, 1 + e));
            link(P(c, o->n - 1), res);
            break;
        case O_TRANSD2:
            c = cell(O_TRANSD2, o->n); c->a = o->a;
            { Subst *t = subst_of_clause(cl->c[b]); c->p = face_subst(o->p, t); subst_release(t); }
            link(val, P(c, 0));
            for (int e = 0; e < ne; e++) link(cp[e][b], P(c, 1 + e));
            link(P(c, o->n - 1), res);
            break;
        default: fprintf(stderr, "distribute: kind %d\n", o->kind); exit(2);
        }
    }
    for (int e = 0; e < ne; e++) free(cp[e]);
    link(P(ns, 0), out);
    cell_free(o); cell_free(v);
}

/* a stuck projection is a neutral retaining its operand; its type is the
 * Σ's first component, or its second at the first projection */
static void neutral_proj(Cell *o, Cell *v) {
    bool first = o->kind == O_FST;
    Cell *n = cell(first ? V_NFST : V_NSND, 3);
    Port out = o->port[1];
    /* its type is computed from the spine when needed (O_NTYPE): stored, the type of a projection
     * would hold the earlier projections each with its own type, exponential in the depth */
    (void)first;
    link(P(v, 0), P(n, 1)); link(unk(), P(n, 2));
    link(P(n, 0), out);
    cell_free(o);
}

/* ---------------- values as data ----------------
 * %view gives a value's head as a constructor of View (lib/code.ctt) whose fields are the
 * value's own ports: nothing is copied, and a part is read further only by viewing it. */
enum { W_LAM, W_PAIR, W_PI, W_SIGMA, W_U, W_PATH, W_PLAM, W_IV, W_FACE, W_SYS, W_GLUE, W_GLUEV, W_DATA, W_CON,
       W_HCOMP, W_VAR, W_APP, W_FST, W_SND, W_PAPP, W_COMP, W_UNGLUE, W_ELIM, W_TRANS, W_LEVEL, W_OTHER, W_N };
static const char *WNAME[W_N] = { "wlam", "wpair", "wpi", "wsigma", "wu", "wpath", "wplam", "wiv", "wface", "wsys", "wglue",
    "wgluev", "wdata", "wcon", "whcomp", "wvar", "wapp", "wfst", "wsnd", "wpapp", "wcomp", "wunglue", "welim", "wtrans",
    "wlevel", "wother" };
static int WC[W_N], C_NZ = -1, C_NS, C_LNIL, C_LCONS, C_TRUE, C_FALSE;
static void need_cons(void) {
    if (C_NZ >= 0) return;
    for (int w = 0; w < W_N; w++) if ((WC[w] = con_index(WNAME[w])) < 0) { fprintf(stderr, "%%view needs the data type View (lib/code.ctt)\n"); exit(2); }
    C_NS = con_index("ns"); C_LNIL = con_index("lnil"); C_LCONS = con_index("lcons");
    C_TRUE = con_index("true"); C_FALSE = con_index("false");
    if (C_NS < 0 || C_LNIL < 0 || C_LCONS < 0 || C_TRUE < 0 || C_FALSE < 0) { fprintf(stderr, "the checker's data types are missing\n"); exit(2); }
    __atomic_store_n(&C_NZ, con_index("nz"), __ATOMIC_RELEASE);
}
static Port mk(int c, Port a, Port b, Port d, Port e) {
    Port f[4] = { a, b, d, e };
    return con_build(c, f, NULL);
}
static Port numeral_of(uint64_t n) {
    Port p = con_build(C_NZ, NULL, NULL);
    for (uint64_t k = 0; k < n; k++) { Port f[1] = { p }; p = con_build(C_NS, f, NULL); }
    return p;
}
static Port list_of(const Port *xs, int n) {
    Port l = con_build(C_LNIL, NULL, NULL);
    for (int k = n - 1; k >= 0; k--) l = mk(C_LCONS, xs[k], l, 0, 0);
    return l;
}
static Port pair_of(Port a, Port b) { Cell *c = cell(V_PAIR, 3); link(a, P(c, 1)); link(b, P(c, 2)); return P(c, 0); }
static Port face_cell(Dnf *f);
static void rule_view(Cell *o, Cell *v) {
    need_cons();
    Port out = o->port[1], r = 0;
    int vk = v->kind;
    bool keep = false;   /* the value itself is the field */
    switch (vk) {
    case V_LAM: case V_SITEF: case V_CASEF: r = mk(WC[W_LAM], P(v, 0), 0, 0, 0); keep = true; break;
    case V_PLAM: r = mk(WC[W_PLAM], P(v, 0), 0, 0, 0); keep = true; break;
    case V_IV: r = mk(WC[W_IV], P(v, 0), 0, 0, 0); keep = true; break;
    case V_FACE: r = mk(WC[W_FACE], P(v, 0), 0, 0, 0); keep = true; break;
    case V_SUSP: {
        /* an induction hypothesis is its elimination */
        Cell *fo = cell(O_FORCE, 2), *w = cell(O_VIEW, 2);
        link(P(fo, 1), P(w, 0)); link(P(w, 1), out); link(P(v, 0), P(fo, 0));
        cell_free(o); return;
    }
    case V_PAIR: r = mk(WC[W_PAIR], v->port[1], v->port[2], 0, 0); break;
    case V_PI: r = mk(WC[W_PI], v->port[1], v->port[2], 0, 0); break;
    case V_SIGMA: r = mk(WC[W_SIGMA], v->port[1], v->port[2], 0, 0); break;
    case V_U: r = mk(WC[W_U], v->port[1], 0, 0, 0); break;
    case V_PATHP: r = mk(WC[W_PATH], v->port[1], v->port[2], v->port[3], 0); break;
    case V_GLUE: r = mk(WC[W_GLUE], v->port[1], v->port[2], 0, 0); break;
    case V_GLUEV: r = mk(WC[W_GLUEV], v->port[1], v->port[2], 0, 0); break;
    case V_HCOMP: r = mk(WC[W_HCOMP], v->port[1], v->port[2], 0, 0); break;
    case V_SYS: {
        int nb = v->n - 1; Dnf *cl = v->p;
        Port *bs = malloc((size_t)(nb + 1) * sizeof(Port));
        for (int k = 0; k < nb; k++) bs[k] = pair_of(face_cell(face_of_clause(cl->c[k])), v->port[k + 1]);
        r = mk(WC[W_SYS], list_of(bs, nb), 0, 0, 0);
        free(bs);
        break;
    }
    case V_DATA: {
        int d = data_checked_index((int)v->a);
        if (!strcmp(DATA[v->a].name, "Level")) { r = con_build(WC[W_LEVEL], NULL, NULL); break; }
        if (d < 0) { for (int k = 1; k < v->n; k++) era(v->port[k]); r = con_build(WC[W_OTHER], NULL, NULL); break; }
        r = mk(WC[W_DATA], numeral_of((uint64_t)d), list_of(&v->port[1], v->n - 1), 0, 0);
        break;
    }
    case V_CON: {
        /* a constructor of a checked data type, or of Level (as data type 0: levels are read by
         * their constructors only); of any other, nothing the checker reads */
        ConInfo *k = &CON[v->a];
        int d = data_checked_index(k->data);
        if (d < 0 && strcmp(DATA[k->data].name, "Level")) { for (int q = 1; q < v->n; q++) era(v->port[q]); r = con_build(WC[W_OTHER], NULL, NULL); break; }
        r = mk(WC[W_CON], numeral_of((uint64_t)(d < 0 ? 0 : d)), numeral_of((uint64_t)k->index), list_of(&v->port[1], k->nfields), list_of(&v->port[1 + k->nfields], k->ndims));
        break;
    }
    case V_NVAR:
        if (v->a & LVL_TAG) r = mk(WC[W_VAR], numeral_of(v->a & ~LVL_TAG), v->port[1], 0, 0);
        else { era(v->port[1]); r = con_build(WC[W_OTHER], NULL, NULL); }
        break;
    case V_NAPP: r = mk(WC[W_APP], v->port[1], v->port[2], v->port[3], 0); break;
    case V_NFST: r = mk(WC[W_FST], v->port[1], v->port[2], 0, 0); break;
    case V_NSND: r = mk(WC[W_SND], v->port[1], v->port[2], 0, 0); break;
    case V_NPAPP: {
        Cell *iv = cell(V_IV, 1); iv->p = dnf_retain(v->p);
        if (v->x) { era(v->port[2]); era(v->port[3]); }
        r = mk(WC[W_PAPP], v->port[1], P(iv, 0), v->port[v->n - 1], 0);
        break;
    }
    case V_NCOMP: r = mk(WC[W_COMP], v->port[1], v->port[2], v->port[3], v->port[4]); break;
    case V_NUNGLUE: r = mk(WC[W_UNGLUE], v->port[1], v->port[2], v->port[3], 0); break;
    case V_NCASE: {
        /* the elimination as a function of its scrutinee: its table, motive and environment */
        CaseTab *tb = v->p;
        if (data_checked_index(tb->d) < 0) { for (int q = 1; q < v->n; q++) era(v->port[q]); r = con_build(WC[W_OTHER], NULL, NULL); break; }
        Cell *f = cell(V_CASEF, v->n - 2); f->x = v->x; f->p = tb;
        for (int k = 2; k < v->n - 1; k++) link(v->port[k], P(f, k - 1));
        r = mk(WC[W_ELIM], numeral_of((uint64_t)data_checked_index(tb->d)), v->port[1], P(f, 0), v->port[v->n - 1]);
        break;
    }
    case V_NTRANS: {
        int np = v->n - 3;
        if (data_checked_index((int)v->a) < 0) { for (int q = 1; q < v->n; q++) era(v->port[q]); r = con_build(WC[W_OTHER], NULL, NULL); break; }
        Cell *fc = cell(V_FACE, 1); fc->p = dnf_retain(v->p);
        Port l = list_of(&v->port[2], np);
        Port f[5] = { numeral_of((uint64_t)data_checked_index((int)v->a)), P(fc, 0), l, v->port[1], v->port[v->n - 1] };
        r = con_build(WC[W_TRANS], f, NULL);
        break;
    }
    default:
        for (int k = 1; k < v->n; k++) era(v->port[k]);
        r = con_build(WC[W_OTHER], NULL, NULL);
        break;
    }
    link(r, out);
    cell_free(o);
    if (!keep) cell_free(v);
}

/* ---------------- the rules ---------------- */
static void interact(Cell *o, Cell *v) {
    ADD(stat_steps, 1); ADD(stat_kind[o->kind], 1);
    switch (o->kind) {
    case O_ERA: rule_era(o, v); return;
    case O_DUP: rule_dup(o, v); return;
    case O_SUBST: rule_subst(o, v); return;
    case O_MKPLAM: rule_mkplam(o, v); return;
    default: break;
    }
    if (v->kind == V_GLOBAL) {
        if (o->kind == O_APP && site_open(o, v)) return;
        /* a definition is used: its value is copied in */
        Port r = global_copy((long)v->a);
        if (!r) { global_park((long)v->a, o, v); return; }
        link(r, P(o, 0));
        cell_free(v);
        return;
    }
    if (v->kind == V_DEFER) { defer_force(o, v); return; }
    int vk = v->kind;
    if (vk == V_UNK && o->kind != O_VIEW && o->kind != O_CLOS && o->kind != O_CLOS2 && o->kind != O_PEND) {
        /* an eliminator of an unknown type gives an unknown type */
        for (int k = 1; k < o->n - 1; k++) era(o->port[k]);
        link(P(v, 0), out_of(o));
        cell_free(o);
        return;
    }
    switch (o->kind) {
    case O_APP:
        if (vk == V_SITEF) { site_apply(o, v); return; }
        if (vk == V_CASEF) {
            /* the elimination as a function, applied: the case on the argument */
            Cell *c = cell(O_CASE, v->n + 1); c->x = v->x; c->p = v->p;
            mv(o, 1, P(c, 0));
            for (int k = 1; k < v->n; k++) link(v->port[k], P(c, k));
            link(P(c, c->n - 1), o->port[2]);
            cell_free(o); cell_free(v);
            return;
        }
        if (vk == V_LAM && ((Record *)v->p)->nparam == 1) {
            if (prof_on) ADD(prof_count[((Record *)v->p)->where], 1);
            Port r = record_build(v->p, o->port[1], &v->port[1]);
            link(r, o->port[2]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else {
            /* stuck: a neutral application (its type computed from the spine when needed) */
            Cell *n = cell(V_NAPP, 4);
            mv(o, 1, P(n, 2)); link(unk(), P(n, 3));
            link(P(v, 0), P(n, 1));
            link(P(n, 0), o->port[2]);
            cell_free(o);
        }
        return;
    case O_FORCE:
        if (vk == V_LAM && ((Record *)v->p)->nparam == 0) {
            if (prof_on) ADD(prof_count[((Record *)v->p)->where], 1);
            link(record_build(v->p, 0, &v->port[1]), o->port[1]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SUSP) {
            /* an induction hypothesis forced: the elimination of its field */
            /* 1=field [2=motive] environment → 0=field [1=motive] environment out */
            Cell *c = cell(O_CASE, v->n); c->x = v->x; c->p = v->p;
            for (int k = 1; k < v->n; k++) link(v->port[k], P(c, k - 1));
            link(P(c, c->n - 1), o->port[1]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else { link(P(v, 0), o->port[1]); cell_free(o); }
        return;
    case O_FST: case O_SND:
        if (vk == V_PAIR) {
            int keep = o->kind == O_FST ? 1 : 2;
            link(v->port[keep], o->port[1]); era(v->port[3 - keep]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else neutral_proj(o, v);
        return;
    case O_PAPPR: {
        if (vk != V_IV) { fprintf(stderr, "path applied to a non-interval\n"); exit(2); }
        Dnf *r = v->p;
        if (o->x && (dnf_is_zero(r) || dnf_is_one(r))) {
            /* an endpoint: answered without the path */
            int z = dnf_is_zero(r);
            link(o->port[z ? 2 : 3], o->port[4]);
            era(o->port[1]); era(o->port[z ? 3 : 2]);
        } else {
            Cell *pp = cell(O_PAPPP, o->x ? 4 : 2); pp->x = o->x; pp->p = dnf_retain(r);
            mv(o, 1, P(pp, 0));
            if (o->x) { mv(o, 2, P(pp, 1)); mv(o, 3, P(pp, 2)); }
            link(P(pp, pp->n - 1), out_of(o));
        }
        cell_free(o); cell_free(v);
        return;
    }
    case O_PAPPP:
        if (vk == V_PLAM) {
            Subst *t = subst_single((Dim)v->a, o->p);
            link(sub(v->port[1], t), out_of(o));
            subst_release(t);
            if (o->x) { era(o->port[1]); era(o->port[2]); }
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else {
            Dnf *r = o->p;
            if (!o->x && is_neutral(vk) && (dnf_is_zero(r) || dnf_is_one(r))) {
                /* an endpoint of a neutral path, read from its type (computed from a copy of the
                 * spine): t 0 = u0 for t : Path A u0 u1 */
                Port p1, p2; split2(P(v, 0), &p1, &p2);
                Cell *e = cell(O_PEND, 3); e->p = dnf_retain(r);
                Cell *nt = cell(O_NTYPE, 2); link(p1, P(nt, 0)); link(P(nt, 1), P(e, 0));
                link(p2, P(e, 1)); link(P(e, 2), out_of(o));
                cell_free(o);
                return;
            }
            /* stuck: a neutral path application */
            Cell *n = cell(V_NPAPP, o->x ? 5 : 3); n->x = o->x; n->p = dnf_retain(r);
            link(unk(), P(n, n->n - 1));
            link(P(v, 0), P(n, 1));
            if (o->x) { mv(o, 1, P(n, 2)); mv(o, 2, P(n, 3)); }
            link(P(n, 0), out_of(o));
            cell_free(o);
        }
        return;
    case O_COMP:
        if (vk == V_SYS) {
            /* the tube is partial: look at the family */
            Cell *ca = cell(O_COMPA, 4);
            mv(o, 1, P(ca, 0)); link(P(v, 0), P(ca, 1)); mv(o, 2, P(ca, 2)); link(P(ca, 3), o->port[3]);
        } else {
            /* the tube covers: its end */
            Cell *pr = cell(O_PAPPR, 3);
            link(iv_cell(dnf_one()), P(pr, 0)); link(P(v, 0), P(pr, 1)); link(P(pr, 2), o->port[3]);
            era(o->port[1]); era(o->port[2]);
        }
        cell_free(o);
        return;
    case O_COMPA:
        if (vk == V_PLAM) {
            /* the family at its own fresh dimension; its head decides */
            Cell *ch = cell(O_COMPH, 4); ch->a = v->a;
            link(v->port[1], P(ch, 0)); mv(o, 1, P(ch, 1)); mv(o, 2, P(ch, 2)); link(P(ch, 3), o->port[3]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else {
            /* a neutral family: a neutral composition, of type the family at 1 */
            Cell *n = cell(V_NCOMP, 5);
            link(P(v, 0), P(n, 1)); mv(o, 1, P(n, 2)); mv(o, 2, P(n, 3)); link(unk(), P(n, 4));
            link(P(n, 0), o->port[3]);
            cell_free(o);
        }
        return;
    case O_COMPH: {
        Dim i = (Dim)o->a;
        Port u = o->port[1], a0 = o->port[2], out = o->port[3];
        Port args[5];
        const char *clause = NULL; int n = 0;
        switch (vk) {
        case V_PI: case V_SIGMA:
            args[0] = mkplam_of(v->port[1], i); args[1] = mkplam_of(v->port[2], i); args[2] = u; args[3] = a0; n = 4;
            clause = vk == V_PI ? "%comp-pi" : "%comp-sigma"; break;
        case V_PATHP:
            args[0] = mkplam_of(v->port[1], i); args[1] = mkplam_of(v->port[2], i); args[2] = mkplam_of(v->port[3], i);
            args[3] = u; args[4] = a0; n = 5; clause = "%comp-path"; break;
        case V_U: era(v->port[1]); args[0] = u; args[1] = a0; n = 2; clause = "%comp-u"; break;
        case V_DATA: {
            /* CHM: comp = hcomp after transport; %comp-D is generated by the declaration */
            int np = v->n - 1;
            Port *da = malloc((size_t)(np + 3) * sizeof(Port));
            for (int k = 0; k < np; k++) da[k] = mkplam_of(v->port[k + 1], i);
            da[np] = u; da[np + 1] = a0;
            link(apply_gid(DATA[v->a].comp, da, np + 2), out);
            free(da);
            cell_free(o); cell_free(v);
            return;
        }
        case V_GLUE:
            args[0] = mkplam_of(v->port[1], i); args[1] = mkplam_of(v->port[2], i); args[2] = u; args[3] = a0; n = 4;
            clause = "%comp-glue"; break;
        case V_SYS: {
            /* a system of families: each branch whose clause holds along the
             * whole line, ∀i, composes in its own family */
            int nb = v->n - 1; Dnf *cl = v->p;
            int keep = 0;
            for (int k = 0; k < nb; k++) if (!clause_mentions(cl->c[k], i)) keep++;
            Cell *ns = cell(V_SYS, keep + 1);
            Clause **kc = malloc((size_t)(keep + 1) * sizeof(Clause *));
            Port *uc = malloc((size_t)(keep + 1) * sizeof(Port)), *ac = malloc((size_t)(keep + 1) * sizeof(Port));
            int q = 0;
            for (int k = 0; k < nb; k++) if (!clause_mentions(cl->c[k], i)) kc[q++] = cl->c[k];
            Dnf *kl = clause_list(kc, (uint32_t)keep); free(kc);
            ns->p = kl;
            split_restrict(u, kl, keep, uc); split_restrict(a0, kl, keep, ac);
            q = 0;
            for (int k = 0; k < nb; k++) {
                if (clause_mentions(cl->c[k], i)) { era(v->port[k + 1]); continue; }
                Cell *c = cell(O_COMP, 4);
                link(uc[q], P(c, 0)); link(mkplam_of(v->port[k + 1], i), P(c, 1)); link(ac[q], P(c, 2)); link(P(c, 3), P(ns, q + 1));
                q++;
            }
            free(uc); free(ac);
            link(P(ns, 0), out);
            cell_free(o); cell_free(v);
            return;
        }
        default: {
            /* a neutral head: a neutral composition, of type the head at i = 1 */
            Cell *nc = cell(V_NCOMP, 5);
            link(mkplam_of(P(v, 0), i), P(nc, 1)); link(u, P(nc, 2)); link(a0, P(nc, 3)); link(unk(), P(nc, 4)); link(P(nc, 0), out);
            cell_free(o);
            return;
        }
        }
        link(apply_global(clause, args, n), out);
        cell_free(o); cell_free(v);
        return;
    }
    case O_MKGLUE:
        if (vk == V_SYS) { Cell *g = cell(V_GLUE, 3); mv(o, 1, P(g, 1)); link(P(v, 0), P(g, 2)); link(P(g, 0), o->port[2]); }
        else { Cell *f = cell(O_FST, 2); link(P(v, 0), P(f, 0)); link(P(f, 1), o->port[2]); era(o->port[1]); }
        cell_free(o);
        return;
    case O_MKGLUEV:
        if (vk == V_SYS) { Cell *g = cell(V_GLUEV, 3); link(P(v, 0), P(g, 1)); mv(o, 1, P(g, 2)); link(P(g, 0), o->port[2]); }
        else { link(P(v, 0), o->port[2]); era(o->port[1]); }
        cell_free(o);
        return;
    case O_UNGLUE:
        if (vk == V_SYS) {
            Cell *u2 = cell(O_UNGLUE2, 3);
            mv(o, 1, P(u2, 0)); link(P(v, 0), P(u2, 1)); link(P(u2, 2), o->port[2]);
        } else {
            /* on the face: the equivalence's map */
            Cell *sn = cell(O_SND, 2), *f = cell(O_FST, 2), *a = cell(O_APP, 3);
            link(P(v, 0), P(sn, 0)); link(P(sn, 1), P(f, 0)); link(P(f, 1), P(a, 0)); mv(o, 1, P(a, 1)); link(P(a, 2), o->port[2]);
        }
        cell_free(o);
        return;
    case O_UNGLUE2:
        if (vk == V_GLUEV) {
            link(v->port[2], o->port[2]); era(v->port[1]); era(o->port[1]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else {
            /* stuck: a neutral unglue, of type the Glue type's base */
            Cell *n = cell(V_NUNGLUE, 4);
            link(unk(), P(n, 3));
            mv(o, 1, P(n, 1)); link(P(v, 0), P(n, 2)); link(P(n, 0), o->port[2]);
            cell_free(o);
        }
        return;
    case O_FACEOF: {
        Cell *f = cell(V_FACE, 1);
        if (vk == V_SYS) {
            f->p = face_of_clauses(v->p);
            for (int k = 1; k < v->n; k++) era(v->port[k]);
            cell_free(v);
        } else { f->p = dnf_one(); era(P(v, 0)); }
        link(P(f, 0), o->port[1]);
        cell_free(o);
        return;
    }
    case O_NEG:
        if (vk != V_IV) { fprintf(stderr, "~ of a non-interval\n"); exit(2); }
        { Dnf *n2 = iv_neg(v->p); dnf_release(v->p); v->p = n2; }
        link(P(v, 0), o->port[1]); cell_free(o);
        return;
    case O_BIN: {
        if (vk != V_IV && vk != V_FACE) { fprintf(stderr, "lattice operation on a non-interval\n"); exit(2); }
        Cell *b = cell(O_BIN2, 2); b->x = o->x; b->p = dnf_retain(v->p);
        mv(o, 1, P(b, 0)); link(P(b, 1), o->port[2]);
        cell_free(o); cell_free(v);
        return;
    }
    case O_BIN2: {
        bool face = o->x == B_FAND || o->x == B_FOR;
        if (vk != (face ? V_FACE : V_IV)) { fprintf(stderr, "lattice operation on mismatched operands\n"); exit(2); }
        Dnf *n2 = (o->x == B_MEET || o->x == B_FAND) ? dnf_meet(o->p, v->p, face) : dnf_join(o->p, v->p, face);
        dnf_release(v->p); v->p = n2;
        link(P(v, 0), o->port[1]); cell_free(o);
        return;
    }
    case O_FEQ: {
        if (vk != V_IV) { fprintf(stderr, "(= r e) of a non-interval\n"); exit(2); }
        Cell *f = cell(V_FACE, 1); f->p = face_eq(v->p, (int)o->a);
        link(P(f, 0), o->port[1]); cell_free(o); cell_free(v);
        return;
    }
    case O_FORALL:
        if (vk != V_FACE) { fprintf(stderr, "forall of a non-face\n"); exit(2); }
        { Dnf *n2 = face_forall(v->p, (Dim)o->a); dnf_release(v->p); v->p = n2; }
        link(P(v, 0), o->port[1]); cell_free(o);
        return;
    case O_SYSCONS: {
        if (vk != V_FACE) { fprintf(stderr, "system branch guarded by a non-face\n"); exit(2); }
        Dnf *f = v->p;
        if (dnf_is_one(f)) {
            Cell *fo = cell(O_FORCE, 2); mv(o, 1, P(fo, 0)); link(P(fo, 1), o->port[3]); era(o->port[2]);
        } else if (dnf_is_zero(f)) {
            link(o->port[2], o->port[3]); era(o->port[1]);
        } else {
            Cell *s2 = cell(O_SYSCONS2, 3); s2->p = dnf_retain(f);
            mv(o, 2, P(s2, 0)); mv(o, 1, P(s2, 1)); link(P(s2, 2), o->port[3]);
        }
        cell_free(o); cell_free(v);
        return;
    }
    case O_SYSCONS2:
        if (vk == V_SYS) {
            /* the branch, forced under each clause of its face, joins the system */
            Dnf *f = o->p;
            int nb = v->n - 1, m = (int)f->n;
            Cell *ns = cell(V_SYS, nb + m + 1);
            Clause **ncl = malloc((size_t)(nb + m + 1) * sizeof(Clause *));
            Dnf *cl = v->p;
            for (int k = 0; k < nb; k++) { ncl[k] = cl->c[k]; mv(v, k + 1, P(ns, k + 1)); }
            Port *cp = malloc((size_t)(m + 1) * sizeof(Port));
            split_restrict(o->port[1], f, m, cp);
            for (int q = 0; q < m; q++) {
                ncl[nb + q] = f->c[q];
                Cell *fo = cell(O_FORCE, 2); link(cp[q], P(fo, 0)); link(P(fo, 1), P(ns, nb + q + 1));
            }
            ns->p = clause_list(ncl, (uint32_t)(nb + m));
            free(ncl);
            free(cp);
            link(P(ns, 0), o->port[2]);
            cell_free(o); cell_free(v);
        } else {
            /* the rest is total */
            link(P(v, 0), o->port[2]); era(o->port[1]);
            cell_free(o);
        }
        return;
    case O_TPART: {
        int k = (int)o->a;
        if ((vk == V_PI || vk == V_SIGMA || vk == V_PATHP || vk == V_GLUE) && k < v->n) {
            link(v->port[k], o->port[1]);
            for (int m = 1; m < v->n; m++) if (m != k) era(v->port[m]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else { link(unk(), o->port[1]); era(P(v, 0)); cell_free(o); }
        return;
    }
    case O_CONCHK: {
        int n = o->n - 3;
        if (vk == V_FACE && dnf_is_one(v->p)) {
            /* the boundary's face holds: the constructor is its boundary */
            link(o->port[1], o->port[n + 2]);
            for (int j = 0; j < n; j++) era(o->port[2 + j]);
        } else {
            Cell *c = cell(V_CON, n + 1); c->a = o->a;
            for (int j = 0; j < n; j++) mv(o, 2 + j, P(c, 1 + j));
            era(o->port[1]);
            link(P(c, 0), o->port[n + 2]);
        }
        cell_free(o); cell_free(v);
        return;
    }
    case O_HCOMP:
        if (vk == V_SYS) {
            /* a partial tube: a formal hcomp, a value of the data type */
            Cell *h = cell(V_HCOMP, 3);
            link(P(v, 0), P(h, 1)); mv(o, 1, P(h, 2)); link(P(h, 0), o->port[2]);
        } else {
            Cell *pr = cell(O_PAPPR, 3);
            link(iv_cell(dnf_one()), P(pr, 0)); link(P(v, 0), P(pr, 1)); link(P(pr, 2), o->port[2]);
            era(o->port[1]);
        }
        cell_free(o);
        return;
    case O_TRANSD1: {
        int np = o->n - 3;
        if (vk != V_FACE) { fprintf(stderr, "transport face is not a face\n"); exit(2); }
        if (dnf_is_one(v->p)) {
            /* on ψ the family is constant: transport is the identity */
            link(o->port[np + 1], o->port[np + 2]);
            for (int k = 1; k <= np; k++) era(o->port[k]);
        } else {
            Cell *t = cell(O_TRANSD2, np + 2); t->a = o->a; t->p = dnf_retain(v->p);
            mv(o, np + 1, P(t, 0));
            for (int k = 1; k <= np; k++) mv(o, k, P(t, k));
            link(P(t, np + 1), o->port[np + 2]);
        }
        cell_free(o); cell_free(v);
        return;
    }
    case O_TRANSD2: {
        int np = o->n - 2;
        Port out = o->port[np + 1];
        if (vk == V_CON) {
            ConInfo *k = &CON[v->a];
            int n = k->nfields + k->ndims;
            Port *a = malloc((size_t)(np + n + 2) * sizeof(Port));
            for (int j = 0; j < np; j++) a[j] = o->port[1 + j];
            a[np] = face_cell(dnf_retain(o->p));
            for (int j = 0; j < n; j++) a[np + 1 + j] = v->port[1 + j];
            link(apply_gid(k->trans, a, np + 1 + n), out);
            free(a);
            cell_free(o); cell_free(v);
        } else if (vk == V_HCOMP) {
            Port *a = malloc((size_t)(np + 4) * sizeof(Port));
            for (int j = 0; j < np; j++) a[j] = o->port[1 + j];
            a[np] = face_cell(dnf_retain(o->p)); a[np + 1] = v->port[1]; a[np + 2] = v->port[2];
            link(apply_gid(DATA[o->a].transh, a, np + 3), out);
            free(a);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else {
            Cell *n = cell(V_NTRANS, np + 3); n->a = o->a; n->p = dnf_retain(o->p);
            link(P(v, 0), P(n, 1));
            for (int j = 0; j < np; j++) mv(o, 1 + j, P(n, 2 + j));
            link(unk(), P(n, np + 2));
            link(P(n, 0), out);
            cell_free(o);
        }
        return;
    }
    case O_CASE: {
        /* 0=scrutinee [1=motive] then the environment, out */
        CaseTab *tb = o->p;
        int ne = tb->nenv, mb = o->x ? 1 : 0, e0 = 1 + mb;
        if (vk == V_CON) {
            /* the selected branch's body is built with the constructor's fields and dimensions
             * and the shared variables: one interaction. A branch taking induction hypotheses
             * gets, per recursive field, its elimination by the same case, suspended */
            ConInfo *ci = &CON[v->a];
            int k = ci->index, nf = ci->nfields, nd = ci->ndims, nr = ci->nrec;
            bool ih = nr && (tb->mask >> k & 1);
            int np = nf + (ih ? nr : 0) + nd;
            Port prm[np + 1], env[ne + 1];
            if (!ih) {
                for (int j = 0; j < nf + nd; j++) prm[j] = v->port[1 + j];
                for (int e = 0; e < ne; e++) env[e] = o->port[e0 + e];
                if (mb) era(o->port[1]);
            } else {
                Port mc[nr + 1], ec[ne + 1][nr + 2];
                if (mb) split(o->port[1], nr, mc);
                for (int e = 0; e < ne; e++) { split(o->port[e0 + e], nr + 1, ec[e]); env[e] = ec[e][0]; }
                int q = 0;
                for (int j = 0; j < nf; j++) {
                    if (ci->recmask >> j & 1) {
                        Port fa, fb; split2(v->port[1 + j], &fa, &fb);
                        prm[j] = fa;
                        /* 1=field [2=motive] then the environment */
                        Cell *h = cell(V_SUSP, ne + 2 + mb); h->x = o->x; h->p = tb;
                        link(fb, P(h, 1));
                        if (mb) link(mc[q], P(h, 2));
                        for (int e = 0; e < ne; e++) link(ec[e][q + 1], P(h, 2 + mb + e));
                        prm[nf + q] = P(h, 0);
                        q++;
                    } else prm[j] = v->port[1 + j];
                }
                for (int j = 0; j < nd; j++) prm[nf + nr + j] = v->port[1 + nf + j];
            }
            link(record_build_n(tb->br[k], prm, env), o->port[o->n - 1]);
            cell_free(o); cell_free(v);
        } else if (vk == V_HCOMP && o->x) {
            /* f (hcomp^i [φ ↦ u] u0) = comp^i P(hfill) [φ ↦ f u] (f u0), f this elimination */
            Port m1, m2; split2(o->port[1], &m1, &m2);
            Cell *f = cell(V_CASEF, ne + 2); f->x = 1; f->p = tb;
            link(m2, P(f, 1));
            for (int e = 0; e < ne; e++) link(o->port[e0 + e], P(f, 2 + e));
            Port a[4] = { m1, P(f, 0), v->port[1], v->port[2] };
            link(apply_gid(case_hcomp_global, a, 4), o->port[o->n - 1]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else {
            /* stuck: a neutral elimination, of type the motive at the scrutinee */
            /* 1=scrutinee [2=motive] then the environment, type */
            Cell *n = cell(V_NCASE, ne + 3 + mb); n->x = o->x; n->p = tb;
            link(P(v, 0), P(n, 1)); link(unk(), P(n, n->n - 1));
            if (mb) mv(o, 1, P(n, 2));
            for (int e = 0; e < ne; e++) mv(o, e0 + e, P(n, 2 + mb + e));
            link(P(n, 0), o->port[o->n - 1]);
            cell_free(o);
        }
        return;
    }
    case O_VIEW: rule_view(o, v); return;
    case O_MKVAR: case O_MKDIM: case O_ABS: {
        /* 0=level as a numeral: counted one successor per interaction */
        need_cons();
        if (vk != V_CON) { fprintf(stderr, "%%var/%%dim: a level is a numeral\n"); exit(2); }
        if ((int)v->a == C_NS) {
            Cell *c = cell(o->kind, o->n); c->a = o->a + 1;
            for (int k = 1; k < o->n; k++) mv(o, k, P(c, k));
            link(v->port[1], P(c, 0));
            cell_free(o); cell_free(v);
            return;
        }
        if (o->kind == O_MKVAR) {
            Cell *n = cell(V_NVAR, 2); n->a = LVL_TAG | o->a; n->ty = 1;
            mv(o, 1, P(n, 1)); link(P(n, 0), o->port[2]);
        } else if (o->kind == O_ABS) {
            Cell *m = cell(O_MKPLAM, 2); m->a = DIM_LVL + (Dim)o->a;
            mv(o, 1, P(m, 0)); link(P(m, 1), o->port[2]);
        } else {
            Cell *iv = cell(V_IV, 1); iv->p = iv_atom(DIM_LVL + (Dim)o->a); link(P(iv, 0), o->port[1]);
        }
        cell_free(o); cell_free(v);
        return;
    }
    case O_GLOB: {
        need_cons();
        if (vk != V_CON) { fprintf(stderr, "%%gval/%%gty/%%dtab/%%dent: an index is a numeral\n"); exit(2); }
        if ((int)v->a == C_NS) {
            Cell *c = cell(O_GLOB, 2); c->x = o->x; c->a = o->a + 1;
            mv(o, 1, P(c, 1)); link(v->port[1], P(c, 0));
            cell_free(o); cell_free(v);
            return;
        }
        long g = table_global((int)o->x, (long)o->a);
        if (g < 0) { fprintf(stderr, "checker table %u has no entry %llu\n", o->x, (unsigned long long)o->a); exit(2); }
        if (o->x == TB_VAL) {
            /* a checked definition's own value: the checker does not follow the identities
             * declared on it (they are what it checks) */
            Port val = global_copy(g);
            if (!val) { fprintf(stderr, "a checked definition without a value\n"); exit(2); }
            link(val, o->port[1]);
        } else { Cell *r = cell(V_GLOBAL, 1); r->a = (uint64_t)g; link(P(r, 0), o->port[1]); }
        cell_free(o); cell_free(v);
        return;
    }
    case O_NTYPE: {
        Port out = o->port[1], T;
        switch (vk) {
        case V_NVAR: T = v->ty ? v->port[1] : (era(v->port[1]), unk()); break;
        case V_NAPP: era(v->port[3]); T = app2(tpart(ntype_of(v->port[1]), 2), v->port[2]); break;
        case V_NFST: era(v->port[2]); T = tpart(ntype_of(v->port[1]), 1); break;
        case V_NSND: {
            era(v->port[2]);
            Port p1, p2; split2(v->port[1], &p1, &p2);
            Cell *f = cell(O_FST, 2); link(p2, P(f, 0));
            T = app2(tpart(ntype_of(p1), 2), P(f, 1));
            break;
        }
        case V_NPAPP:
            if (v->x) { era(v->port[2]); era(v->port[3]); }
            era(v->port[v->n - 1]);
            T = papp_at(tpart(ntype_of(v->port[1]), 1), dnf_retain(v->p));
            break;
        case V_NCOMP: era(v->port[2]); era(v->port[3]); era(v->port[4]); T = papp_at(v->port[1], dnf_one()); break;
        case V_NUNGLUE: era(v->port[1]); era(v->port[3]); T = tpart(ntype_of(v->port[2]), 1); break;
        case V_NCASE:
            for (int k = 2 + (v->x ? 1 : 0); k < v->n; k++) era(v->port[k]);
            T = v->x ? app2(v->port[2], v->port[1]) : (era(v->port[1]), unk());
            break;
        case V_NTRANS: {
            int np = v->n - 3;
            Cell *d = cell(V_DATA, np + 1); d->a = v->a;
            for (int j = 0; j < np; j++) link(papp_at(v->port[2 + j], dnf_one()), P(d, 1 + j));
            era(v->port[1]); era(v->port[v->n - 1]);
            T = P(d, 0);
            break;
        }
        default: for (int k = 1; k < v->n; k++) era(v->port[k]); T = unk(); break;
        }
        link(T, out);
        cell_free(o);
        cell_free(v);
        return;
    }
    case O_PEND: {
        /* 0=the type, 1=the neutral path, 2=out */
        if (vk == V_PATHP) {
            int z = dnf_is_zero(o->p);
            link(v->port[z ? 2 : 3], o->port[2]); era(v->port[1]); era(v->port[z ? 3 : 2]); era(o->port[1]);
            cell_free(o); cell_free(v);
            return;
        }
        for (int k = 1; k < v->n; k++) era(v->port[k]);
        Cell *n = cell(V_NPAPP, 3); n->p = dnf_retain(o->p);
        mv(o, 1, P(n, 1)); link(unk(), P(n, 2)); link(P(n, 0), o->port[2]);
        cell_free(o); cell_free(v);
        return;
    }
    case O_CLOS: {
        Cell *c = cell(O_CLOS2, 3);
        mv(o, 1, P(c, 0)); link(P(v, 0), P(c, 1)); mv(o, 2, P(c, 2));
        cell_free(o);
        return;
    }
    case O_CLOS2: {
        need_cons();
        static int C_SAME = -1, C_DIFF;
        if (C_SAME < 0) { C_DIFF = con_index("cdiff"); __atomic_store_n(&C_SAME, con_index("csame"), __ATOMIC_RELEASE); }
        if (C_SAME < 0 || C_DIFF < 0) { fprintf(stderr, "%%clos needs CloCmp (lib/code.ctt)\n"); exit(2); }
        Cell *f = PC(o->port[1]);
        bool fl = PI(o->port[1]) == 0 && f->kind == V_LAM;
        if (fl && vk == V_LAM && f->p == v->p && f->n == v->n) {
            /* copies of the two environments, paired; the λs themselves are kept for applying
             * when the environments differ */
            int ne = v->n - 1;
            Port *ps = malloc((size_t)(ne + 1) * sizeof(Port));
            for (int k = 0; k < ne; k++) {
                Port a1, a2, b1, b2;
                split2(f->port[k + 1], &a1, &a2); split2(v->port[k + 1], &b1, &b2);
                link(a2, P(f, k + 1)); link(b2, P(v, k + 1));
                ps[k] = pair_of(a1, b1);
            }
            Port fs[3] = { list_of(ps, ne), P(f, 0), P(v, 0) };
            link(con_build(C_SAME, fs, NULL), o->port[2]);
            free(ps);
            cell_free(o);
            return;
        }
        Port fs[2] = { o->port[1], P(v, 0) };
        link(con_build(C_DIFF, fs, NULL), o->port[2]);
        cell_free(o);
        return;
    }
    case O_BRANCH: {
        /* the branch of an elimination at given fields, hypotheses and dimensions */
        if (vk != V_CASEF) { fprintf(stderr, "%%branch: not an elimination\n"); exit(2); }
        CaseTab *tb = v->p;
        int mb = v->x ? 1 : 0, ne = tb->nenv;
        Cell *c = cell(O_BRANCHC, ne + 3); c->p = tb; c->a = 0;
        mv(o, 1, P(c, 0)); mv(o, 2, P(c, 1));
        if (mb) era(v->port[1]);
        for (int e = 0; e < ne; e++) link(v->port[1 + mb + e], P(c, 2 + e));
        link(P(c, ne + 2), o->port[3]);
        cell_free(o); cell_free(v);
        return;
    }
    case O_BRANCHC: {
        need_cons();
        if (vk != V_CON) { fprintf(stderr, "%%branch: a constructor index is a numeral\n"); exit(2); }
        Cell *c;
        if ((int)v->a == C_NS) {
            c = cell(O_BRANCHC, o->n); c->p = o->p; c->a = o->a + 1;
            for (int k = 1; k < o->n; k++) mv(o, k, P(c, k));
            link(v->port[1], P(c, 0));
        } else {
            /* 0=rest of the list, environment, out */
            c = cell(O_BRANCHL, o->n - 1); c->p = o->p; c->a = o->a; c->x = 0;
            for (int k = 2; k < o->n; k++) mv(o, k, P(c, k - 1));
            mv(o, 1, P(c, 0));
        }
        cell_free(o); cell_free(v);
        return;
    }
    case O_BRANCHL: {
        need_cons();
        CaseTab *tb = o->p;
        int ne = tb->nenv, np = (int)o->x;
        if (vk != V_CON) { fprintf(stderr, "%%branch: parameters are a list\n"); exit(2); }
        if ((int)v->a == C_LCONS) {
            Cell *c = cell(O_BRANCHL, o->n + 1); c->p = tb; c->a = o->a; c->x = (uint32_t)np + 1;
            for (int k = 1; k <= ne + np; k++) mv(o, k, P(c, k));
            link(v->port[1], P(c, ne + np + 1));
            mv(o, o->n - 1, P(c, c->n - 1));
            link(v->port[2], P(c, 0));
            cell_free(o); cell_free(v);
            return;
        }
        /* the parameters are fields, a hypothesis per recursive field, dimensions; a branch not
         * taking hypotheses is given the others */
        ConInfo *ci = &CON[DATA[tb->d].cons[o->a]];
        bool ih = ci->nrec && (tb->mask >> o->a & 1);
        Port env[ne + 1], prm[np + 1];
        int m = 0;
        for (int e = 0; e < ne; e++) env[e] = o->port[1 + e];
        for (int q = 0; q < np; q++) {
            Port x = o->port[1 + ne + q];
            if (!ih && q >= ci->nfields && q < ci->nfields + ci->nrec) era(x); else prm[m++] = x;
        }
        if (m != tb->br[o->a]->nparam) { fprintf(stderr, "%%branch: %d parameters for a branch of %d\n", m, tb->br[o->a]->nparam); exit(2); }
        link(record_build_n(tb->br[o->a], prm, env), o->port[o->n - 1]);
        cell_free(o); cell_free(v);
        return;
    }
    case O_IEQ: case O_FEQL: {
        if (vk != (o->kind == O_IEQ ? V_IV : V_FACE)) { fprintf(stderr, "%%ieq/%%feq: not an interval or face\n"); exit(2); }
        Cell *c = cell(o->kind == O_IEQ ? O_IEQB : O_FEQLB, 2); c->p = dnf_retain(v->p);
        mv(o, 1, P(c, 0)); mv(o, 2, P(c, 1));
        cell_free(o); cell_free(v);
        return;
    }
    case O_IEQB: case O_FEQLB: {
        need_cons();
        if (vk != (o->kind == O_IEQB ? V_IV : V_FACE)) { fprintf(stderr, "%%ieq/%%feq: not an interval or face\n"); exit(2); }
        link(con_build(dnf_equal(o->p, v->p) ? C_TRUE : C_FALSE, NULL, NULL), o->port[1]);
        cell_free(o); cell_free(v);
        return;
    }
    case O_CLAUSES: {
        need_cons();
        if (vk != V_FACE) { fprintf(stderr, "%%clauses: not a face\n"); exit(2); }
        Dnf *d = v->p; int n = d ? (int)d->n : 0;
        Port *cs = malloc((size_t)(n + 1) * sizeof(Port));
        for (int k = 0; k < n; k++) cs[k] = face_cell(face_of_clause(d->c[k]));
        link(list_of(cs, n), o->port[1]);
        free(cs);
        cell_free(o); cell_free(v);
        return;
    }
    case O_RESTRICT: {
        if (vk != V_FACE || !v->p || ((Dnf *)v->p)->n != 1) { fprintf(stderr, "%%restrict: not a clause\n"); exit(2); }
        Subst *t = subst_of_clause(((Dnf *)v->p)->c[0]);
        link(sub(o->port[1], t), o->port[2]);
        subst_release(t);
        cell_free(o); cell_free(v);
        return;
    }
    case O_SYSMAP:
        if (vk == V_SYS) distribute(o, v);
        else { Cell *a = cell(O_APP, 3); mv(o, 1, P(a, 0)); link(P(v, 0), P(a, 1)); link(P(a, 2), o->port[2]); cell_free(o); }
        return;
    default:
        fprintf(stderr, "no rule for operation %d\n", o->kind); exit(2);
    }
}

/* ---------------- rewriting one active pair (HANDOFF §20) ----------------
 * Lock the pair and every cell whose port the rule may rewrite (the pair's
 * neighbours; for a definition, the cell holding its value and that value's
 * cell), in address order; revalidate that the neighbours are unchanged;
 * rewrite; release; then retire the consumed cells. */
static int cell_cmp(const void *x, const void *y) {
    uintptr_t a = (uintptr_t)*(Cell *const *)x, b = (uintptr_t)*(Cell *const *)y;
    return a < b ? -1 : a > b;
}
static int lockset(Cell *o, Cell *v, Cell **S) {
    int n = 0;
    S[n++] = o; S[n++] = v;
    for (int k = 1; k < o->n; k++) { Port p = rd(o, k); if (p) S[n++] = PC(p); }
    for (int k = 1; k < v->n; k++) { Port p = rd(v, k); if (p) S[n++] = PC(p); }
    if (v->kind == V_GLOBAL) { Cell *r = global_res((long)v->a); S[n++] = r; Port p = rd(r, 0); if (p) S[n++] = PC(p); }
    qsort(S, (size_t)n, sizeof(Cell *), cell_cmp);
    int m = 0;
    for (int i = 0; i < n; i++) if (m == 0 || S[m - 1] != S[i]) S[m++] = S[i];
    return m;
}
static void rewrite(Redex r) {
    Cell *o = r.op, *v = r.v;
    int cap = o->n + v->n + 4;
    Cell *buf1[64], *buf2[64];
    Cell **S = cap <= 64 ? buf1 : malloc((size_t)cap * sizeof(Cell *));
    Cell **T = cap <= 64 ? buf2 : malloc((size_t)cap * sizeof(Cell *));
    int n;
    for (;;) {
        n = lockset(o, v, S);
        for (int i = 0; i < n; i++) lock(S[i]);
        int m = lockset(o, v, T), j = 0;
        bool ok = true;
        for (int i = 0; i < m && ok; i++) { while (j < n && S[j] < T[i]) j++; if (j == n || S[j] != T[i]) ok = false; }
        if (ok) break;
        for (int i = n - 1; i >= 0; i--) unlock(S[i]);
    }
    interact(o, v);
    for (int i = n - 1; i >= 0; i--) unlock(S[i]);
    flush_frees();
    publish();
    if (cap > 64) { free(S); free(T); }
    ADD(pending, -1);
}

/* ---------------- workers ---------------- */
static int nworkers;
static pthread_t *workers;
static pthread_mutex_t wmu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t wcv = PTHREAD_COND_INITIALIZER, pcv = PTHREAD_COND_INITIALIZER;
static int running, parked;
static void *worker(void *arg) {
    myq = (int)(intptr_t)arg;
    for (;;) {
        if (!__atomic_load_n(&running, __ATOMIC_ACQUIRE)) {
            pthread_mutex_lock(&wmu);
            parked++; pthread_cond_broadcast(&pcv);
            while (!__atomic_load_n(&running, __ATOMIC_ACQUIRE)) pthread_cond_wait(&wcv, &wmu);
            parked--;
            pthread_mutex_unlock(&wmu);
        }
        Redex r;
        if (pop(&r)) rewrite(r); else sched_yield();
    }
    return NULL;
}
void net_start(int n) {
    queues_init(n + 1);
    nworkers = n;
    workers = calloc((size_t)n + 1, sizeof(pthread_t));
    for (int i = 0; i < n; i++) pthread_create(&workers[i], NULL, worker, (void *)(intptr_t)(i + 1));
    pthread_mutex_lock(&wmu);
    while (parked < nworkers) pthread_cond_wait(&pcv, &wmu);
    pthread_mutex_unlock(&wmu);
}
static bool observed(Cell *root) {
    if (!root) return false;
    lock(root);
    Port q = root->port[0];
    bool ok = q && PI(q) == 0 && is_value(PC(q)->kind);
    unlock(root);
    return ok;
}
/* an observation: reduce, every worker taking pairs in arrival order, until
 * the observed port holds a value; the rest of the net stands */
bool net_observe(Cell *root, long limit) {
    publish();
    if (nworkers) { pthread_mutex_lock(&wmu); __atomic_store_n(&running, 1, __ATOMIC_RELEASE); pthread_cond_broadcast(&wcv); pthread_mutex_unlock(&wmu); }
    long n = 0;
    bool ok;
    for (;;) {
        if ((ok = observed(root))) break;
        if (__atomic_load_n(&pending, __ATOMIC_ACQUIRE) == 0 || (limit >= 0 && n >= limit)) break;
        Redex r;
        if (pop(&r)) { rewrite(r); n++; } else sched_yield();
    }
    if (nworkers) {
        pthread_mutex_lock(&wmu);
        __atomic_store_n(&running, 0, __ATOMIC_RELEASE);
        while (parked < nworkers) pthread_cond_wait(&pcv, &wmu);
        pthread_mutex_unlock(&wmu);
    }
    return ok || observed(root);
}
/* reduce every pending pair: the workload's normal form, or what waits on an input */
void net_drain(void) { net_observe(NULL, -1); }

/* ---------------- building a net from syntax ---------------- */
typedef struct { Port *sup; int cur, n; } Supply;
typedef struct { Supply *s; int nslots; const int *uses; } Frame;

static void bind(Frame *f, int slot, Port prov) {
    int u = f->uses[slot];
    Supply *s = &f->s[slot];
    s->sup = malloc((size_t)(u + 1) * sizeof(Port)); s->n = u; s->cur = 0;
    split(prov, u, s->sup);
}
static void bind_dim(Frame *f, int slot, Dim i) {
    int u = f->uses[slot];
    Supply *s = &f->s[slot];
    s->sup = malloc((size_t)(u + 1) * sizeof(Port)); s->n = u; s->cur = 0;
    for (int k = 0; k < u; k++) s->sup[k] = iv_cell(iv_atom(i));
}
static Port build(Syn *t, Frame *f);
static Port op1(int kind, Syn *a, Frame *f) { Cell *c = cell(kind, 2); link(build(a, f), P(c, 0)); return P(c, 1); }

static Port build(Syn *t, Frame *f) {
    Cell *c;
    switch (t->tag) {
    case S_VAR: {
        Supply *s = &f->s[t->slot];
        if (s->cur >= s->n) { fprintf(stderr, "internal: slot %d used beyond its count\n", t->slot); exit(2); }
        return s->sup[s->cur++];
    }
    case S_LAM:
        c = cell(V_LAM, t->n + 1); c->p = t->rec;
        for (int k = 0; k < t->n; k++) link(build(t->k[k], f), P(c, k + 1));
        return P(c, 0);
    case S_APP: c = cell(O_APP, 3); link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); return P(c, 2);
    case S_PAIR: c = cell(V_PAIR, 3); goto fields;
    case S_PI: c = cell(V_PI, 3); goto fields;
    case S_SIGMA: c = cell(V_SIGMA, 3); goto fields;
    case S_PATHP: c = cell(V_PATHP, 4); goto fields;
    fields:
        for (int k = 0; k < c->n - 1; k++) link(build(t->k[k], f), P(c, k + 1));
        return P(c, 0);
    case S_FST: return op1(O_FST, t->k[0], f);
    case S_SND: return op1(O_SND, t->k[0], f);
    case S_U: {
        /* U at its level: lzero when none is written */
        c = cell(V_U, 2);
        if (t->n) link(build(t->k[0], f), P(c, 1));
        else { int z = con_index("lzero"); if (z < 0) { fprintf(stderr, "U needs Level (lib/prelude.ctt)\n"); exit(2); } link(con_build(z, NULL, NULL), P(c, 1)); }
        return P(c, 0);
    }
    case S_GLOBTAB:
        c = cell(O_GLOB, 2); c->x = t->x;
        link(build(t->k[0], f), P(c, 0));
        return P(c, 1);
    case S_PRIM:
        c = cell((int)t->x, t->n + 1);
        for (int k = 0; k < t->n; k++) link(build(t->k[k], f), P(c, k));
        return P(c, t->n);
    case S_PLAM: {
        Dim i = fresh_dim();
        bind_dim(f, t->slot, i);
        Cell *m = cell(O_MKPLAM, 2); m->a = i;
        link(build(t->k[0], f), P(m, 0));
        return P(m, 1);
    }
    case S_FORALL: {
        Dim i = fresh_dim();
        bind_dim(f, t->slot, i);
        Cell *m = cell(O_FORALL, 2); m->a = i;
        link(build(t->k[0], f), P(m, 0));
        return P(m, 1);
    }
    case S_PAPP:
        c = cell(O_PAPPR, t->x ? 5 : 3); c->x = t->x;
        link(build(t->k[1], f), P(c, 0)); link(build(t->k[0], f), P(c, 1));
        if (t->x) { link(build(t->k[2], f), P(c, 2)); link(build(t->k[3], f), P(c, 3)); }
        return P(c, c->n - 1);
    case S_IV0: return iv_cell(dnf_zero());
    case S_IV1: return iv_cell(dnf_one());
    case S_NEG: return op1(O_NEG, t->k[0], f);
    case S_BIN: c = cell(O_BIN, 3); c->x = t->x; link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); return P(c, 2);
    case S_FEQ: c = cell(O_FEQ, 2); c->a = t->x; link(build(t->k[0], f), P(c, 0)); return P(c, 1);
    case S_FTT: c = cell(V_FACE, 1); c->p = dnf_one(); return P(c, 0);
    case S_FFF: c = cell(V_FACE, 1); c->p = dnf_zero(); return P(c, 0);
    case S_FACEOF: return op1(O_FACEOF, t->k[0], f);
    case S_SYS0: c = cell(V_SYS, 1); c->p = NULL; return P(c, 0);
    case S_SYSCONS:
        c = cell(O_SYSCONS, 4);
        link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); link(build(t->k[2], f), P(c, 2));
        return P(c, 3);
    case S_SYSMAP: c = cell(O_SYSMAP, 3); link(build(t->k[1], f), P(c, 0)); link(build(t->k[0], f), P(c, 1)); return P(c, 2);
    case S_COMP:
        c = cell(O_COMP, 4);
        link(build(t->k[1], f), P(c, 0)); link(build(t->k[0], f), P(c, 1)); link(build(t->k[2], f), P(c, 2));
        return P(c, 3);
    case S_GLUE: c = cell(O_MKGLUE, 3); link(build(t->k[1], f), P(c, 0)); link(build(t->k[0], f), P(c, 1)); return P(c, 2);
    case S_GLUEV: c = cell(O_MKGLUEV, 3); link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); return P(c, 2);
    case S_UNGLUE: c = cell(O_UNGLUE, 3); link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); return P(c, 2);
    case S_GLOBAL: c = cell(V_GLOBAL, 1); c->a = (uint64_t)t->id; return P(c, 0);
    case S_AXIOM:
        c = cell(V_NVAR, 2); c->a = (uint64_t)t->id;
        if (t->slot >= 0) { Cell *g = cell(V_GLOBAL, 1); g->a = (uint64_t)t->slot; link(P(g, 0), P(c, 1)); c->ty = 1; }
        else link(unk(), P(c, 1));
        return P(c, 0);
    case S_FORCE: return op1(O_FORCE, t->k[0], f);
    case S_DATA: c = cell(V_DATA, t->n + 1); c->a = (uint64_t)t->id; goto fields;
    case S_CON: {
        Port *a = malloc((size_t)(t->n + 1) * sizeof(Port));
        for (int k = 0; k < t->n; k++) a[k] = build(t->k[k], f);
        Port r = con_build((int)t->id, a, a + CON[t->id].nfields);
        free(a);
        return r;
    }
    case S_HCOMPD: c = cell(O_HCOMP, 3); link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); return P(c, 2);
    case S_TRANSD:
        c = cell(O_TRANSD1, t->n + 1); c->a = (uint64_t)t->id;
        for (int k = 0; k < t->n; k++) link(build(t->k[k], f), P(c, k));
        return P(c, t->n);
    case S_CASE: {
        /* k[0]=scrutinee k[1]=motive (or none) k[2..]=the shared variables */
        int ne = t->tab->nenv, mb = t->x ? 1 : 0;
        c = cell(O_CASE, ne + 2 + mb); c->x = t->x; c->p = t->tab;
        link(build(t->k[0], f), P(c, 0));
        if (mb) link(build(t->k[1], f), P(c, 1));
        for (int e = 0; e < ne; e++) link(build(t->k[2 + e], f), P(c, 1 + mb + e));
        return P(c, c->n - 1);
    }
    case S_LET: {
        bind(f, t->slot, build(t->k[0], f));
        return build(t->k[1], f);
    }
    }
    fprintf(stderr, "build: tag %d\n", t->tag); exit(2);
}

static Port run_frame(Syn *body, int nslots, const int *uses, int nparam, const Port *params, int nenv, const int *env_slot, const Port *env) {
    Frame f = { calloc((size_t)nslots + 1, sizeof(Supply)), nslots, uses };
    for (int k = 0; k < nparam; k++) bind(&f, k, params[k]);
    for (int k = 0; k < nenv; k++) bind(&f, env_slot[k], env[k]);
    Port r = build(body, &f);
    for (int k = 0; k < nslots; k++) {
        if (f.s[k].cur != f.s[k].n) { fprintf(stderr, "internal: slot %d built %d of %d uses\n", k, f.s[k].cur, f.s[k].n); exit(2); }
        free(f.s[k].sup);
    }
    free(f.s);
    return r;
}
Port record_build(const Record *r, Port param, const Port *env) {
    return run_frame(r->body, r->nslots, r->uses, r->nparam, &param, r->nenv, r->env_slot, env);
}
Port record_build_n(const Record *r, const Port *params, const Port *env) {
    return run_frame(r->body, r->nslots, r->uses, r->nparam, params, r->nenv, r->env_slot, env);
}
Port top_build(Syn *body, int nslots, const int *uses) {
    return run_frame(body, nslots, uses, 0, NULL, 0, NULL, NULL);
}
