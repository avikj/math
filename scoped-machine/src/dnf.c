/* dnf.c — the interval (free De Morgan algebra) and the face lattice.
 *
 * Both are joins of clauses (meets of literals), kept as an antichain.
 * An interval literal is a dimension or its negation; i ∧ ~i is NOT zero.
 * A face literal is (i = 0) or (i = 1); (i=0) ∧ (i=1) is false.
 * The free bounded distributive lattice on the literals has the antichain
 * of clauses as canonical form, so 0, 1 and equality are read off directly.
 *
 * Payloads are immutable and reference counted. Every function borrows its
 * arguments and returns a reference its caller owns.
 */
#include "core.h"
#include <string.h>

static Dim next_dim = 1;
Dim fresh_dim(void) { return __atomic_fetch_add(&next_dim, 1, __ATOMIC_RELAXED); }

long stat_payloads;
#define LIVE(d) __atomic_fetch_add(&stat_payloads, (d), __ATOMIC_RELAXED)
static Clause *cl_new(uint32_t n) { Clause *c = malloc(sizeof(Clause) + n * sizeof(uint64_t)); c->rc = 1; c->n = n; LIVE(1); return c; }
static Dnf *dnf_new(uint32_t n) { Dnf *d = malloc(sizeof(Dnf) + n * sizeof(Clause *)); d->rc = 1; d->n = n; LIVE(1); return d; }
Clause *clause_retain(Clause *c) { __atomic_fetch_add(&c->rc, 1, __ATOMIC_RELAXED); return c; }
void clause_release(Clause *c) { if (c && __atomic_sub_fetch(&c->rc, 1, __ATOMIC_ACQ_REL) == 0) { free(c); LIVE(-1); } }
Dnf *dnf_retain(Dnf *d) { if (d) __atomic_fetch_add(&d->rc, 1, __ATOMIC_RELAXED); return d; }
void dnf_release(Dnf *d) {
    if (d && __atomic_sub_fetch(&d->rc, 1, __ATOMIC_ACQ_REL) == 0) {
        for (uint32_t i = 0; i < d->n; i++) clause_release(d->c[i]);
        free(d); LIVE(-1);
    }
}
/* a list of clauses taken as given (a system's branches): retains each */
Dnf *clause_list(Clause *const *c, uint32_t n) {
    Dnf *d = dnf_new(n);
    for (uint32_t i = 0; i < n; i++) d->c[i] = clause_retain(c[i]);
    return d;
}

static int cl_cmp(const Clause *a, const Clause *b) {
    if (a->n != b->n) return a->n < b->n ? -1 : 1;
    for (uint32_t i = 0; i < a->n; i++) if (a->l[i] != b->l[i]) return a->l[i] < b->l[i] ? -1 : 1;
    return 0;
}
static int cl_qcmp(const void *x, const void *y) { return cl_cmp(*(Clause *const *)x, *(Clause *const *)y); }
static bool cl_subset(const Clause *a, const Clause *b) {
    uint32_t i = 0, j = 0;
    while (i < a->n && j < b->n) {
        if (a->l[i] == b->l[j]) { i++; j++; }
        else if (a->l[i] > b->l[j]) j++;
        else return false;
    }
    return i == a->n;
}
/* union of two clauses; for faces NULL when a dimension gets both endpoints */
static Clause *cl_union(const Clause *a, const Clause *b, bool face) {
    Clause *c = cl_new(a->n + b->n);
    uint32_t i = 0, j = 0, k = 0;
    while (i < a->n || j < b->n) {
        uint64_t x;
        if (j >= b->n || (i < a->n && a->l[i] < b->l[j])) x = a->l[i++];
        else if (i >= a->n || b->l[j] < a->l[i]) x = b->l[j++];
        else { x = a->l[i]; i++; j++; }
        if (face && k > 0 && (c->l[k - 1] >> 1) == (x >> 1)) { clause_release(c); return NULL; }
        c->l[k++] = x;
    }
    c->n = k;
    return c;
}
/* normalize, consuming the references in a: drop NULLs, sort, dedup, absorb */
static Dnf *normalize(Clause **a, uint32_t n) {
    uint32_t m = 0;
    for (uint32_t i = 0; i < n; i++) if (a[i]) a[m++] = a[i];
    qsort(a, m, sizeof(Clause *), cl_qcmp);
    Dnf *d = dnf_new(m);
    uint32_t k = 0;
    for (uint32_t i = 0; i < m; i++) {
        bool absorbed = false;
        for (uint32_t j = 0; j < k && !absorbed; j++) if (cl_subset(d->c[j], a[i])) absorbed = true;
        if (absorbed) clause_release(a[i]); else d->c[k++] = a[i];
    }
    d->n = k;
    return d;
}

Dnf *dnf_zero(void) { return dnf_new(0); }
Dnf *dnf_one(void) { Dnf *d = dnf_new(1); d->c[0] = cl_new(0); return d; }
static Dnf *dnf_lit(uint64_t lit) { Dnf *d = dnf_new(1); d->c[0] = cl_new(1); d->c[0]->l[0] = lit; return d; }
Dnf *iv_atom(Dim i) { return dnf_lit(i << 1); }
bool dnf_is_zero(const Dnf *x) { return x->n == 0; }
bool dnf_is_one(const Dnf *x) { return x->n == 1 && x->c[0]->n == 0; }
bool clause_mentions(const Clause *c, Dim i) {
    for (uint32_t k = 0; k < c->n; k++) if ((c->l[k] >> 1) == i) return true;
    return false;
}
bool dnf_mentions(const Dnf *x, Dim i) {
    for (uint32_t j = 0; j < x->n; j++) if (clause_mentions(x->c[j], i)) return true;
    return false;
}
Dnf *dnf_join(const Dnf *x, const Dnf *y, bool face) {
    (void)face;
    Clause **a = malloc((x->n + y->n + 1) * sizeof(Clause *));
    uint32_t n = 0;
    for (uint32_t i = 0; i < x->n; i++) a[n++] = clause_retain(x->c[i]);
    for (uint32_t i = 0; i < y->n; i++) a[n++] = clause_retain(y->c[i]);
    Dnf *d = normalize(a, n);
    free(a);
    return d;
}
Dnf *dnf_meet(const Dnf *x, const Dnf *y, bool face) {
    Clause **a = malloc(((size_t)x->n * y->n + 1) * sizeof(Clause *));
    uint32_t n = 0;
    for (uint32_t i = 0; i < x->n; i++)
        for (uint32_t j = 0; j < y->n; j++) a[n++] = cl_union(x->c[i], y->c[j], face);
    Dnf *d = normalize(a, n);
    free(a);
    return d;
}
/* acc := acc ∧ d / acc ∨ d, releasing both */
static Dnf *meet_into(Dnf *acc, Dnf *d, bool face) { Dnf *r = dnf_meet(acc, d, face); dnf_release(acc); dnf_release(d); return r; }
static Dnf *join_into(Dnf *acc, Dnf *d, bool face) { Dnf *r = dnf_join(acc, d, face); dnf_release(acc); dnf_release(d); return r; }

/* ~(∨_c ∧_l l) = ∧_c ∨_l ~l */
Dnf *iv_neg(const Dnf *x) {
    Dnf *acc = dnf_one();
    for (uint32_t i = 0; i < x->n; i++) {
        Dnf *d = dnf_zero();
        for (uint32_t k = 0; k < x->c[i]->n; k++) d = join_into(d, dnf_lit(x->c[i]->l[k] ^ 1), false);
        acc = meet_into(acc, d, false);
    }
    return acc;
}
const Dnf *subst_get(const Subst *s, Dim j) {
    for (uint32_t i = 0; i < s->n; i++) if (s->d[i] == j) return s->v[i];
    return NULL;
}
Dnf *iv_subst(const Dnf *x, const Subst *s) {
    Dnf *acc = dnf_zero();
    for (uint32_t i = 0; i < x->n; i++) {
        Dnf *m = dnf_one();
        for (uint32_t k = 0; k < x->c[i]->n; k++) {
            uint64_t lit = x->c[i]->l[k];
            const Dnf *v = subst_get(s, lit >> 1);
            Dnf *w = v ? dnf_retain((Dnf *)v) : iv_atom(lit >> 1);
            if (lit & 1) { Dnf *nw = iv_neg(w); dnf_release(w); w = nw; }
            m = meet_into(m, w, false);
        }
        acc = join_into(acc, m, false);
    }
    return acc;
}
/* (r = 0) is the meet over clauses of the join of (l = 0);
 * (r = 1) is the join over clauses of the meet of (l = 1).
 * (i = e) is the face literal i<<1|e; (~i = e) is (i = 1-e). */
Dnf *face_eq(const Dnf *r, int eps) {
    if (eps == 0) {
        Dnf *acc = dnf_one();
        for (uint32_t i = 0; i < r->n; i++) {
            Dnf *d = dnf_zero();
            for (uint32_t k = 0; k < r->c[i]->n; k++) d = join_into(d, dnf_lit(r->c[i]->l[k]), true);
            acc = meet_into(acc, d, true);
        }
        return acc;
    }
    Dnf *acc = dnf_zero();
    for (uint32_t i = 0; i < r->n; i++) {
        Dnf *m = dnf_one();
        for (uint32_t k = 0; k < r->c[i]->n; k++) m = meet_into(m, dnf_lit(r->c[i]->l[k] ^ 1), true);
        acc = join_into(acc, m, true);
    }
    return acc;
}
Dnf *face_subst(const Dnf *f, const Subst *s) {
    Dnf *acc = dnf_zero();
    for (uint32_t i = 0; i < f->n; i++) {
        Dnf *m = dnf_one();
        for (uint32_t k = 0; k < f->c[i]->n; k++) {
            uint64_t lit = f->c[i]->l[k];
            const Dnf *v = subst_get(s, lit >> 1);
            m = meet_into(m, v ? face_eq(v, (int)(lit & 1)) : dnf_lit(lit), true);
        }
        acc = join_into(acc, m, true);
    }
    return acc;
}
Dnf *face_of_clause(const Clause *c) { Dnf *d = dnf_new(1); d->c[0] = clause_retain((Clause *)c); return d; }
Dnf *face_of_clauses(const Dnf *list) {
    uint32_t n = list ? list->n : 0;
    Clause **a = malloc((n + 1) * sizeof(Clause *));
    for (uint32_t i = 0; i < n; i++) a[i] = clause_retain(list->c[i]);
    Dnf *d = normalize(a, n);
    free(a);
    return d;
}
Dnf *face_forall(const Dnf *f, Dim i) {
    Clause **a = malloc((f->n + 1) * sizeof(Clause *));
    uint32_t n = 0;
    for (uint32_t k = 0; k < f->n; k++) if (!clause_mentions(f->c[k], i)) a[n++] = clause_retain(f->c[k]);
    Dnf *d = normalize(a, n);
    free(a);
    return d;
}

void (*subst_hook_retain)(void *box);
void (*subst_hook_release)(void *box);
void *(*subst_hook_then)(void *box, const Subst *t);
static Subst *subst_new(uint32_t n) {
    Subst *s = malloc(sizeof(Subst));
    s->rc = 1; s->n = n; s->d = malloc((n + 1) * sizeof(Dim)); s->v = malloc((n + 1) * sizeof(Dnf *));
    s->nt = 0; s->tx = NULL; s->tv = NULL;
    LIVE(1);
    return s;
}
static void terms_alloc(Subst *s, uint32_t n) { s->tx = malloc((n + 1) * sizeof(uint64_t)); s->tv = malloc((n + 1) * sizeof(void *)); s->nt = 0; }
static void term_add(Subst *s, uint64_t x, void *box) { s->tx[s->nt] = x; s->tv[s->nt] = box; s->nt++; }
void *subst_term_get(const Subst *s, uint64_t x) { for (uint32_t i = 0; i < s->nt; i++) if (s->tx[i] == x) return s->tv[i]; return NULL; }
Subst *subst_term(uint64_t x, void *box) { Subst *s = subst_new(0); terms_alloc(s, 1); term_add(s, x, box); return s; }
/* t's term entries copied into u (retained), unless u already maps the variable */
static void terms_copy(Subst *u, const Subst *s) {
    for (uint32_t i = 0; i < s->nt; i++) if (!subst_term_get(u, s->tx[i])) { subst_hook_retain(s->tv[i]); term_add(u, s->tx[i], s->tv[i]); }
}
Subst *subst_retain(Subst *s) { if (s) __atomic_fetch_add(&s->rc, 1, __ATOMIC_RELAXED); return s; }
void subst_release(Subst *s) {
    if (s && __atomic_sub_fetch(&s->rc, 1, __ATOMIC_ACQ_REL) == 0) {
        for (uint32_t i = 0; i < s->n; i++) dnf_release(s->v[i]);
        for (uint32_t i = 0; i < s->nt; i++) subst_hook_release(s->tv[i]);
        free(s->d); free(s->v); free(s->tx); free(s->tv); free(s); LIVE(-1);
    }
}
Subst *subst_single(Dim i, const Dnf *r) { Subst *s = subst_new(1); s->d[0] = i; s->v[0] = dnf_retain((Dnf *)r); return s; }
Subst *subst_of_clause(const Clause *c) {
    Subst *s = subst_new(c->n);
    for (uint32_t k = 0; k < c->n; k++) { s->d[k] = c->l[k] >> 1; s->v[k] = (c->l[k] & 1) ? dnf_one() : dnf_zero(); }
    return s;
}
Subst *subst_then_clause(const Subst *s, const Clause *d) {
    Subst *ds = subst_of_clause(d);
    Subst *t = subst_new(s->n + d->n);
    uint32_t n = 0;
    for (uint32_t i = 0; i < s->n; i++) { t->d[n] = s->d[i]; t->v[n] = iv_subst(s->v[i], ds); n++; }
    for (uint32_t k = 0; k < ds->n; k++)
        if (!subst_get(s, ds->d[k])) { t->d[n] = ds->d[k]; t->v[n] = dnf_retain(ds->v[k]); n++; }
    t->n = n;
    if (s->nt) { terms_alloc(t, s->nt); for (uint32_t i = 0; i < s->nt; i++) term_add(t, s->tx[i], subst_hook_then(s->tv[i], ds)); }
    subst_release(ds);
    return t;
}
bool subst_range_mentions(const Subst *s, Dim j) {
    for (uint32_t i = 0; i < s->n; i++) if (dnf_mentions(s->v[i], j)) return true;
    return false;
}
Subst *subst_without(const Subst *s, Dim j) {
    Subst *t = subst_new(s->n);
    uint32_t n = 0;
    for (uint32_t i = 0; i < s->n; i++) if (s->d[i] != j) { t->d[n] = s->d[i]; t->v[n] = dnf_retain(s->v[i]); n++; }
    t->n = n;
    if (s->nt) { terms_alloc(t, s->nt); terms_copy(t, s); }
    return t;
}
Subst *subst_with(const Subst *s, Dim j, const Dnf *r) {
    Subst *t = subst_new(s->n + 1);
    uint32_t n = 0;
    for (uint32_t i = 0; i < s->n; i++) if (s->d[i] != j) { t->d[n] = s->d[i]; t->v[n] = dnf_retain(s->v[i]); n++; }
    t->d[n] = j; t->v[n] = dnf_retain((Dnf *)r); n++;
    t->n = n;
    if (s->nt) { terms_alloc(t, s->nt); terms_copy(t, s); }
    return t;
}
/* s, then t: x ↦ s(x)[t], and t's entries for the dimensions s leaves alone */
Subst *subst_compose(const Subst *s, const Subst *t) {
    Subst *u = subst_new(s->n + t->n);
    uint32_t n = 0;
    for (uint32_t i = 0; i < s->n; i++) { u->d[n] = s->d[i]; u->v[n] = iv_subst(s->v[i], t); n++; }
    for (uint32_t k = 0; k < t->n; k++)
        if (!subst_get(s, t->d[k])) { u->d[n] = t->d[k]; u->v[n] = dnf_retain(t->v[k]); n++; }
    u->n = n;
    if (s->nt || t->nt) {
        terms_alloc(u, s->nt + t->nt);
        /* x ↦ s(x) then t; t's own variables s leaves alone */
        for (uint32_t i = 0; i < s->nt; i++) term_add(u, s->tx[i], subst_hook_then(s->tv[i], t));
        terms_copy(u, t);
    }
    return u;
}
/* s without its entry for the term variable x */
Subst *subst_minus_term(const Subst *s, uint64_t x) {
    Subst *u = subst_new(s->n);
    for (uint32_t i = 0; i < s->n; i++) { u->d[i] = s->d[i]; u->v[i] = dnf_retain(s->v[i]); }
    if (s->nt) { terms_alloc(u, s->nt); for (uint32_t i = 0; i < s->nt; i++) if (s->tx[i] != x) { subst_hook_retain(s->tv[i]); term_add(u, s->tx[i], s->tv[i]); } }
    return u;
}
Subst *subst_id(void) { return subst_new(0); }

void clause_print(FILE *o, const Clause *c, DimName nm) {
    if (c->n == 0) { fputs("tt", o); return; }
    if (c->n > 1) fputs("(&", o);
    for (uint32_t k = 0; k < c->n; k++) fprintf(o, "%s(= %s %u)", c->n > 1 ? " " : "", nm(c->l[k] >> 1), (unsigned)(c->l[k] & 1));
    if (c->n > 1) fputs(")", o);
}
void dnf_print(FILE *o, const Dnf *x, bool face, DimName nm) {
    if (face) {
        if (x->n == 0) { fputs("ff", o); return; }
        if (x->n > 1) fputs("(|", o);
        for (uint32_t i = 0; i < x->n; i++) { if (x->n > 1) fputc(' ', o); clause_print(o, x->c[i], nm); }
        if (x->n > 1) fputs(")", o);
        return;
    }
    if (x->n == 0) { fputs("0", o); return; }
    if (dnf_is_one(x)) { fputs("1", o); return; }
    if (x->n > 1) fputs("(\\/", o);
    for (uint32_t i = 0; i < x->n; i++) {
        const Clause *c = x->c[i];
        if (x->n > 1) fputc(' ', o);
        if (c->n > 1) fputs("(/\\", o);
        for (uint32_t k = 0; k < c->n; k++) {
            if (c->n > 1) fputc(' ', o);
            if (c->l[k] & 1) fprintf(o, "(~ %s)", nm(c->l[k] >> 1)); else fputs(nm(c->l[k] >> 1), o);
        }
        if (c->n > 1) fputs(")", o);
    }
    if (x->n > 1) fputs(")", o);
}

/* equality of canonical forms: the same antichain of clauses, each the same set of literals */
static bool clause_equal(const Clause *a, const Clause *b) {
    if (a->n != b->n) return false;
    for (uint32_t i = 0; i < a->n; i++) {
        bool found = false;
        for (uint32_t j = 0; j < b->n && !found; j++) found = a->l[i] == b->l[j];
        if (!found) return false;
    }
    return true;
}
bool dnf_equal(const Dnf *x, const Dnf *y) {
    uint32_t nx = x ? x->n : 0, ny = y ? y->n : 0;
    if (nx != ny) return false;
    for (uint32_t i = 0; i < nx; i++) {
        bool found = false;
        for (uint32_t j = 0; j < ny && !found; j++) found = clause_equal(x->c[i], y->c[j]);
        if (!found) return false;
    }
    return true;
}
