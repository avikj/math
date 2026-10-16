#include "dnf.h"
#include "fine.h"

void dnf_init(Dnf *d) { d->c = NULL; d->n = d->cap = 0; }

void dnf_free(Dnf *d) {
    for (size_t i = 0; i < d->n; i++) free(d->c[i].a);
    free(d->c);
    d->c = NULL; d->n = d->cap = 0;
}

static Clause *dnf_new_clause(Dnf *d) {
    if (d->n == d->cap) {
        d->cap = d->cap ? d->cap * 2 : 4;
        d->c = realloc(d->c, d->cap * sizeof(Clause));
        require(d->c, "out of memory");
    }
    Clause *c = &d->c[d->n++];
    c->a = NULL; c->n = c->cap = 0;
    return c;
}

static void clause_reserve(Clause *c, size_t n) {
    if (n > c->cap) {
        c->cap = n < 4 ? 4 : n;
        c->a = realloc(c->a, c->cap * sizeof(uint64_t));
        require(c->a, "out of memory");
    }
}

void dnf_add_clause(Dnf *d, const uint64_t *atoms, size_t n) {
    Clause *c = dnf_new_clause(d); fine_add(FC_DNF_CLAUSE_STEPS, n + 1);
    clause_reserve(c, n);
    if (n) memcpy(c->a, atoms, n * sizeof(uint64_t));
    c->n = n;
}

void dnf_add_clause_union(Dnf *d, const Clause *x, const Clause *y) {
    Clause *c = dnf_new_clause(d); fine_add(FC_DNF_CLAUSE_STEPS, x->n + y->n + 1);
    clause_reserve(c, x->n + y->n);
    if (x->n) memcpy(c->a, x->a, x->n * sizeof(uint64_t));
    if (y->n) memcpy(c->a + x->n, y->a, y->n * sizeof(uint64_t));
    c->n = x->n + y->n;
}

bool clause_subset(const Clause *small, const Clause *big) {
    size_t i = 0, j = 0;
    while (i < small->n) {
        fine_bump(FC_DNF_CLAUSE_STEPS);
        if (j >= big->n) return false;
        if (small->a[i] == big->a[j]) { i++; j++; }
        else if (small->a[i] > big->a[j]) j++;
        else return false;
    }
    return true;
}

static int clause_cmp(const void *pa, const void *pb) {
    const Clause *a = pa, *b = pb;
    if (a->n != b->n) return a->n < b->n ? -1 : 1;
    for (size_t i = 0; i < a->n; i++)
        if (a->a[i] != b->a[i]) return a->a[i] < b->a[i] ? -1 : 1;
    return 0;
}

void dnf_normalize(Dnf *d, bool (*contradiction)(const Clause *)) {
    /* 1. normalize each clause */
    for (size_t i = 0; i < d->n; i++) { fine_add(FC_DNF_CLAUSE_STEPS, d->c[i].n + 1); d->c[i].n = sort_unique_u64(d->c[i].a, d->c[i].n); }
    /* 2. drop contradictory clauses (faces only) */
    if (contradiction) {
        size_t j = 0;
        for (size_t i = 0; i < d->n; i++) {
            if (contradiction(&d->c[i])) free(d->c[i].a);
            else d->c[j++] = d->c[i];
        }
        d->n = j;
    }
    /* 3. sort clauses, remove duplicates */
    if (d->n > 1) qsort(d->c, d->n, sizeof(Clause), clause_cmp);
    {
        size_t j = 0;
        for (size_t i = 0; i < d->n; i++) {
            if (j > 0 && clause_cmp(&d->c[j - 1], &d->c[i]) == 0) free(d->c[i].a);
            else d->c[j++] = d->c[i];
        }
        d->n = j;
    }
    /* 4. absorption: remove any clause strictly containing another.
     * Since clauses are sorted by length, a container is always later than
     * the clause it contains. */
    {
        bool *dead = calloc(d->n ? d->n : 1, sizeof(bool));
        require(dead, "out of memory");
        for (size_t i = 0; i < d->n; i++) {
            if (dead[i]) continue;
            for (size_t k = i + 1; k < d->n; k++) {
                fine_bump(FC_DNF_CLAUSE_STEPS);
                if (dead[k] || d->c[k].n <= d->c[i].n) continue;
                if (clause_subset(&d->c[i], &d->c[k])) dead[k] = true;
            }
        }
        size_t j = 0;
        for (size_t i = 0; i < d->n; i++) {
            if (dead[i]) free(d->c[i].a);
            else d->c[j++] = d->c[i];
        }
        d->n = j;
        free(dead);
    }
}

void dnf_decode(Dnf *d, const uint64_t *w, size_t n) {
    dnf_init(d);
    require(n >= 1, "malformed DNF record");
    size_t nc = (size_t)w[0], p = 1;
    for (size_t i = 0; i < nc; i++) {
        require(p < n, "malformed DNF record");
        size_t len = (size_t)w[p++];
        require(p + len <= n, "malformed DNF record");
        dnf_add_clause(d, w + p, len);
        p += len;
    }
}

void dnf_encode(const Dnf *d, Words *out) {
    words_push(out, (uint64_t)d->n);
    for (size_t i = 0; i < d->n; i++) {
        words_push(out, (uint64_t)d->c[i].n);
        words_append(out, d->c[i].a, d->c[i].n);
    }
}
