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

/* the clause loops are frame families (kframe.h): one transition per literal / clause step, a suspension point after each */
KF_DECL_EXT(dnf_add_clause, void, dnf_add_clause_PARAMS, Clause *c; size_t i;)
KF_STEP(dnf_add_clause) {
    KF_BEGIN(dnf_add_clause);
    F->c = dnf_new_clause(F->d); fine_bump(FC_DNF_CLAUSE_STEPS);
    clause_reserve(F->c, F->n);
    for (F->i = 0; F->i < F->n; F->i++) { F->c->a[F->i] = F->atoms[F->i]; fine_bump(FC_DNF_CLAUSE_STEPS); KF_SAFE(); }   /* one transition per literal (§94) */
    F->c->n = F->n;
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(dnf_add_clause, dnf_add_clause_PARAMS, dnf_add_clause(Dnf *d, const uint64_t *atoms, size_t n))

KF_DECL_EXT(dnf_add_clause_union, void, dnf_add_clause_union_PARAMS, Clause *c; size_t i;)
KF_STEP(dnf_add_clause_union) {
    KF_BEGIN(dnf_add_clause_union);
    F->c = dnf_new_clause(F->d); fine_bump(FC_DNF_CLAUSE_STEPS);
    clause_reserve(F->c, F->x->n + F->y->n);
    for (F->i = 0; F->i < F->x->n; F->i++) { F->c->a[F->i] = F->x->a[F->i]; fine_bump(FC_DNF_CLAUSE_STEPS); KF_SAFE(); }
    for (F->i = 0; F->i < F->y->n; F->i++) { F->c->a[F->x->n + F->i] = F->y->a[F->i]; fine_bump(FC_DNF_CLAUSE_STEPS); KF_SAFE(); }
    F->c->n = F->x->n + F->y->n;
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(dnf_add_clause_union, dnf_add_clause_union_PARAMS, dnf_add_clause_union(Dnf *d, const Clause *x, const Clause *y))

KF_DECL_EXT(clause_subset, bool, clause_subset_PARAMS, size_t i, j;)
KF_STEP(clause_subset) {
    KF_BEGIN(clause_subset);
    F->i = 0; F->j = 0;
    while (F->i < F->small->n) {
        fine_bump(FC_DNF_CLAUSE_STEPS);
        if (F->j >= F->big->n) KF_RET(false);
        if (F->small->a[F->i] == F->big->a[F->j]) { F->i++; F->j++; }
        else if (F->small->a[F->i] > F->big->a[F->j]) F->j++;
        else KF_RET(false);
        KF_SAFE();
    }
    KF_RET(true);
    KF_END;
}
KF_SYNC_DEF(clause_subset, bool, clause_subset_PARAMS, clause_subset(const Clause *small, const Clause *big))

#define clause_cmp_PARAMS(X) X(const Clause *, a) X(const Clause *, b)
KF_DECL(clause_cmp, int, clause_cmp_PARAMS, size_t i;)
KF_STEP(clause_cmp) {
    KF_BEGIN(clause_cmp);
    if (F->a->n != F->b->n) KF_RET(F->a->n < F->b->n ? -1 : 1);
    for (F->i = 0; F->i < F->a->n; F->i++) {
        fine_bump(FC_DNF_CLAUSE_STEPS);
        if (F->a->a[F->i] != F->b->a[F->i]) KF_RET(F->a->a[F->i] < F->b->a[F->i] ? -1 : 1);
        KF_SAFE();
    }
    KF_RET(0);
    KF_END;
}
/* §94: clauses are heap-sorted, one sift per transition (≤ 64 iterations of a bounded comparison each) */
#define clause_sift_PARAMS(X) X(Clause *, h) X(size_t, n) X(size_t, i)
KF_DECL(clause_sift, void, clause_sift_PARAMS, size_t l, r, m; int c;)
KF_STEP(clause_sift) {
    KF_BEGIN(clause_sift);
    for (;;) {
        F->l = 2 * F->i + 1; F->r = F->l + 1; F->m = F->i;
        if (F->l < F->n) { KF_CALL(clause_cmp, &F->c, &F->h[F->l], &F->h[F->m]); if (F->c > 0) F->m = F->l; }
        if (F->r < F->n) { KF_CALL(clause_cmp, &F->c, &F->h[F->r], &F->h[F->m]); if (F->c > 0) F->m = F->r; }
        if (F->m == F->i) KF_RETV();
        { Clause t = F->h[F->i]; F->h[F->i] = F->h[F->m]; F->h[F->m] = t; }
        F->i = F->m;
    }
    KF_END;
}
#define clauses_sort_PARAMS(X) X(Clause *, c) X(size_t, n)
KF_DECL(clauses_sort, void, clauses_sort_PARAMS, size_t i, e;)
KF_STEP(clauses_sort) {
    KF_BEGIN(clauses_sort);
    if (F->n < 2) KF_RETV();
    for (F->i = F->n / 2; F->i > 0; F->i--) { KF_CALL(clause_sift, NULL, F->c, F->n, F->i - 1); fine_bump(FC_SORT_STEPS); }
    for (F->e = F->n - 1; F->e > 0; F->e--) { Clause t = F->c[0]; F->c[0] = F->c[F->e]; F->c[F->e] = t; KF_CALL(clause_sift, NULL, F->c, F->e, 0); fine_bump(FC_SORT_STEPS); }
    KF_RETV();
    KF_END;
}

KF_DECL_EXT_DROP(dnf_normalize, void, dnf_normalize_PARAMS, dnf_normalize_drop, size_t i, j, k; bool *dead; int c; bool sub;)
static void dnf_normalize_drop(dnf_normalize_F *F) { free(F->dead); F->dead = NULL; }
KF_STEP(dnf_normalize) {
    KF_BEGIN(dnf_normalize);
    /* 1. normalize each clause */
    for (F->i = 0; F->i < F->d->n; F->i++) { fine_bump(FC_DNF_CLAUSE_STEPS); KF_CALL(sort_unique_u64, &F->d->c[F->i].n, F->d->c[F->i].a, F->d->c[F->i].n); }   /* the sort's sifts are transitions */
    /* 2. drop contradictory clauses (faces only) */
    if (F->contradiction) {
        size_t j = 0;
        for (size_t i = 0; i < F->d->n; i++) {
            if (F->contradiction(&F->d->c[i])) free(F->d->c[i].a);
            else F->d->c[j++] = F->d->c[i];
        }
        F->d->n = j;
    }
    /* 3. sort clauses, remove duplicates */
    KF_CALL(clauses_sort, NULL, F->d->c, F->d->n);
    F->j = 0;
    for (F->i = 0; F->i < F->d->n; F->i++) {
        F->c = 1;
        if (F->j > 0) KF_CALL(clause_cmp, &F->c, &F->d->c[F->j - 1], &F->d->c[F->i]);
        if (F->c == 0) free(F->d->c[F->i].a);
        else F->d->c[F->j++] = F->d->c[F->i];
    }
    F->d->n = F->j;
    /* 4. absorption: remove any clause strictly containing another.
     * Since clauses are sorted by length, a container is always later than
     * the clause it contains. */
    F->dead = calloc(F->d->n ? F->d->n : 1, sizeof(bool));
    require(F->dead, "out of memory");
    for (F->i = 0; F->i < F->d->n; F->i++) {
        if (F->dead[F->i]) continue;
        for (F->k = F->i + 1; F->k < F->d->n; F->k++) {
            fine_bump(FC_DNF_CLAUSE_STEPS);
            if (F->dead[F->k] || F->d->c[F->k].n <= F->d->c[F->i].n) { KF_SAFE(); continue; }
            KF_CALL(clause_subset, &F->sub, &F->d->c[F->i], &F->d->c[F->k]);
            if (F->sub) F->dead[F->k] = true;
        }
    }
    {
        size_t j = 0;
        for (size_t i = 0; i < F->d->n; i++) {
            if (F->dead[i]) free(F->d->c[i].a);
            else F->d->c[j++] = F->d->c[i];
        }
        F->d->n = j;
    }
    free(F->dead); F->dead = NULL;
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(dnf_normalize, dnf_normalize_PARAMS, dnf_normalize(Dnf *d, ClauseTest contradiction))

KF_DECL_EXT(dnf_decode, void, dnf_decode_PARAMS, size_t nc, p, i, len;)
KF_STEP(dnf_decode) {
    KF_BEGIN(dnf_decode);
    dnf_init(F->d);
    require(F->n >= 1, "malformed DNF record");
    F->nc = (size_t)F->w[0]; F->p = 1;
    for (F->i = 0; F->i < F->nc; F->i++) {
        require(F->p < F->n, "malformed DNF record");
        F->len = (size_t)F->w[F->p++];
        require(F->p + F->len <= F->n, "malformed DNF record");
        KF_CALL(dnf_add_clause, NULL, F->d, F->w + F->p, F->len);
        F->p += F->len;
    }
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(dnf_decode, dnf_decode_PARAMS, dnf_decode(Dnf *d, const uint64_t *w, size_t n))

KF_DECL_EXT(dnf_encode, void, dnf_encode_PARAMS, size_t i;)
KF_STEP(dnf_encode) {
    KF_BEGIN(dnf_encode);
    words_push(F->out, (uint64_t)F->d->n);
    for (F->i = 0; F->i < F->d->n; F->i++) {
        words_push(F->out, (uint64_t)F->d->c[F->i].n);
        KF_CALL(words_append, NULL, F->out, F->d->c[F->i].a, F->d->c[F->i].n);
    }
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(dnf_encode, dnf_encode_PARAMS, dnf_encode(const Dnf *d, Words *out))
