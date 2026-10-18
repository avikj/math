#include "face.h"
#include "fine.h"

static bool face_contradiction(const Clause *c) {
    /* sorted: (i=0) = 2i and (i=1) = 2i+1 are adjacent when both present */
    for (size_t k = 0; k + 1 < c->n; k++)
        if ((c->a[k] & 1u) == 0 && c->a[k + 1] == c->a[k] + 1) return true;
    return false;
}

KF_DECL_EXT_DROP(fc_from_dnf, FaceId, fc_from_dnf_PARAMS, fc_from_dnf_drop, Words w; FaceId id;)
static void fc_from_dnf_drop(fc_from_dnf_F *F) { words_free(&F->w); dnf_free(F->d); }
KF_STEP(fc_from_dnf) {
    KF_BEGIN(fc_from_dnf);
    KF_CALL(dnf_normalize, NULL, F->d, face_contradiction);
    words_init(&F->w);
    KF_CALL(dnf_encode, NULL, F->d, &F->w);
    KF_CALL(interner_intern, &F->id, &M.faces, F->w.w, F->w.n, NULL);
    words_free(&F->w);
    dnf_free(F->d);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(fc_from_dnf, FaceId, fc_from_dnf_PARAMS, fc_from_dnf(Dnf *d))

KF_DECL_EXT(fc_to_dnf, void, fc_to_dnf_PARAMS, )
KF_STEP(fc_to_dnf) {
    KF_BEGIN(fc_to_dnf);
    { size_t n; const uint64_t *w = interner_get(&M.faces, F->a, &n); KF_CALL(dnf_decode, NULL, F->d, w, n); }
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(fc_to_dnf, fc_to_dnf_PARAMS, fc_to_dnf(FaceId a, Dnf *d))

/* a constant face of at most one clause of at most one literal */
#define fc_small_PARAMS(X) X(int, nclauses) X(uint64_t, lit) X(int, nlits)
KF_DECL_DROP(fc_small, FaceId, fc_small_PARAMS, fc_small_drop, Dnf d; FaceId id;)
static void fc_small_drop(fc_small_F *F) { dnf_free(&F->d); }
KF_STEP(fc_small) {
    KF_BEGIN(fc_small);
    dnf_init(&F->d);
    if (F->nclauses) KF_CALL(dnf_add_clause, NULL, &F->d, &F->lit, (size_t)F->nlits);
    KF_CALL(fc_from_dnf, &F->id, &F->d);
    KF_RET(F->id);
    KF_END;
}
KF_DECL_EXT(fc_false, FaceId, KF_NOPARAMS, FaceId r;)
KF_STEP(fc_false) { KF_BEGIN(fc_false); KF_CALL(fc_small, &F->r, 0, 0, 0); KF_RET(F->r); KF_END; }
FaceId fc_false(void) { FaceId r; KStack *s_ = kf_sync_begin(); fc_false_push(s_, &r); kf_sync_run(s_); kf_sync_end(s_); return r; }
KF_DECL_EXT(fc_true, FaceId, KF_NOPARAMS, FaceId r;)
KF_STEP(fc_true) { KF_BEGIN(fc_true); KF_CALL(fc_small, &F->r, 1, 0, 0); KF_RET(F->r); KF_END; }
FaceId fc_true(void) { FaceId r; KStack *s_ = kf_sync_begin(); fc_true_push(s_, &r); kf_sync_run(s_); kf_sync_end(s_); return r; }
KF_DECL_EXT(fc_lit, FaceId, fc_lit_PARAMS, FaceId r;)
KF_STEP(fc_lit) { KF_BEGIN(fc_lit); KF_CALL(fc_small, &F->r, 1, FC_LIT(F->i, F->eps), 1); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(fc_lit, FaceId, fc_lit_PARAMS, fc_lit(DimVarId i, int eps))
bool fc_is_false(FaceId a) { size_t n; const uint64_t *w = interner_get(&M.faces, a, &n); return w[0] == 0; }
bool fc_is_true(FaceId a) { size_t n; const uint64_t *w = interner_get(&M.faces, a, &n); return w[0] == 1 && w[1] == 0; }

KF_DECL_EXT_DROP(fc_join, FaceId, fc_join_PARAMS, fc_join_drop, Dnf x, y; size_t i; FaceId id;)
static void fc_join_drop(fc_join_F *F) { dnf_free(&F->x); dnf_free(&F->y); }
KF_STEP(fc_join) {
    KF_BEGIN(fc_join);
    fine_bump(FC_FACE_OPS);
    KF_CALL(fc_to_dnf, NULL, F->a, &F->x); KF_CALL(fc_to_dnf, NULL, F->b, &F->y);
    for (F->i = 0; F->i < F->y.n; F->i++) KF_CALL(dnf_add_clause, NULL, &F->x, F->y.c[F->i].a, F->y.c[F->i].n);
    dnf_free(&F->y);
    KF_CALL(fc_from_dnf, &F->id, &F->x);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(fc_join, FaceId, fc_join_PARAMS, fc_join(FaceId a, FaceId b))

KF_DECL_EXT_DROP(fc_meet, FaceId, fc_meet_PARAMS, fc_meet_drop, Dnf x, y, out; size_t i, j; FaceId id;)
static void fc_meet_drop(fc_meet_F *F) { dnf_free(&F->x); dnf_free(&F->y); dnf_free(&F->out); }
KF_STEP(fc_meet) {
    KF_BEGIN(fc_meet);
    fine_bump(FC_FACE_OPS);
    KF_CALL(fc_to_dnf, NULL, F->a, &F->x); KF_CALL(fc_to_dnf, NULL, F->b, &F->y); dnf_init(&F->out);
    for (F->i = 0; F->i < F->x.n; F->i++)
        for (F->j = 0; F->j < F->y.n; F->j++)
            KF_CALL(dnf_add_clause_union, NULL, &F->out, &F->x.c[F->i], &F->y.c[F->j]);
    dnf_free(&F->x); dnf_free(&F->y);
    KF_CALL(fc_from_dnf, &F->id, &F->out);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(fc_meet, FaceId, fc_meet_PARAMS, fc_meet(FaceId a, FaceId b))

/* (¬i = eps) = (i = 1-eps) */
#define atom_endpoint_PARAMS(X) X(uint64_t, atom) X(int, eps)
KF_DECL(atom_endpoint, FaceId, atom_endpoint_PARAMS, FaceId r;)
KF_STEP(atom_endpoint) { KF_BEGIN(atom_endpoint); KF_CALL(fc_lit, &F->r, IV_ATOM_DIM(F->atom), IV_ATOM_NEG(F->atom) ? 1 - F->eps : F->eps); KF_RET(F->r); KF_END; }

KF_DECL_EXT_DROP(fc_endpoint, FaceId, fc_endpoint_PARAMS, fc_endpoint_drop, Dnf a; size_t i, k; FaceId out, cl, t;)
static void fc_endpoint_drop(fc_endpoint_F *F) { dnf_free(&F->a); }
KF_STEP(fc_endpoint) {
    KF_BEGIN(fc_endpoint);
    KF_CALL(iv_to_dnf, NULL, F->r, &F->a);
    if (F->eps == 1) {
        /* (r=1) = OR over clauses of AND over atoms of (a=1) */
        KF_CALL0(fc_false, &F->out);
        for (F->i = 0; F->i < F->a.n; F->i++) {
            KF_CALL0(fc_true, &F->cl);
            for (F->k = 0; F->k < F->a.c[F->i].n; F->k++) { KF_CALL(atom_endpoint, &F->t, F->a.c[F->i].a[F->k], 1); KF_CALL(fc_meet, &F->cl, F->cl, F->t); }
            KF_CALL(fc_join, &F->out, F->out, F->cl);
        }
    } else {
        /* (r=0) = AND over clauses of OR over atoms of (a=0) */
        KF_CALL0(fc_true, &F->out);
        for (F->i = 0; F->i < F->a.n; F->i++) {
            KF_CALL0(fc_false, &F->cl);
            for (F->k = 0; F->k < F->a.c[F->i].n; F->k++) { KF_CALL(atom_endpoint, &F->t, F->a.c[F->i].a[F->k], 0); KF_CALL(fc_join, &F->cl, F->cl, F->t); }
            KF_CALL(fc_meet, &F->out, F->out, F->cl);
        }
    }
    dnf_free(&F->a);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(fc_endpoint, FaceId, fc_endpoint_PARAMS, fc_endpoint(IntervalId r, int eps))

KF_DECL_EXT_DROP(fc_substitute, FaceId, fc_substitute_PARAMS, fc_substitute_drop, Dnf a; size_t i, k; FaceId out, cl, t; IntervalId im; uint64_t l;)
static void fc_substitute_drop(fc_substitute_F *F) { dnf_free(&F->a); }
KF_STEP(fc_substitute) {
    KF_BEGIN(fc_substitute);
    KF_CALL(fc_to_dnf, NULL, F->phi, &F->a);
    KF_CALL0(fc_false, &F->out);
    for (F->i = 0; F->i < F->a.n; F->i++) {
        KF_CALL0(fc_true, &F->cl);
        for (F->k = 0; F->k < F->a.c[F->i].n; F->k++) {
            F->l = F->a.c[F->i].a[F->k];
            KF_CALLP(F->img, &F->im, FC_LIT_DIM(F->l), F->ctx);
            KF_CALL(fc_endpoint, &F->t, F->im, FC_LIT_EPS(F->l));
            KF_CALL(fc_meet, &F->cl, F->cl, F->t);
        }
        KF_CALL(fc_join, &F->out, F->out, F->cl);
    }
    dnf_free(&F->a);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(fc_substitute, FaceId, fc_substitute_PARAMS, fc_substitute(FaceId phi, DimImagePush img, void *ctx))

KF_DECL_EXT_DROP(fc_entails, bool, fc_entails_PARAMS, fc_entails_drop, Dnf x, y; size_t i, j; bool ok, found, sub;)
static void fc_entails_drop(fc_entails_F *F) { dnf_free(&F->x); dnf_free(&F->y); }
KF_STEP(fc_entails) {
    KF_BEGIN(fc_entails);
    fine_bump(FC_FACE_OPS);
    KF_CALL(fc_to_dnf, NULL, F->chi, &F->x); KF_CALL(fc_to_dnf, NULL, F->phi, &F->y);
    F->ok = true;
    for (F->i = 0; F->i < F->x.n && F->ok; F->i++) {
        F->found = false;
        for (F->j = 0; F->j < F->y.n && !F->found; F->j++) {
            fine_bump(FC_DNF_CLAUSE_STEPS);
            KF_CALL(clause_subset, &F->sub, &F->y.c[F->j], &F->x.c[F->i]);
            if (F->sub) F->found = true;
        }
        F->ok = F->found;
    }
    dnf_free(&F->x); dnf_free(&F->y);
    KF_RET(F->ok);
    KF_END;
}
KF_SYNC_DEF(fc_entails, bool, fc_entails_PARAMS, fc_entails(FaceId chi, FaceId phi))

KF_DECL_EXT_DROP(fc_forall, FaceId, fc_forall_PARAMS, fc_forall_drop, Dnf a, out; size_t c; FaceId id;)
static void fc_forall_drop(fc_forall_F *F) { dnf_free(&F->a); dnf_free(&F->out); }
KF_STEP(fc_forall) {
    KF_BEGIN(fc_forall);
    fine_bump(FC_FACE_OPS);
    KF_CALL(fc_to_dnf, NULL, F->phi, &F->a); dnf_init(&F->out);
    for (F->c = 0; F->c < F->a.n; F->c++) {
        bool mentions = false;
        for (size_t k = 0; k < F->a.c[F->c].n; k++) if (FC_LIT_DIM(F->a.c[F->c].a[k]) == F->i) { mentions = true; break; }
        if (!mentions) KF_CALL(dnf_add_clause, NULL, &F->out, F->a.c[F->c].a, F->a.c[F->c].n);
    }
    dnf_free(&F->a);
    KF_CALL(fc_from_dnf, &F->id, &F->out);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(fc_forall, FaceId, fc_forall_PARAMS, fc_forall(DimVarId i, FaceId phi))

static bool sorted_contains(const uint64_t *S, size_t n, uint64_t x) {
    size_t lo = 0, hi = n;
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        if (S[mid] == x) return true;
        if (S[mid] < x) lo = mid + 1; else hi = mid;
    }
    return false;
}

KF_DECL_EXT_DROP(fc_project, FaceId, fc_project_PARAMS, fc_project_drop, Dnf a, out; Words buf; size_t c; FaceId id;)
static void fc_project_drop(fc_project_F *F) { dnf_free(&F->a); dnf_free(&F->out); words_free(&F->buf); }
KF_STEP(fc_project) {
    KF_BEGIN(fc_project);
    fine_bump(FC_FACE_OPS);
    /* chi is canonical: contradictory clauses are already gone */
    KF_CALL(fc_to_dnf, NULL, F->chi, &F->a); dnf_init(&F->out);
    words_init(&F->buf);
    for (F->c = 0; F->c < F->a.n; F->c++) {
        F->buf.n = 0;
        for (size_t k = 0; k < F->a.c[F->c].n; k++)
            if (sorted_contains(F->S, F->nS, FC_LIT_DIM(F->a.c[F->c].a[k]))) words_push(&F->buf, F->a.c[F->c].a[k]);
        KF_CALL(dnf_add_clause, NULL, &F->out, F->buf.w, F->buf.n);
    }
    words_free(&F->buf);
    dnf_free(&F->a);
    KF_CALL(fc_from_dnf, &F->id, &F->out);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(fc_project, FaceId, fc_project_PARAMS, fc_project(FaceId chi, const uint64_t *S, size_t nS))

void fc_dims(FaceId phi, Words *out) {
    size_t n; const uint64_t *w = interner_get(&M.faces, phi, &n);
    size_t nc = (size_t)w[0], p = 1;
    for (size_t i = 0; i < nc; i++) {
        size_t len = (size_t)w[p++];
        for (size_t k = 0; k < len; k++) words_push(out, FC_LIT_DIM(w[p + k]));
        p += len;
    }
}

/* diagnostics: reads the canonical record directly (no working form) */
void fc_print(FaceId a, FILE *f) {
    size_t n; const uint64_t *w = interner_get(&M.faces, a, &n);
    size_t nc = (size_t)w[0], p = 1;
    if (nc == 0) { fprintf(f, "⊥"); return; }
    for (size_t i = 0; i < nc; i++) {
        size_t len = (size_t)w[p++];
        if (i) fprintf(f, " ∨ ");
        if (len == 0) { fprintf(f, "⊤"); continue; }
        for (size_t k = 0; k < len; k++) {
            if (k) fprintf(f, "∧");
            fprintf(f, "(d%llu=%d)", (unsigned long long)FC_LIT_DIM(w[p + k]), FC_LIT_EPS(w[p + k]));
        }
        p += len;
    }
}

/* ---- sets ---- */
#define set_make_PARAMS(X) X(Interner *, t) X(uint64_t *, elems) X(size_t, n)
KF_DECL(set_make, uint64_t, set_make_PARAMS, uint64_t id;)
KF_STEP(set_make) {
    KF_BEGIN(set_make);
    KF_CALL(sort_unique_u64, &F->n, F->elems, F->n);
    KF_CALL(interner_intern, &F->id, F->t, F->elems, F->n, NULL);
    KF_RET(F->id);
    KF_END;
}
#define set_union_PARAMS(X) X(Interner *, t) X(uint64_t, a) X(uint64_t, b)
KF_DECL_DROP(set_union, uint64_t, set_union_PARAMS, set_union_drop, uint64_t *buf; uint64_t id;)
static void set_union_drop(set_union_F *F) { free(F->buf); F->buf = NULL; }
KF_STEP(set_union) {
    KF_BEGIN(set_union);
    if (F->a == F->b) KF_RET(F->a);
    {
        size_t na, nb;
        const uint64_t *x = interner_get(F->t, F->a, &na);
        const uint64_t *y = interner_get(F->t, F->b, &nb);
        if (na == 0) KF_RET(F->b);
        if (nb == 0) KF_RET(F->a);
        F->buf = malloc((na + nb) * sizeof(uint64_t));
        require(F->buf, "out of memory");
        memcpy(F->buf, x, na * sizeof(uint64_t));
        memcpy(F->buf + na, y, nb * sizeof(uint64_t));
        KF_CALL(set_make, &F->id, F->t, F->buf, na + nb);
    }
    free(F->buf); F->buf = NULL;
    KF_RET(F->id);
    KF_END;
}
#define set_remove_PARAMS(X) X(Interner *, t) X(uint64_t, a) X(uint64_t, v)
KF_DECL_DROP(set_remove, uint64_t, set_remove_PARAMS, set_remove_drop, uint64_t *buf; uint64_t id;)
static void set_remove_drop(set_remove_F *F) { free(F->buf); F->buf = NULL; }
KF_STEP(set_remove) {
    KF_BEGIN(set_remove);
    {
        size_t n; const uint64_t *x = interner_get(F->t, F->a, &n);
        if (!sorted_contains(x, n, F->v)) KF_RET(F->a);
        F->buf = malloc((n ? n : 1) * sizeof(uint64_t));
        require(F->buf, "out of memory");
        size_t m = 0;
        for (size_t i = 0; i < n; i++) if (x[i] != F->v) F->buf[m++] = x[i];
        KF_CALL(interner_intern, &F->id, F->t, F->buf, m, NULL);
    }
    free(F->buf); F->buf = NULL;
    KF_RET(F->id);
    KF_END;
}
static bool set_contains(Interner *t, uint64_t a, uint64_t v) {
    size_t n; const uint64_t *x = interner_get(t, a, &n);
    return sorted_contains(x, n, v);
}

KF_DECL_EXT(dimset_make, DimSetId, dimset_make_PARAMS, DimSetId r;)
KF_STEP(dimset_make) { KF_BEGIN(dimset_make); KF_CALL(set_make, &F->r, &M.dimsets, F->elems, F->n); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(dimset_make, DimSetId, dimset_make_PARAMS, dimset_make(uint64_t *elems, size_t n))
const uint64_t *dimset_get(DimSetId s, size_t *n) { return interner_get(&M.dimsets, s, n); }
KF_DECL_EXT(dimset_union, DimSetId, dimset_union_PARAMS, DimSetId r;)
KF_STEP(dimset_union) { KF_BEGIN(dimset_union); KF_CALL(set_union, &F->r, &M.dimsets, F->a, F->b); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(dimset_union, DimSetId, dimset_union_PARAMS, dimset_union(DimSetId a, DimSetId b))
KF_DECL_EXT(dimset_remove, DimSetId, dimset_remove_PARAMS, DimSetId r;)
KF_STEP(dimset_remove) { KF_BEGIN(dimset_remove); KF_CALL(set_remove, &F->r, &M.dimsets, F->a, F->x); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(dimset_remove, DimSetId, dimset_remove_PARAMS, dimset_remove(DimSetId a, uint64_t x))
bool dimset_contains(DimSetId a, uint64_t x) { return set_contains(&M.dimsets, a, x); }
KF_DECL_EXT(varset_make, VarSetId, varset_make_PARAMS, VarSetId r;)
KF_STEP(varset_make) { KF_BEGIN(varset_make); KF_CALL(set_make, &F->r, &M.varsets, F->elems, F->n); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(varset_make, VarSetId, varset_make_PARAMS, varset_make(uint64_t *elems, size_t n))
const uint64_t *varset_get(VarSetId s, size_t *n) { return interner_get(&M.varsets, s, n); }
KF_DECL_EXT(varset_union, VarSetId, varset_union_PARAMS, VarSetId r;)
KF_STEP(varset_union) { KF_BEGIN(varset_union); KF_CALL(set_union, &F->r, &M.varsets, F->a, F->b); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(varset_union, VarSetId, varset_union_PARAMS, varset_union(VarSetId a, VarSetId b))
KF_DECL_EXT(varset_remove, VarSetId, varset_remove_PARAMS, VarSetId r;)
KF_STEP(varset_remove) { KF_BEGIN(varset_remove); KF_CALL(set_remove, &F->r, &M.varsets, F->a, F->x); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(varset_remove, VarSetId, varset_remove_PARAMS, varset_remove(VarSetId a, uint64_t x))
bool varset_contains(VarSetId a, uint64_t x) { return set_contains(&M.varsets, a, x); }
