#include "interval.h"
#include "fine.h"

/* the clause algorithms are frame families (kframe.h); a working Dnf or
 * buffer held by a frame is released by its drop */
KF_DECL_EXT_DROP(iv_from_dnf, IntervalId, iv_from_dnf_PARAMS, iv_from_dnf_drop, Words w; IntervalId id;)
static void iv_from_dnf_drop(iv_from_dnf_F *F) { words_free(&F->w); dnf_free(F->d); }
KF_STEP(iv_from_dnf) {
    KF_BEGIN(iv_from_dnf);
    KF_CALL(dnf_normalize, NULL, F->d, NULL);
    words_init(&F->w);
    KF_CALL(dnf_encode, NULL, F->d, &F->w);
    KF_CALL(interner_intern, &F->id, &M.intervals, F->w.w, F->w.n, NULL);
    words_free(&F->w);
    dnf_free(F->d);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(iv_from_dnf, IntervalId, iv_from_dnf_PARAMS, iv_from_dnf(Dnf *d))

KF_DECL_EXT(iv_to_dnf, void, iv_to_dnf_PARAMS, )
KF_STEP(iv_to_dnf) {
    KF_BEGIN(iv_to_dnf);
    { size_t n; const uint64_t *w = interner_get(&M.intervals, F->r, &n); KF_CALL(dnf_decode, NULL, F->d, w, n); }
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(iv_to_dnf, iv_to_dnf_PARAMS, iv_to_dnf(IntervalId r, Dnf *d))

/* a constant interval of at most one clause of at most one atom */
#define iv_small_PARAMS(X) X(int, nclauses) X(uint64_t, atom) X(int, natoms)
KF_DECL_DROP(iv_small, IntervalId, iv_small_PARAMS, iv_small_drop, Dnf d; IntervalId id;)
static void iv_small_drop(iv_small_F *F) { dnf_free(&F->d); }
KF_STEP(iv_small) {
    KF_BEGIN(iv_small);
    dnf_init(&F->d);
    if (F->nclauses) KF_CALL(dnf_add_clause, NULL, &F->d, &F->atom, (size_t)F->natoms);
    KF_CALL(iv_from_dnf, &F->id, &F->d);
    KF_RET(F->id);
    KF_END;
}
KF_DECL_EXT(iv_zero, IntervalId, KF_NOPARAMS, IntervalId r;)
KF_STEP(iv_zero) { KF_BEGIN(iv_zero); KF_CALL(iv_small, &F->r, 0, 0, 0); KF_RET(F->r); KF_END; }
IntervalId iv_zero(void) { IntervalId r; KStack *s_ = kf_sync_begin(); iv_zero_push(s_, &r); kf_sync_run(s_); kf_sync_end(s_); return r; }
KF_DECL_EXT(iv_one, IntervalId, KF_NOPARAMS, IntervalId r;)
KF_STEP(iv_one) { KF_BEGIN(iv_one); KF_CALL(iv_small, &F->r, 1, 0, 0); KF_RET(F->r); KF_END; }
IntervalId iv_one(void) { IntervalId r; KStack *s_ = kf_sync_begin(); iv_one_push(s_, &r); kf_sync_run(s_); kf_sync_end(s_); return r; }
KF_DECL_EXT(iv_var, IntervalId, iv_var_PARAMS, IntervalId r;)
KF_STEP(iv_var) { KF_BEGIN(iv_var); KF_CALL(iv_small, &F->r, 1, IV_ATOM(F->i, 0), 1); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(iv_var, IntervalId, iv_var_PARAMS, iv_var(DimVarId i))
#define iv_atom_PARAMS(X) X(uint64_t, atom)
KF_DECL(iv_atom, IntervalId, iv_atom_PARAMS, IntervalId r;)
KF_STEP(iv_atom) { KF_BEGIN(iv_atom); KF_CALL(iv_small, &F->r, 1, F->atom, 1); KF_RET(F->r); KF_END; }

bool iv_is_zero(IntervalId r) { size_t n; const uint64_t *w = interner_get(&M.intervals, r, &n); return w[0] == 0; }
bool iv_is_one(IntervalId r) { size_t n; const uint64_t *w = interner_get(&M.intervals, r, &n); return w[0] == 1 && w[1] == 0; }

KF_DECL_EXT_DROP(iv_join, IntervalId, iv_join_PARAMS, iv_join_drop, Dnf a, b; size_t i; IntervalId id;)
static void iv_join_drop(iv_join_F *F) { dnf_free(&F->a); dnf_free(&F->b); }
KF_STEP(iv_join) {
    KF_BEGIN(iv_join);
    KF_CALL(iv_to_dnf, NULL, F->r, &F->a); KF_CALL(iv_to_dnf, NULL, F->s, &F->b);
    for (F->i = 0; F->i < F->b.n; F->i++) KF_CALL(dnf_add_clause, NULL, &F->a, F->b.c[F->i].a, F->b.c[F->i].n);
    dnf_free(&F->b);
    KF_CALL(iv_from_dnf, &F->id, &F->a);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(iv_join, IntervalId, iv_join_PARAMS, iv_join(IntervalId r, IntervalId s))

KF_DECL_EXT_DROP(iv_meet, IntervalId, iv_meet_PARAMS, iv_meet_drop, Dnf a, b, out; size_t i, j; IntervalId id;)
static void iv_meet_drop(iv_meet_F *F) { dnf_free(&F->a); dnf_free(&F->b); dnf_free(&F->out); }
KF_STEP(iv_meet) {
    KF_BEGIN(iv_meet);
    KF_CALL(iv_to_dnf, NULL, F->r, &F->a); KF_CALL(iv_to_dnf, NULL, F->s, &F->b); dnf_init(&F->out);
    for (F->i = 0; F->i < F->a.n; F->i++)
        for (F->j = 0; F->j < F->b.n; F->j++)
            KF_CALL(dnf_add_clause_union, NULL, &F->out, &F->a.c[F->i], &F->b.c[F->j]);
    dnf_free(&F->a); dnf_free(&F->b);
    KF_CALL(iv_from_dnf, &F->id, &F->out);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(iv_meet, IntervalId, iv_meet_PARAMS, iv_meet(IntervalId r, IntervalId s))

KF_DECL_EXT_DROP(iv_negate, IntervalId, iv_negate_PARAMS, iv_negate_drop, Dnf a; size_t i, k; IntervalId out, comp, t;)
static void iv_negate_drop(iv_negate_F *F) { dnf_free(&F->a); }
KF_STEP(iv_negate) {
    KF_BEGIN(iv_negate);
    KF_CALL(iv_to_dnf, NULL, F->r, &F->a);
    KF_CALL0(iv_one, &F->out);
    for (F->i = 0; F->i < F->a.n; F->i++) {
        KF_CALL0(iv_zero, &F->comp);
        for (F->k = 0; F->k < F->a.c[F->i].n; F->k++) {
            { uint64_t at = F->a.c[F->i].a[F->k]; KF_CALL(iv_atom, &F->t, IV_ATOM(IV_ATOM_DIM(at), !IV_ATOM_NEG(at))); }
            KF_CALL(iv_join, &F->comp, F->comp, F->t);
        }
        KF_CALL(iv_meet, &F->out, F->out, F->comp);
    }
    dnf_free(&F->a);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(iv_negate, IntervalId, iv_negate_PARAMS, iv_negate(IntervalId r))

/* Insert the image of each original dimension once (positive atom →
 * image, negative atom → negation of image), combine by the original
 * meets and joins. No recursion into inserted images. */
KF_DECL_EXT_DROP(iv_substitute, IntervalId, iv_substitute_PARAMS, iv_substitute_drop, Dnf a; size_t i, k; IntervalId out, cl, im; uint64_t at;)
static void iv_substitute_drop(iv_substitute_F *F) { dnf_free(&F->a); }
KF_STEP(iv_substitute) {
    KF_BEGIN(iv_substitute);
    KF_CALL(iv_to_dnf, NULL, F->r, &F->a);
    KF_CALL0(iv_zero, &F->out);
    for (F->i = 0; F->i < F->a.n; F->i++) {
        KF_CALL0(iv_one, &F->cl);
        for (F->k = 0; F->k < F->a.c[F->i].n; F->k++) {
            F->at = F->a.c[F->i].a[F->k];
            KF_CALLP(F->img, &F->im, IV_ATOM_DIM(F->at), F->ctx);
            if (IV_ATOM_NEG(F->at)) KF_CALL(iv_negate, &F->im, F->im);
            KF_CALL(iv_meet, &F->cl, F->cl, F->im);
        }
        KF_CALL(iv_join, &F->out, F->out, F->cl);
    }
    dnf_free(&F->a);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(iv_substitute, IntervalId, iv_substitute_PARAMS, iv_substitute(IntervalId r, DimImagePush img, void *ctx))

void iv_dims(IntervalId r, Words *out) {
    size_t n; const uint64_t *w = interner_get(&M.intervals, r, &n);
    size_t nc = (size_t)w[0], p = 1;
    for (size_t i = 0; i < nc; i++) {
        size_t len = (size_t)w[p++];
        for (size_t k = 0; k < len; k++) words_push(out, IV_ATOM_DIM(w[p + k]));
        p += len;
    }
}

/* diagnostics: reads the canonical record directly (no working form) */
void iv_print(IntervalId r, FILE *f) {
    size_t n; const uint64_t *w = interner_get(&M.intervals, r, &n);
    size_t nc = (size_t)w[0], p = 1;
    if (nc == 0) { fprintf(f, "0"); return; }
    for (size_t i = 0; i < nc; i++) {
        size_t len = (size_t)w[p++];
        if (i) fprintf(f, " ∨ ");
        if (len == 0) { fprintf(f, "1"); continue; }
        for (size_t k = 0; k < len; k++) {
            if (k) fprintf(f, "∧");
            uint64_t at = w[p + k];
            fprintf(f, "%sd%llu", IV_ATOM_NEG(at) ? "¬" : "", (unsigned long long)IV_ATOM_DIM(at));
        }
        p += len;
    }
}
