/* shape.c — structural computation identity (§76). See shape.h. */
#include "shape.h"
#include "state.h"
#include "reuse.h"
#include "fine.h"

/* the procedures of this file are frame families (kframe.h): shape
 * construction nests through heap frames, never the native stack.
 * §94: the shape interner and memo are internally synchronized; no outer lock
 * is held around the hashing/copy of an input-sized shape record */

/* ρ extended by one bound identity */
#define rho_extend_PARAMS(X) X(MapId, rho) X(Sort, sort) X(uint64_t, concrete) X(size_t, depth) X(BinderSlot, slot)
KF_DECL_DROP(rho_extend, MapId, rho_extend_PARAMS, rho_extend_drop, MapBuilder b; IntervalId iv; MapId m; uint64_t bid; RefId r; size_t nt, nd, k;)
static void rho_extend_drop(rho_extend_F *F) { words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(rho_extend) {
    KF_BEGIN(rho_extend);
    mapb_init(&F->b);
    F->nt = map_n_terms(F->rho); F->nd = map_n_dims(F->rho);
    KF_MAPB_RESERVE(&F->b, F->nt + 1, F->nd + 1);
    for (F->k = 0; F->k < F->nt; F->k++) { TermVarId x; RefId im; map_term_entry(F->rho, F->k, &x, &im); if (!(F->sort == S_TERM && x == F->concrete)) mapb_term(&F->b, x, im); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
    for (F->k = 0; F->k < F->nd; F->k++) { DimVarId i; IntervalId im; map_dim_entry(F->rho, F->k, &i, &im); if (!(F->sort == S_DIM && i == F->concrete)) mapb_dim(&F->b, i, im); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
    KF_CALL(bound_id, &F->bid, F->depth, F->slot);
    if (F->sort == S_TERM) { KF_CALL(ref_var, &F->r, F->bid); mapb_term(&F->b, F->concrete, F->r); }
    else { KF_CALL(iv_var, &F->iv, F->bid); mapb_dim(&F->b, F->concrete, F->iv); }
    KF_CALL(mapb_finish, &F->m, &F->b);   /* releases the builder */
    KF_RET(F->m);
    KF_END;
}

/* ρ restricted to the free boundary of t: a shared subterm under different
 * unrelated binders has one memo entry (the §76 form depends only on the
 * bound identities of t's own free variables and dimensions) */
#define rho_restrict_PARAMS(X) X(MapId, rho) X(RefId, t)
KF_DECL_DROP(rho_restrict, MapId, rho_restrict_PARAMS, rho_restrict_drop, Words rd; DimSetId reqd; MapBuilder b; MapId m; size_t nt, nd, k;)
static void rho_restrict_drop(rho_restrict_F *F) { words_free(&F->rd); words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(rho_restrict) {
    KF_BEGIN(rho_restrict);
    if (map_is_identity(F->rho)) KF_RET(F->rho);
    words_init(&F->rd); fc_dims(ref_required(F->t), &F->rd);
    KF_CALL(dimset_make, &F->reqd, F->rd.w, F->rd.n); words_free(&F->rd);   /* the required face may mention dimensions outside the support */
    mapb_init(&F->b);
    F->nt = map_n_terms(F->rho); F->nd = map_n_dims(F->rho);
    KF_MAPB_RESERVE(&F->b, F->nt, F->nd);
    for (F->k = 0; F->k < F->nt; F->k++) { TermVarId x; RefId im; map_term_entry(F->rho, F->k, &x, &im); if (varset_contains(ref_freevars(F->t), x)) mapb_term(&F->b, x, im); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
    for (F->k = 0; F->k < F->nd; F->k++) { DimVarId i; IntervalId im; map_dim_entry(F->rho, F->k, &i, &im); if (dimset_contains(ref_support(F->t), i) || dimset_contains(F->reqd, i)) mapb_dim(&F->b, i, im); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
    KF_CALL(mapb_finish, &F->m, &F->b);
    KF_RET(F->m);
    KF_END;
}

KF_DECL_EXT_DROP(shape_under, ShapeId, shape_under_PARAMS, shape_under_drop, uint64_t key[3]; ShapeId memo, id, sub; bool have; Words w; Head h; bool open; size_t k, np; MapId rho2; RefId body; uint64_t x; SymbolId sym; MapId vm; RefId im; FaceId fr; IntervalId ivr; TermOpen to; DimOpen dop;)
static void shape_under_drop(shape_under_F *F) { words_free(&F->w); if (F->open) { head_free(&F->h); F->open = false; } }
KF_STEP(shape_under) {
    KF_BEGIN(shape_under);
    KF_CALL(rho_restrict, &F->rho, F->rho, F->t);
    F->key[0] = F->t; F->key[1] = F->rho; F->key[2] = F->depth;
    KF_CALL(wordmap_get, &F->have, &M.shape_memo, F->key, 3, &F->memo);
    if (F->have) KF_RET(F->memo);
    words_init(&F->w);
    if (ref_is_var(F->t)) {
        KF_CALL(map_term_image, &F->im, F->rho, ref_var_id(F->t));
        if (F->im != F->t && ref_is_var(F->im) && is_bound_id(ref_var_id(F->im))) { words_push(&F->w, SH_BOUND); words_push(&F->w, ref_var_id(F->im)); }
        else { words_push(&F->w, SH_FREE); words_push(&F->w, ref_var_id(F->t)); }
    } else {
        F->open = true; KF_CALL(open_ref, NULL, F->t, &F->h);
        KF_CALL(words_reserve, NULL, &F->w, 6 + 3 * F->h.n);   /* the node's words: no growth inside the field loop */
        words_push(&F->w, SH_NODE); words_push(&F->w, F->h.tag); words_push(&F->w, F->h.payload); words_push(&F->w, F->h.levels);
        KF_CALL(fc_reindex, &F->fr, ref_required(F->t), F->rho); words_push(&F->w, F->fr);
        words_push(&F->w, F->h.n);
        for (F->k = 0; F->k < F->h.n; F->k++) {
            words_push(&F->w, F->h.f[F->k].kind);
            if (!F->h.f[F->k].is_binder) {
                words_push(&F->w, 0);
                switch (F->h.f[F->k].kind) {
                case F_REF: KF_CALL(shape_under, &F->sub, F->h.f[F->k].id, F->rho, F->depth); words_push(&F->w, F->sub); break;
                case F_INTERVAL: KF_CALL(iv_reindex, &F->ivr, F->h.f[F->k].id, F->rho); words_push(&F->w, F->ivr); break;
                case F_FACE: KF_CALL(fc_reindex, &F->fr, F->h.f[F->k].id, F->rho); words_push(&F->w, F->fr); break;
                }
                continue;
            }
            words_push(&F->w, F->h.f[F->k].sort);
            if (F->h.f[F->k].sort == S_TERM) {
                KF_CALL(resolve_term_binder, &F->to, F->t, F->h.f[F->k].slot, F->h.f[F->k].index);
                F->body = F->to.body; F->x = F->to.x;
                KF_CALL(rho_extend, &F->rho2, F->rho, S_TERM, F->x, F->depth, F->h.f[F->k].slot);
            } else {
                KF_CALL(resolve_dim_binder, &F->dop, F->t, F->h.f[F->k].slot, F->h.f[F->k].index);
                F->body = F->dop.body; F->x = F->dop.j;
                KF_CALL(rho_extend, &F->rho2, F->rho, S_DIM, F->x, F->depth, F->h.f[F->k].slot);
            }
            KF_CALL(shape_under, &F->sub, F->body, F->rho2, F->depth + 1);
            words_push(&F->w, F->sub);
        }
        if (F->h.tag == T_GLOBAL && !ref_is_tview(F->t)) {
            /* a global's free boundary is carried by its view map, not by
             * fields: the images of its declared parameters and dimensions
             * are part of its structural identity (F and F[i↦0] are
             * different computations) */
            F->sym = (SymbolId)F->h.payload; F->vm = ref_map(F->t);
            varset_get(global_params(F->sym), &F->np);
            KF_CALL(words_reserve, NULL, &F->w, F->np);
            for (F->k = 0; F->k < F->np; F->k++) {
                { size_t n; const uint64_t *ps = varset_get(global_params(F->sym), &n); KF_CALL(map_term_image, &F->im, F->vm, ps[F->k]); }
                KF_CALL(shape_under, &F->sub, F->im, F->rho, F->depth);
                words_push(&F->w, F->sub);
            }
            dimset_get(global_dims(F->sym), &F->np);
            KF_CALL(words_reserve, NULL, &F->w, F->np);
            for (F->k = 0; F->k < F->np; F->k++) {
                { size_t n; const uint64_t *dsx = dimset_get(global_dims(F->sym), &n); KF_CALL(map_dim_image, &F->ivr, F->vm, dsx[F->k]); }
                KF_CALL(iv_reindex, &F->ivr, F->ivr, F->rho);
                words_push(&F->w, F->ivr);
            }
        }
        head_free(&F->h); F->open = false;
    }
    reuse_bump(REUSE_SHAPE_NODE); fine_bump(FC_SHAPE_NODES);
    KF_CALL(interner_intern, &F->id, &M.shapes, F->w.w, F->w.n, NULL);
    words_free(&F->w);
    F->key[0] = F->t; F->key[1] = F->rho; F->key[2] = F->depth;
    KF_CALL(wordmap_put, NULL, &M.shape_memo, F->key, 3, F->id);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(shape_under, ShapeId, shape_under_PARAMS, shape_under(RefId t, MapId rho, size_t depth))
KF_DECL_EXT(shape_of, ShapeId, shape_of_PARAMS, ShapeId r; MapId id;)
KF_STEP(shape_of) { KF_BEGIN(shape_of); KF_CALL0(map_identity, &F->id); KF_CALL(shape_under, &F->r, F->t, F->id, 0); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(shape_of, ShapeId, shape_of_PARAMS, shape_of(RefId t))
const uint64_t *shape_words(ShapeId s, size_t *n) { return interner_get(&M.shapes, s, n); }
size_t shape_count(void) { return interner_count(&M.shapes); }
