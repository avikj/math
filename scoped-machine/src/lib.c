#include "lib.h"

void lib_free(void) { templates_free(); }
size_t lib_template_count(void) { return interner_count(&M.tnodes); }

IntervalId iv_line(IntervalId r, IntervalId s, DimVarId j) {
    IntervalId vj = iv_var(j);
    return iv_join(iv_meet(r, iv_negate(vj)), iv_meet(s, vj));
}

/* ------------------------------------------------------------------ */
/* capture adapters                                                      */

/* the capture adapters and program invocations are frame families (kframe.h) */
#define capture_decl_PARAMS(X) X(size_t, n) X(Sort, s0) X(uint64_t, id0) X(RefId, t0) X(uint64_t, l0) X(Sort, s1) X(uint64_t, id1) X(RefId, t1) X(uint64_t, l1) X(ValSort, bsort) X(uint64_t, body) X(RefId, type) X(uint64_t, level) X(FaceId, guard)
KF_DECL(capture_decl, ScopeId, capture_decl_PARAMS, CaptureDecl d[2]; FaceId tt; ScopeId r; Val b;)
KF_STEP(capture_decl) {   /* one or two declarations; a dimension declaration and a guard of 0 take ⊤ */
    KF_BEGIN(capture_decl);
    KF_CALL0(fc_true, &F->tt);
    F->d[0] = (CaptureDecl){ F->s0, F->id0, F->t0, F->l0, F->s0 == S_TERM ? term_var_required(F->id0) : F->tt };
    if (F->n > 1) F->d[1] = (CaptureDecl){ F->s1, F->id1, F->t1, F->l1, F->s1 == S_TERM ? term_var_required(F->id1) : F->tt };
    F->b.sort = F->bsort; F->b.id = F->body;
    KF_CALL(capture_scope, &F->r, F->n, F->d, F->b, F->type, F->level, F->guard ? F->guard : F->tt);
    KF_RET(F->r);
    KF_END;
}
KF_DECL_EXT(capture_dim1, ScopeId, capture_dim1_PARAMS, ScopeId r;)
KF_STEP(capture_dim1) { KF_BEGIN(capture_dim1); KF_CALL(capture_decl, &F->r, 1, S_DIM, F->j, 0, LEVEL_NONE, 0, 0, 0, 0, VS_REF, F->body, F->type, F->level, F->guard); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(capture_dim1, ScopeId, capture_dim1_PARAMS, capture_dim1(DimVarId j, RefId body, RefId type, uint64_t level, FaceId guard))
KF_DECL_EXT(capture_dim1_face, ScopeId, capture_dim1_face_PARAMS, ScopeId r;)
KF_STEP(capture_dim1_face) { KF_BEGIN(capture_dim1_face); KF_CALL(capture_decl, &F->r, 1, S_DIM, F->j, 0, LEVEL_NONE, 0, 0, 0, 0, VS_FACE, F->body, 0, LEVEL_NONE, 0); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(capture_dim1_face, ScopeId, capture_dim1_face_PARAMS, capture_dim1_face(DimVarId j, FaceId body))
KF_DECL_EXT(capture_dim2, ScopeId, capture_dim2_PARAMS, ScopeId r;)
KF_STEP(capture_dim2) { KF_BEGIN(capture_dim2); KF_CALL(capture_decl, &F->r, 2, S_DIM, F->i, 0, LEVEL_NONE, S_DIM, F->j, 0, LEVEL_NONE, VS_REF, F->body, F->type, F->level, F->guard); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(capture_dim2, ScopeId, capture_dim2_PARAMS, capture_dim2(DimVarId i, DimVarId j, RefId body, RefId type, uint64_t level, FaceId guard))
KF_DECL_EXT(capture_dim_term, ScopeId, capture_dim_term_PARAMS, ScopeId r;)
KF_STEP(capture_dim_term) { KF_BEGIN(capture_dim_term); KF_CALL(capture_decl, &F->r, 2, S_DIM, F->j, 0, LEVEL_NONE, S_TERM, F->x, F->xtype, F->xlevel, VS_REF, F->body, F->type, F->level, F->guard); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(capture_dim_term, ScopeId, capture_dim_term_PARAMS, capture_dim_term(DimVarId j, TermVarId x, RefId xtype, uint64_t xlevel, RefId body, RefId type, uint64_t level, FaceId guard))
KF_DECL_EXT(capture_term2, ScopeId, capture_term2_PARAMS, ScopeId r;)
KF_STEP(capture_term2) { KF_BEGIN(capture_term2); KF_CALL(capture_decl, &F->r, 2, S_TERM, F->x, F->xtype, F->xlevel, S_TERM, F->e, F->etype, F->elevel, VS_REF, F->body, F->type, F->level, F->guard); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(capture_term2, ScopeId, capture_term2_PARAMS, capture_term2(TermVarId x, RefId xtype, uint64_t xlevel, TermVarId e, RefId etype, uint64_t elevel, RefId body, RefId type, uint64_t level, FaceId guard))

/* ------------------------------------------------------------------ */
/* §52 programs                                                          */

static TVal VL(uint64_t n) { TVal v = { PS_LEVEL, n }; return v; }
static TVal VR(RefId r) { TVal v = { PS_REF, r }; return v; }
static TVal VI(IntervalId r) { TVal v = { PS_INTERVAL, r }; return v; }
static TVal VF(FaceId f) { TVal v = { PS_FACE, f }; return v; }
static TVal VS(ScopeId s) { TVal v = { PS_SCOPE, s }; return v; }
/* each §52 program is one template invocation: its argument vector lives in the frame */
KF_DECL_EXT(mk_path_const, RefId, mk_path_const_PARAMS, TVal pa_[4]; TVal pr_;)
KF_STEP(mk_path_const) { KF_BEGIN(mk_path_const); { TVal a_[] = { VL(F->l), VR(F->A), VR(F->lft), VR(F->r) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_PATHCONST, 4, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_path_const, RefId, mk_path_const_PARAMS, mk_path_const(uint64_t l, RefId A, RefId lft, RefId r))
KF_DECL_EXT(mk_refl, RefId, mk_refl_PARAMS, TVal pa_[3]; TVal pr_;)
KF_STEP(mk_refl) { KF_BEGIN(mk_refl); { TVal a_[] = { VL(F->l), VR(F->A), VR(F->a) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_REFL, 3, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_refl, RefId, mk_refl_PARAMS, mk_refl(uint64_t l, RefId A, RefId a))
KF_DECL_EXT(mk_papp_const, RefId, mk_papp_const_PARAMS, TVal pa_[6]; TVal pr_;)
KF_STEP(mk_papp_const) { KF_BEGIN(mk_papp_const); { TVal a_[] = { VL(F->l), VR(F->A), VR(F->lft), VR(F->r), VR(F->p), VI(F->s) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_PAPPCONST, 6, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_papp_const, RefId, mk_papp_const_PARAMS, mk_papp_const(uint64_t l, RefId A, RefId lft, RefId r, RefId p, IntervalId s))
KF_DECL_EXT(mk_path_rev, RefId, mk_path_rev_PARAMS, TVal pa_[5]; TVal pr_;)
KF_STEP(mk_path_rev) { KF_BEGIN(mk_path_rev); { TVal a_[] = { VL(F->l), VR(F->A), VR(F->lft), VR(F->r), VR(F->p) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_REVERSE, 5, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_path_rev, RefId, mk_path_rev_PARAMS, mk_path_rev(uint64_t l, RefId A, RefId lft, RefId r, RefId p))
KF_DECL_EXT(mk_path_concat, RefId, mk_path_concat_PARAMS, TVal pa_[7]; TVal pr_;)
KF_STEP(mk_path_concat) { KF_BEGIN(mk_path_concat); { TVal a_[] = { VL(F->l), VR(F->A), VR(F->x), VR(F->y), VR(F->z), VR(F->p), VR(F->q) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_CONCAT, 7, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_path_concat, RefId, mk_path_concat_PARAMS, mk_path_concat(uint64_t l, RefId A, RefId x, RefId y, RefId z, RefId p, RefId q))
KF_DECL_EXT(mk_fun, RefId, mk_fun_PARAMS, TVal pa_[4]; TVal pr_;)
KF_STEP(mk_fun) { KF_BEGIN(mk_fun); { TVal a_[] = { VL(F->l), VL(F->m), VR(F->X_), VR(F->Y) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_FUN, 4, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_fun, RefId, mk_fun_PARAMS, mk_fun(uint64_t l, uint64_t m, RefId X_, RefId Y))
KF_DECL_EXT(mk_contr, RefId, mk_contr_PARAMS, TVal pa_[2]; TVal pr_;)
KF_STEP(mk_contr) { KF_BEGIN(mk_contr); { TVal a_[] = { VL(F->l), VR(F->X_) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_CONTR, 2, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_contr, RefId, mk_contr_PARAMS, mk_contr(uint64_t l, RefId X_))
KF_DECL_EXT(mk_fib, RefId, mk_fib_PARAMS, TVal pa_[6]; TVal pr_;)
KF_STEP(mk_fib) { KF_BEGIN(mk_fib); { TVal a_[] = { VL(F->l), VL(F->m), VR(F->X_), VR(F->Y), VR(F->f), VR(F->y) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_FIB, 6, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_fib, RefId, mk_fib_PARAMS, mk_fib(uint64_t l, uint64_t m, RefId X_, RefId Y, RefId f, RefId y))
KF_DECL_EXT(mk_equiv, RefId, mk_equiv_PARAMS, TVal pa_[4]; TVal pr_;)
KF_STEP(mk_equiv) { KF_BEGIN(mk_equiv); { TVal a_[] = { VL(F->l), VL(F->m), VR(F->X_), VR(F->Y) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_EQUIV, 4, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_equiv, RefId, mk_equiv_PARAMS, mk_equiv(uint64_t l, uint64_t m, RefId X_, RefId Y))
KF_DECL_EXT(mk_id_fun, RefId, mk_id_fun_PARAMS, TVal pa_[2]; TVal pr_;)
KF_STEP(mk_id_fun) { KF_BEGIN(mk_id_fun); { TVal a_[] = { VL(F->l), VR(F->X_) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_IDFUN, 2, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_id_fun, RefId, mk_id_fun_PARAMS, mk_id_fun(uint64_t l, RefId X_))
KF_DECL_EXT(mk_id_equiv, RefId, mk_id_equiv_PARAMS, TVal pa_[2]; TVal pr_;)
KF_STEP(mk_id_equiv) { KF_BEGIN(mk_id_equiv); { TVal a_[] = { VL(F->l), VR(F->X_) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_IDEQUIV, 2, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_id_equiv, RefId, mk_id_equiv_PARAMS, mk_id_equiv(uint64_t l, RefId X_))
KF_DECL_EXT(equiv_map, RefId, equiv_map_PARAMS, TVal pa_[5]; TVal pr_;)
KF_STEP(equiv_map) { KF_BEGIN(equiv_map); { TVal a_[] = { VL(F->l), VL(F->m), VR(F->X_), VR(F->Y), VR(F->e) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_EQUIVMAP, 5, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(equiv_map, RefId, equiv_map_PARAMS, equiv_map(uint64_t l, uint64_t m, RefId X_, RefId Y, RefId e))
KF_DECL_EXT(equiv_contr, RefId, equiv_contr_PARAMS, TVal pa_[6]; TVal pr_;)
KF_STEP(equiv_contr) { KF_BEGIN(equiv_contr); { TVal a_[] = { VL(F->l), VL(F->m), VR(F->X_), VR(F->Y), VR(F->e), VR(F->y) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_EQUIVCONTR, 6, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(equiv_contr, RefId, equiv_contr_PARAMS, equiv_contr(uint64_t l, uint64_t m, RefId X_, RefId Y, RefId e, RefId y))
KF_DECL_EXT(mk_fill, RefId, mk_fill_PARAMS, TVal pa_[6]; TVal pr_;)
KF_STEP(mk_fill) { KF_BEGIN(mk_fill); { TVal a_[] = { VL(F->l), VS(F->A), VF(F->phi), VS(F->u), VR(F->cap), VI(F->r) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_FILL, 6, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_fill, RefId, mk_fill_PARAMS, mk_fill(uint64_t l, ScopeId A, FaceId phi, ScopeId u, RefId cap, IntervalId r))
KF_DECL_EXT(mk_hcomp, RefId, mk_hcomp_PARAMS, TVal pa_[5]; TVal pr_;)
KF_STEP(mk_hcomp) { KF_BEGIN(mk_hcomp); { TVal a_[] = { VL(F->l), VR(F->X_), VF(F->phi), VS(F->u), VR(F->cap) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_HCOMP, 5, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_hcomp, RefId, mk_hcomp_PARAMS, mk_hcomp(uint64_t l, RefId X_, FaceId phi, ScopeId u, RefId cap))
KF_DECL_EXT(mk_coe, RefId, mk_coe_PARAMS, TVal pa_[3]; TVal pr_;)
KF_STEP(mk_coe) { KF_BEGIN(mk_coe); { TVal a_[] = { VL(F->l), VS(F->A), VR(F->cap) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_COE, 3, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_coe, RefId, mk_coe_PARAMS, mk_coe(uint64_t l, ScopeId A, RefId cap))
KF_DECL_EXT(mk_extend_contr, RefId, mk_extend_contr_PARAMS, TVal pa_[6]; TVal pr_;)
KF_STEP(mk_extend_contr) { KF_BEGIN(mk_extend_contr); { TVal a_[] = { VL(F->l), VR(F->X_), VR(F->c), VR(F->k), VF(F->theta), VR(F->v) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_EXTENDCONTR, 6, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_extend_contr, RefId, mk_extend_contr_PARAMS, mk_extend_contr(uint64_t l, RefId X_, RefId c, RefId k, FaceId theta, RefId v))
KF_DECL_EXT(mk_line_equiv, RefId, mk_line_equiv_PARAMS, TVal pa_[2]; TVal pr_;)
KF_STEP(mk_line_equiv) { KF_BEGIN(mk_line_equiv); { TVal a_[] = { VL(F->l), VS(F->X_) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_LINEEQUIV, 2, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_line_equiv, RefId, mk_line_equiv_PARAMS, mk_line_equiv(uint64_t l, ScopeId X_))
KF_DECL_EXT(mk_ua, RefId, mk_ua_PARAMS, TVal pa_[4]; TVal pr_;)
KF_STEP(mk_ua) { KF_BEGIN(mk_ua); { TVal a_[] = { VL(F->l), VR(F->X_), VR(F->Y), VR(F->e) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_UA, 4, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_ua, RefId, mk_ua_PARAMS, mk_ua(uint64_t l, RefId X_, RefId Y, RefId e))
KF_DECL_EXT(mk_down, RefId, mk_down_PARAMS, TVal pa_[8]; TVal pr_;)
KF_STEP(mk_down) { KF_BEGIN(mk_down); { TVal a_[] = { VL(F->l), VL(F->lA), VR(F->A), VR(F->t), VS(F->D), VR(F->x), VR(F->e), VR(F->z) }; memcpy(F->pa_, a_, sizeof a_); } KF_CALL(template_call, &F->pr_, TD_DOWN, 8, F->pa_); KF_RET(F->pr_.id); KF_END; }
KF_SYNC_DEF(mk_down, RefId, mk_down_PARAMS, mk_down(uint64_t l, uint64_t lA, RefId A, RefId t, ScopeId D, RefId x, RefId e, RefId z))

KF_DECL_EXT(mk_coe_at, RefId, mk_coe_at_PARAMS, FaceId k; ScopeId A; RefId r, U; uint64_t ls;)
KF_STEP(mk_coe_at) {
    KF_BEGIN(mk_coe_at);
    KF_CALL0(template_kappa, &F->k);
    KF_CALL(level_succ, &F->ls, F->l); KF_CALL(mk_universe, &F->U, F->l);
    KF_CALL(capture_dim1, &F->A, F->i, F->A_i, F->U, F->ls, F->k);
    KF_CALL(mk_coe, &F->r, F->l, F->A, F->cap);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_coe_at, RefId, mk_coe_at_PARAMS, mk_coe_at(uint64_t l, DimVarId i, RefId A_i, RefId cap))
KF_DECL_EXT(mk_fill_at, RefId, mk_fill_at_PARAMS, FaceId k, g; ScopeId A, u; RefId r, U; uint64_t ls;)
KF_STEP(mk_fill_at) {
    KF_BEGIN(mk_fill_at);
    KF_CALL0(template_kappa, &F->k);
    KF_CALL(level_succ, &F->ls, F->l); KF_CALL(mk_universe, &F->U, F->l);
    KF_CALL(capture_dim1, &F->A, F->i, F->A_i, F->U, F->ls, F->k);
    KF_CALL(fc_meet, &F->g, F->k, F->phi);
    KF_CALL(capture_dim1, &F->u, F->i, F->u_i, F->A_i, F->l, F->g);
    KF_CALL(mk_fill, &F->r, F->l, F->A, F->phi, F->u, F->cap, F->rr);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_fill_at, RefId, mk_fill_at_PARAMS, mk_fill_at(uint64_t l, DimVarId i, RefId A_i, FaceId phi, RefId u_i, RefId cap, IntervalId rr))
KF_DECL_EXT(mk_hcomp_at, RefId, mk_hcomp_at_PARAMS, FaceId k, g; ScopeId u; RefId r;)
KF_STEP(mk_hcomp_at) {
    KF_BEGIN(mk_hcomp_at);
    KF_CALL0(template_kappa, &F->k);
    KF_CALL(fc_meet, &F->g, F->k, F->phi);
    KF_CALL(capture_dim1, &F->u, F->j, F->u_j, F->X_, F->l, F->g);
    KF_CALL(mk_hcomp, &F->r, F->l, F->X_, F->phi, F->u, F->cap);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_hcomp_at, RefId, mk_hcomp_at_PARAMS, mk_hcomp_at(uint64_t l, DimVarId j, RefId X_, FaceId phi, RefId u_j, RefId cap))

/* ------------------------------------------------------------------ */
/* §54: capture the retained components of an exposed head and select the one fixed clause */

/* §59.1: a family without its required level annotation is not admitted
 * core syntax; no clause is instantiated for it (the evaluator reports the
 * demand as invalid) and no scope is manufactured without its declared type */
#define U_of_PARAMS(X) X(uint64_t, l)
KF_DECL(U_of, RefId, U_of_PARAMS, RefId r;)
KF_STEP(U_of) { KF_BEGIN(U_of); KF_CALL(mk_universe, &F->r, F->l); KF_RET(F->r); KF_END; }
KF_DECL_EXT_DROP(comp_clause, RefId, comp_clause_PARAMS, comp_clause_drop,
    FaceId saved, tube_guard, g; Head h; RefId out, u0, u1, u2, t0, t1; uint64_t m, n, l; TermOpen o; DimOpen Bk; ScopeId D, E, u, B, left, right, A, alpha, T, e; TVal a[8]; TVal r; IntervalId z; uint64_t ls, lm; RefId rd;)
static void comp_clause_drop(comp_clause_F *F) { if (F->h.f) head_free(&F->h); template_set_kappa(F->saved); }
KF_STEP(comp_clause) {
    KF_BEGIN(comp_clause);
    KF_CALL0(template_kappa, &F->saved);
    template_set_kappa(F->eta);
    KF_CALL(open_ref, NULL, F->fam, &F->h);
    F->out = 0;
    {
        Head *h = &F->h;
        if ((h->tag == T_PI || h->tag == T_SIGMA || h->tag == T_PATH || h->tag == T_GLUE_TYPE) && (h->levels == LEVELS_NONE || levels_first(h->levels) == LEVEL_NONE || ((h->tag == T_PI || h->tag == T_SIGMA) && levels_second(h->levels) == LEVEL_NONE))) {
            head_free(h); template_set_kappa(F->saved); KF_RET(0);
        }
    }
    KF_CALL(fc_meet, &F->tube_guard, F->eta, F->phi);
    switch (F->h.tag) {
    case T_PI: case T_SIGMA:
        F->m = levels_first(F->h.levels); F->n = levels_second(F->h.levels);
        KF_CALL(resolve_term_binder, &F->o, F->fam, 0, 1);                  /* resolved once: (x, D_j, codomain) */
        KF_CALL(U_of, &F->u0, F->m);
        KF_CALL(level_succ, &F->ls, F->m);
        KF_CALL(capture_dim1, &F->D, F->j, F->h.f[0].id, F->u0, F->ls, F->eta);
        KF_CALL(U_of, &F->u1, F->n);
        KF_CALL(level_succ, &F->ls, F->n);
        KF_CALL(capture_dim_term, &F->E, F->j, F->o.x, F->o.type, F->m, F->o.body, F->u1, F->ls, F->eta);
        KF_CALL(level_max, &F->lm, F->m, F->n);
        KF_CALL(capture_dim1, &F->u, F->j, F->tube_j, F->fam, F->lm, F->tube_guard);
        F->a[0] = VL(F->m); F->a[1] = VL(F->n); F->a[2] = VS(F->D); F->a[3] = VS(F->E); F->a[4] = VF(F->phi); F->a[5] = VS(F->u); F->a[6] = VR(F->cap);
        KF_CALL(template_call, &F->r, F->h.tag == T_PI ? TD_PICOMP : TD_SIGMACOMP, 7, F->a); F->out = F->r.id;
        break;
    case T_PATH:
        F->n = levels_first(F->h.levels);
        KF_CALL(resolve_dim_binder, &F->Bk, F->fam, 0, 0);                   /* (k, B(j,k)) */
        KF_CALL(U_of, &F->u0, F->n);
        KF_CALL(level_succ, &F->ls, F->n);
        KF_CALL(capture_dim2, &F->B, F->j, F->Bk.j, F->Bk.body, F->u0, F->ls, F->eta);
        KF_CALL0(iv_zero, &F->z);
        KF_CALL(reindex_dim, &F->rd, F->Bk.body, F->Bk.j, F->z);
        KF_CALL(capture_dim1, &F->left, F->j, F->h.f[1].id, F->rd, F->n, F->eta);
        KF_CALL0(iv_one, &F->z);
        KF_CALL(reindex_dim, &F->rd, F->Bk.body, F->Bk.j, F->z);
        KF_CALL(capture_dim1, &F->right, F->j, F->h.f[2].id, F->rd, F->n, F->eta);
        KF_CALL(capture_dim1, &F->u, F->j, F->tube_j, F->fam, F->n, F->tube_guard);
        F->a[0] = VL(F->n); F->a[1] = VS(F->B); F->a[2] = VS(F->left); F->a[3] = VS(F->right); F->a[4] = VF(F->phi); F->a[5] = VS(F->u); F->a[6] = VR(F->cap);
        KF_CALL(template_call, &F->r, TD_PATHCOMP, 7, F->a); F->out = F->r.id;
        break;
    case T_GLUE_TYPE:
        F->n = levels_first(F->h.levels);
        KF_CALL(U_of, &F->u0, F->n);
        KF_CALL(level_succ, &F->ls, F->n);
        KF_CALL(capture_dim1, &F->A, F->j, F->h.f[0].id, F->u0, F->ls, F->eta);
        KF_CALL(capture_dim1_face, &F->alpha, F->j, F->h.f[1].id);
        KF_CALL(fc_meet, &F->g, F->eta, F->h.f[1].id);
        KF_CALL(capture_dim1, &F->T, F->j, F->h.f[2].id, F->u0, F->ls, F->g);
        KF_CALL(mk_equiv, &F->t0, F->n, F->n, F->h.f[2].id, F->h.f[0].id);
        KF_CALL(capture_dim1, &F->e, F->j, F->h.f[3].id, F->t0, F->n, F->g);
        KF_CALL(capture_dim1, &F->u, F->j, F->tube_j, F->fam, F->n, F->tube_guard);
        F->a[0] = VL(F->n); F->a[1] = VS(F->A); F->a[2] = VS(F->alpha); F->a[3] = VS(F->T); F->a[4] = VS(F->e); F->a[5] = VF(F->phi); F->a[6] = VS(F->u); F->a[7] = VR(F->cap);
        KF_CALL(template_call, &F->r, TD_GLUECOMP, 8, F->a); F->out = F->r.id;
        break;
    case T_UNIVERSE:
        F->l = F->h.payload;
        KF_CALL(level_succ, &F->ls, F->l);
        KF_CALL(capture_dim1, &F->u, F->j, F->tube_j, F->fam, F->ls, F->tube_guard);
        F->a[0] = VL(F->l); F->a[1] = VF(F->phi); F->a[2] = VS(F->u); F->a[3] = VR(F->cap);
        KF_CALL(template_call, &F->r, TD_UNIVERSECOMP, 4, F->a); F->out = F->r.id;
        break;
    default: break;
    }
    head_free(&F->h);
    template_set_kappa(F->saved);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(comp_clause, RefId, comp_clause_PARAMS, comp_clause(DimVarId j, RefId fam, FaceId phi, RefId tube_j, RefId cap, FaceId eta))
