#include "lib.h"
#include "eval.h"

void lib_free(void) { templates_free(); }


/* ------------------------------------------------------------------ */
/* capture adapters                                                      */

ScopeId capture_dim1(DimVarId j, RefId body, RefId type, uint64_t level, FaceId guard) {
    CaptureDecl d[1] = { { S_DIM, j, 0, LEVEL_NONE, fc_true() } };
    Val b = { VS_REF, body };
    return capture_scope(1, d, b, type, level, guard);
}

/* ------------------------------------------------------------------ */
/* §52 programs                                                          */

static TVal VL(uint64_t n) { TVal v = { PS_LEVEL, n }; return v; }
static TVal VR(RefId r) { TVal v = { PS_REF, r }; return v; }
static TVal VI(IntervalId r) { TVal v = { PS_INTERVAL, r }; return v; }
static TVal VS(ScopeId s) { TVal v = { PS_SCOPE, s }; return v; }
#define CALLT(def, ...) ({ TVal _a[] = { __VA_ARGS__ }; template_call(def, sizeof _a / sizeof _a[0], _a).id; })

RefId mk_path_const(uint64_t l, RefId A, RefId lft, RefId r) { return CALLT(TD_PATHCONST, VL(l), VR(A), VR(lft), VR(r)); }
RefId mk_papp_const(uint64_t l, RefId A, RefId lft, RefId r, RefId p, IntervalId s) { return CALLT(TD_PAPPCONST, VL(l), VR(A), VR(lft), VR(r), VR(p), VI(s)); }
RefId mk_fun(uint64_t l, uint64_t m, RefId X, RefId Y) { return CALLT(TD_FUN, VL(l), VL(m), VR(X), VR(Y)); }
RefId mk_equiv(uint64_t l, uint64_t m, RefId X, RefId Y) { return CALLT(TD_EQUIV, VL(l), VL(m), VR(X), VR(Y)); }
RefId mk_id_equiv(uint64_t l, RefId X) { return CALLT(TD_IDEQUIV, VL(l), VR(X)); }
RefId mk_coe(uint64_t l, ScopeId A, RefId cap) { return CALLT(TD_COE, VL(l), VS(A), VR(cap)); }
RefId mk_ua(uint64_t l, RefId X, RefId Y, RefId e) { return CALLT(TD_UA, VL(l), VR(X), VR(Y), VR(e)); }

RefId mk_coe_at(uint64_t l, DimVarId i, RefId A_i, RefId cap) {
    return mk_coe(l, capture_dim1(i, A_i, mk_universe(l), level_succ(l), fc_true()), cap);
}

/* ------------------------------------------------------------------ */
/* §54: capture the retained components of an exposed head and select the one fixed clause */

/* §59.1: a family without its required level annotation is not admitted
 * core syntax; no clause is instantiated for it (the evaluator reports the
 * demand as invalid) and no scope is manufactured without its declared type.
 *
 * comp.clause([j, fam, φ, u_j, cap]) is a frame family: the retained
 * components of the exposed family head are captured (independent demands,
 * one join), each scope guarded by the face its body is defined on, then the
 * one fixed clause is interpreted.
 * Its value is the clause instance, or 0 when no clause applies. */
static uint64_t universe_request(uint64_t l) { uint64_t w[CREQ_MAX]; return rq(creq_fixed(w, T_UNIVERSE, l, LEVELS_NONE, 0, NULL, 0), w); }
/* capture requests [n, (sort, id, type, level, required)*, body_sort, body, type, level, guard] */
static uint64_t cap1(DimVarId j, ValSort bs, uint64_t body, RefId type, uint64_t level, FaceId guard) {
    uint64_t w[11] = { 1, S_DIM, j, 0, LEVEL_NONE, fc_true(), bs, body, type, level, guard };
    return interner_intern(&M.keys, w, 11, NULL);
}
static uint64_t cap2(uint64_t s1, uint64_t id1, RefId t1, uint64_t l1, FaceId r1, uint64_t s2, uint64_t id2, RefId t2, uint64_t l2, FaceId r2, uint64_t body, RefId type, uint64_t level, FaceId guard) {
    uint64_t w[16] = { 2, s1, id1, t1, l1, r1, s2, id2, t2, l2, r2, VS_REF, body, type, level, guard };
    return interner_intern(&M.keys, w, 16, NULL);
}
typedef struct {
    uint64_t j, fam, phi, tube, cap, tag, levels, m, n, sm, sn, mn, tg, a0, a1, a2, a3, x, xr, Um, Un, eq, er; ExprId root;
    Family kf[5]; uint64_t ka[5], kb[5], kv[5]; size_t nk, ki;   /* independent demands: launched, then awaited in order */
    WordBuf wb; bool created;
} CcLoc;
#define DEMAND(f, a, b) do { L->kf[L->nk] = (f); L->ka[L->nk] = (a); L->kb[L->nk] = (b); L->nk++; } while (0)
#define LAUNCH_AWAIT_ALL() for (L->ki = 0; L->ki < L->nk; L->ki++) family_launch(L->kf[L->ki], L->ka[L->ki], L->kb[L->ki]); \
    for (L->ki = 0; L->ki < L->nk; L->ki++) FR_AWAIT(k, L->kv[L->ki], L->kf[L->ki], L->ka[L->ki], L->kb[L->ki])
static void compclause_step(Cont *k, uint64_t v) {
    CcLoc *L = FR_LOC(k, CcLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    { size_t n; const uint64_t *w = rget(k->w[0], &n); L->j = w[0]; L->fam = w[1]; L->phi = w[2]; L->tube = w[3]; L->cap = w[4]; }
    L->tag = ref_tag(L->fam);
    FR_AWAIT(k, L->levels, F_HEAD, L->fam, 1);
    if ((L->tag == T_PI || L->tag == T_SIGMA || L->tag == T_PATH || L->tag == T_GLUE_TYPE) &&
        (L->levels == LEVELS_NONE || levels_first(L->levels) == LEVEL_NONE || ((L->tag == T_PI || L->tag == T_SIGMA) && levels_second(L->levels) == LEVEL_NONE)))
        FR_FINISH(k, 0);
    L->tg = L->phi;                                                    /* the tube is defined on φ */
    if (L->tag == T_PI || L->tag == T_SIGMA) {
        L->m = levels_first(L->levels); L->n = levels_second(L->levels);
        FR_LSUCC(k, L->sm, L->m);
        FR_LSUCC(k, L->sn, L->n);
        FR_LMAX(k, L->mn, L->m, L->n);
        FR_AWAIT(k, L->a0, F_FIELD, L->fam, 0);
        L->x = binder_term_var(L->fam, 0, L->a0);                       /* (x, D_j, codomain) */
        FR_AWAIT(k, L->xr, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->a1, F_BINDER, L->fam, binder_req(S_TERM, 0, 1, L->xr));
        FR_AWAIT(k, L->Um, F_CONSTRUCT, universe_request(L->m), 0);
        FR_AWAIT(k, L->Un, F_CONSTRUCT, universe_request(L->n), 0);
        L->nk = 0;
        DEMAND(F_CAPTURE, cap1(L->j, VS_REF, L->a0, L->Um, L->sm, fc_true()), 0);
        DEMAND(F_CAPTURE, cap2(S_DIM, L->j, 0, LEVEL_NONE, fc_true(), S_TERM, L->x, L->a0, L->m, term_var_required(L->x), L->a1, L->Un, L->sn, fc_true()), 0);
        DEMAND(F_CAPTURE, cap1(L->j, VS_REF, L->tube, L->fam, L->mn, L->tg), 0);
        LAUNCH_AWAIT_ALL();
        {   TVal a[7] = { { PS_LEVEL, L->m }, { PS_LEVEL, L->n }, { PS_SCOPE, L->kv[0] }, { PS_SCOPE, L->kv[1] }, { PS_FACE, L->phi }, { PS_SCOPE, L->kv[2] }, { PS_REF, L->cap } };
            template_call_env(L->tag == T_PI ? TD_PICOMP : TD_SIGMACOMP, 7, a, &L->wb, &L->root); }
        goto interpret;
    }
    if (L->tag == T_PATH) {
        L->n = levels_first(L->levels);
        FR_LSUCC(k, L->sn, L->n);
        L->x = binder_dim_var(L->fam, 0);                                /* (k, B(j,k)) */
        FR_AWAIT(k, L->a0, F_BINDER, L->fam, binder_req(S_DIM, 0, 0, iv_var(L->x)));
        L->nk = 0;
        DEMAND(F_FIELD, L->fam, 1);
        DEMAND(F_FIELD, L->fam, 2);
        DEMAND(F_TREF, L->a0, re_key(map_single_dim(L->x, iv_zero())));
        DEMAND(F_TREF, L->a0, re_key(map_single_dim(L->x, iv_one())));
        DEMAND(F_CONSTRUCT, universe_request(L->n), 0);
        LAUNCH_AWAIT_ALL();
        L->a1 = L->kv[0]; L->a2 = L->kv[1]; L->a3 = L->kv[2]; L->eq = L->kv[3]; L->Un = L->kv[4];
        L->nk = 0;
        DEMAND(F_CAPTURE, cap2(S_DIM, L->j, 0, LEVEL_NONE, fc_true(), S_DIM, L->x, 0, LEVEL_NONE, fc_true(), L->a0, L->Un, L->sn, fc_true()), 0);
        DEMAND(F_CAPTURE, cap1(L->j, VS_REF, L->a1, L->a3, L->n, fc_true()), 0);
        DEMAND(F_CAPTURE, cap1(L->j, VS_REF, L->a2, L->eq, L->n, fc_true()), 0);
        DEMAND(F_CAPTURE, cap1(L->j, VS_REF, L->tube, L->fam, L->n, L->tg), 0);
        LAUNCH_AWAIT_ALL();
        {   TVal a[7] = { { PS_LEVEL, L->n }, { PS_SCOPE, L->kv[0] }, { PS_SCOPE, L->kv[1] }, { PS_SCOPE, L->kv[2] }, { PS_FACE, L->phi }, { PS_SCOPE, L->kv[3] }, { PS_REF, L->cap } };
            template_call_env(TD_PATHCOMP, 7, a, &L->wb, &L->root); }
        goto interpret;
    }
    if (L->tag == T_GLUE_TYPE) {
        L->n = levels_first(L->levels);
        FR_LSUCC(k, L->sn, L->n);
        L->nk = 0;
        DEMAND(F_FIELD, L->fam, 0);
        DEMAND(F_FIELD, L->fam, 1);
        DEMAND(F_FIELD, L->fam, 2);
        DEMAND(F_FIELD, L->fam, 3);
        DEMAND(F_CONSTRUCT, universe_request(L->n), 0);
        LAUNCH_AWAIT_ALL();
        L->a0 = L->kv[0]; L->a1 = L->kv[1]; L->a2 = L->kv[2]; L->a3 = L->kv[3]; L->Un = L->kv[4];
        L->x = L->a1;                                                    /* T_j and e_j are defined on α_j */
        FR_AWAIT(k, L->eq, F_EQUIV, RQ(L->n, L->n, L->a2, L->a0), 0);   /* Equiv(T_j, A_j) */
        L->nk = 0;
        DEMAND(F_CAPTURE, cap1(L->j, VS_REF, L->a0, L->Un, L->sn, fc_true()), 0);
        DEMAND(F_CAPTURE, cap1(L->j, VS_FACE, L->a1, 0, LEVEL_NONE, fc_true()), 0);
        DEMAND(F_CAPTURE, cap1(L->j, VS_REF, L->a2, L->Un, L->sn, L->x), 0);
        DEMAND(F_CAPTURE, cap1(L->j, VS_REF, L->a3, L->eq, L->n, L->x), 0);
        DEMAND(F_CAPTURE, cap1(L->j, VS_REF, L->tube, L->fam, L->n, L->tg), 0);
        LAUNCH_AWAIT_ALL();
        {   TVal a[8] = { { PS_LEVEL, L->n }, { PS_SCOPE, L->kv[0] }, { PS_SCOPE, L->kv[1] }, { PS_SCOPE, L->kv[2] }, { PS_SCOPE, L->kv[3] }, { PS_FACE, L->phi }, { PS_SCOPE, L->kv[4] }, { PS_REF, L->cap } };
            template_call_env(TD_GLUECOMP, 8, a, &L->wb, &L->root); }
        goto interpret;
    }
    if (L->tag == T_UNIVERSE) {
        FR_AWAIT(k, L->n, F_HEAD, L->fam, 0);
        FR_LSUCC(k, L->sn, L->n);
        FR_AWAIT(k, L->x, F_CAPTURE, cap1(L->j, VS_REF, L->tube, L->fam, L->sn, L->tg), 0);
        {   TVal a[4] = { { PS_LEVEL, L->n }, { PS_FACE, L->phi }, { PS_SCOPE, L->x }, { PS_REF, L->cap } };
            template_call_env(TD_UNIVERSECOMP, 4, a, &L->wb, &L->root); }
        goto interpret;
    }
    FR_FINISH(k, 0);
interpret:
    FR_CALL(k, L->er, intern_sub(k, &M.keys, &L->wb, &L->created));
    FR_AWAIT(k, r, F_INTERP, L->root, L->er);
    FR_FINISH(k, rword(r, 1));
    FR_END(k);
}
/* Equiv(l, m, X, Y): the library program, one interpretation (its value is
 * the type) */
typedef struct { uint64_t x, y; WordBuf wb; bool created; } EqLoc;
static void equiv_step(Cont *k, uint64_t v) {
    EqLoc *L = FR_LOC(k, EqLoc);
    size_t nq; const uint64_t *q = rget(k->w[0], &nq);
    uint64_t r = 0;
    FR_BEGIN(k);
    {   TVal a[4] = { { PS_LEVEL, q[0] }, { PS_LEVEL, q[1] }, { PS_REF, q[2] }, { PS_REF, q[3] } };
        ExprId root; template_call_env(TD_EQUIV, 4, a, &L->wb, &root); L->x = root; }
    FR_CALL(k, L->y, intern_sub(k, &M.keys, &L->wb, &L->created));
    FR_AWAIT(k, r, F_INTERP, L->x, L->y);
    { size_t n; FR_FINISH(k, rget(r, &n)[1]); }
    FR_END(k);
}
void lib_families_init(void) {
    family_define(F_EQUIV, "lib.equiv", equiv_step, sizeof(EqLoc));
    family_define(F_COMPCLAUSE, "comp.clause", compclause_step, sizeof(CcLoc));
}
