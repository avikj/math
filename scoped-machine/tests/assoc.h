/* The complete associativity instance of §46, shared by the compiler and
 * schedule tests. Parameters X : U₀, m : X → X → X, a b c : X,
 * α : m(m(a,b),c) = m(a,m(b,c)); left diagram u = m(a,b) with witness s and
 * output m(u,c); right diagram v = m(b,c) with witness t and output m(a,v).
 * T = id_action(X, L, R, α, y) : Maps(R_L y, R_R y), an ordinary term. */
#ifndef CUBICAL_TEST_ASSOC_H
#define CUBICAL_TEST_ASSOC_H

#include "../src/compiler.h"

typedef struct {
    TermVarId vX, vm, va, vb, vc, valpha, vu, vs, vv, vt, vy;
    RefId X, m, a, b, c, alpha, mab, mbc, lhs, rhs;
    ContextId G, Gy;
    RefId L, R, T, domain, codomain;     /* domain/codomain: the realization telescopes at y */
} Assoc;

static inline RefId m2(RefId m, RefId x, RefId y) { return mk_app(mk_app(m, x), y); }

static inline void assoc_build(Assoc *A) {
    RefId U0 = mk_universe(0);
    A->vX = declare_term(U0, fc_true()); A->X = ref_var(A->vX);
    RefId XX = mk_fun(0, 0, A->X, A->X), XXX = mk_fun(0, 0, A->X, XX);
    A->vm = declare_term(XXX, fc_true()); A->m = ref_var(A->vm);
    A->va = declare_term(A->X, fc_true()); A->a = ref_var(A->va);
    A->vb = declare_term(A->X, fc_true()); A->b = ref_var(A->vb);
    A->vc = declare_term(A->X, fc_true()); A->c = ref_var(A->vc);
    A->mab = m2(A->m, A->a, A->b); A->mbc = m2(A->m, A->b, A->c);
    A->lhs = m2(A->m, A->mab, A->c); A->rhs = m2(A->m, A->a, A->mbc);
    A->valpha = declare_term(mk_path_const(0, A->X, A->lhs, A->rhs), fc_true()); A->alpha = ref_var(A->valpha);
    CtxDecl d[6] = { { S_TERM, A->vX}, { S_TERM, A->vm}, { S_TERM, A->va}, { S_TERM, A->vb}, { S_TERM, A->vc}, { S_TERM, A->valpha} };
    A->G = context_make(6, d, fc_true());
    A->vy = declare_term(A->X, fc_true()); RefId y = ref_var(A->vy);
    A->Gy = context_extend_term(A->G, A->vy);
    A->vu = declare_term(A->X, fc_true());
    RefId Ps = mk_path_const(0, A->X, A->mab, ref_var(A->vu));
    A->vs = declare_term(Ps, fc_true());
    DiagNode ln = { A->vu, A->vs, A->X, 0, A->mab };
    uint64_t rl, rr;
    A->L = diagram_fold(1, &ln, A->X, 0, m2(A->m, ref_var(A->vu), A->c), &rl);
    A->vv = declare_term(A->X, fc_true());
    RefId Pt = mk_path_const(0, A->X, A->mbc, ref_var(A->vv));
    A->vt = declare_term(Pt, fc_true());
    DiagNode rn = { A->vv, A->vt, A->X, 0, A->mbc };
    A->R = diagram_fold(1, &rn, A->X, 0, m2(A->m, A->a, ref_var(A->vv)), &rr);
    A->domain = mk_sigma_lv(0, 0, A->vu, A->X, mk_sigma_lv(0, 0, A->vs, Ps, mk_path_const(0, A->X, m2(A->m, ref_var(A->vu), A->c), y)));
    A->codomain = mk_sigma_lv(0, 0, A->vv, A->X, mk_sigma_lv(0, 0, A->vt, Pt, mk_path_const(0, A->X, m2(A->m, A->a, ref_var(A->vv)), y)));
    RefId args[5] = { A->X, A->L, A->R, A->alpha, y };
    RefId f = id_action(0, rl, rr);
    for (int k = 0; k < 5; k++) f = mk_app(f, args[k]);
    A->T = f;
}
static inline MapId assoc_sigma(const Assoc *A, RefId y) { return map_single_term(A->vy, y); }
static inline RefId assoc_call(const Assoc *A, int dir, MapId sigma, RefId arg) { return maps_apply(reindex(A->T, sigma), dir, arg); }
/* r_L = (m(a,b), refl, α) : R_L[σ] */
static inline RefId assoc_left_arg(const Assoc *A, MapId sigma) {
    RefId RL = reindex(A->domain, sigma);
    return mk_pair_at_lv(0, RL, A->mab, mk_pair_at_lv(0, apply_term_binder(RL, 0, 1, A->mab), mk_refl(0, A->X, A->mab), A->alpha));
}
static inline RefId assoc_right_arg(const Assoc *A, MapId sigma) {
    RefId RR = reindex(A->codomain, sigma);
    return mk_pair_at_lv(0, RR, A->mbc, mk_pair_at_lv(0, apply_term_binder(RR, 0, 1, A->mbc), mk_refl(0, A->X, A->mbc), mk_refl(0, A->X, A->rhs)));
}

#endif
