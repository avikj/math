/* The complete associativity instance of §46, shared by the compiler and
 * schedule tests. Parameters X : U₀, m : X → X → X, a b c : X,
 * α : m(m(a,b),c) = m(a,m(b,c)); left diagram u = m(a,b) with witness s and
 * output m(u,c); right diagram v = m(b,c) with witness t and output m(a,v). */
#ifndef CUBICAL_TEST_ASSOC_H
#define CUBICAL_TEST_ASSOC_H

#include "../src/compiler.h"

typedef struct {
    TermVarId vX, vm, va, vb, vc, valpha, vu, vs, vv, vt;
    RefId X, m, a, b, c, alpha, mab, mbc, lhs, rhs;
    ContextId G;
    DiagramId L, R;
    Action T; bool ok;
} Assoc;

static inline RefId m2(RefId m, RefId x, RefId y) { return mk_app(mk_app(m, x), y); }

static inline void assoc_build(Assoc *A, const char **why) {
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
    CtxDecl d[6] = { { S_TERM, A->vX, U0 }, { S_TERM, A->vm, XXX }, { S_TERM, A->va, A->X }, { S_TERM, A->vb, A->X }, { S_TERM, A->vc, A->X }, { S_TERM, A->valpha, term_var_type(A->valpha) } };
    A->G = context_make(6, d, fc_true());
    /* left: u = m(a,b), s : m(a,b) = u, output m(u,c) */
    A->vu = declare_term(A->X, fc_true());
    A->vs = declare_term(mk_path_const(0, A->X, A->mab, ref_var(A->vu)), fc_true());
    DiagNode ln = { 1, A->vu, A->vs, A->X, 0, A->mab };
    A->L = diagram_declare(A->G, 1, &ln, A->X, 0, m2(A->m, ref_var(A->vu), A->c));
    /* right: v = m(b,c), t : m(b,c) = v, output m(a,v) */
    A->vv = declare_term(A->X, fc_true());
    A->vt = declare_term(mk_path_const(0, A->X, A->mbc, ref_var(A->vv)), fc_true());
    DiagNode rn = { 2, A->vv, A->vt, A->X, 0, A->mbc };
    A->R = diagram_declare(A->G, 1, &rn, A->X, 0, m2(A->m, A->a, ref_var(A->vv)));
    IdentityDecl decl = { 1, A->G, fc_true(), A->X, 0, A->L, A->R, A->alpha };
    A->ok = compile_identity(&decl, &A->T, why) == CK_VALID;
}

/* σ for an invocation with y := rhs, and the realization argument
 * r_L = (m(a,b), refl, α) : R_L[σ] */
static inline MapId assoc_sigma(const Assoc *A, RefId y) {
    return map_single_term(A->T.y, y);
}
static inline RefId assoc_left_arg(const Assoc *A, MapId sigma) {
    RefId RL = reindex(A->T.domain, sigma);                       /* Σ(u:X).Σ(s:m(a,b)=u).(m(u,c)=y) */
    RefId inner = apply_term_binder(RL, 0, 1, A->mab);
    return mk_pair_at_lv(0, RL, A->mab, mk_pair_at_lv(0, inner, mk_refl(0, A->X, A->mab), A->alpha));
}
static inline RefId assoc_right_arg(const Assoc *A, MapId sigma) {
    RefId RR = reindex(A->T.codomain, sigma);                     /* Σ(v:X).Σ(t:m(b,c)=v).(m(a,v)=y) with y = rhs */
    RefId inner = apply_term_binder(RR, 0, 1, A->mbc);
    return mk_pair_at_lv(0, RR, A->mbc, mk_pair_at_lv(0, inner, mk_refl(0, A->X, A->mbc), mk_refl(0, A->X, A->rhs)));
}

#endif
