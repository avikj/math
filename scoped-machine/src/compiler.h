/* compiler.h — identities as ordinary values (HANDOFF §§80, 83–84, 96).
 *
 * The constructions are closed terms of the core, written once:
 *   Maps(X,Y)     = Σ(c:X→Y).Σ(d:Y→X).(Π x. d(c x) = x) × (Π y. c(d y) = y)
 *   Res_{z,r}     = Σ(T:U_z).Σ(X:U_r).Maps(X,T)            (a presentation of T)
 *   Diagram_{b,r}(B) = Σ(C:B).Σ(R:B→U_r).Π y.Maps(R y, C = y)
 * res_zero / res_node build presentations (the dependent singleton composed
 * with the tail's maps, both inverse proofs retained); a diagram is the
 * pointwise presentation of C = y, so dg_zero / dg_node are res_zero /
 * res_node at each y. res_action(L, R, E) = M_R⁻¹ ∘ E ∘ M_L with E a Maps of
 * the terminals; the identity action of p : C_L = C_R at y is res_action
 * with E the middle maps p⁻¹·_ / p·_ (inverse paths from the groupoid laws,
 * by path induction and the K(w) words). A source declaration is a right
 * fold of node ending in zero; an invocation is application. Nothing here is
 * registered: equal constructions are equal references by interning.
 */
#ifndef CUBICAL_COMPILER_H
#define CUBICAL_COMPILER_H

#include "check.h"
#include "lib.h"

/* types */
RefId maps_type(uint64_t a, uint64_t b, RefId X, RefId Y);
RefId res_type(uint64_t z, uint64_t r);
RefId diagram_type(uint64_t b, uint64_t r, RefId B);

/* projections */
RefId maps_c(RefId M); RefId maps_d(RefId M); RefId maps_h(RefId M); RefId maps_k(RefId M);
RefId res_T(RefId P); RefId res_X(RefId P); RefId res_M(RefId P);
RefId dg_C(RefId D); RefId dg_R(RefId D, RefId y); RefId dg_M(RefId D, RefId y);

/* the closed constructions (levels exact) */
RefId res_zero(uint64_t z);                              /* λ T. (T, T, id) */
RefId res_node(uint64_t a, uint64_t z, uint64_t r);      /* λ A t Q. presentation of T_{Q t refl} */
RefId dg_zero(uint64_t b);                               /* λ B c. zero */
RefId dg_node(uint64_t a, uint64_t b, uint64_t r);       /* λ B A t Q. node */
RefId res_action(uint64_t zl, uint64_t rl, uint64_t zr, uint64_t rr);   /* λ TL TR L R E. Maps(X_L, X_R) */
RefId id_action(uint64_t b, uint64_t rl, uint64_t rr);   /* λ B L R p y. Maps(R_L y, R_R y) */
RefId equiv_maps(uint64_t l, uint64_t m);                /* λ X Y e. Maps(X, Y) */
RefId cut_maps(uint64_t b);                              /* λ B C D. Maps(Σz.Σ(u:C=z).(D=z), C = D) */
RefId fibre_maps(uint64_t b, uint64_t r);                /* λ B R k. Maps(Σb.R b, B) */

/* a source diagram (§39): node x : A (A : U_level), e : t = x */
typedef struct { TermVarId x, e; RefId A; uint64_t level; RefId t; } DiagNode;
/* the right fold of node ending in zero(B, o) (residual: res_zero(Z)); *r the realization level */
RefId diagram_fold(size_t n, const DiagNode *nodes, RefId B, uint64_t lB, RefId o, uint64_t *r);
RefId residual_fold(size_t n, const DiagNode *nodes, RefId Z, uint64_t lZ, uint64_t *r);

enum { DIR_FORWARD = 0, DIR_REVERSE = 1 };
RefId maps_apply(RefId M, int dir, RefId a);             /* app(c M, a) / app(d M, a) */

#endif
