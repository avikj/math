/* runtime.h — the ordinary values of HANDOFF §§80, 83–84, 96.
 *
 * Maps(X,Y) = Σ(c:X→Y).Σ(d:Y→X).(Π x. d(c x) = x) × (Π y. c(d y) = y), its
 * identity, composite and inverse; the dependent singleton presentation with
 * both inverse proofs; Diagram_{b,r}(B) = Σ(C:B).Σ(R:B→U_r).Π y.Maps(R y, C = y)
 * with zero and the extension node; the generic identity action
 * F/G = d_R(p⁻¹·c_L r) / d_L(p·c_R s) with its middle inverse paths built
 * from the groupoid laws (path induction J and the K(w) words); the maps of
 * a supplied equivalence, of CUT_TO_PATH and of COLLAPSE_FIBRE; residual
 * presentations Res_{z,r} = Σ(Z:U_z).Σ(X:U_r).Maps(X,Z) with their zero, node
 * and action along an equivalence of terminals.
 *
 * Every recipe is built once per exact level tuple (machine lifetime) as an
 * open body over keyed formals and as the closed function abstracting them.
 * A runtime program applies the closed function to computed arguments; the
 * host adapter instantiates the open body by one simultaneous substitution.
 * Both are ordinary terms; nothing here is a registry consulted by execution.
 */
#ifndef CUBICAL_RUNTIME_H
#define CUBICAL_RUNTIME_H

#include "check.h"
#include "lib.h"

typedef enum {
    RK_MAPS_TYPE = 1, RK_MAPS_ID, RK_MAPS_COMP, RK_MAPS_INV, RK_SINGLETON,
    RK_DIAGRAM_TYPE, RK_ZERO, RK_NODE,
    RK_LUNIT, RK_RUNIT, RK_RINV, RK_LINV, RK_ASSOC, RK_MID, RK_ACTION,
    RK_EQUIV_MAPS, RK_CUT_MAPS, RK_FIBRE_MAPS,
    RK_RES_TYPE, RK_RES_ZERO, RK_RES_NODE, RK_RES_ACTION,
    RK_COUNT
} RecipeKind;

#define RT_MAXF 8
typedef struct {
    RecipeKind kind; uint64_t lv[4];
    size_t n; TermVarId formal[RT_MAXF]; RefId ftype[RT_MAXF]; uint64_t flevel[RT_MAXF];
    RefId body, body_type; uint64_t body_level;     /* open over the formals; body : body_type : U_body_level */
    RefId value, type; uint64_t level;              /* the closed function : type : U_level */
    ContextId telescope;                            /* the formals at their types: the recipe's signature */
} Recipe;

/* the recipe at an exact level tuple (unused levels 0) */
const Recipe *rt_recipe(RecipeKind kind, uint64_t l0, uint64_t l1, uint64_t l2, uint64_t l3);
RefId rt_inst(const Recipe *r, const RefId *args);        /* body[formals ↦ args] */
RefId rt_inst_type(const Recipe *r, const RefId *args);   /* body_type[formals ↦ args] */
RefId rt_apply(const Recipe *r, const RefId *args);       /* value args… (ordinary application) */
MapId rt_args(const Recipe *r, const RefId *args);        /* formals ↦ args (the instance's substitution) */

/* projections (ordinary Σ projections and applications) */
RefId rt_c(RefId M); RefId rt_d(RefId M); RefId rt_h(RefId M); RefId rt_k(RefId M);
RefId rt_dg_C(RefId D); RefId rt_dg_R(RefId D, RefId y); RefId rt_dg_M(RefId D, RefId y);
RefId rt_res_Z(RefId P); RefId rt_res_X(RefId P); RefId rt_res_M(RefId P);

/* types, instantiated (no redex) */
RefId rt_maps_type(uint64_t a, uint64_t b, RefId X, RefId Y);
RefId rt_diagram_type(uint64_t b, uint64_t r, RefId B);
RefId rt_res_type(uint64_t z, uint64_t r);

void rt_free(void);

#endif
