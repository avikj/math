/* face.h — canonical faces, endpoint tests, entailment, quantification and
 * cache projection (§4–5).
 *
 * Literal encoding: (dim << 1) | eps. A clause containing both (i=0) and
 * (i=1) is discarded before absorption and before any projection.
 */
#ifndef CUBICAL_FACE_H
#define CUBICAL_FACE_H

#include "state.h"
#include "dnf.h"
#include "interval.h"

#define FC_LIT(dim, eps) (((uint64_t)(dim) << 1) | ((eps) ? 1u : 0u))
#define FC_LIT_DIM(l) ((DimVarId)((l) >> 1))
#define FC_LIT_EPS(l) ((int)((l) & 1u))

FaceId fc_false(void);
FaceId fc_true(void);
FaceId fc_lit(DimVarId i, int eps);
FaceId fc_join(FaceId a, FaceId b);
FaceId fc_meet(FaceId a, FaceId b);
bool fc_is_false(FaceId a);
bool fc_is_true(FaceId a);
/* (r = eps) for an interval r */
FaceId fc_endpoint(IntervalId r, int eps);
/* chi ⇒ phi by clause containment; inputs canonical */
bool fc_entails(FaceId chi, FaceId phi);
/* ∀i.phi: retain the clauses with no literal on i */
FaceId fc_forall(DimVarId i, FaceId phi);
/* π_S(chi): delete literals whose dimension is not in the dimension set S */
FaceId fc_project(FaceId chi, DimSetId S);
void fc_print(FaceId a, FILE *f);

/* ---- interned sorted sets (dimension sets and term-variable sets) ---- */
uint64_t set_make(uint64_t *elems, size_t n);      /* sorts/dedups in place */
const uint64_t *set_get(uint64_t s, size_t *n);
uint64_t set_union(uint64_t a, uint64_t b);
uint64_t set_remove(uint64_t a, uint64_t x);
bool set_contains(uint64_t a, uint64_t x);

#endif
