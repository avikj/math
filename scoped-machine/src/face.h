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
FaceId fc_substitute(FaceId phi, DimImagePush img, void *ctx);
/* chi ⇒ phi by clause containment; inputs canonical */
bool fc_entails(FaceId chi, FaceId phi);
/* ∀i.phi: retain the clauses with no literal on i */
FaceId fc_forall(DimVarId i, FaceId phi);
/* π_S(chi): delete literals whose dimension is not in S (sorted list) */
FaceId fc_project(FaceId chi, const uint64_t *S, size_t nS);
void fc_dims(FaceId phi, Words *out);
FaceId fc_from_dnf(Dnf *d);
void fc_to_dnf(FaceId a, Dnf *d);
void fc_print(FaceId a, FILE *f);

/* ---- interned sorted sets (dimension sets and term-variable sets) ---- */
DimSetId dimset_make(uint64_t *elems, size_t n);      /* sorts/dedups in place */
const uint64_t *dimset_get(DimSetId s, size_t *n);
DimSetId dimset_union(DimSetId a, DimSetId b);
DimSetId dimset_remove(DimSetId a, uint64_t x);
bool dimset_contains(DimSetId a, uint64_t x);
VarSetId varset_make(uint64_t *elems, size_t n);
const uint64_t *varset_get(VarSetId s, size_t *n);
static inline size_t varset_n(VarSetId s) { size_t n; varset_get(s, &n); return n; }
static inline size_t dimset_n(DimSetId s) { size_t n; dimset_get(s, &n); return n; }
VarSetId varset_union(VarSetId a, VarSetId b);
VarSetId varset_remove(VarSetId a, uint64_t x);
bool varset_contains(VarSetId a, uint64_t x);
/* frame families (kframe.h) */
#define fc_from_dnf_PARAMS(X) X(Dnf *, d)
#define fc_to_dnf_PARAMS(X) X(FaceId, a) X(Dnf *, d)
#define fc_lit_PARAMS(X) X(DimVarId, i) X(int, eps)
#define fc_join_PARAMS(X) X(FaceId, a) X(FaceId, b)
#define fc_meet_PARAMS(X) X(FaceId, a) X(FaceId, b)
#define fc_endpoint_PARAMS(X) X(IntervalId, r) X(int, eps)
#define fc_substitute_PARAMS(X) X(FaceId, phi) X(DimImagePush, img) X(void *, ctx)
#define fc_entails_PARAMS(X) X(FaceId, chi) X(FaceId, phi)
#define fc_forall_PARAMS(X) X(DimVarId, i) X(FaceId, phi)
#define fc_project_PARAMS(X) X(FaceId, chi) X(const uint64_t *, S) X(size_t, nS)
#define dimset_make_PARAMS(X) X(uint64_t *, elems) X(size_t, n)
#define dimset_union_PARAMS(X) X(DimSetId, a) X(DimSetId, b)
#define dimset_remove_PARAMS(X) X(DimSetId, a) X(uint64_t, x)
#define varset_make_PARAMS(X) X(uint64_t *, elems) X(size_t, n)
#define varset_union_PARAMS(X) X(VarSetId, a) X(VarSetId, b)
#define varset_remove_PARAMS(X) X(VarSetId, a) X(uint64_t, x)
KF_PROTO(fc_from_dnf, FaceId, fc_from_dnf_PARAMS);
KF_PROTO(fc_to_dnf, void, fc_to_dnf_PARAMS);
KF_PROTO(fc_false, FaceId, KF_NOPARAMS);
KF_PROTO(fc_true, FaceId, KF_NOPARAMS);
KF_PROTO(fc_lit, FaceId, fc_lit_PARAMS);
KF_PROTO(fc_join, FaceId, fc_join_PARAMS);
KF_PROTO(fc_meet, FaceId, fc_meet_PARAMS);
KF_PROTO(fc_endpoint, FaceId, fc_endpoint_PARAMS);
KF_PROTO(fc_substitute, FaceId, fc_substitute_PARAMS);
KF_PROTO(fc_entails, bool, fc_entails_PARAMS);
KF_PROTO(fc_forall, FaceId, fc_forall_PARAMS);
KF_PROTO(fc_project, FaceId, fc_project_PARAMS);
KF_PROTO(dimset_make, DimSetId, dimset_make_PARAMS);
KF_PROTO(dimset_union, DimSetId, dimset_union_PARAMS);
KF_PROTO(dimset_remove, DimSetId, dimset_remove_PARAMS);
KF_PROTO(varset_make, VarSetId, varset_make_PARAMS);
KF_PROTO(varset_union, VarSetId, varset_union_PARAMS);
KF_PROTO(varset_remove, VarSetId, varset_remove_PARAMS);

#endif
