/* interval.h — the free De Morgan algebra on dimension identities (§3).
 *
 * Canonical antichain DNF of clauses of signed atoms. Atom encoding:
 * (dim << 1) | sign, sign 0 = positive, 1 = negated. A clause containing
 * both +i and -i is retained: the algebra is not Boolean.
 */
#ifndef CUBICAL_INTERVAL_H
#define CUBICAL_INTERVAL_H

#include "state.h"
#include "dnf.h"

#define IV_ATOM(dim, neg) (((uint64_t)(dim) << 1) | ((neg) ? 1u : 0u))
#define IV_ATOM_DIM(a) ((DimVarId)((a) >> 1))
#define IV_ATOM_NEG(a) (((a) & 1u) != 0)

IntervalId iv_zero(void);
IntervalId iv_one(void);
IntervalId iv_var(DimVarId i);
IntervalId iv_join(IntervalId r, IntervalId s);
IntervalId iv_meet(IntervalId r, IntervalId s);
IntervalId iv_negate(IntervalId r);
bool iv_is_zero(IntervalId r);
bool iv_is_one(IntervalId r);
/* image used by substitution: dimension → interval, a frame family (kframe.h) given by its push function */
typedef void (*DimImagePush)(KStack *ks, IntervalId *ret, DimVarId i, void *ctx);
IntervalId iv_substitute(IntervalId r, DimImagePush img, void *ctx);
/* append the dimensions occurring in r to out (unsorted, may repeat) */
void iv_dims(IntervalId r, Words *out);
/* intern from a working DNF (normalizes) */
IntervalId iv_from_dnf(Dnf *d);
void iv_to_dnf(IntervalId r, Dnf *d);
void iv_print(IntervalId r, FILE *f);
/* frame families (kframe.h) */
#define iv_from_dnf_PARAMS(X) X(Dnf *, d)
#define iv_to_dnf_PARAMS(X) X(IntervalId, r) X(Dnf *, d)
#define iv_var_PARAMS(X) X(DimVarId, i)
#define iv_join_PARAMS(X) X(IntervalId, r) X(IntervalId, s)
#define iv_meet_PARAMS(X) X(IntervalId, r) X(IntervalId, s)
#define iv_negate_PARAMS(X) X(IntervalId, r)
#define iv_substitute_PARAMS(X) X(IntervalId, r) X(DimImagePush, img) X(void *, ctx)
KF_PROTO(iv_from_dnf, IntervalId, iv_from_dnf_PARAMS);
KF_PROTO(iv_to_dnf, void, iv_to_dnf_PARAMS);
KF_PROTO(iv_zero, IntervalId, KF_NOPARAMS);
KF_PROTO(iv_one, IntervalId, KF_NOPARAMS);
KF_PROTO(iv_var, IntervalId, iv_var_PARAMS);
KF_PROTO(iv_join, IntervalId, iv_join_PARAMS);
KF_PROTO(iv_meet, IntervalId, iv_meet_PARAMS);
KF_PROTO(iv_negate, IntervalId, iv_negate_PARAMS);
KF_PROTO(iv_substitute, IntervalId, iv_substitute_PARAMS);

#endif
