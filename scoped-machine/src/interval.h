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
void iv_print(IntervalId r, FILE *f);

#endif
