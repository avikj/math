/* shape.h — structural computation identity (§76).
 *
 * shape(t, ρ) is the interned structural description of the opened
 * construction t: every constructor field, its sort and order, the packed
 * formation levels, the required face, binder slots, with locally bound
 * identities replaced by canonical (depth, slot) tokens and free identities
 * left anchored. It is alpha/view normalization of syntax: no evaluation, no
 * unfolding of GLOBAL bodies, no comparison up to any identity other than
 * binder renaming. Two references with the same shape and the same
 * projected face are the same computation; the evaluator keys producers by
 * it (§76.3).
 *
 * Shapes are built over a shared DAG and memoized per (reference, renaming
 * environment, depth); each constructed node is counted (REUSE_SHAPE_NODE).
 */
#ifndef CUBICAL_SHAPE_H
#define CUBICAL_SHAPE_H

#include "term.h"

typedef uint64_t ShapeId;
enum { SH_FREE = 1, SH_BOUND = 2, SH_NODE = 3 };

ShapeId shape_of(RefId t);                                   /* ρ = identity, depth 0 */
ShapeId shape_under(RefId t, MapId rho, size_t depth);
const uint64_t *shape_words(ShapeId s, size_t *n);           /* [SH_FREE, x] | [SH_BOUND, token] | [SH_NODE, tag, payload, levels, required, nfields, (kind, binder sort or 0, value)...] */
size_t shape_count(void);
/* frame families (kframe.h) */
#define shape_of_PARAMS(X) X(RefId, t)
#define shape_under_PARAMS(X) X(RefId, t) X(MapId, rho) X(size_t, depth)
KF_PROTO(shape_of, ShapeId, shape_of_PARAMS);
KF_PROTO(shape_under, ShapeId, shape_under_PARAMS);

#endif
