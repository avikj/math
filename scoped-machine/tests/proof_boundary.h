#ifndef REVIEW_PROOF_BOUNDARY_H
#define REVIEW_PROOF_BOUNDARY_H
#include "../src/compiler.h"

/* This finite conservative boundary audits mathematical use of evidence.
 * It does not replace check(), decide termination, or reject partial programs.
 * CORE and ASSUMED are judgments relative to the supplied occurrence context.
 * PENDING is NOT an inequality, a refutation, or a failed program-type check.
 */
typedef enum { PB_CORE, PB_ASSUMED, PB_PENDING, PB_INVALID, PB_UNRESOLVED } ProofBoundaryStatus;
typedef struct {
    ProofBoundaryStatus status;
    ContextId context;
    FaceId face;
    RefId evidence, type;
    uint64_t environment; /* snapshot guard, not a timeless proof flag */
    Words assumptions; /* reachable opaque symbols */
    Words recursive;   /* reachable cyclic declaration/body components */
    const char *reason; /* existing session-owned checker diagnostic, or literal */
} ProofBoundary;
ProofBoundary proof_boundary(ContextId context, FaceId face, RefId evidence, RefId type);
void proof_boundary_free(ProofBoundary *result);
#endif
