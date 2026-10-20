/* proof.h — the proof-use boundary (HANDOFF §88).
 *
 * Mathematical use of (Γ, φ, e, E) is one judgment, judge.admit of kind
 * AD_PROOF (check.c): the context, E a type and e : E under φ, the
 * conservative audit (audit.c: the symbols reached through declarations and
 * bodies, each read once through the request's view), the body of every
 * revision read by the derivation or reached by the audit validated, and the
 * audited graph's strongly connected components (proof.scc: an iterative
 * Tarjan, one edge per step). A cyclic component gives PENDING, a reached
 * opaque revision ASSUMED, otherwise CORE. A judgment under the false face is
 * face-local. Effect preparation requests the same judgment.
 */
#ifndef CUBICAL_PROOF_H
#define CUBICAL_PROOF_H

#include "check.h"

typedef enum { PU_CORE = 1, PU_ASSUMED, PU_PENDING, PU_INVALID, PU_UNRESOLVED } ProofStatus;
typedef struct {
    ProofStatus status;
    uint64_t revisions;                  /* the set of revisions validated as its premises */
    size_t n_assumptions, n_recursive;
    SymbolId *assumptions, *recursive;   /* reachable opaque symbols; members of cyclic components */
    const char *reason;
} ProofUse;

ProofUse proof_use(ContextId context, FaceId face, RefId evidence, RefId type);
void proof_use_free(ProofUse *u);
const char *proof_status_name(ProofStatus s);
void proof_families_init(void);

#endif
