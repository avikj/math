/* proof.h — the proof-use boundary (HANDOFF §88).
 *
 * Mathematical use of (Γ, φ, e, E) requires the program-typing judgments
 * (Γ, E under φ, e : E under φ, with the bodies of their pinned symbols) and
 * an audit of the request's pin set (pins.h: the symbols reached through
 * declarations and the bodies of the revisions read): its strongly connected
 * components, by an iterative Tarjan, one edge per step. A cyclic component
 * gives PENDING, reachable opaque declarations ASSUMED, otherwise CORE. A
 * judgment under the false face is face-local. Keyed by the pin set.
 */
#ifndef CUBICAL_PROOF_H
#define CUBICAL_PROOF_H

#include "check.h"
#include "pins.h"

typedef enum { PU_CORE = 1, PU_ASSUMED, PU_PENDING, PU_INVALID, PU_UNRESOLVED } ProofStatus;
typedef struct {
    ProofStatus status;
    PinSet revisions;
    size_t n_assumptions, n_recursive;
    SymbolId *assumptions, *recursive;   /* reachable opaque symbols; members of cyclic components */
    const char *reason;
} ProofUse;

ProofUse proof_use(ContextId context, FaceId face, RefId evidence, RefId type);
void proof_use_free(ProofUse *u);
const char *proof_status_name(ProofStatus s);
void proof_families_init(void);

#endif
