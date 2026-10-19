/* proof.h — the proof-use boundary (HANDOFF §88) as judgment families.
 *
 * A complete judgment (Γ, φ, e, E) is accepted for mathematical use only on
 * its dependency closure: the program-typing judgments of the request (the
 * context, the formation of E and e : E under each clause of φ, the bodies
 * of the pinned symbols) and an audit of the symbols its stored syntax
 * reaches through declarations and the bodies of the revisions read. The
 * audit graph's strongly connected components are computed by an iterative
 * Tarjan, one edge per step. A cyclic component gives PENDING (no verdict on
 * the proposition, execution unaffected); reachable opaque declarations give
 * ASSUMED (evidence relative to them); otherwise CORE. A judgment under the
 * false face is face-local (CORE for false, never a theorem under true).
 * The result is keyed by the request and its revisions (pin sets), never by
 * an environment version, and shared by every requester.
 */
#ifndef CUBICAL_PROOF_H
#define CUBICAL_PROOF_H

#include "check.h"
#include "pins.h"

typedef enum { PU_CORE = 1, PU_ASSUMED, PU_PENDING, PU_INVALID, PU_UNRESOLVED } ProofStatus;
typedef struct {
    ProofStatus status;
    ContextId context; FaceId face; RefId evidence, type;
    PinSet revisions;                 /* the audited revisions (symbol ↦ body read) */
    size_t n_assumptions, n_recursive;
    SymbolId *assumptions;            /* reachable opaque symbols */
    SymbolId *recursive;              /* members of reachable cyclic components */
    const char *reason;
} ProofUse;

ProofUse proof_use(ContextId context, FaceId face, RefId evidence, RefId type);
void proof_use_free(ProofUse *u);
const char *proof_status_name(ProofStatus s);
void proof_families_init(void);

#endif
