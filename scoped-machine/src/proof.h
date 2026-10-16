/* proof.h — the proof-use boundary (§88).
 *
 * `check` establishes program typing for a partial language and
 * `certificate_verify` establishes that a compiled record is the compiler's
 * own derivation of its inputs. Neither establishes that evidence is an
 * unconditional mathematical witness: a well-typed recursive declaration can
 * carry a circular proof (§88.1). Mathematical use of evidence — discharging
 * an obligation, justifying equivalence-based reuse, erasing a residual as
 * contractible — additionally needs the result of this audit of the complete
 * judgment (Γ, φ, e, E, definition dependencies).
 *
 * The audit is a finite, memoized, stored-syntax traversal with an explicit
 * owned stack: it includes inactive branches, binder domains, map images,
 * scope declarations, template environments and compiled call bodies; it
 * never evaluates, never opens a scope outside its telescope and never
 * unfolds a global into syntax. Reached globals form a dependency graph on
 * their declarations, parameters and bodies; a cyclic component is PENDING,
 * an opaque declaration is an explicit assumption, and an acyclic reached
 * graph expands topologically into the cubical core (CORE). It is
 * deliberately conservative: a syntactically recursive total program may
 * stay PENDING; PENDING is never a refutation, an inequality or a failed
 * program check. Completed sub-traversals and verdicts persist under the
 * exact symbol revisions they read (§79), not under a whole-environment
 * counter.
 */
#ifndef CUBICAL_PROOF_H
#define CUBICAL_PROOF_H

#include "compiler.h"

typedef enum { PU_CORE = 0, PU_ASSUMED, PU_PENDING, PU_INVALID, PU_UNRESOLVED } ProofUseStatus;

typedef struct {
    ProofUseStatus status;
    ContextId context; FaceId face; RefId evidence, type;
    uint64_t session, env;            /* the snapshot the typing part ran in */
    size_t nassumptions; const uint64_t *assumptions;   /* reachable opaque symbols (sorted) */
    size_t nrecursive; const uint64_t *recursive;       /* members of reached cyclic components (sorted) */
    size_t ndeps; const uint64_t *deps;                 /* (symbol, revision) pairs the verdict read */
    const char *reason;
} ProofUse;

/* audit (Γ, φ, e, E): admission, context validity, formation of E, e : E,
 * then the dependency audit; cached per judgment and reused while every
 * recorded symbol revision is current */
ProofUse proof_use(ContextId G, FaceId face, RefId e, RefId E);
/* the proof-use result for a compiled record's actual evidence and expected
 * type (the identity path, the equivalence, the terminal equivalence, the
 * pointwise contraction; a cut's own generic construction) */
ProofUse transform_proof_use(TransformId id);
const char *proof_use_name(ProofUseStatus s);
/* the symbols reachable in the stored syntax of a reference (memoized) */
size_t ref_symbols(RefId t, const uint64_t **out);
uint64_t proof_audit_steps(void);

void proof_init(void);
void proof_free(void);

#endif
