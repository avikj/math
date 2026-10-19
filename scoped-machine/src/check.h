/* check.h — checking the annotated core against the declared signature, and
 * definitional conversion (§33–§34).
 *
 * Judgments: Γ;χ ⊢ A : U_ℓ, Γ;χ ⊢ t : A, Γ;χ ⊢ t ≡ u : A, and validity of a
 * typed substitution. Outcomes are host statuses: VALID / INVALID(reason) /
 * UNRESOLVED(reason) for checking, EQUAL / UNEQUAL / UNRESOLVED for
 * conversion. An interrupted or cyclic normalization, or an exhausted
 * budget, is UNRESOLVED: never accepted as a judgment, never cached as a
 * mathematical inequality.
 *
 * Occurrences of views are checked through the substitution lemma: an origin
 * is validated once in its own parameter context (memoized), and a view of it
 * is valid when its map is a checked typed map into that context.
 *
 * Conversion is type directed and runs under each consistent clause of the
 * ambient face; it uses weak-head observation, the η rules of Π, Σ, Path and
 * Glue, and structural comparison of neutral spines. Fresh comparison
 * identities are minted from an immutable comparison-request record in a
 * distinct owner namespace and applied to both sides.
 *
 * Checking runs synchronously on the calling thread as an admission phase; its
 * weak-head observations use the ordinary evaluation cache and count as
 * ordinary evaluation events.
 */
#ifndef CUBICAL_CHECK_H
#define CUBICAL_CHECK_H

#include "eval.h"

typedef enum { CK_VALID = 0, CK_INVALID, CK_UNRESOLVED } CheckStatus;
typedef enum { CV_EQUAL = 0, CV_UNEQUAL, CV_UNRESOLVED } ConvStatus;

typedef struct { CheckStatus st; RefId type; const char *reason; } Inference;

void check_init(void);
void check_free(void);
/* budget of checking/conversion steps per top-level request (0 = unlimited);
 * exceeding it yields UNRESOLVED("budget") */
void check_set_budget(size_t steps);
size_t check_budget(void);
/* §59.4: begin a new admission attempt (unresolved outcomes of the previous
 * attempt are recomputed on demand) */

CheckStatus check_context(ContextId G, const char **reason);
/* sigma : (Delta;psi) -> (Gamma;chi) */
CheckStatus check_map(ContextId Delta, FaceId psi, MapId sigma, ContextId Gamma, FaceId chi, const char **reason);
/* validate a construction node at its generic instance; returns that
 * instance's context, required face and checked type */
Inference infer(ContextId G, FaceId chi, RefId t);
/* Γ;χ ⊢ A : U_level (formation in a universe; a term with some type is not a type) */
CheckStatus check_is_type(ContextId G, FaceId chi, RefId A, uint64_t *level, const char **reason);
CheckStatus check(ContextId G, FaceId chi, RefId t, RefId A, const char **reason);
ConvStatus convert_type(ContextId G, FaceId chi, RefId A, RefId B);
ConvStatus convert_term(ContextId G, FaceId chi, RefId t, RefId u, RefId A);
/* checked observation of an occurrence: validates the context, infers the
 * type of t under the context's assumption (compatible types by conversion,
 * §33 item 3), then observes. An INVALID or UNRESOLVED check yields
 * W_INVALID / W_STUCK respectively with no observation. */
EvalResult observe_checked(ContextId G, RefId t, WhnfStatus *status, const char **reason);
/* validate every declared symbol with a body against its declared type
 * (the private driver of the admission transaction) */
CheckStatus check_signature(const char **reason);
/* Legacy explicit whole-environment admission operation. Freezes the registered
 * declarations and bodies (the environment version), validates all of them
 * once per version, and returns the environment's verdict. Checked observation
 * and compiler publication validate their own premises and do not call it. */
/* open a new candidate environment after an admission: retires the checker
 * session (claims, verdicts, diagnostic text) and every evaluator observation
 * (EvalResult pointers and diagnostic pointers obtained before are dead);
 * registration is open again. A closed session boundary: no checker,
 * compiler or observation client may be in progress and evaluator work must
 * have drained (both enforced); stop admitting new clients while crossing. */

const char *check_status_name(CheckStatus s);
const char *conv_status_name(ConvStatus s);

#endif
