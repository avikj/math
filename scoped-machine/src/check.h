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
/* §59.4: begin a new admission attempt (unresolved outcomes of the previous
 * attempt are recomputed on demand) */
void check_new_attempt(void);
uint64_t check_attempt(void);   /* the current attempt (a changed budget or check_new_attempt starts one): an UNRESOLVED outcome is local to it */

CheckStatus check_context(ContextId G, const char **reason);
/* sigma : (Delta;psi) -> (Gamma;chi) */
CheckStatus check_map(ContextId Delta, FaceId psi, MapId sigma, ContextId Gamma, FaceId chi, const char **reason);
/* validate an origin in its own parameter context; returns that context,
 * required face and checked type */
CheckStatus check_origin(OriginId C, ContextId *ctx_out, FaceId *required_out, RefId *type_out, const char **reason);
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
EvalResult *observe_checked(ContextId G, RefId t, WhnfStatus *status, const char **reason);
/* validate every declared symbol with a body against its declared type
 * (the private driver of the admission transaction) */
CheckStatus check_signature(const char **reason);
/* §57 R1: the whole-environment admission gate. Freezes the registered
 * declarations and bodies (the environment version), validates all of them
 * once per version, and returns the environment's verdict; public checked
 * execution and compiler publication require VALID. */
CheckStatus check_admission(const char **reason);
/* open a new candidate environment after an admission: retires the checker
 * session (claims, verdicts, diagnostic text) and every evaluator observation
 * (EvalResult pointers and diagnostic pointers obtained before are dead);
 * registration is open again. A closed session boundary: no checker,
 * compiler or observation client may be in progress and evaluator work must
 * have drained (both enforced); stop admitting new clients while crossing. */
void check_open_environment(void);
uint64_t check_session_id(void);
/* frame families (kframe.h): the same judgments as resumable frames */
#define origin_context_PARAMS(X) X(OriginId, C)
#define check_context_PARAMS(X) X(ContextId, G) X(const char **, reason)
#define check_map_PARAMS(X) X(ContextId, Delta) X(FaceId, psi) X(MapId, sigma) X(ContextId, Gamma) X(FaceId, chi) X(const char **, reason)
#define check_origin_PARAMS(X) X(OriginId, C) X(ContextId *, ctx_out) X(FaceId *, required_out) X(RefId *, type_out) X(const char **, reason)
#define infer_PARAMS(X) X(ContextId, G) X(FaceId, chi) X(RefId, t)
#define check_is_type_PARAMS(X) X(ContextId, G) X(FaceId, chi) X(RefId, A) X(uint64_t *, level) X(const char **, reason)
#define check_PARAMS(X) X(ContextId, G) X(FaceId, chi) X(RefId, t) X(RefId, A) X(const char **, reason)
#define convert_type_PARAMS(X) X(ContextId, G) X(FaceId, chi) X(RefId, A) X(RefId, B)
#define convert_term_PARAMS(X) X(ContextId, G) X(FaceId, chi) X(RefId, t) X(RefId, u) X(RefId, A)
#define observe_checked_PARAMS(X) X(ContextId, G) X(RefId, t) X(WhnfStatus *, status) X(const char **, reason)
#define check_signature_PARAMS(X) X(const char **, reason)
#define check_admission_PARAMS(X) X(const char **, reason)
KF_PROTO(origin_context, ContextId, origin_context_PARAMS);
KF_PROTO(check_context, CheckStatus, check_context_PARAMS);
KF_PROTO(check_map, CheckStatus, check_map_PARAMS);
KF_PROTO(check_origin, CheckStatus, check_origin_PARAMS);
KF_PROTO(infer, Inference, infer_PARAMS);
KF_PROTO(check_is_type, CheckStatus, check_is_type_PARAMS);
KF_PROTO(check, CheckStatus, check_PARAMS);
KF_PROTO(convert_type, ConvStatus, convert_type_PARAMS);
KF_PROTO(convert_term, ConvStatus, convert_term_PARAMS);
KF_PROTO(observe_checked, EvalResult *, observe_checked_PARAMS);
KF_PROTO(check_signature, CheckStatus, check_signature_PARAMS);
KF_PROTO(check_admission, CheckStatus, check_admission_PARAMS);   /* changes with every checker session; session-dependent caches are qualified by it */

/* the parameter context of an origin: its free dimensions, then its free
 * term variables in dependency order with their declared types; assumption
 * = the origin's required face */
ContextId origin_context(OriginId C);

const char *check_status_name(CheckStatus s);
const char *conv_status_name(ConvStatus s);

#endif
