/* scope.h — contextual parameters: scopes, capture, application (§50).
 *
 * A scope is a reference (or interval / face) abstracted over a finite
 * ordered local telescope. Local occurrences inside its records are
 * (depth, slot) atoms in the variable / dimension id space (term.h
 * `bound_id`); depth 0 is the immediately enclosing telescope. Capture
 * closes concrete identities into those atoms; application substitutes
 * arguments for depth-0 atoms and lowers deeper ones; ambient reindexing
 * touches free identities only. Applying a scope is simultaneous
 * substitution: no APP, PAPP, β step or evaluator request. */
#ifndef CUBICAL_SCOPE_H
#define CUBICAL_SCOPE_H

#include "term.h"

typedef uint64_t ScopeId;
typedef enum { VS_REF = 1, VS_INTERVAL, VS_FACE } ValSort;
typedef struct { ValSort sort; uint64_t id; } Val;

/* a local declaration as stored (closed over the earlier slots) */
typedef struct { Sort sort; RefId type; uint64_t level; FaceId required; } LocalDecl;
/* a local declaration for capture: a concrete identity with its type over the
 * ambient context and the earlier locals */
typedef struct { Sort sort; uint64_t id; RefId type; uint64_t level; FaceId required; } CaptureDecl;

typedef struct { Val body; RefId type; uint64_t level; FaceId guard; } TypedPartial;

/* ---- scoped traversal (scopefam.c) ----
 * A traversal key [kind, depth, context]. The binders are scopes and
 * construction nodes; their locals are (depth, slot) atoms. CLOSE (context:
 * the record identity ↦ slot) closes identities into atoms of the key's
 * depth; APPLY (context: an environment slot ↦ value) replaces those atoms
 * and lowers deeper ones; LOWER removes one empty level (∀); RE (context: a
 * map) substitutes free identities and carries no depth. A scope's own
 * records sit one level deeper than its occurrence. */
enum { TR_CLOSE = 1, TR_APPLY, TR_RE, TR_LOWER };
uint64_t trav_key(unsigned kind, unsigned depth, uint64_t ctx);
uint64_t re_key(uint64_t map);      /* RE at a map */
uint64_t close_key(uint64_t ctx);   /* CLOSE at depth 0 */
uint64_t apply_key(uint64_t env);   /* APPLY at depth 0 */
ScopeId scope_records_traverse(ScopeId S, uint64_t tk);   /* records at tk's depth */
ScopeId scope_with_side(uint64_t pre);               /* the scope whose words (without side data) are the record pre */
ScopeId capture_request(const uint64_t *req, size_t n);
void scope_families_init(void);

/* ---- scopes ---- */
ScopeId capture_scope(size_t n, const CaptureDecl *delta, Val body, RefId result_type, uint64_t result_level, FaceId guard);
ScopeId scope_intern(size_t n, const LocalDecl *locals, Val body, RefId result_type, uint64_t result_level, FaceId guard);   /* already closed */
size_t scope_arity(ScopeId S);
LocalDecl scope_local(ScopeId S, size_t k);
Val scope_body(ScopeId S);
RefId scope_type(ScopeId S);
uint64_t scope_level(ScopeId S);
FaceId scope_guard(ScopeId S);
DimSetId scope_support(ScopeId S);        /* free dimensions (bound atoms excluded) */
VarSetId scope_freevars(ScopeId S);
ScopeId reindex_scope(ScopeId S, MapId sigma);
/* §50.1–2 structural validity, independent of any face: every bound
 * occurrence in the scope's records (and in scopes nested anywhere inside
 * them, through views and template environments) names an existing
 * enclosing telescope, an in-range slot of the right sort; a local's
 * declaration uses only earlier slots of its own telescope; required
 * metadata is present. Must hold before the scope is opened. */
bool scope_validate(ScopeId S, const char **reason);
#endif
