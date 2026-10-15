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

/* ---- generic depth-aware traversal over scoped values ---- */
typedef struct {
    RefId (*term)(uint64_t x, unsigned depth, void *ctx);        /* 0 = keep the occurrence */
    IntervalId (*dim)(uint64_t i, unsigned depth, void *ctx);    /* 0 = keep */
    uint64_t key;                                                /* memo key of this traversal */
    void *ctx;
} Trav;
RefId trav_ref(RefId t, const Trav *tv, unsigned depth);
IntervalId trav_iv(IntervalId r, const Trav *tv, unsigned depth);
FaceId trav_fc(FaceId f, const Trav *tv, unsigned depth);
ScopeId trav_scope(ScopeId S, const Trav *tv, unsigned depth);    /* the scope's records are at depth+1 */
Val trav_val(Val v, const Trav *tv, unsigned depth);

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
TypedPartial apply_scope(ScopeId S, size_t n, const Val *args);
ScopeId reindex_scope(ScopeId S, MapId sigma);
FaceId forall_scope(ScopeId S);           /* unary dimension scope of total face syntax */
/* open with fresh concrete locals minted from `key` (checking); ids receives
 * the minted identities in slot order */
TypedPartial open_scope_fresh(ScopeId S, uint64_t key, uint64_t *ids);

/* free (unbound) part of a dimension set / variable set */
DimSetId dimset_free(DimSetId s);
VarSetId varset_free(VarSetId s);

#endif
