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
/* the occurrence callbacks are frame families (kframe.h) given by their push functions */
typedef void (*TravTermPush)(KStack *ks, RefId *ret, uint64_t x, size_t depth, void *ctx);       /* 0 = keep the occurrence */
typedef void (*TravDimPush)(KStack *ks, IntervalId *ret, uint64_t i, size_t depth, void *ctx);   /* 0 = keep */
typedef struct {
    TravTermPush term;
    TravDimPush dim;
    uint64_t key;                                                /* memo key of this traversal */
    void *ctx;
    void (*enter)(ScopeId S, size_t depth, void *ctx);         /* optional: a scope's records are about to be traversed at depth */
    void (*leave)(ScopeId S, size_t depth, void *ctx);
} Trav;
RefId trav_ref(RefId t, const Trav *tv, size_t depth);
IntervalId trav_iv(IntervalId r, const Trav *tv, size_t depth);
FaceId trav_fc(FaceId f, const Trav *tv, size_t depth);
ScopeId trav_scope(ScopeId S, const Trav *tv, size_t depth);    /* the scope's records are at depth+1 */
Val trav_val(Val v, const Trav *tv, size_t depth);

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
void scope_local_at(ScopeId S, size_t k, const Val *args, RefId *type, FaceId *req, uint64_t *level);   /* local k's declaration at the prefix args[0..k) */
ScopeId reindex_scope(ScopeId S, MapId sigma);
FaceId forall_scope(ScopeId S);           /* unary dimension scope of total face syntax */
/* open with fresh concrete locals minted from `key` (checking); ids receives
 * the minted identities in slot order */
TypedPartial open_scope_fresh(ScopeId S, uint64_t key, uint64_t *ids);
/* §50.1–2 structural validity, independent of any face: every bound
 * occurrence in the scope's records (and in scopes nested anywhere inside
 * them, through views and template environments) names an existing
 * enclosing telescope, an in-range slot of the right sort; a local's
 * declaration uses only earlier slots of its own telescope; required
 * metadata is present. Must hold before the scope is opened. */
bool scope_validate(ScopeId S, const char **reason);
/* the same finite check for a whole reference used at the top level
 * (outside any telescope): every scope reachable through its template
 * environments is validated with its actual enclosing stack */
bool ref_validate(RefId t, const char **reason);

/* free (unbound) part of a dimension set / variable set */
DimSetId dimset_free(DimSetId s);
VarSetId varset_free(VarSetId s);

/* frame families (kframe.h) */
#define trav_ref_PARAMS(X) X(RefId, t) X(const Trav *, tv) X(size_t, depth)
#define trav_iv_PARAMS(X) X(IntervalId, r) X(const Trav *, tv) X(size_t, depth)
#define trav_fc_PARAMS(X) X(FaceId, f) X(const Trav *, tv) X(size_t, depth)
#define trav_scope_PARAMS(X) X(ScopeId, S) X(const Trav *, tv) X(size_t, depth)
#define trav_val_PARAMS(X) X(Val, v) X(const Trav *, tv) X(size_t, depth)
#define capture_scope_PARAMS(X) X(size_t, n) X(const CaptureDecl *, delta) X(Val, body) X(RefId, result_type) X(uint64_t, result_level) X(FaceId, guard)
#define scope_intern_PARAMS(X) X(size_t, n) X(const LocalDecl *, locals) X(Val, body) X(RefId, result_type) X(uint64_t, result_level) X(FaceId, guard)
#define apply_scope_PARAMS(X) X(ScopeId, S) X(size_t, n) X(const Val *, args)
#define scope_local_at_PARAMS(X) X(ScopeId, S) X(size_t, k) X(const Val *, args) X(RefId *, type) X(FaceId *, req) X(uint64_t *, level)
#define reindex_scope_PARAMS(X) X(ScopeId, S) X(MapId, sigma)
#define forall_scope_PARAMS(X) X(ScopeId, S)
#define open_scope_fresh_PARAMS(X) X(ScopeId, S) X(uint64_t, key) X(uint64_t *, ids)
#define scope_validate_PARAMS(X) X(ScopeId, S) X(const char **, reason)
#define ref_validate_PARAMS(X) X(RefId, t) X(const char **, reason)
#define dimset_free_PARAMS(X) X(DimSetId, s)
#define varset_free_PARAMS(X) X(VarSetId, s)
KF_PROTO(trav_ref, RefId, trav_ref_PARAMS);
KF_PROTO(trav_iv, IntervalId, trav_iv_PARAMS);
KF_PROTO(trav_fc, FaceId, trav_fc_PARAMS);
KF_PROTO(trav_scope, ScopeId, trav_scope_PARAMS);
KF_PROTO(trav_val, Val, trav_val_PARAMS);
KF_PROTO(capture_scope, ScopeId, capture_scope_PARAMS);
KF_PROTO(scope_intern, ScopeId, scope_intern_PARAMS);
KF_PROTO(apply_scope, TypedPartial, apply_scope_PARAMS);
KF_PROTO(scope_local_at, void, scope_local_at_PARAMS);
KF_PROTO(reindex_scope, ScopeId, reindex_scope_PARAMS);
KF_PROTO(forall_scope, FaceId, forall_scope_PARAMS);
KF_PROTO(open_scope_fresh, TypedPartial, open_scope_fresh_PARAMS);
KF_PROTO(scope_validate, bool, scope_validate_PARAMS);
KF_PROTO(ref_validate, bool, ref_validate_PARAMS);
KF_PROTO(dimset_free, DimSetId, dimset_free_PARAMS);
KF_PROTO(varset_free, VarSetId, varset_free_PARAMS);

#endif
