#include "scope.h"
#include "template.h"   /* the validator walks template environments */

#define SSIDE(id) ((ScopeSide *)chunked_at(&M.scope_side, (id) - 1))

DimSetId dimset_free(DimSetId s) {
    size_t n; const uint64_t *d = dimset_get(s, &n);
    uint64_t *w = malloc((n ? n : 1) * sizeof(uint64_t)); size_t m = 0;
    for (size_t k = 0; k < n; k++) if (!is_bound_id(d[k])) w[m++] = d[k];
    DimSetId out = dimset_make(w, m); free(w); return out;
}
VarSetId varset_free(VarSetId s) {
    size_t n; const uint64_t *d = varset_get(s, &n);
    uint64_t *w = malloc((n ? n : 1) * sizeof(uint64_t)); size_t m = 0;
    for (size_t k = 0; k < n; k++) if (!is_bound_id(d[k])) w[m++] = d[k];
    VarSetId out = varset_make(w, m); free(w); return out;
}

/* ------------------------------------------------------------------ */
/* scope records: [n, (sort, type, level, required)*, result_sort, type, level, guard, body] */

static const uint64_t *scope_words(ScopeId S, size_t *n) { return interner_get(&M.scopes, S, n); }
size_t scope_arity(ScopeId S) { size_t n; return (size_t)scope_words(S, &n)[0]; }
LocalDecl scope_local(ScopeId S, size_t k) {
    size_t n; const uint64_t *w = scope_words(S, &n);
    require(k < w[0], "scope slot out of range");
    LocalDecl d = { (Sort)w[1 + 4 * k], w[2 + 4 * k], w[3 + 4 * k], w[4 + 4 * k] };
    return d;
}
static const uint64_t *scope_tail(ScopeId S) { size_t n; const uint64_t *w = scope_words(S, &n); return w + 1 + 4 * w[0]; }
Val scope_body(ScopeId S) { const uint64_t *t = scope_tail(S); Val v = { (ValSort)t[0], t[4] }; return v; }
RefId scope_type(ScopeId S) { return scope_tail(S)[1]; }
uint64_t scope_level(ScopeId S) { return scope_tail(S)[2]; }
FaceId scope_guard(ScopeId S) { return scope_tail(S)[3]; }
DimSetId scope_support(ScopeId S) { return SSIDE(S)->support; }
VarSetId scope_freevars(ScopeId S) { return SSIDE(S)->freevars; }

ScopeId scope_intern(size_t n, const LocalDecl *locals, Val body, RefId result_type, uint64_t result_level, FaceId guard) {
    Words w; words_init(&w);
    words_push(&w, n);
    for (size_t k = 0; k < n; k++) { words_push(&w, locals[k].sort); words_push(&w, locals[k].type); words_push(&w, locals[k].level); words_push(&w, locals[k].required); }
    words_push(&w, body.sort); words_push(&w, result_type); words_push(&w, result_level); words_push(&w, guard); words_push(&w, body.id);
    ScopeId id = interner_intern(&M.scopes, w.w, w.n, NULL);
    words_free(&w);
    return scope_with_side(id);            /* the side data is written before the id is returned */
}

/* ------------------------------------------------------------------ */
/* capture: close the concrete locals of Δ into (depth, slot) atoms         */

ScopeId capture_scope(size_t n, const CaptureDecl *delta, Val body, RefId result_type, uint64_t result_level, FaceId guard) {
    Words w; words_init(&w);
    words_push(&w, n);
    for (size_t k = 0; k < n; k++) { words_push(&w, delta[k].sort); words_push(&w, delta[k].id); words_push(&w, delta[k].type); words_push(&w, delta[k].level); words_push(&w, delta[k].required); }
    words_push(&w, body.sort); words_push(&w, body.id); words_push(&w, result_type); words_push(&w, result_level); words_push(&w, guard);
    ScopeId S = capture_request(w.w, w.n);
    words_free(&w);
    return S;
}

/* ------------------------------------------------------------------ */
/* structural validation (§50.1–2)                                       */

/* A finite walk over the environments of references, the stored field
 * constants of constructions, and every scope reachable from them with the
 * actual enclosing telescope stack. Memoized per (record, telescope stack): a
 * validity established inside a telescope is never reused at another one.
 * GLOBAL bodies are not unfolded: their definitions are the admission
 * checker's. */
typedef struct { VEC(ScopeId) stack; const char *why; } ValCtx;
static uint64_t stack_key(const ValCtx *v) { return v->stack.len ? interner_intern(&M.keys, v->stack.data, v->stack.len, NULL) : 0; }
static bool validated_before(uint64_t kind, uint64_t id, uint64_t stk) {
    uint64_t k[3] = { kind, id, stk }, val;
    pthread_mutex_lock(&M.term_mu); bool have = wordmap_get(&M.trav_memo, k, 3, &val); pthread_mutex_unlock(&M.term_mu);
    return have;
}
static void remember_validated(uint64_t kind, uint64_t id, uint64_t stk) {
    uint64_t k[3] = { kind, id, stk };
    pthread_mutex_lock(&M.term_mu); wordmap_put(&M.trav_memo, k, 3, 1); pthread_mutex_unlock(&M.term_mu);
}
static bool val_atom(ValCtx *v, uint64_t id, Sort want) {
    uint32_t d = bound_depth(id), s = bound_slot(id);
    if (d >= v->stack.len) { v->why = "bound occurrence names no enclosing telescope"; return false; }
    ScopeId T = v->stack.data[v->stack.len - 1 - d];
    if (s >= scope_arity(T)) { v->why = "bound occurrence names a slot outside its telescope"; return false; }
    if (scope_local(T, s).sort != want) { v->why = "bound occurrence has the wrong sort for its slot"; return false; }
    return true;
}
static void val_ref(RefId t, ValCtx *v);
static void val_scope(ScopeId S, ValCtx *v);
static void val_dims(const Words *w, ValCtx *v) { for (size_t k = 0; k < w->n && !v->why; k++) if (is_bound_id(w->w[k])) val_atom(v, w->w[k], S_DIM); }
static void val_iv(IntervalId r, ValCtx *v) { Words w; words_init(&w); iv_dims(r, &w); val_dims(&w, v); words_free(&w); }
static void val_fc(FaceId f, ValCtx *v) { Words w; words_init(&w); fc_dims(f, &w); val_dims(&w, v); words_free(&w); }
static void val_ref(RefId t, ValCtx *v) {
    if (v->why) return;
    if (ref_is_var(t)) { uint64_t x = ref_var_id(t); if (is_bound_id(x)) val_atom(v, x, S_TERM); return; }
    uint64_t stk = stack_key(v);
    if (validated_before(0x4EF1, t, stk)) return;
    /* the environment's images, then a construction's stored field constants
     * (inactive branches and metadata included) and its declared face: a
     * constant is closed over the node's own atoms, but a scope stored in it
     * is validated at the actual telescope stack (binders are ordinary
     * identities, so the depth is unchanged) */
    TEnvId E = tenv_of(t); size_t n = tenv_size(E);
    for (size_t k = 0; k < n && !v->why; k++) {
        uint64_t slot; TVal val; tenv_entry(E, k, &slot, &val);
        switch (val.sort) {
        case PS_REF: val_ref(val.id, v); break;
        case PS_INTERVAL: val_iv(val.id, v); break;
        case PS_FACE: val_fc(val.id, v); break;
        case PS_SCOPE: val_scope(val.id, v); break;
        case PS_LEVEL: break;
        }
    }
    TNodeId Q = tnode_of(t);
    if (tnode_is_construction(Q)) {
        size_t nf = tnode_nfields(Q);
        for (size_t k = 0; k < nf && !v->why; k++) {
            uint64_t c = tnode_const_field(Q, k); FieldKind kd = tnode_field_kind(Q, k);
            if (kd == F_REF) val_ref(c, v); else if (kd == F_INTERVAL) val_iv(c, v); else val_fc(c, v);
        }
        if (!v->why && tnode_const_declared(Q)) val_fc(tnode_const_declared(Q), v);
    }
    if (!v->why) remember_validated(0x4EF1, t, stk);
}
/* a prefix view of a telescope: the first k locals */
static ScopeId prefix_scope(ScopeId S, size_t k) {
    LocalDecl *ls = malloc((k ? k : 1) * sizeof(LocalDecl));
    for (size_t q = 0; q < k; q++) ls[q] = scope_local(S, q);
    Val b = { VS_FACE, fc_true() };
    ScopeId P = scope_intern(k, ls, b, 0, LEVEL_NONE, fc_true());
    free(ls); return P;
}
static void val_scope(ScopeId S, ValCtx *v) {
    if (v->why) return;
    uint64_t stk = stack_key(v);
    if (validated_before(0x5CA1, S, stk)) return;
    size_t n = scope_arity(S);
    Val body = scope_body(S);
    for (size_t k = 0; k < n && !v->why; k++) {
        LocalDecl d = scope_local(S, k);
        if (d.sort == S_TERM && !d.type) v->why = "term local without a declared type";
        else if (d.sort == S_DIM && d.type) v->why = "dimension local with a type";
    }
    if (!v->why && body.sort == VS_REF && !scope_type(S)) v->why = "reference scope without a declared result type";
    /* each local's declaration over its prefix telescope and the enclosing stack */
    for (size_t k = 0; k < n && !v->why; k++) {
        LocalDecl d = scope_local(S, k);
        vec_push(&v->stack, prefix_scope(S, k));
        if (d.type) val_ref(d.type, v);
        if (!v->why) val_fc(d.required, v);
        v->stack.len--;
        if (v->why) v->why = "local declaration uses a later or absent slot";
    }
    if (v->why) return;
    /* body, result type and guard over the whole telescope */
    vec_push(&v->stack, S);
    switch (body.sort) { case VS_REF: val_ref(body.id, v); break; case VS_INTERVAL: val_iv(body.id, v); break; case VS_FACE: val_fc(body.id, v); break; }
    if (!v->why && scope_type(S)) val_ref(scope_type(S), v);
    if (!v->why) val_fc(scope_guard(S), v);
    v->stack.len--;
    if (!v->why) remember_validated(0x5CA1, S, stk);
}
bool scope_validate(ScopeId S, const char **reason) {
    ValCtx v; memset(&v, 0, sizeof v);
    val_scope(S, &v);                      /* no outer telescope at the top level */
    vec_free(&v.stack);
    if (v.why) { *reason = v.why; return false; }
    return true;
}
bool ref_validate(RefId t, const char **reason) {
    ValCtx v; memset(&v, 0, sizeof v);
    val_ref(t, &v);
    vec_free(&v.stack);
    if (v.why) { *reason = v.why; return false; }
    return true;
}

/* ------------------------------------------------------------------ */
/* application and ambient reindexing                                    */

static uint64_t args_record(size_t n, const Val *args) {
    Words w; words_init(&w);
    for (size_t k = 0; k < n; k++) { words_push(&w, args[k].sort); words_push(&w, args[k].id); }
    uint64_t key = interner_intern(&M.keys, w.w, w.n, NULL);
    words_free(&w);
    return key;
}

TypedPartial apply_scope(ScopeId S, size_t n, const Val *args) {
    require(n == scope_arity(S), "scope application arity");
    uint64_t tk = trav_key(TR_APPLY, 0, args_record(n, args));
    TypedPartial p;
    p.body = trav_val(scope_body(S), tk);
    p.type = scope_type(S) ? trav_ref(scope_type(S), tk) : 0;
    p.level = scope_level(S);
    p.guard = trav_fc(scope_guard(S), tk);
    return p;
}

/* the k-th local's declaration instantiated at the argument prefix args[0..k) */
void scope_local_at(ScopeId S, size_t k, const Val *args, RefId *type, FaceId *req, uint64_t *level) {
    LocalDecl d = scope_local(S, k);
    uint64_t tk = trav_key(TR_APPLY, 0, args_record(k, args));
    *type = d.type ? trav_ref(d.type, tk) : 0;
    *req = trav_fc(d.required, tk);
    *level = d.level;
}

ScopeId reindex_scope(ScopeId S, MapId sigma) {
    if (map_is_identity(sigma)) return S;
    return scope_records_traverse(S, trav_key(TR_RE, 0, sigma));
}

/* remove the single binder level after ∀ */
FaceId forall_scope(ScopeId S) {
    require(scope_arity(S) == 1 && scope_local(S, 0).sort == S_DIM && scope_body(S).sort == VS_FACE, "forall of a non-unary face scope");
    return trav_fc(fc_forall(bound_id(0, 0), scope_body(S).id), trav_key(TR_LOWER, 0, 0));
}

TypedPartial open_scope_fresh(ScopeId S, uint64_t key, uint64_t *ids) {
    size_t n = scope_arity(S);
    Val *args = calloc(n ? n : 1, sizeof(Val));
    for (size_t k = 0; k < n; k++) {
        LocalDecl d = scope_local(S, k);
        KeyWord kw[4] = { { KW_CONST, 9000 }, { KW_CONST, key }, { KW_CONST, S }, { KW_CONST, k } };
        if (d.sort == S_DIM) { DimVarId j = fresh_dim_keyed(kw, 4); args[k].sort = VS_INTERVAL; args[k].id = iv_var(j); if (ids) ids[k] = j; }
        else {
            /* the declaration type over the earlier fresh locals */
            uint64_t tk = trav_key(TR_APPLY, 0, args_record(k, args));
            RefId ty = trav_ref(d.type, tk);
            FaceId rq = trav_fc(d.required, tk);
            TermVarId x = fresh_term_keyed_req(kw, 4, ty, rq);
            args[k].sort = VS_REF; args[k].id = ref_var(x);
            if (ids) ids[k] = x;
        }
    }
    TypedPartial p = apply_scope(S, n, args);
    free(args);
    return p;
}
