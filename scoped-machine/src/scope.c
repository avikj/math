#include "kstack.h"
#include "scope.h"
#include "fine.h"
#include "template.h"   /* the validator walks template environments */

/* template layer: traversal of a TVIEW's environment (template.c) */
RefId tview_traverse(RefId t, const Trav *tv, size_t depth);

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
/* traversal                                                             */

typedef struct { const Trav *tv; size_t depth; } DimCb;
static IntervalId dim_cb(DimVarId i, void *ctx) {
    DimCb *c = ctx;
    IntervalId r = c->tv->dim ? c->tv->dim(i, c->depth, c->tv->ctx) : 0;
    return r ? r : iv_var(i);
}
IntervalId trav_iv(IntervalId r, const Trav *tv, size_t depth) { DimCb c = { tv, depth }; return iv_substitute(r, dim_cb, &c); }
FaceId trav_fc(FaceId f, const Trav *tv, size_t depth) { DimCb c = { tv, depth }; return fc_substitute(f, dim_cb, &c); }

static RefId trav_ref_body(RefId t, const Trav *tv, size_t depth);
typedef struct { RefId t; const Trav *tv; size_t depth; RefId out; } trav_ref_args;
static void trav_ref_thunk(void *p) { trav_ref_args *a = p; a->out = trav_ref_body(a->t, a->tv, a->depth); }
RefId trav_ref(RefId t, const Trav *tv, size_t depth) {
    if (!kstack_low()) return trav_ref_body(t, tv, depth);
    trav_ref_args a = { t, tv, depth, 0 }; kstack_run(trav_ref_thunk, &a); return a.out;
}
static RefId trav_ref_body(RefId t, const Trav *tv, size_t depth) {
    if (ref_is_var(t)) {
        RefId r = tv->term ? tv->term(ref_var_id(t), depth, tv->ctx) : 0;
        return r ? r : t;
    }
    uint64_t key[4] = { 1, t, tv->key, depth }, out;
    if (tv->key && wordmap_get(&M.trav_memo, key, 4, &out)) return out;
    if (ref_is_tview(t)) out = tview_traverse(t, tv, depth);
    else {
        OriginId c = ref_origin(t);
        MapId tau = ref_map(t);
        MapBuilder b; mapb_init(&b);
        size_t n; const uint64_t *xs = varset_get(origin_ft(c), &n);
        for (size_t k = 0; k < n; k++) mapb_term(&b, xs[k], trav_ref(map_term_image(tau, xs[k]), tv, depth));
        const uint64_t *ds = dimset_get(origin_fd(c), &n);
        for (size_t k = 0; k < n; k++) mapb_dim(&b, ds[k], trav_iv(map_dim_image(tau, ds[k]), tv, depth));
        out = make_view(c, mapb_finish(&b));
    }
    if (tv->key) wordmap_put(&M.trav_memo, key, 4, out);
    return out;
}

Val trav_val(Val v, const Trav *tv, size_t depth) {
    Val o = v;
    switch (v.sort) {
    case VS_REF: o.id = trav_ref(v.id, tv, depth); break;
    case VS_INTERVAL: o.id = trav_iv(v.id, tv, depth); break;
    case VS_FACE: o.id = trav_fc(v.id, tv, depth); break;
    }
    return o;
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

static void acc_val(Val v, DimSetId *sup, VarSetId *fv) {
    switch (v.sort) {
    case VS_REF: *sup = dimset_union(*sup, ref_support(v.id)); *fv = varset_union(*fv, ref_freevars(v.id)); break;
    case VS_INTERVAL: { Words w; words_init(&w); iv_dims(v.id, &w); *sup = dimset_union(*sup, dimset_make(w.w, w.n)); words_free(&w); break; }
    case VS_FACE: { Words w; words_init(&w); fc_dims(v.id, &w); *sup = dimset_union(*sup, dimset_make(w.w, w.n)); words_free(&w); break; }
    }
}

ScopeId scope_intern(size_t n, const LocalDecl *locals, Val body, RefId result_type, uint64_t result_level, FaceId guard) {
    Words w; words_init(&w);
    words_push(&w, n);
    for (size_t k = 0; k < n; k++) { words_push(&w, locals[k].sort); words_push(&w, locals[k].type); words_push(&w, locals[k].level); words_push(&w, locals[k].required); }
    words_push(&w, body.sort); words_push(&w, result_type); words_push(&w, result_level); words_push(&w, guard); words_push(&w, body.id);
    pthread_mutex_lock(&M.term_mu); ScopeId have = interner_find(&M.scopes, w.w, w.n); pthread_mutex_unlock(&M.term_mu);
    if (have) { words_free(&w); return have; }
    /* free boundary: every record, bound atoms excluded — computed outside
     * the lock on immutable data (§94: its loops are transition points of a
     * kernel continuation); the lock is held to intern and publish only */
    DimSetId sup = dimset_make(NULL, 0); VarSetId fv = varset_make(NULL, 0);
    for (size_t k = 0; k < n; k++) {
        if (locals[k].type) { Val tv = { VS_REF, locals[k].type }; acc_val(tv, &sup, &fv); }
        Val rv = { VS_FACE, locals[k].required }; acc_val(rv, &sup, &fv);
    }
    if (result_type) { Val tv = { VS_REF, result_type }; acc_val(tv, &sup, &fv); }
    { Val gv = { VS_FACE, guard }; acc_val(gv, &sup, &fv); }
    acc_val(body, &sup, &fv);
    DimSetId sup_id = dimset_free(sup); VarSetId fv_id = varset_free(fv);
    bool created;
    pthread_mutex_lock(&M.term_mu);
    ScopeId id = interner_intern(&M.scopes, w.w, w.n, &created);
    if (created) { ScopeSide *s = SSIDE(id); s->support = sup_id; s->freevars = fv_id; }
    pthread_mutex_unlock(&M.term_mu);
    words_free(&w);
    return id;
}

/* ------------------------------------------------------------------ */
/* capture: close the concrete locals of Δ into (depth, slot) atoms         */

typedef struct { size_t n; const CaptureDecl *d; } CloseCtx;
static RefId close_term(uint64_t x, size_t depth, void *c) {
    CloseCtx *cc = c;
    if (is_bound_id(x)) return 0;
    for (size_t k = 0; k < cc->n; k++) if (cc->d[k].sort == S_TERM && cc->d[k].id == x) return ref_var(bound_id(depth, k));
    return 0;
}
static IntervalId close_dim(uint64_t i, size_t depth, void *c) {
    CloseCtx *cc = c;
    if (is_bound_id(i)) return 0;
    for (size_t k = 0; k < cc->n; k++) if (cc->d[k].sort == S_DIM && cc->d[k].id == i) return iv_var(bound_id(depth, k));
    return 0;
}
static uint64_t ids_key(size_t n, const CaptureDecl *d) {
    Words w; words_init(&w);
    for (size_t k = 0; k < n; k++) { words_push(&w, d[k].sort); words_push(&w, d[k].id); }
    uint64_t key = interner_intern(&M.keys, w.w, w.n, NULL);
    words_free(&w);
    return key;
}

ScopeId capture_scope(size_t n, const CaptureDecl *delta, Val body, RefId result_type, uint64_t result_level, FaceId guard) {
    CloseCtx cc = { n, delta };
    Trav tv = { close_term, close_dim, 0x100000000ULL + ids_key(n, delta), &cc };
    LocalDecl *ls = malloc((n ? n : 1) * sizeof(LocalDecl));
    for (size_t k = 0; k < n; k++) {
        ls[k].sort = delta[k].sort; ls[k].level = delta[k].level;
        ls[k].type = delta[k].type ? trav_ref(delta[k].type, &tv, 0) : 0;
        ls[k].required = trav_fc(delta[k].required, &tv, 0);
    }
    Val b = trav_val(body, &tv, 0);
    RefId ty = result_type ? trav_ref(result_type, &tv, 0) : 0;
    FaceId g = trav_fc(guard, &tv, 0);
    ScopeId S = scope_intern(n, ls, b, ty, result_level, g);
    free(ls);
    return S;
}

/* traverse a scope whose own records sit at `rd` */
static ScopeId trav_scope_records_body(ScopeId S, const Trav *tv, size_t rd);
typedef struct { ScopeId S; const Trav *tv; size_t rd; ScopeId out; } trav_scope_args;
static void trav_scope_thunk(void *p) { trav_scope_args *a = p; a->out = trav_scope_records_body(a->S, a->tv, a->rd); }
static ScopeId trav_scope_records(ScopeId S, const Trav *tv, size_t rd) {
    if (!kstack_low()) return trav_scope_records_body(S, tv, rd);
    trav_scope_args a = { S, tv, rd, 0 }; kstack_run(trav_scope_thunk, &a); return a.out;
}
static ScopeId trav_scope_records_body(ScopeId S, const Trav *tv, size_t rd) {
    uint64_t key[4] = { 2, S, tv->key, rd }, out;
    if (tv->key && wordmap_get(&M.trav_memo, key, 4, &out)) return out;
    if (tv->enter) tv->enter(S, rd, tv->ctx);
    size_t n = scope_arity(S);
    LocalDecl *ls = malloc((n ? n : 1) * sizeof(LocalDecl));
    for (size_t k = 0; k < n; k++) {
        ls[k] = scope_local(S, k);
        if (ls[k].type) ls[k].type = trav_ref(ls[k].type, tv, rd);
        ls[k].required = trav_fc(ls[k].required, tv, rd);
    }
    Val b = trav_val(scope_body(S), tv, rd);
    RefId ty = scope_type(S) ? trav_ref(scope_type(S), tv, rd) : 0;
    FaceId g = trav_fc(scope_guard(S), tv, rd);
    out = scope_intern(n, ls, b, ty, scope_level(S), g);
    free(ls);
    if (tv->leave) tv->leave(S, rd, tv->ctx);
    if (tv->key) wordmap_put(&M.trav_memo, key, 4, out);
    return out;
}
ScopeId trav_scope(ScopeId S, const Trav *tv, size_t depth) { return trav_scope_records(S, tv, depth + 1); }

/* ------------------------------------------------------------------ */
/* structural validation (§50.1–2)                                       */

/* A separate finite walk, distinct from the substitution traversal (which
 * visits only a raw view's boundary images by the representation contract):
 * it visits the boundary images, the stored fields of raw origins (binders
 * are ordinary identities, so the depth is unchanged), the environments of
 * template views, and every scope reachable from them with the actual
 * enclosing telescope stack. Memoized per (record, telescope stack): a
 * validity established inside a telescope is never reused at another one.
 * GLOBAL bodies are not unfolded: their definitions are the admission
 * checker's. */
typedef struct { VEC(ScopeId) stack; const char *why; } ValCtx;
static uint64_t stack_key(const ValCtx *v) { return v->stack.len ? interner_intern(&M.keys, v->stack.data, v->stack.len, NULL) : 0; }
static bool validated_before(uint64_t kind, uint64_t id, uint64_t stk) {
    uint64_t k[3] = { kind, id, stk }, val;
    bool have = wordmap_get(&M.trav_memo, k, 3, &val);   /* the map is internally synchronized (§94: no outer lock around its hashing) */
    return have;
}
static void remember_validated(uint64_t kind, uint64_t id, uint64_t stk) {
    uint64_t k[3] = { kind, id, stk };
    wordmap_put(&M.trav_memo, k, 3, 1);
}
static bool val_atom(ValCtx *v, uint64_t id, Sort want) {
    size_t d = bound_depth(id), s = bound_slot(id);
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
/* nesting continues on a fresh stack segment when this one is low (kstack.h) */
static void val_ref_body(RefId t, ValCtx *v);
typedef struct { RefId t; ValCtx *v; } val_ref_args;
static void val_ref_thunk(void *p) { val_ref_args *a = p; val_ref_body(a->t, a->v); }
static void val_ref(RefId t, ValCtx *v) {
    if (!kstack_low()) { val_ref_body(t, v); return; }
    val_ref_args a = { t, v }; kstack_run(val_ref_thunk, &a);
}
static void val_ref_body(RefId t, ValCtx *v) {
    if (v->why) return;
    if (ref_is_var(t)) { uint64_t x = ref_var_id(t); if (is_bound_id(x)) val_atom(v, x, S_TERM); return; }
    uint64_t stk = stack_key(v);
    if (validated_before(0x4EF1, t, stk)) return;
    fine_bump(FC_VALIDATE_STEPS);   /* §94: one transition per node, field and local visited */
    if (ref_is_tview(t)) {
        TEnvId E = tenv_of(t); size_t n = tenv_size(E);
        for (size_t k = 0; k < n && !v->why; k++) {
            uint64_t slot; TVal val; tenv_entry(E, k, &slot, &val); fine_bump(FC_VALIDATE_STEPS);
            switch (val.sort) {
            case PS_REF: val_ref(val.id, v); break;
            case PS_INTERVAL: val_iv(val.id, v); break;
            case PS_FACE: val_fc(val.id, v); break;
            case PS_SCOPE: val_scope(val.id, v); break;
            case PS_LEVEL: break;
            }
        }
    } else {
        OriginId c = ref_origin(t); MapId tau = ref_map(t);
        /* boundary images */
        size_t n; const uint64_t *xs = varset_get(origin_ft(c), &n);
        for (size_t k = 0; k < n && !v->why; k++) { fine_bump(FC_VALIDATE_STEPS); val_ref(map_term_image(tau, xs[k]), v); }
        const uint64_t *ds = dimset_get(origin_fd(c), &n);
        for (size_t k = 0; k < n && !v->why; k++) { fine_bump(FC_VALIDATE_STEPS); val_iv(map_dim_image(tau, ds[k]), v); }
        /* stored fields, including inactive branches and metadata */
        size_t nf = origin_nfields(c);
        for (size_t k = 0; k < nf && !v->why; k++) {
            Field f = origin_field(c, (FieldIndex)k); fine_bump(FC_VALIDATE_STEPS);
            if (f.kind == F_REF) val_ref(f.id, v); else if (f.kind == F_INTERVAL) val_iv(f.id, v); else val_fc(f.id, v);
        }
        if (!v->why && origin_declared_required(c)) val_fc(origin_declared_required(c), v);   /* 0 = no annotation */
    }
    if (!v->why) remember_validated(0x4EF1, t, stk);
    fine_bump(FC_VALIDATE_STEPS);   /* the node's exit is a transition too (the unwinding of a deep term) */
}
/* a prefix view of a telescope: the first k locals */
static ScopeId prefix_scope(ScopeId S, size_t k) {
    LocalDecl *ls = malloc((k ? k : 1) * sizeof(LocalDecl));
    for (size_t q = 0; q < k; q++) ls[q] = scope_local(S, q);
    Val b = { VS_FACE, fc_true() };
    ScopeId P = scope_intern(k, ls, b, 0, LEVEL_NONE, fc_true());
    free(ls); return P;
}
/* nesting continues on a fresh stack segment when this one is low (kstack.h) */
static void val_scope_body(ScopeId S, ValCtx *v);
typedef struct { ScopeId S; ValCtx *v; } val_scope_args;
static void val_scope_thunk(void *p) { val_scope_args *a = p; val_scope_body(a->S, a->v); }
static void val_scope(ScopeId S, ValCtx *v) {
    if (!kstack_low()) { val_scope_body(S, v); return; }
    val_scope_args a = { S, v }; kstack_run(val_scope_thunk, &a);
}
static void val_scope_body(ScopeId S, ValCtx *v) {
    if (v->why) return;
    uint64_t stk = stack_key(v);
    if (validated_before(0x5CA1, S, stk)) return;
    fine_bump(FC_VALIDATE_STEPS);
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
        LocalDecl d = scope_local(S, k); fine_bump(FC_VALIDATE_STEPS);
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
    fine_bump(FC_VALIDATE_STEPS);
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

typedef struct { size_t n; const Val *args; } ApplyCtx;
static RefId apply_term(uint64_t x, size_t depth, void *c) {
    ApplyCtx *a = c;
    if (!is_bound_id(x)) return 0;
    size_t d = bound_depth(x), s = bound_slot(x);
    if (d < depth) return 0;
    if (d == depth) { require(s < a->n && a->args[s].sort == VS_REF && a->args[s].id, "scope application: missing or ill-sorted term argument"); return a->args[s].id; }
    return ref_var(bound_id(d - 1, s));
}
static IntervalId apply_dim(uint64_t i, size_t depth, void *c) {
    ApplyCtx *a = c;
    if (!is_bound_id(i)) return 0;
    size_t d = bound_depth(i), s = bound_slot(i);
    if (d < depth) return 0;
    if (d == depth) { require(s < a->n && a->args[s].sort == VS_INTERVAL && a->args[s].id, "scope application: missing or ill-sorted interval argument"); return a->args[s].id; }
    return iv_var(bound_id(d - 1, s));
}
static uint64_t args_key(size_t n, const Val *args) {
    Words w; words_init(&w);
    for (size_t k = 0; k < n; k++) { words_push(&w, args[k].sort); words_push(&w, args[k].id); }
    uint64_t key = interner_intern(&M.keys, w.w, w.n, NULL);
    words_free(&w);
    return key;
}

TypedPartial apply_scope(ScopeId S, size_t n, const Val *args) {
    require(n == scope_arity(S), "scope application arity");
    ApplyCtx a = { n, args };
    Trav tv = { apply_term, apply_dim, 0x200000000ULL + args_key(n, args), &a };
    TypedPartial p;
    p.body = trav_val(scope_body(S), &tv, 0);
    p.type = scope_type(S) ? trav_ref(scope_type(S), &tv, 0) : 0;
    p.level = scope_level(S);
    p.guard = trav_fc(scope_guard(S), &tv, 0);
    return p;
}

/* the k-th local's declaration instantiated at the argument prefix args[0..k) */
void scope_local_at(ScopeId S, size_t k, const Val *args, RefId *type, FaceId *req, uint64_t *level) {
    LocalDecl d = scope_local(S, k);
    ApplyCtx a = { k, args };
    Trav tv = { apply_term, apply_dim, 0x200000000ULL + args_key(k, args), &a };
    *type = d.type ? trav_ref(d.type, &tv, 0) : 0;
    *req = trav_fc(d.required, &tv, 0);
    *level = d.level;
}

typedef struct { MapId sigma; } ReCtx;
static RefId re_term(uint64_t x, size_t depth, void *c) { (void)depth; if (is_bound_id(x)) return 0; RefId im = map_term_image(((ReCtx *)c)->sigma, x); return im == ref_var(x) ? 0 : im; }
static IntervalId re_dim(uint64_t i, size_t depth, void *c) { (void)depth; if (is_bound_id(i)) return 0; IntervalId im = map_dim_image(((ReCtx *)c)->sigma, i); return im == iv_var(i) ? 0 : im; }
ScopeId reindex_scope(ScopeId S, MapId sigma) {
    if (map_is_identity(sigma)) return S;
    ReCtx c = { sigma };
    Trav tv = { re_term, re_dim, 0x300000000ULL + sigma, &c };
    return trav_scope_records(S, &tv, 0);
}

/* remove the single binder level after ∀ */
static RefId lower_term(uint64_t x, size_t depth, void *c) { (void)c; if (!is_bound_id(x)) return 0; size_t d = bound_depth(x); require(d != depth, "forall: a local remained"); return d > depth ? ref_var(bound_id(d - 1, bound_slot(x))) : 0; }
static IntervalId lower_dim(uint64_t i, size_t depth, void *c) { (void)c; if (!is_bound_id(i)) return 0; size_t d = bound_depth(i); require(d != depth, "forall: a local remained"); return d > depth ? iv_var(bound_id(d - 1, bound_slot(i))) : 0; }
FaceId forall_scope(ScopeId S) {
    require(scope_arity(S) == 1 && scope_local(S, 0).sort == S_DIM && scope_body(S).sort == VS_FACE, "forall of a non-unary face scope");
    FaceId f = fc_forall(bound_id(0, 0), scope_body(S).id);
    Trav tv = { lower_term, lower_dim, 0x400000000ULL, NULL };
    return trav_fc(f, &tv, 0);
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
            ApplyCtx a = { k, args };
            Trav tv = { apply_term, apply_dim, 0, &a };
            RefId ty = trav_ref(d.type, &tv, 0);
            FaceId rq = trav_fc(d.required, &tv, 0);
            TermVarId x = fresh_term_keyed_req(kw, 4, ty, rq);
            args[k].sort = VS_REF; args[k].id = ref_var(x);
            if (ids) ids[k] = x;
        }
    }
    TypedPartial p = apply_scope(S, n, args);
    free(args);
    return p;
}
