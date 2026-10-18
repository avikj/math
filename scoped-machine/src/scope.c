#include "scope.h"
#include "fine.h"
#include "template.h"   /* the validator walks template environments */

/* template layer: traversal of a TVIEW's environment (template.c) */
RefId tview_traverse(RefId t, const Trav *tv, size_t depth);

#define SSIDE(id) ((ScopeSide *)chunked_at(&M.scope_side, (id) - 1))

/* the procedures of this file are frame families (kframe.h): traversal,
 * capture, application and validation nest through heap frames, never the
 * native stack */
#define set_free_PARAMS(X) X(uint64_t, s) X(int, dims)
KF_DECL_DROP(set_free, uint64_t, set_free_PARAMS, set_free_drop, uint64_t *w; uint64_t out;)
static void set_free_drop(set_free_F *F) { free(F->w); F->w = NULL; }
KF_STEP(set_free) {
    KF_BEGIN(set_free);
    {
        size_t n; const uint64_t *d = F->dims ? dimset_get(F->s, &n) : varset_get(F->s, &n);
        size_t m = 0;
        F->w = malloc((n ? n : 1) * sizeof(uint64_t));
        for (size_t k = 0; k < n; k++) if (!is_bound_id(d[k])) F->w[m++] = d[k];
        if (F->dims) KF_CALL(dimset_make, &F->out, F->w, m);
        else KF_CALL(varset_make, &F->out, F->w, m);
    }
    free(F->w); F->w = NULL;
    KF_RET(F->out);
    KF_END;
}
KF_DECL_EXT(dimset_free, DimSetId, dimset_free_PARAMS, DimSetId r;)
KF_STEP(dimset_free) { KF_BEGIN(dimset_free); KF_CALL(set_free, &F->r, F->s, 1); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(dimset_free, DimSetId, dimset_free_PARAMS, dimset_free(DimSetId s))
KF_DECL_EXT(varset_free, VarSetId, varset_free_PARAMS, VarSetId r;)
KF_STEP(varset_free) { KF_BEGIN(varset_free); KF_CALL(set_free, &F->r, F->s, 0); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(varset_free, VarSetId, varset_free_PARAMS, varset_free(VarSetId s))

/* ------------------------------------------------------------------ */
/* traversal                                                             */

typedef struct { const Trav *tv; size_t depth; } DimCb;
#define dim_cb_PARAMS(X) X(DimVarId, i) X(void *, ctx)
KF_DECL(dim_cb, IntervalId, dim_cb_PARAMS, IntervalId r;)
KF_STEP(dim_cb) {
    KF_BEGIN(dim_cb);
    F->r = 0;
    { DimCb *c = F->ctx; if (c->tv->dim) KF_CALLP(c->tv->dim, &F->r, F->i, c->depth, c->tv->ctx); }
    if (!F->r) KF_CALL(iv_var, &F->r, F->i);
    KF_RET(F->r);
    KF_END;
}
KF_DECL_EXT(trav_iv, IntervalId, trav_iv_PARAMS, DimCb c; IntervalId out;)
KF_STEP(trav_iv) {
    KF_BEGIN(trav_iv);
    F->c.tv = F->tv; F->c.depth = F->depth;
    KF_CALL(iv_substitute, &F->out, F->r, dim_cb_push, &F->c);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(trav_iv, IntervalId, trav_iv_PARAMS, trav_iv(IntervalId r, const Trav *tv, size_t depth))
KF_DECL_EXT(trav_fc, FaceId, trav_fc_PARAMS, DimCb c; FaceId out;)
KF_STEP(trav_fc) {
    KF_BEGIN(trav_fc);
    F->c.tv = F->tv; F->c.depth = F->depth;
    KF_CALL(fc_substitute, &F->out, F->f, dim_cb_push, &F->c);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(trav_fc, FaceId, trav_fc_PARAMS, trav_fc(FaceId f, const Trav *tv, size_t depth))

KF_DECL_EXT_DROP(trav_ref, RefId, trav_ref_PARAMS, trav_ref_drop, uint64_t key[4]; uint64_t out; bool have; OriginId c; MapId tau; MapBuilder b; size_t k, n; RefId r, im; IntervalId iv, dim; MapId m;)
static void trav_ref_drop(trav_ref_F *F) { words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(trav_ref) {
    KF_BEGIN(trav_ref);
    if (ref_is_var(F->t)) {
        F->r = 0;
        if (F->tv->term) KF_CALLP(F->tv->term, &F->r, ref_var_id(F->t), F->depth, F->tv->ctx);
        KF_RET(F->r ? F->r : F->t);
    }
    F->key[0] = 1; F->key[1] = F->t; F->key[2] = F->tv->key; F->key[3] = F->depth;
    if (F->tv->key) { KF_CALL(wordmap_get, &F->have, &M.trav_memo, F->key, 4, &F->out); if (F->have) KF_RET(F->out); }
    if (ref_is_tview(F->t)) KF_CALL(tview_traverse, &F->out, F->t, F->tv, F->depth);
    else {
        F->c = ref_origin(F->t);
        F->tau = ref_map(F->t);
        mapb_init(&F->b);
        KF_MAPB_RESERVE(&F->b, varset_n(origin_ft(F->c)), dimset_n(origin_fd(F->c)));
        varset_get(origin_ft(F->c), &F->n);
        for (F->k = 0; F->k < F->n; F->k++) {
            size_t n; const uint64_t *xs = varset_get(origin_ft(F->c), &n);
            KF_CALL(map_term_image, &F->im, F->tau, xs[F->k]);
            KF_CALL(trav_ref, &F->r, F->im, F->tv, F->depth);
            xs = varset_get(origin_ft(F->c), &n);
            mapb_term(&F->b, xs[F->k], F->r);
        }
        dimset_get(origin_fd(F->c), &F->n);
        for (F->k = 0; F->k < F->n; F->k++) {
            size_t n; const uint64_t *ds = dimset_get(origin_fd(F->c), &n);
            KF_CALL(map_dim_image, &F->dim, F->tau, ds[F->k]);
            KF_CALL(trav_iv, &F->iv, F->dim, F->tv, F->depth);
            ds = dimset_get(origin_fd(F->c), &n);
            mapb_dim(&F->b, ds[F->k], F->iv);
        }
        KF_CALL(mapb_finish, &F->m, &F->b);   /* releases the builder */
        KF_CALL(make_view, &F->out, F->c, F->m);
    }
    if (F->tv->key) KF_CALL(wordmap_put, NULL, &M.trav_memo, F->key, 4, F->out);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(trav_ref, RefId, trav_ref_PARAMS, trav_ref(RefId t, const Trav *tv, size_t depth))

KF_DECL_EXT(trav_val, Val, trav_val_PARAMS, Val o;)
KF_STEP(trav_val) {
    KF_BEGIN(trav_val);
    F->o = F->v;
    switch (F->v.sort) {
    case VS_REF: KF_CALL(trav_ref, &F->o.id, F->v.id, F->tv, F->depth); break;
    case VS_INTERVAL: KF_CALL(trav_iv, &F->o.id, F->v.id, F->tv, F->depth); break;
    case VS_FACE: KF_CALL(trav_fc, &F->o.id, F->v.id, F->tv, F->depth); break;
    }
    KF_RET(F->o);
    KF_END;
}
KF_SYNC_DEF(trav_val, Val, trav_val_PARAMS, trav_val(Val v, const Trav *tv, size_t depth))

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

#define acc_val_PARAMS(X) X(Val, v) X(DimSetId *, sup) X(VarSetId *, fv)
KF_DECL_DROP(acc_val, void, acc_val_PARAMS, acc_val_drop, Words w; DimSetId d;)
static void acc_val_drop(acc_val_F *F) { words_free(&F->w); }
KF_STEP(acc_val) {
    KF_BEGIN(acc_val);
    switch (F->v.sort) {
    case VS_REF: KF_CALL(dimset_union, F->sup, *F->sup, ref_support(F->v.id)); KF_CALL(varset_union, F->fv, *F->fv, ref_freevars(F->v.id)); break;
    case VS_INTERVAL: case VS_FACE:
        words_init(&F->w);
        if (F->v.sort == VS_INTERVAL) iv_dims(F->v.id, &F->w); else fc_dims(F->v.id, &F->w);
        KF_CALL(dimset_make, &F->d, F->w.w, F->w.n);
        KF_CALL(dimset_union, F->sup, *F->sup, F->d);
        words_free(&F->w);
        break;
    }
    KF_RETV();
    KF_END;
}

KF_DECL_EXT_DROP(scope_intern, ScopeId, scope_intern_PARAMS, scope_intern_drop, Words w; ScopeId have, id; DimSetId sup, sup_id; VarSetId fv, fv_id; size_t k; Val tmp; bool created;)
static void scope_intern_drop(scope_intern_F *F) { words_free(&F->w); }
KF_STEP(scope_intern) {
    KF_BEGIN(scope_intern);
    words_init(&F->w); KF_CALL(words_reserve, NULL, &F->w, 6 + 4 * F->n);   /* the record's exact length: no growth */
    words_push(&F->w, F->n);
    for (size_t k = 0; k < F->n; k++) { words_push(&F->w, F->locals[k].sort); words_push(&F->w, F->locals[k].type); words_push(&F->w, F->locals[k].level); words_push(&F->w, F->locals[k].required); }
    words_push(&F->w, F->body.sort); words_push(&F->w, F->result_type); words_push(&F->w, F->result_level); words_push(&F->w, F->guard); words_push(&F->w, F->body.id);
    pthread_mutex_lock(&M.term_mu); F->have = interner_find(&M.scopes, F->w.w, F->w.n); pthread_mutex_unlock(&M.term_mu);
    if (F->have) { words_free(&F->w); KF_RET(F->have); }
    /* free boundary: every record, bound atoms excluded — computed outside
     * the lock on immutable data (§94: its loops are suspension points); the
     * lock is held to intern and publish only */
    KF_CALL(dimset_make, &F->sup, NULL, 0); KF_CALL(varset_make, &F->fv, NULL, 0);
    for (F->k = 0; F->k < F->n; F->k++) {
        if (F->locals[F->k].type) { F->tmp.sort = VS_REF; F->tmp.id = F->locals[F->k].type; KF_CALL(acc_val, NULL, F->tmp, &F->sup, &F->fv); }
        F->tmp.sort = VS_FACE; F->tmp.id = F->locals[F->k].required; KF_CALL(acc_val, NULL, F->tmp, &F->sup, &F->fv);
    }
    if (F->result_type) { F->tmp.sort = VS_REF; F->tmp.id = F->result_type; KF_CALL(acc_val, NULL, F->tmp, &F->sup, &F->fv); }
    F->tmp.sort = VS_FACE; F->tmp.id = F->guard; KF_CALL(acc_val, NULL, F->tmp, &F->sup, &F->fv);
    KF_CALL(acc_val, NULL, F->body, &F->sup, &F->fv);
    KF_CALL(dimset_free, &F->sup_id, F->sup); KF_CALL(varset_free, &F->fv_id, F->fv);
    pthread_mutex_lock(&M.term_mu);
    F->id = interner_intern(&M.scopes, F->w.w, F->w.n, &F->created);
    if (F->created) { ScopeSide *s = SSIDE(F->id); s->support = F->sup_id; s->freevars = F->fv_id; }
    pthread_mutex_unlock(&M.term_mu);
    words_free(&F->w);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(scope_intern, ScopeId, scope_intern_PARAMS, scope_intern(size_t n, const LocalDecl *locals, Val body, RefId result_type, uint64_t result_level, FaceId guard))

/* a word key of the (sort, id) pairs of a capture telescope or an argument list */
#define pairs_key_PARAMS(X) X(size_t, n) X(const CaptureDecl *, d) X(const Val *, args)
KF_DECL_DROP(pairs_key, uint64_t, pairs_key_PARAMS, pairs_key_drop, Words w; uint64_t key;)
static void pairs_key_drop(pairs_key_F *F) { words_free(&F->w); }
KF_STEP(pairs_key) {
    KF_BEGIN(pairs_key);
    words_init(&F->w); KF_CALL(words_reserve, NULL, &F->w, 2 * F->n);
    for (size_t k = 0; k < F->n; k++) {
        if (F->d) { words_push(&F->w, F->d[k].sort); words_push(&F->w, F->d[k].id); }
        else { words_push(&F->w, F->args[k].sort); words_push(&F->w, F->args[k].id); }
    }
    KF_CALL(interner_intern, &F->key, &M.keys, F->w.w, F->w.n, NULL);
    words_free(&F->w);
    KF_RET(F->key);
    KF_END;
}

/* ------------------------------------------------------------------ */
/* capture: close the concrete locals of Δ into (depth, slot) atoms         */

typedef struct { size_t n; const CaptureDecl *d; } CloseCtx;
#define trav_cb_PARAMS(X) X(uint64_t, x) X(size_t, depth) X(void *, c)
KF_DECL(close_term, RefId, trav_cb_PARAMS, size_t k; uint64_t b; RefId r;)
KF_STEP(close_term) {
    KF_BEGIN(close_term);
    if (is_bound_id(F->x)) KF_RET(0);
    for (F->k = 0; F->k < ((CloseCtx *)F->c)->n; F->k++) {
        const CaptureDecl *d = &((CloseCtx *)F->c)->d[F->k];
        if (d->sort == S_TERM && d->id == F->x) { KF_CALL(bound_id, &F->b, F->depth, F->k); KF_CALL(ref_var, &F->r, F->b); KF_RET(F->r); }
    }
    KF_RET(0);
    KF_END;
}
KF_DECL(close_dim, IntervalId, trav_cb_PARAMS, size_t k; IntervalId r; uint64_t b;)
KF_STEP(close_dim) {
    KF_BEGIN(close_dim);
    if (is_bound_id(F->x)) KF_RET(0);
    for (F->k = 0; F->k < ((CloseCtx *)F->c)->n; F->k++) {
        const CaptureDecl *d = &((CloseCtx *)F->c)->d[F->k];
        if (d->sort == S_DIM && d->id == F->x) { KF_CALL(bound_id, &F->b, F->depth, F->k); KF_CALL(iv_var, &F->r, F->b); KF_RET(F->r); }
    }
    KF_RET(0);
    KF_END;
}

KF_DECL_EXT_DROP(capture_scope, ScopeId, capture_scope_PARAMS, capture_scope_drop, CloseCtx cc; Trav tv; LocalDecl *ls; size_t k; uint64_t key; Val b; RefId ty; FaceId g; ScopeId S;)
static void capture_scope_drop(capture_scope_F *F) { free(F->ls); F->ls = NULL; }
KF_STEP(capture_scope) {
    KF_BEGIN(capture_scope);
    F->cc.n = F->n; F->cc.d = F->delta;
    KF_CALL(pairs_key, &F->key, F->n, F->delta, NULL);
    memset(&F->tv, 0, sizeof F->tv);
    F->tv.term = close_term_push; F->tv.dim = close_dim_push; F->tv.key = 0x100000000ULL + F->key; F->tv.ctx = &F->cc;
    F->ls = malloc((F->n ? F->n : 1) * sizeof(LocalDecl));
    for (F->k = 0; F->k < F->n; F->k++) {
        F->ls[F->k].sort = F->delta[F->k].sort; F->ls[F->k].level = F->delta[F->k].level;
        F->ls[F->k].type = 0;
        if (F->delta[F->k].type) KF_CALL(trav_ref, &F->ls[F->k].type, F->delta[F->k].type, &F->tv, 0);
        KF_CALL(trav_fc, &F->ls[F->k].required, F->delta[F->k].required, &F->tv, 0);
    }
    KF_CALL(trav_val, &F->b, F->body, &F->tv, 0);
    F->ty = 0;
    if (F->result_type) KF_CALL(trav_ref, &F->ty, F->result_type, &F->tv, 0);
    KF_CALL(trav_fc, &F->g, F->guard, &F->tv, 0);
    KF_CALL(scope_intern, &F->S, F->n, F->ls, F->b, F->ty, F->result_level, F->g);
    free(F->ls); F->ls = NULL;
    KF_RET(F->S);
    KF_END;
}
KF_SYNC_DEF(capture_scope, ScopeId, capture_scope_PARAMS, capture_scope(size_t n, const CaptureDecl *delta, Val body, RefId result_type, uint64_t result_level, FaceId guard))

/* traverse a scope whose own records sit at `rd` */
#define trav_scope_records_PARAMS(X) X(ScopeId, S) X(const Trav *, tv) X(size_t, rd)
KF_DECL_DROP(trav_scope_records, ScopeId, trav_scope_records_PARAMS, trav_scope_records_drop, uint64_t key[4]; uint64_t out; bool have; size_t n, k; LocalDecl *ls; Val b; RefId ty; FaceId g;)
static void trav_scope_records_drop(trav_scope_records_F *F) { free(F->ls); F->ls = NULL; }
KF_STEP(trav_scope_records) {
    KF_BEGIN(trav_scope_records);
    F->key[0] = 2; F->key[1] = F->S; F->key[2] = F->tv->key; F->key[3] = F->rd;
    if (F->tv->key) { KF_CALL(wordmap_get, &F->have, &M.trav_memo, F->key, 4, &F->out); if (F->have) KF_RET(F->out); }
    if (F->tv->enter) F->tv->enter(F->S, F->rd, F->tv->ctx);
    F->n = scope_arity(F->S);
    F->ls = malloc((F->n ? F->n : 1) * sizeof(LocalDecl));
    for (F->k = 0; F->k < F->n; F->k++) {
        F->ls[F->k] = scope_local(F->S, F->k);
        if (F->ls[F->k].type) KF_CALL(trav_ref, &F->ls[F->k].type, F->ls[F->k].type, F->tv, F->rd);
        KF_CALL(trav_fc, &F->ls[F->k].required, F->ls[F->k].required, F->tv, F->rd);
    }
    KF_CALL(trav_val, &F->b, scope_body(F->S), F->tv, F->rd);
    F->ty = 0;
    if (scope_type(F->S)) KF_CALL(trav_ref, &F->ty, scope_type(F->S), F->tv, F->rd);
    KF_CALL(trav_fc, &F->g, scope_guard(F->S), F->tv, F->rd);
    KF_CALL(scope_intern, &F->out, F->n, F->ls, F->b, F->ty, scope_level(F->S), F->g);
    free(F->ls); F->ls = NULL;
    if (F->tv->leave) F->tv->leave(F->S, F->rd, F->tv->ctx);
    if (F->tv->key) KF_CALL(wordmap_put, NULL, &M.trav_memo, F->key, 4, F->out);
    KF_RET(F->out);
    KF_END;
}
KF_DECL_EXT(trav_scope, ScopeId, trav_scope_PARAMS, ScopeId r;)
KF_STEP(trav_scope) { KF_BEGIN(trav_scope); KF_CALL(trav_scope_records, &F->r, F->S, F->tv, F->depth + 1); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(trav_scope, ScopeId, trav_scope_PARAMS, trav_scope(ScopeId S, const Trav *tv, size_t depth))

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
#define stack_key_PARAMS(X) X(const ValCtx *, v)
KF_DECL(stack_key, uint64_t, stack_key_PARAMS, uint64_t r;)
KF_STEP(stack_key) {
    KF_BEGIN(stack_key);
    if (!F->v->stack.len) KF_RET(0);
    KF_CALL(interner_intern, &F->r, &M.keys, F->v->stack.data, F->v->stack.len, NULL);
    KF_RET(F->r);
    KF_END;
}
static bool val_atom(ValCtx *v, uint64_t id, Sort want) {
    size_t d = bound_depth(id), s = bound_slot(id);
    if (d >= v->stack.len) { v->why = "bound occurrence names no enclosing telescope"; return false; }
    ScopeId T = v->stack.data[v->stack.len - 1 - d];
    if (s >= scope_arity(T)) { v->why = "bound occurrence names a slot outside its telescope"; return false; }
    if (scope_local(T, s).sort != want) { v->why = "bound occurrence has the wrong sort for its slot"; return false; }
    return true;
}
static void val_dims(const Words *w, ValCtx *v) { for (size_t k = 0; k < w->n && !v->why; k++) if (is_bound_id(w->w[k])) val_atom(v, w->w[k], S_DIM); }
static void val_iv(IntervalId r, ValCtx *v) { Words w; words_init(&w); iv_dims(r, &w); val_dims(&w, v); words_free(&w); }
static void val_fc(FaceId f, ValCtx *v) { Words w; words_init(&w); fc_dims(f, &w); val_dims(&w, v); words_free(&w); }

#define val_scope_PARAMS(X) X(ScopeId, S) X(ValCtx *, v)
KF_PROTO(val_scope, void, val_scope_PARAMS);
#define val_ref_PARAMS(X) X(RefId, t) X(ValCtx *, v)
KF_DECL(val_ref, void, val_ref_PARAMS, uint64_t stk, k[3], val; bool have; size_t i, n; OriginId c; MapId tau; RefId im; IntervalId dim;)
KF_STEP(val_ref) {
    KF_BEGIN(val_ref);
    if (F->v->why) KF_RETV();
    if (ref_is_var(F->t)) { uint64_t x = ref_var_id(F->t); if (is_bound_id(x)) val_atom(F->v, x, S_TERM); KF_RETV(); }
    KF_CALL(stack_key, &F->stk, F->v);
    F->k[0] = 0x4EF1; F->k[1] = F->t; F->k[2] = F->stk;
    KF_CALL(wordmap_get, &F->have, &M.trav_memo, F->k, 3, &F->val);   /* the map is internally synchronized (§94: no outer lock around its hashing) */
    if (F->have) KF_RETV();
    fine_bump(FC_VALIDATE_STEPS);   /* §94: one transition per node, field and local visited */
    if (ref_is_tview(F->t)) {
        F->n = tenv_size(tenv_of(F->t));
        for (F->i = 0; F->i < F->n && !F->v->why; F->i++) {
            uint64_t slot; TVal val; tenv_entry(tenv_of(F->t), F->i, &slot, &val); fine_bump(FC_VALIDATE_STEPS);
            switch (val.sort) {
            case PS_REF: KF_CALL(val_ref, NULL, val.id, F->v); break;
            case PS_INTERVAL: val_iv(val.id, F->v); KF_SAFE(); break;
            case PS_FACE: val_fc(val.id, F->v); KF_SAFE(); break;
            case PS_SCOPE: KF_CALL(val_scope, NULL, val.id, F->v); break;
            case PS_LEVEL: KF_SAFE(); break;
            }
        }
    } else {
        F->c = ref_origin(F->t); F->tau = ref_map(F->t);
        /* boundary images */
        varset_get(origin_ft(F->c), &F->n);
        for (F->i = 0; F->i < F->n && !F->v->why; F->i++) {
            size_t n; const uint64_t *xs = varset_get(origin_ft(F->c), &n);
            fine_bump(FC_VALIDATE_STEPS);
            KF_CALL(map_term_image, &F->im, F->tau, xs[F->i]);
            KF_CALL(val_ref, NULL, F->im, F->v);
        }
        dimset_get(origin_fd(F->c), &F->n);
        for (F->i = 0; F->i < F->n && !F->v->why; F->i++) {
            { size_t n; const uint64_t *ds = dimset_get(origin_fd(F->c), &n);
              fine_bump(FC_VALIDATE_STEPS); KF_CALL(map_dim_image, &F->dim, F->tau, ds[F->i]); }
            val_iv(F->dim, F->v); KF_SAFE();
        }
        /* stored fields, including inactive branches and metadata */
        F->n = origin_nfields(F->c);
        for (F->i = 0; F->i < F->n && !F->v->why; F->i++) {
            Field f = origin_field(F->c, (FieldIndex)F->i); fine_bump(FC_VALIDATE_STEPS);
            if (f.kind == F_REF) KF_CALL(val_ref, NULL, f.id, F->v);
            else { if (f.kind == F_INTERVAL) val_iv(f.id, F->v); else val_fc(f.id, F->v); KF_SAFE(); }
        }
        if (!F->v->why && origin_declared_required(F->c)) val_fc(origin_declared_required(F->c), F->v);   /* 0 = no annotation */
    }
    if (!F->v->why) { F->k[0] = 0x4EF1; F->k[1] = F->t; F->k[2] = F->stk; KF_CALL(wordmap_put, NULL, &M.trav_memo, F->k, 3, 1); }
    fine_bump(FC_VALIDATE_STEPS);   /* the node's exit is a transition too (the unwinding of a deep term) */
    KF_RETV();
    KF_END;
}
/* a prefix view of a telescope: the first k locals */
#define prefix_scope_PARAMS(X) X(ScopeId, S) X(size_t, k)
KF_DECL_DROP(prefix_scope, ScopeId, prefix_scope_PARAMS, prefix_scope_drop, LocalDecl *ls; Val b; FaceId t; ScopeId P;)
static void prefix_scope_drop(prefix_scope_F *F) { free(F->ls); F->ls = NULL; }
KF_STEP(prefix_scope) {
    KF_BEGIN(prefix_scope);
    F->ls = malloc((F->k ? F->k : 1) * sizeof(LocalDecl));
    for (size_t q = 0; q < F->k; q++) F->ls[q] = scope_local(F->S, q);
    KF_CALL0(fc_true, &F->t);
    F->b.sort = VS_FACE; F->b.id = F->t;
    KF_CALL(scope_intern, &F->P, F->k, F->ls, F->b, 0, LEVEL_NONE, F->t);
    free(F->ls); F->ls = NULL;
    KF_RET(F->P);
    KF_END;
}
KF_DECL_EXT(val_scope, void, val_scope_PARAMS, uint64_t stk, k[3], val; bool have; size_t n, i; Val body; LocalDecl d; ScopeId P;)
KF_STEP(val_scope) {
    KF_BEGIN(val_scope);
    if (F->v->why) KF_RETV();
    KF_CALL(stack_key, &F->stk, F->v);
    F->k[0] = 0x5CA1; F->k[1] = F->S; F->k[2] = F->stk;
    KF_CALL(wordmap_get, &F->have, &M.trav_memo, F->k, 3, &F->val);
    if (F->have) KF_RETV();
    fine_bump(FC_VALIDATE_STEPS);
    F->n = scope_arity(F->S);
    F->body = scope_body(F->S);
    for (size_t k = 0; k < F->n && !F->v->why; k++) {
        LocalDecl d = scope_local(F->S, k);
        if (d.sort == S_TERM && !d.type) F->v->why = "term local without a declared type";
        else if (d.sort == S_DIM && d.type) F->v->why = "dimension local with a type";
    }
    if (!F->v->why && F->body.sort == VS_REF && !scope_type(F->S)) F->v->why = "reference scope without a declared result type";
    /* each local's declaration over its prefix telescope and the enclosing stack */
    for (F->i = 0; F->i < F->n && !F->v->why; F->i++) {
        F->d = scope_local(F->S, F->i); fine_bump(FC_VALIDATE_STEPS);
        KF_CALL(prefix_scope, &F->P, F->S, F->i);
        vec_push(&F->v->stack, F->P);
        if (F->d.type) KF_CALL(val_ref, NULL, F->d.type, F->v);
        if (!F->v->why) val_fc(F->d.required, F->v);
        F->v->stack.len--;
        if (F->v->why) F->v->why = "local declaration uses a later or absent slot";
    }
    if (F->v->why) KF_RETV();
    /* body, result type and guard over the whole telescope */
    vec_push(&F->v->stack, F->S);
    switch (F->body.sort) { case VS_REF: KF_CALL(val_ref, NULL, F->body.id, F->v); break; case VS_INTERVAL: val_iv(F->body.id, F->v); break; case VS_FACE: val_fc(F->body.id, F->v); break; }
    if (!F->v->why && scope_type(F->S)) KF_CALL(val_ref, NULL, scope_type(F->S), F->v);
    if (!F->v->why) val_fc(scope_guard(F->S), F->v);
    F->v->stack.len--;
    if (!F->v->why) { F->k[0] = 0x5CA1; F->k[1] = F->S; F->k[2] = F->stk; KF_CALL(wordmap_put, NULL, &M.trav_memo, F->k, 3, 1); }
    fine_bump(FC_VALIDATE_STEPS);
    KF_RETV();
    KF_END;
}
KF_DECL_EXT_DROP(scope_validate, bool, scope_validate_PARAMS, scope_validate_drop, ValCtx v;)
static void scope_validate_drop(scope_validate_F *F) { vec_free(&F->v.stack); }
KF_STEP(scope_validate) {
    KF_BEGIN(scope_validate);
    KF_CALL(val_scope, NULL, F->S, &F->v);                      /* no outer telescope at the top level */
    vec_free(&F->v.stack);
    if (F->v.why) { *F->reason = F->v.why; KF_RET(false); }
    KF_RET(true);
    KF_END;
}
KF_SYNC_DEF(scope_validate, bool, scope_validate_PARAMS, scope_validate(ScopeId S, const char **reason))
KF_DECL_EXT_DROP(ref_validate, bool, ref_validate_PARAMS, ref_validate_drop, ValCtx v;)
static void ref_validate_drop(ref_validate_F *F) { vec_free(&F->v.stack); }
KF_STEP(ref_validate) {
    KF_BEGIN(ref_validate);
    KF_CALL(val_ref, NULL, F->t, &F->v);
    vec_free(&F->v.stack);
    if (F->v.why) { *F->reason = F->v.why; KF_RET(false); }
    KF_RET(true);
    KF_END;
}
KF_SYNC_DEF(ref_validate, bool, ref_validate_PARAMS, ref_validate(RefId t, const char **reason))

/* ------------------------------------------------------------------ */
/* application and ambient reindexing                                    */

typedef struct { size_t n; const Val *args; } ApplyCtx;
KF_DECL(apply_term, RefId, trav_cb_PARAMS, uint64_t b; RefId r;)
KF_STEP(apply_term) {
    KF_BEGIN(apply_term);
    {
        ApplyCtx *a = F->c;
        if (!is_bound_id(F->x)) KF_RET(0);
        size_t d = bound_depth(F->x), s = bound_slot(F->x);
        if (d < F->depth) KF_RET(0);
        if (d == F->depth) { require(s < a->n && a->args[s].sort == VS_REF && a->args[s].id, "scope application: missing or ill-sorted term argument"); KF_RET(a->args[s].id); }
        KF_CALL(bound_id, &F->b, d - 1, s);
    }
    KF_CALL(ref_var, &F->r, F->b);
    KF_RET(F->r);
    KF_END;
}
KF_DECL(apply_dim, IntervalId, trav_cb_PARAMS, IntervalId r; uint64_t b;)
KF_STEP(apply_dim) {
    KF_BEGIN(apply_dim);
    {
        ApplyCtx *a = F->c;
        if (!is_bound_id(F->x)) KF_RET(0);
        size_t d = bound_depth(F->x), s = bound_slot(F->x);
        if (d < F->depth) KF_RET(0);
        if (d == F->depth) { require(s < a->n && a->args[s].sort == VS_INTERVAL && a->args[s].id, "scope application: missing or ill-sorted interval argument"); KF_RET(a->args[s].id); }
        KF_CALL(bound_id, &F->b, d - 1, s);
    }
    KF_CALL(iv_var, &F->r, F->b);
    KF_RET(F->r);
    KF_END;
}
KF_DECL_EXT(apply_scope, TypedPartial, apply_scope_PARAMS, ApplyCtx a; Trav tv; uint64_t key; TypedPartial p;)
KF_STEP(apply_scope) {
    KF_BEGIN(apply_scope);
    require(F->n == scope_arity(F->S), "scope application arity");
    F->a.n = F->n; F->a.args = F->args;
    KF_CALL(pairs_key, &F->key, F->n, NULL, F->args);
    F->tv.term = apply_term_push; F->tv.dim = apply_dim_push; F->tv.key = 0x200000000ULL + F->key; F->tv.ctx = &F->a;
    KF_CALL(trav_val, &F->p.body, scope_body(F->S), &F->tv, 0);
    F->p.type = 0;
    if (scope_type(F->S)) KF_CALL(trav_ref, &F->p.type, scope_type(F->S), &F->tv, 0);
    F->p.level = scope_level(F->S);
    KF_CALL(trav_fc, &F->p.guard, scope_guard(F->S), &F->tv, 0);
    KF_RET(F->p);
    KF_END;
}
KF_SYNC_DEF(apply_scope, TypedPartial, apply_scope_PARAMS, apply_scope(ScopeId S, size_t n, const Val *args))

/* the k-th local's declaration instantiated at the argument prefix args[0..k) */
KF_DECL_EXT(scope_local_at, void, scope_local_at_PARAMS, LocalDecl d; ApplyCtx a; Trav tv; uint64_t key;)
KF_STEP(scope_local_at) {
    KF_BEGIN(scope_local_at);
    F->d = scope_local(F->S, F->k);
    F->a.n = F->k; F->a.args = F->args;
    KF_CALL(pairs_key, &F->key, F->k, NULL, F->args);
    F->tv.term = apply_term_push; F->tv.dim = apply_dim_push; F->tv.key = 0x200000000ULL + F->key; F->tv.ctx = &F->a;
    *F->type = 0;
    if (F->d.type) KF_CALL(trav_ref, F->type, F->d.type, &F->tv, 0);
    KF_CALL(trav_fc, F->req, F->d.required, &F->tv, 0);
    *F->level = F->d.level;
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(scope_local_at, scope_local_at_PARAMS, scope_local_at(ScopeId S, size_t k, const Val *args, RefId *type, FaceId *req, uint64_t *level))

typedef struct { MapId sigma; } ReCtx;
KF_DECL(re_term, RefId, trav_cb_PARAMS, RefId im, v;)
KF_STEP(re_term) {
    KF_BEGIN(re_term);
    if (is_bound_id(F->x)) KF_RET(0);
    KF_CALL(map_term_image, &F->im, ((ReCtx *)F->c)->sigma, F->x);
    KF_CALL(ref_var, &F->v, F->x);
    KF_RET(F->im == F->v ? 0 : F->im);
    KF_END;
}
KF_DECL(re_dim, IntervalId, trav_cb_PARAMS, IntervalId im, v;)
KF_STEP(re_dim) {
    KF_BEGIN(re_dim);
    if (is_bound_id(F->x)) KF_RET(0);
    KF_CALL(map_dim_image, &F->im, ((ReCtx *)F->c)->sigma, F->x);
    KF_CALL(iv_var, &F->v, F->x);
    KF_RET(F->im == F->v ? 0 : F->im);
    KF_END;
}
KF_DECL_EXT(reindex_scope, ScopeId, reindex_scope_PARAMS, ReCtx c; Trav tv; ScopeId r;)
KF_STEP(reindex_scope) {
    KF_BEGIN(reindex_scope);
    if (map_is_identity(F->sigma)) KF_RET(F->S);
    F->c.sigma = F->sigma;
    F->tv.term = re_term_push; F->tv.dim = re_dim_push; F->tv.key = 0x300000000ULL + F->sigma; F->tv.ctx = &F->c;
    KF_CALL(trav_scope_records, &F->r, F->S, &F->tv, 0);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(reindex_scope, ScopeId, reindex_scope_PARAMS, reindex_scope(ScopeId S, MapId sigma))

/* remove the single binder level after ∀ */
KF_DECL(lower_term, RefId, trav_cb_PARAMS, uint64_t b; RefId r;)
KF_STEP(lower_term) {
    KF_BEGIN(lower_term);
    if (!is_bound_id(F->x)) KF_RET(0);
    { size_t d = bound_depth(F->x); require(d != F->depth, "forall: a local remained"); if (d <= F->depth) KF_RET(0); KF_CALL(bound_id, &F->b, d - 1, bound_slot(F->x)); }
    KF_CALL(ref_var, &F->r, F->b);
    KF_RET(F->r);
    KF_END;
}
KF_DECL(lower_dim, IntervalId, trav_cb_PARAMS, IntervalId r; uint64_t b;)
KF_STEP(lower_dim) {
    KF_BEGIN(lower_dim);
    if (!is_bound_id(F->x)) KF_RET(0);
    {
        size_t d = bound_depth(F->x); require(d != F->depth, "forall: a local remained");
        if (d <= F->depth) KF_RET(0);
        KF_CALL(bound_id, &F->b, d - 1, bound_slot(F->x));
    }
    KF_CALL(iv_var, &F->r, F->b);
    KF_RET(F->r);
    KF_END;
}
KF_DECL_EXT(forall_scope, FaceId, forall_scope_PARAMS, FaceId f, r; Trav tv; uint64_t b;)
KF_STEP(forall_scope) {
    KF_BEGIN(forall_scope);
    require(scope_arity(F->S) == 1 && scope_local(F->S, 0).sort == S_DIM && scope_body(F->S).sort == VS_FACE, "forall of a non-unary face scope");
    KF_CALL(bound_id, &F->b, 0, 0);
    KF_CALL(fc_forall, &F->f, F->b, scope_body(F->S).id);
    F->tv.term = lower_term_push; F->tv.dim = lower_dim_push; F->tv.key = 0x400000000ULL; F->tv.ctx = NULL;
    KF_CALL(trav_fc, &F->r, F->f, &F->tv, 0);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(forall_scope, FaceId, forall_scope_PARAMS, forall_scope(ScopeId S))

KF_DECL_EXT_DROP(open_scope_fresh, TypedPartial, open_scope_fresh_PARAMS, open_scope_fresh_drop, size_t n, k; Val *args; LocalDecl d; KeyWord kw[4]; ApplyCtx a; Trav tv; RefId ty; FaceId rq; TypedPartial p; uint64_t nv;)
static void open_scope_fresh_drop(open_scope_fresh_F *F) { free(F->args); F->args = NULL; }
KF_STEP(open_scope_fresh) {
    KF_BEGIN(open_scope_fresh);
    F->n = scope_arity(F->S);
    KF_CALL(k_zalloc, (void **)&F->args, F->n ? F->n : 1, sizeof(Val));
    for (F->k = 0; F->k < F->n; F->k++) {
        F->d = scope_local(F->S, F->k);
        F->kw[0].kind = KW_CONST; F->kw[0].v = 9000; F->kw[1].kind = KW_CONST; F->kw[1].v = F->key;
        F->kw[2].kind = KW_CONST; F->kw[2].v = F->S; F->kw[3].kind = KW_CONST; F->kw[3].v = F->k;
        if (F->d.sort == S_DIM) {
            KF_CALL(nominal_var, &F->nv, F->kw, 4, 3, S_DIM, 0, 0, false);
            F->args[F->k].sort = VS_INTERVAL;
            if (F->ids) F->ids[F->k] = F->nv;
            KF_CALL(iv_var, &F->args[F->k].id, F->nv);
        } else {
            /* the declaration type over the earlier fresh locals */
            F->a.n = F->k; F->a.args = F->args;
            F->tv.term = apply_term_push; F->tv.dim = apply_dim_push; F->tv.key = 0; F->tv.ctx = &F->a;
            KF_CALL(trav_ref, &F->ty, F->d.type, &F->tv, 0);
            KF_CALL(trav_fc, &F->rq, F->d.required, &F->tv, 0);
            KF_CALL(nominal_var, &F->nv, F->kw, 4, 2, S_TERM, F->ty, F->rq, true);
            F->args[F->k].sort = VS_REF;
            if (F->ids) F->ids[F->k] = F->nv;
            KF_CALL(ref_var, &F->args[F->k].id, F->nv);
        }
    }
    KF_CALL(apply_scope, &F->p, F->S, F->n, F->args);
    free(F->args); F->args = NULL;
    KF_RET(F->p);
    KF_END;
}
KF_SYNC_DEF(open_scope_fresh, TypedPartial, open_scope_fresh_PARAMS, open_scope_fresh(ScopeId S, uint64_t key, uint64_t *ids))
