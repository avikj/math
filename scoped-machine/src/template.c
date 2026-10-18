#include "template.h"

/* ------------------------------------------------------------------ */
/* definitions                                                           */

#define MAXP 16
#define MAXL 48
#define MAXSLOT (MAXP + MAXL)

typedef struct {
    const char *name;
    size_t nparams;                /* including κ at slot 0 */
    PSort sorts[MAXP];
    ExprId ptype[MAXP];            /* reference parameters: declared type expression (0 = none) */
    ExprId plevel[MAXP];           /* its level expression */
    ExprId psig[MAXP];             /* scope parameters: the expected contextual signature (a scope expression whose body is the result type) */
    ExprId pguard[MAXP];           /* a partial reference parameter's declared availability (0 = κ) */
    size_t nlocals;
    PSort lsort[MAXL];
    ExprId ltype[MAXL], llevel[MAXL], lreq[MAXL];   /* declarations of term locals (constructor binders and scope locals) */
    Words nodes;                   /* every constructor node of the definition, in construction order */
    ExprId root;
    ExprId rtype, rlevel;          /* the declared result type of the program and its level */
    TNodeId root_node;             /* the root constructor node when the root is a node (0 when the root is a call) */
} TDef;

static struct { TDef defs[TD_COUNT]; uint64_t index_counter[TD_COUNT]; bool init; pthread_mutex_t mu; } TPL;
/* the thread's source face κ is a handle of one machine: it is qualified by
 * the machine generation, and a thread entering a later machine lifetime
 * observes that machine's default true face (review R2 of 9eadaf2) */
static __thread FaceId tl_kappa;
static __thread uint64_t tl_kappa_gen;

/* κ belongs to the computation (kframe.h): a suspended stack carries it to the thread that resumes it */
static void *kappa_addr(void) { return &tl_kappa; }
static void *kappa_gen_addr(void) { return &tl_kappa_gen; }
__attribute__((constructor)) static void kappa_register(void) {
    kf_ctx_register(kappa_addr, sizeof tl_kappa, NULL, NULL);
    kf_ctx_register(kappa_gen_addr, sizeof tl_kappa_gen, NULL, NULL);
}
void template_set_kappa(FaceId kappa) { tl_kappa = kappa; tl_kappa_gen = machine_generation(); }
KF_DECL_EXT(template_kappa, FaceId, KF_NOPARAMS, FaceId r;)
KF_STEP(template_kappa) {
    KF_BEGIN(template_kappa);
    if (tl_kappa_gen != machine_generation()) { tl_kappa = 0; tl_kappa_gen = machine_generation(); }
    if (tl_kappa) KF_RET(tl_kappa);
    KF_CALL0(fc_true, &F->r);
    KF_RET(F->r);
    KF_END;
}
FaceId template_kappa(void) { FaceId r; KStack *s_ = kf_sync_begin(); template_kappa_push(s_, &r); kf_sync_run(s_); kf_sync_end(s_); return r; }

/* ------------------------------------------------------------------ */
/* expressions: interned records [kind, words...]                        */

enum {
    X_PARAM = 1, X_LOCAL, X_LEVEL, X_LSUCC, X_LMAX, X_LEVELS, X_LFIRST, X_NODE, X_CALL, X_SCOPE, X_APPLY, X_APPLY_TYPE, X_APPLY_GUARD,
    X_IV0, X_IV1, X_IVNOT, X_IVAND, X_IVOR, X_FCF, X_FCT, X_FCAND, X_FCOR, X_FCEND, X_FORALL
};

static ExprId xi(size_t n, const uint64_t *w) { return interner_intern(&M.exprs, w, n, NULL); }
static const uint64_t *xw(ExprId e, size_t *n) { return interner_get(&M.exprs, e, n); }
static ExprId x1(uint64_t k, uint64_t a) { uint64_t w[2] = { k, a }; return xi(2, w); }
static ExprId x2(uint64_t k, uint64_t a, uint64_t b) { uint64_t w[3] = { k, a, b }; return xi(3, w); }
static ExprId x0(uint64_t k) { uint64_t w[1] = { k }; return xi(1, w); }

/* ------------------------------------------------------------------ */
/* nodes: [def, index, tag, payload_e, levels_e, nf, (kind, bslot, e)*, nb, (sort, domfield, lslot)*, required_e] */

#define TNSIDE(id) ((TNodeSide *)chunked_at(&M.tnode_side, (id) - 1))
static const uint64_t *nw(TNodeId Q, size_t *n) { return interner_get(&M.tnodes, Q, n); }
TDefId tnode_def(TNodeId Q) { size_t n; return nw(Q, &n)[0]; }
uint64_t tnode_index(TNodeId Q) { size_t n; return nw(Q, &n)[1]; }
Tag tnode_tag(TNodeId Q) { size_t n; return (Tag)nw(Q, &n)[2]; }
static ExprId node_payload_e(TNodeId Q) { size_t n; return nw(Q, &n)[3]; }
static ExprId node_levels_e(TNodeId Q) { size_t n; return nw(Q, &n)[4]; }
size_t tnode_nfields(TNodeId Q) { size_t n; return (size_t)nw(Q, &n)[5]; }
static void node_field(TNodeId Q, size_t k, FieldKind *kind, BinderSlot *bslot, ExprId *e) {
    size_t n; const uint64_t *w = nw(Q, &n);
    *kind = (FieldKind)w[6 + 3 * k]; *bslot = (BinderSlot)w[7 + 3 * k]; *e = w[8 + 3 * k];
}
FieldKind tnode_field_kind(TNodeId Q, size_t k) { FieldKind kd; BinderSlot s; ExprId e; node_field(Q, k, &kd, &s, &e); return kd; }
BinderSlot tnode_field_slot(TNodeId Q, size_t k) { FieldKind kd; BinderSlot s; ExprId e; node_field(Q, k, &kd, &s, &e); return s; }
static const uint64_t *node_btab(TNodeId Q) { size_t n; const uint64_t *w = nw(Q, &n); return w + 6 + 3 * w[5]; }
size_t tnode_nbinders(TNodeId Q) { return (size_t)node_btab(Q)[0]; }
static void node_binder(TNodeId Q, BinderSlot s, Sort *sort, FieldIndex *domfield, size_t *lslot) {
    const uint64_t *b = node_btab(Q);
    require(s < b[0], "template binder slot");
    *sort = (Sort)b[1 + 3 * s]; *domfield = (FieldIndex)b[2 + 3 * s]; *lslot = (size_t)b[3 + 3 * s];
}
Sort tnode_binder_sort(TNodeId Q, BinderSlot s) { Sort so; FieldIndex f; size_t l; node_binder(Q, s, &so, &f, &l); return so; }
static ExprId node_required_e(TNodeId Q) { const uint64_t *b = node_btab(Q); return b[1 + 3 * b[0]]; }
const char *tdef_name(TDefId d) { return d >= 1 && d < TD_COUNT ? TPL.defs[d].name : "?"; }

/* ------------------------------------------------------------------ */
/* free slots of expressions and nodes (syntactic closure)               */

typedef struct { uint64_t bits[(MAXSLOT + 63) / 64]; } SlotSet;
static void ss_set(SlotSet *s, size_t k) { s->bits[k / 64] |= 1ULL << (k % 64); }
static bool ss_has(const SlotSet *s, size_t k) { return (s->bits[k / 64] >> (k % 64)) & 1; }
static void ss_or(SlotSet *a, const SlotSet *b) { for (size_t k = 0; k < (MAXSLOT + 63) / 64; k++) a->bits[k] |= b->bits[k]; }
static void ss_clear(SlotSet *s, size_t k) { s->bits[k / 64] &= ~(1ULL << (k % 64)); }

static void node_free(TNodeId Q, SlotSet *out);
static void expr_free(ExprId e, size_t np, SlotSet *out) {
    size_t n; const uint64_t *w = xw(e, &n);
    switch (w[0]) {
    case X_PARAM: ss_set(out, w[1]); break;
    case X_LOCAL: ss_set(out, np + w[1]); break;
    case X_LEVEL: case X_IV0: case X_IV1: case X_FCF: case X_FCT: break;
    case X_LSUCC: case X_LFIRST: case X_IVNOT: case X_FORALL: case X_APPLY_TYPE: case X_APPLY_GUARD: expr_free(w[1], np, out); break;
    case X_LMAX: case X_LEVELS: case X_IVAND: case X_IVOR: case X_FCAND: case X_FCOR: expr_free(w[1], np, out); expr_free(w[2], np, out); break;
    case X_FCEND: expr_free(w[1], np, out); break;
    case X_NODE: node_free(w[1], out); break;
    case X_CALL: for (size_t k = 0; k < w[2]; k++) expr_free(w[3 + k], np, out); break;
    case X_APPLY: expr_free(w[1], np, out); for (size_t k = 0; k < w[2]; k++) expr_free(w[3 + k], np, out); break;
    case X_SCOPE: {
        /* [X_SCOPE, nloc, (sort, lslot, type_e, level_e, req_e)*, body, type, level, guard] */
        size_t nl = w[1]; const uint64_t *l = w + 2;
        SlotSet inner; memset(&inner, 0, sizeof inner);
        for (size_t k = 0; k < nl; k++) { if (l[5 * k + 2]) expr_free(l[5 * k + 2], np, &inner); if (l[5 * k + 3]) expr_free(l[5 * k + 3], np, &inner); if (l[5 * k + 4]) expr_free(l[5 * k + 4], np, &inner); }
        const uint64_t *t = l + 5 * nl;
        expr_free(t[0], np, &inner); if (t[1]) expr_free(t[1], np, &inner); if (t[2]) expr_free(t[2], np, &inner); expr_free(t[3], np, &inner);
        for (size_t k = 0; k < nl; k++) ss_clear(&inner, np + l[5 * k + 1]);
        ss_or(out, &inner);
        break;
    }
    default: die("bad expression kind");
    }
}
static void node_free(TNodeId Q, SlotSet *out) {
    uint64_t list = TNSIDE(Q)->free_slots;
    size_t n; const uint64_t *w = interner_get(&M.keys, list, &n);
    for (size_t k = 0; k < n; k++) ss_set(out, w[k]);
}
static void node_free_list(TNodeId Q, size_t *n, const uint64_t **w) { *w = interner_get(&M.keys, TNSIDE(Q)->free_slots, n); }

/* ------------------------------------------------------------------ */
/* environments and interpretation                                       */

typedef struct { const TDef *def; TDefId defid; TVal val[MAXSLOT]; bool has[MAXSLOT]; } Env;

/* the interpretation of template programs is a set of frame families (kframe.h) */
#define env_key_PARAMS(X) X(const Env *, env) X(const SlotSet *, only)
KF_DECL_DROP(env_key, uint64_t, env_key_PARAMS, env_key_drop, Words w; uint64_t key;)
static void env_key_drop(env_key_F *F) { words_free(&F->w); }
KF_STEP(env_key) {
    KF_BEGIN(env_key);
    words_init(&F->w); KF_CALL(words_reserve, NULL, &F->w, 3 * (F->env->def->nparams + F->env->def->nlocals));
    {
        const Env *env = F->env;
        size_t n = env->def->nparams + env->def->nlocals;
        for (size_t k = 0; k < n; k++) if (env->has[k] && (!F->only || ss_has(F->only, k))) { words_push(&F->w, k); words_push(&F->w, env->val[k].sort); words_push(&F->w, env->val[k].id); }
    }
    KF_CALL(interner_intern, &F->key, &M.keys, F->w.w, F->w.n, NULL);
    words_free(&F->w);
    KF_RET(F->key);
    KF_END;
}

#define interp_PARAMS(X) X(ExprId, e) X(Env *, env)
KF_DECL(interp, TVal, interp_PARAMS, const uint64_t *w; TVal a, b; uint64_t x; TypedPartial p;)

static TVal tv_level(uint64_t n) { TVal v = { PS_LEVEL, n }; return v; }
static TVal tv_ref(RefId r) { TVal v = { PS_REF, r }; return v; }
static TVal tv_iv(IntervalId r) { TVal v = { PS_INTERVAL, r }; return v; }
static TVal tv_fc(FaceId f) { TVal v = { PS_FACE, f }; return v; }

/* TEnv record: [n, (slot, sort, id)*] */
static const uint64_t *tenv_words(TEnvId E, size_t *n) { return interner_get(&M.tenvs, E, n); }
size_t tenv_size(TEnvId E) { size_t n; return (size_t)tenv_words(E, &n)[0]; }
void tenv_entry(TEnvId E, size_t k, uint64_t *slot, TVal *v) { size_t n; const uint64_t *w = tenv_words(E, &n); *slot = w[1 + 3 * k]; v->sort = (PSort)w[2 + 3 * k]; v->id = w[3 + 3 * k]; }
TNodeId tnode_of(RefId t) { return ref_tnode(t); }
TEnvId tenv_of(RefId t) { return ref_tenv(t); }

static void env_from_tenv(Env *env, TNodeId Q, TEnvId E) {
    memset(env, 0, sizeof *env);
    env->defid = tnode_def(Q); env->def = &TPL.defs[env->defid];
    size_t n = tenv_size(E);
    for (size_t k = 0; k < n; k++) { uint64_t slot; TVal v; tenv_entry(E, k, &slot, &v); env->val[slot] = v; env->has[slot] = true; }
}

#define acc_tval_PARAMS(X) X(TVal, v) X(DimSetId *, sup) X(VarSetId *, fv)
KF_DECL_DROP(acc_tval, void, acc_tval_PARAMS, acc_tval_drop, Words w; uint64_t t;)
static void acc_tval_drop(acc_tval_F *F) { words_free(&F->w); }
KF_STEP(acc_tval) {
    KF_BEGIN(acc_tval);
    switch (F->v.sort) {
    case PS_REF: KF_CALL(dimset_union, F->sup, *F->sup, ref_support(F->v.id)); KF_CALL(varset_union, F->fv, *F->fv, ref_freevars(F->v.id)); break;
    case PS_INTERVAL: words_init(&F->w); iv_dims(F->v.id, &F->w); KF_CALL(dimset_make, &F->t, F->w.w, F->w.n); KF_CALL(dimset_union, F->sup, *F->sup, F->t); words_free(&F->w); break;
    case PS_FACE: words_init(&F->w); fc_dims(F->v.id, &F->w); KF_CALL(dimset_make, &F->t, F->w.w, F->w.n); KF_CALL(dimset_union, F->sup, *F->sup, F->t); words_free(&F->w); break;
    case PS_SCOPE: KF_CALL(dimset_union, F->sup, *F->sup, scope_support(F->v.id)); KF_CALL(varset_union, F->fv, *F->fv, scope_freevars(F->v.id)); break;
    case PS_LEVEL: break;
    }
    KF_RETV();
    KF_END;
}

/* make_template_view (§51.1): restrict to the node's complete typed free
 * slots, intern, publish key and metadata together */
#define make_view_env_PARAMS(X) X(TNodeId, Q) X(const Env *, env)
KF_DECL_DROP(make_view_env, RefId, make_view_env_PARAMS, make_view_env_drop, size_t nf, k, kept; const uint64_t *fl; Words w; DimSetId sup, fsup; VarSetId fv, ffv; TEnvId E; Env e2; TVal req; RefId r;)
static void make_view_env_drop(make_view_env_F *F) { words_free(&F->w); }
KF_STEP(make_view_env) {
    KF_BEGIN(make_view_env);
    node_free_list(F->Q, &F->nf, &F->fl);
    words_init(&F->w); KF_CALL(words_reserve, NULL, &F->w, 1 + 3 * F->nf); words_push(&F->w, 0);
    F->kept = 0;
    KF_CALL(dimset_make, &F->sup, NULL, 0); KF_CALL(varset_make, &F->fv, NULL, 0);
    for (F->k = 0; F->k < F->nf; F->k++) {
        size_t slot = (size_t)F->fl[F->k];
        require(F->env->has[slot], "template view: a required slot has no value (%s slot %zu)", F->env->def->name, slot);
        words_push(&F->w, slot); words_push(&F->w, F->env->val[slot].sort); words_push(&F->w, F->env->val[slot].id); F->kept++;
        KF_CALL(acc_tval, NULL, F->env->val[slot], &F->sup, &F->fv);
    }
    F->w.w[0] = F->kept;
    KF_CALL(interner_intern, &F->E, &M.tenvs, F->w.w, F->w.n, NULL);
    words_free(&F->w);
    /* required face: the instantiated declared recipe */
    F->e2 = *F->env;
    KF_CALL(interp, &F->req, node_required_e(F->Q), &F->e2);
    KF_CALL(dimset_free, &F->fsup, F->sup); KF_CALL(varset_free, &F->ffv, F->fv);
    KF_CALL(ref_intern_tview, &F->r, F->Q, F->E, F->fsup, F->ffv, F->req.id);
    KF_RET(F->r);
    KF_END;
}

RefId make_template_view(TNodeId Q, size_t n, const TVal *slots, const uint64_t *slot_index) {
    Env env; memset(&env, 0, sizeof env);
    env.defid = tnode_def(Q); env.def = &TPL.defs[env.defid];
    for (size_t k = 0; k < n; k++) { env.val[slot_index[k]] = slots[k]; env.has[slot_index[k]] = true; }
    RefId r; KStack *s_ = kf_sync_begin(); make_view_env_push(s_, &r, Q, &env); kf_sync_run(s_); kf_sync_end(s_); return r;
}

#define interp_scope_PARAMS(X) X(ExprId, e) X(Env *, env)
KF_DECL_DROP(interp_scope, TVal, interp_scope_PARAMS, interp_scope_drop,
    const uint64_t *w, *l, *t; size_t nl, np, k, lslot; SlotSet fs; uint64_t kw[3], key, mk[2], out; bool have;
    CaptureDecl *cd; Env inner; Sort sort; KeyWord bk[4]; TVal tv, bodyv; RefId ty, xr; uint64_t lv; FaceId rq, g; IntervalId ivj; ScopeId S; TermVarId x; Val body;)
static void interp_scope_drop(interp_scope_F *F) { free(F->cd); F->cd = NULL; }
KF_STEP(interp_scope) {
    KF_BEGIN(interp_scope);
    { size_t n; F->w = xw(F->e, &n); }
    F->nl = F->w[1]; F->l = F->w + 2; F->t = F->l + 5 * F->nl;
    F->np = F->env->def->nparams;
    /* build key: the expression site and its restricted free environment */
    memset(&F->fs, 0, sizeof F->fs); expr_free(F->e, F->np, &F->fs);
    F->kw[0] = F->e; KF_CALL(env_key, &F->kw[1], F->env, &F->fs); F->kw[2] = F->env->defid;
    KF_CALL(interner_intern, &F->key, &M.keys, F->kw, 3, NULL);
    F->mk[0] = 0x5C0BE; F->mk[1] = F->key;
    KF_CALL(wordmap_get, &F->have, &M.interp_memo, F->mk, 2, &F->out);
    if (F->have) { TVal v = { PS_SCOPE, F->out }; KF_RET(v); }
    F->cd = malloc((F->nl ? F->nl : 1) * sizeof(CaptureDecl));
    F->inner = *F->env;
    for (F->k = 0; F->k < F->nl; F->k++) {
        F->sort = (Sort)F->l[5 * F->k]; F->lslot = F->np + F->l[5 * F->k + 1];
        F->bk[0] = (KeyWord){ KW_CONST, 9100 }; F->bk[1] = (KeyWord){ KW_CONST, F->key }; F->bk[2] = (KeyWord){ KW_CONST, F->k }; F->bk[3] = (KeyWord){ KW_CONST, F->sort };
        F->cd[F->k].sort = F->sort; F->cd[F->k].type = 0; F->cd[F->k].level = LEVEL_NONE;
        KF_CALL0(fc_true, &F->cd[F->k].required);
        if (F->sort == S_DIM) {
            KF_CALL(nominal_var, &F->cd[F->k].id, F->bk, 4, 3, S_DIM, 0, 0, false);
            KF_CALL(iv_var, &F->ivj, F->cd[F->k].id);
            F->inner.val[F->lslot] = tv_iv(F->ivj); F->inner.has[F->lslot] = true;
        } else {
            KF_CALL(interp, &F->tv, F->l[5 * F->k + 2], &F->inner); F->ty = F->tv.id;
            F->lv = LEVEL_NONE;
            if (F->l[5 * F->k + 3]) { KF_CALL(interp, &F->tv, F->l[5 * F->k + 3], &F->inner); F->lv = F->tv.id; }
            if (F->l[5 * F->k + 4]) { KF_CALL(interp, &F->tv, F->l[5 * F->k + 4], &F->inner); F->rq = F->tv.id; }
            else KF_CALL0(fc_true, &F->rq);
            KF_CALL(nominal_var, &F->x, F->bk, 4, 2, S_TERM, F->ty, F->rq, true);
            F->cd[F->k].id = F->x; F->cd[F->k].type = F->ty; F->cd[F->k].level = F->lv; F->cd[F->k].required = F->rq;
            KF_CALL(ref_var, &F->xr, F->x);
            F->inner.val[F->lslot] = tv_ref(F->xr); F->inner.has[F->lslot] = true;
        }
    }
    KF_CALL(interp, &F->bodyv, F->t[0], &F->inner);
    F->ty = 0; F->lv = LEVEL_NONE;
    if (F->t[1]) { KF_CALL(interp, &F->tv, F->t[1], &F->inner); F->ty = F->tv.id; }
    if (F->t[2]) { KF_CALL(interp, &F->tv, F->t[2], &F->inner); F->lv = F->tv.id; }
    KF_CALL(interp, &F->tv, F->t[3], &F->inner); F->g = F->tv.id;
    F->body.sort = F->bodyv.sort == PS_REF ? VS_REF : F->bodyv.sort == PS_INTERVAL ? VS_INTERVAL : VS_FACE; F->body.id = F->bodyv.id;
    KF_CALL(capture_scope, &F->S, F->nl, F->cd, F->body, F->ty, F->lv, F->g);
    free(F->cd); F->cd = NULL;
    KF_CALL(wordmap_put, NULL, &M.interp_memo, F->mk, 2, F->S);
    { TVal v = { PS_SCOPE, F->S }; KF_RET(v); }
    KF_END;
}

/* a call node: the callee's environment is a frame of its own (κ inherited) */
#define interp_call_PARAMS(X) X(const uint64_t *, w) X(Env *, env)
KF_DECL(interp_call, TVal, interp_call_PARAMS, Env e2; const TDef *fd; size_t k; TVal r;)
KF_STEP(interp_call) {
    KF_BEGIN(interp_call);
    {
        TDefId f = F->w[1]; F->fd = &TPL.defs[f];
        memset(&F->e2, 0, sizeof F->e2); F->e2.defid = f; F->e2.def = F->fd;
        F->e2.val[0] = F->env->val[0]; F->e2.has[0] = true;                 /* κ is inherited */
        require(F->w[2] + 1 == F->fd->nparams, "template call arity (%s)", F->fd->name);
    }
    for (F->k = 0; F->k < F->w[2]; F->k++) {
        KF_CALL(interp, &F->e2.val[F->k + 1], F->w[3 + F->k], F->env); F->e2.has[F->k + 1] = true;
        require(F->e2.val[F->k + 1].sort == F->fd->sorts[F->k + 1], "template call sort (%s, %zu)", F->fd->name, F->k);
    }
    KF_CALL(interp, &F->r, F->fd->root, &F->e2);
    KF_RET(F->r);
    KF_END;
}

/* a scope application: the argument vector is owned by its frame */
#define interp_apply_PARAMS(X) X(const uint64_t *, w) X(Env *, env)
KF_DECL_DROP(interp_apply, TVal, interp_apply_PARAMS, interp_apply_drop, TVal sv, a; size_t na, k; Val *args; TypedPartial p;)
static void interp_apply_drop(interp_apply_F *F) { free(F->args); F->args = NULL; }
KF_STEP(interp_apply) {
    KF_BEGIN(interp_apply);
    KF_CALL(interp, &F->sv, F->w[1], F->env); require(F->sv.sort == PS_SCOPE, "scope application of a non-scope");
    F->na = F->w[2];
    F->args = malloc((F->na ? F->na : 1) * sizeof(Val));
    for (F->k = 0; F->k < F->na; F->k++) { KF_CALL(interp, &F->a, F->w[3 + F->k], F->env); F->args[F->k].sort = F->a.sort == PS_REF ? VS_REF : F->a.sort == PS_INTERVAL ? VS_INTERVAL : VS_FACE; F->args[F->k].id = F->a.id; }
    KF_CALL(apply_scope, &F->p, F->sv.id, F->na, F->args);
    free(F->args); F->args = NULL;
    if (F->w[0] == X_APPLY_TYPE) KF_RET(tv_ref(F->p.type));
    if (F->w[0] == X_APPLY_GUARD) KF_RET(tv_fc(F->p.guard));
    { TVal v = { F->p.body.sort == VS_REF ? PS_REF : F->p.body.sort == VS_INTERVAL ? PS_INTERVAL : PS_FACE, F->p.body.id }; KF_RET(v); }
    KF_END;
}

KF_STEP(interp) {
    KF_BEGIN(interp);
    { size_t n; F->w = xw(F->e, &n); }
    switch (F->w[0]) {
    case X_PARAM: require(F->env->has[F->w[1]], "template: parameter %llu unset", (unsigned long long)F->w[1]); KF_RET(F->env->val[F->w[1]]);
    case X_LOCAL: { size_t s = F->env->def->nparams + F->w[1]; require(F->env->has[s], "template: local %llu unbound", (unsigned long long)F->w[1]); KF_RET(F->env->val[s]); }
    case X_LEVEL: KF_RET(tv_level(F->w[1]));
    case X_LSUCC: KF_CALL(interp, &F->a, F->w[1], F->env); KF_CALL(level_succ, &F->x, F->a.id); KF_RET(tv_level(F->x));
    case X_LFIRST: KF_CALL(interp, &F->a, F->w[1], F->env); KF_RET(tv_level(levels_first(F->a.id)));
    case X_LMAX: KF_CALL(interp, &F->a, F->w[1], F->env); KF_CALL(interp, &F->b, F->w[2], F->env); KF_CALL(level_max, &F->x, F->a.id, F->b.id); KF_RET(tv_level(F->x));
    case X_LEVELS: KF_CALL(interp, &F->a, F->w[1], F->env); KF_CALL(interp, &F->b, F->w[2], F->env); KF_CALL(levels_pack, &F->x, F->a.id, F->b.id); KF_RET(tv_level(F->x));
    case X_NODE: KF_CALL(make_view_env, &F->x, F->w[1], F->env); KF_RET(tv_ref(F->x));
    case X_CALL: KF_CALL(interp_call, &F->a, F->w, F->env); KF_RET(F->a);
    case X_SCOPE: KF_CALL(interp_scope, &F->a, F->e, F->env); KF_RET(F->a);
    case X_APPLY: case X_APPLY_TYPE: case X_APPLY_GUARD: KF_CALL(interp_apply, &F->a, F->w, F->env); KF_RET(F->a);
    case X_IV0: KF_CALL0(iv_zero, &F->x); KF_RET(tv_iv(F->x));
    case X_IV1: KF_CALL0(iv_one, &F->x); KF_RET(tv_iv(F->x));
    case X_IVNOT: KF_CALL(interp, &F->a, F->w[1], F->env); KF_CALL(iv_negate, &F->x, F->a.id); KF_RET(tv_iv(F->x));
    case X_IVAND: KF_CALL(interp, &F->a, F->w[1], F->env); KF_CALL(interp, &F->b, F->w[2], F->env); KF_CALL(iv_meet, &F->x, F->a.id, F->b.id); KF_RET(tv_iv(F->x));
    case X_IVOR: KF_CALL(interp, &F->a, F->w[1], F->env); KF_CALL(interp, &F->b, F->w[2], F->env); KF_CALL(iv_join, &F->x, F->a.id, F->b.id); KF_RET(tv_iv(F->x));
    case X_FCF: KF_CALL0(fc_false, &F->x); KF_RET(tv_fc(F->x));
    case X_FCT: KF_CALL0(fc_true, &F->x); KF_RET(tv_fc(F->x));
    case X_FCAND: KF_CALL(interp, &F->a, F->w[1], F->env); KF_CALL(interp, &F->b, F->w[2], F->env); KF_CALL(fc_meet, &F->x, F->a.id, F->b.id); KF_RET(tv_fc(F->x));
    case X_FCOR: KF_CALL(interp, &F->a, F->w[1], F->env); KF_CALL(interp, &F->b, F->w[2], F->env); KF_CALL(fc_join, &F->x, F->a.id, F->b.id); KF_RET(tv_fc(F->x));
    case X_FCEND: KF_CALL(interp, &F->a, F->w[1], F->env); KF_CALL(fc_endpoint, &F->x, F->a.id, (int)F->w[2]); KF_RET(tv_fc(F->x));
    case X_FORALL: KF_CALL(interp, &F->a, F->w[1], F->env); require(F->a.sort == PS_SCOPE, "forall of a non-scope"); KF_CALL(forall_scope, &F->x, F->a.id); KF_RET(tv_fc(F->x));
    default: die("bad expression kind %llu", (unsigned long long)F->w[0]);
    }
    KF_END;
}

/* ------------------------------------------------------------------ */
/* TVIEW operations                                                      */

KF_DECL_EXT(tview_open, void, tview_open_PARAMS, TNodeId Q; Env env; size_t k; TVal v;)
KF_STEP(tview_open) {
    KF_BEGIN(tview_open);
    F->Q = ref_tnode(F->t); env_from_tenv(&F->env, F->Q, ref_tenv(F->t));
    F->h->tag = tnode_tag(F->Q);
    F->h->payload = 0;
    if (node_payload_e(F->Q)) { KF_CALL(interp, &F->v, node_payload_e(F->Q), &F->env); F->h->payload = F->v.id; }
    F->h->levels = LEVELS_NONE;
    if (node_levels_e(F->Q)) { KF_CALL(interp, &F->v, node_levels_e(F->Q), &F->env); F->h->levels = F->v.id; }
    F->h->n = tnode_nfields(F->Q);
    KF_CALL(k_zalloc, (void **)&F->h->f, F->h->n ? F->h->n : 1, sizeof(HField));
    for (F->k = 0; F->k < F->h->n; F->k++) {
        FieldKind kind; BinderSlot bs; ExprId fe; node_field(F->Q, F->k, &kind, &bs, &fe);
        F->h->f[F->k].kind = kind; F->h->f[F->k].index = (FieldIndex)F->k; F->h->f[F->k].slot = bs;
        if (bs != NO_SLOT) { F->h->f[F->k].is_binder = true; F->h->f[F->k].sort = tnode_binder_sort(F->Q, bs); F->h->f[F->k].id = 0; }
        else { KF_CALL(interp, &F->v, fe, &F->env); F->h->f[F->k].id = F->v.id; }
    }
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(tview_open, tview_open_PARAMS, tview_open(RefId t, Head *h))

KF_DECL_EXT(tview_term_binder, TermOpen, tview_term_binder_PARAMS, TNodeId Q; Env env; ExprId de, be; size_t lslot; TermOpen o; TVal v; RefId xr;)
KF_STEP(tview_term_binder) {
    KF_BEGIN(tview_term_binder);
    F->Q = ref_tnode(F->owner); env_from_tenv(&F->env, F->Q, ref_tenv(F->owner));
    {
        Sort sort; FieldIndex domf; node_binder(F->Q, F->slot, &sort, &domf, &F->lslot);
        require(sort == S_TERM, "sort mismatch: expected term binder");
        FieldKind kd; BinderSlot bs;
        node_field(F->Q, domf, &kd, &bs, &F->de);
        node_field(F->Q, F->body_field, &kd, &bs, &F->be);
        require(bs == F->slot, "template field is not under this binder");
    }
    KF_CALL(interp, &F->v, F->de, &F->env); F->o.type = F->v.id;
    KF_CALL(binder_var, &F->o.x, F->owner, F->slot, S_TERM, F->o.type);
    KF_CALL(ref_var, &F->xr, F->o.x);
    { size_t s = F->env.def->nparams + F->lslot; F->env.val[s] = tv_ref(F->xr); F->env.has[s] = true; }
    KF_CALL(interp, &F->v, F->be, &F->env); F->o.body = F->v.id;
    KF_RET(F->o);
    KF_END;
}
KF_SYNC_DEF(tview_term_binder, TermOpen, tview_term_binder_PARAMS, tview_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field))

KF_DECL_EXT(tview_dim_binder, DimOpen, tview_dim_binder_PARAMS, TNodeId Q; Env env; ExprId be; size_t lslot; DimOpen o; TVal v; IntervalId iv;)
KF_STEP(tview_dim_binder) {
    KF_BEGIN(tview_dim_binder);
    F->Q = ref_tnode(F->owner); env_from_tenv(&F->env, F->Q, ref_tenv(F->owner));
    {
        Sort sort; FieldIndex domf; node_binder(F->Q, F->slot, &sort, &domf, &F->lslot);
        require(sort == S_DIM, "sort mismatch: expected dimension binder");
        FieldKind kd; BinderSlot bs;
        node_field(F->Q, F->body_field, &kd, &bs, &F->be);
        require(bs == F->slot, "template field is not under this binder");
    }
    KF_CALL(binder_var, &F->o.j, F->owner, F->slot, S_DIM, 0);
    KF_CALL(iv_var, &F->iv, F->o.j);
    { size_t s = F->env.def->nparams + F->lslot; F->env.val[s] = tv_iv(F->iv); F->env.has[s] = true; }
    KF_CALL(interp, &F->v, F->be, &F->env); F->o.body = F->v.id;
    KF_RET(F->o);
    KF_END;
}
KF_SYNC_DEF(tview_dim_binder, DimOpen, tview_dim_binder_PARAMS, tview_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field))

#define reindex_tval_PARAMS(X) X(TVal, v) X(MapId, sigma)
KF_DECL(reindex_tval, TVal, reindex_tval_PARAMS, )
KF_STEP(reindex_tval) {
    KF_BEGIN(reindex_tval);
    switch (F->v.sort) {
    case PS_REF: KF_CALL(reindex, &F->v.id, F->v.id, F->sigma); break;
    case PS_INTERVAL: KF_CALL(iv_reindex, &F->v.id, F->v.id, F->sigma); break;
    case PS_FACE: KF_CALL(fc_reindex, &F->v.id, F->v.id, F->sigma); break;
    case PS_SCOPE: KF_CALL(reindex_scope, &F->v.id, F->v.id, F->sigma); break;
    case PS_LEVEL: break;
    }
    KF_RET(F->v);
    KF_END;
}
KF_DECL_EXT_DROP(tenv_make, TEnvId, tenv_make_PARAMS, tenv_make_drop, Words w; TEnvId E;)
static void tenv_make_drop(tenv_make_F *F) { words_free(&F->w); }
KF_STEP(tenv_make) {
    KF_BEGIN(tenv_make);
    words_init(&F->w); KF_CALL(words_reserve, NULL, &F->w, 1 + 3 * F->n); words_push(&F->w, F->n);
    for (size_t k = 0; k < F->n; k++) { words_push(&F->w, F->slots[k]); words_push(&F->w, F->vals[k].sort); words_push(&F->w, F->vals[k].id); }
    KF_CALL(interner_intern, &F->E, &M.tenvs, F->w.w, F->w.n, NULL); words_free(&F->w);
    KF_RET(F->E);
    KF_END;
}
KF_SYNC_DEF(tenv_make, TEnvId, tenv_make_PARAMS, tenv_make(size_t n, const uint64_t *slots, const TVal *vals))
KF_DECL_EXT_DROP(tenv_reindex, TEnvId, tenv_reindex_PARAMS, tenv_reindex_drop, size_t n, k; uint64_t *slots; TVal *vals; TEnvId out;)
static void tenv_reindex_drop(tenv_reindex_F *F) { free(F->slots); free(F->vals); F->slots = NULL; F->vals = NULL; }
KF_STEP(tenv_reindex) {
    KF_BEGIN(tenv_reindex);
    F->n = tenv_size(F->E);
    F->slots = malloc((F->n ? F->n : 1) * sizeof(uint64_t)); F->vals = malloc((F->n ? F->n : 1) * sizeof(TVal));
    require(F->slots && F->vals, "out of memory");
    for (F->k = 0; F->k < F->n; F->k++) { tenv_entry(F->E, F->k, &F->slots[F->k], &F->vals[F->k]); KF_CALL(reindex_tval, &F->vals[F->k], F->vals[F->k], F->sigma); }
    KF_CALL(tenv_make, &F->out, F->n, F->slots, F->vals);
    free(F->slots); free(F->vals); F->slots = NULL; F->vals = NULL;
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(tenv_reindex, TEnvId, tenv_reindex_PARAMS, tenv_reindex(TEnvId E, MapId sigma))
KF_DECL_EXT(tenv_instantiate, RefId, tenv_instantiate_PARAMS, Env env; RefId r;)
KF_STEP(tenv_instantiate) {
    KF_BEGIN(tenv_instantiate);
    env_from_tenv(&F->env, F->Q, F->E);
    KF_CALL(make_view_env, &F->r, F->Q, &F->env);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(tenv_instantiate, RefId, tenv_instantiate_PARAMS, tenv_instantiate(TNodeId Q, TEnvId E))
KF_DECL_EXT(tview_reindex, RefId, tview_reindex_PARAMS, TNodeId Q; Env env; size_t n, k; RefId r;)
KF_STEP(tview_reindex) {
    KF_BEGIN(tview_reindex);
    F->Q = ref_tnode(F->t); env_from_tenv(&F->env, F->Q, ref_tenv(F->t));
    F->n = F->env.def->nparams + F->env.def->nlocals;
    for (F->k = 0; F->k < F->n; F->k++) if (F->env.has[F->k]) KF_CALL(reindex_tval, &F->env.val[F->k], F->env.val[F->k], F->sigma);
    KF_CALL(make_view_env, &F->r, F->Q, &F->env);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(tview_reindex, RefId, tview_reindex_PARAMS, tview_reindex(RefId t, MapId sigma))
KF_DECL_EXT(tview_traverse, RefId, tview_traverse_PARAMS, TNodeId Q; Env env; size_t n, k; RefId r;)
KF_STEP(tview_traverse) {
    KF_BEGIN(tview_traverse);
    F->Q = ref_tnode(F->t); env_from_tenv(&F->env, F->Q, ref_tenv(F->t));
    F->n = F->env.def->nparams + F->env.def->nlocals;
    for (F->k = 0; F->k < F->n; F->k++) if (F->env.has[F->k]) {
        switch (F->env.val[F->k].sort) {
        case PS_REF: KF_CALL(trav_ref, &F->env.val[F->k].id, F->env.val[F->k].id, F->tv, F->depth); break;
        case PS_INTERVAL: KF_CALL(trav_iv, &F->env.val[F->k].id, F->env.val[F->k].id, F->tv, F->depth); break;
        case PS_FACE: KF_CALL(trav_fc, &F->env.val[F->k].id, F->env.val[F->k].id, F->tv, F->depth); break;
        case PS_SCOPE: KF_CALL(trav_scope, &F->env.val[F->k].id, F->env.val[F->k].id, F->tv, F->depth); break;
        case PS_LEVEL: break;
        }
    }
    KF_CALL(make_view_env, &F->r, F->Q, &F->env);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(tview_traverse, RefId, tview_traverse_PARAMS, tview_traverse(RefId t, const Trav *tv, size_t depth))

KF_DECL_EXT(tnode_signature, size_t, tnode_signature_PARAMS, TNodeId Q; Env env; size_t nf, n, np, k, slot, l; const uint64_t *fl; TVal v;)
KF_STEP(tnode_signature) {
    KF_BEGIN(tnode_signature);
    F->Q = ref_tnode(F->t); env_from_tenv(&F->env, F->Q, ref_tenv(F->t));
    node_free_list(F->Q, &F->nf, &F->fl);
    F->n = 0;
    F->np = F->env.def->nparams;
    for (F->k = 0; F->k < F->nf; F->k++) {
        F->slot = (size_t)F->fl[F->k];
        if (F->slot >= F->np && (F->env.def->lsort[F->slot - F->np] != PS_REF || !F->env.def->ltype[F->slot - F->np])) continue;
        if (!F->out) { F->n++; continue; }
        require(F->n < F->max, "template signature output buffer too small; query complete size first");
        /* the node's environment is closed under the declarations (finish),
         * so every declared type is interpretable here */
        if (F->slot < F->np) {
            const TDef *d = F->env.def; ParamSig *o = &F->out[F->n];
            o->slot = F->slot; o->sort = d->sorts[F->slot];
            o->type = 0; if (d->ptype[F->slot]) { KF_CALL(interp, &F->v, F->env.def->ptype[F->slot], &F->env); F->out[F->n].type = F->v.id; }
            F->out[F->n].level = LEVEL_NONE; if (F->env.def->plevel[F->slot]) { KF_CALL(interp, &F->v, F->env.def->plevel[F->slot], &F->env); F->out[F->n].level = F->v.id; }
            F->out[F->n].sig = 0; if (F->env.def->psig[F->slot]) { KF_CALL(interp, &F->v, F->env.def->psig[F->slot], &F->env); F->out[F->n].sig = F->v.id; }
            if (F->env.def->pguard[F->slot]) { KF_CALL(interp, &F->v, F->env.def->pguard[F->slot], &F->env); F->out[F->n].guard = F->v.id; }
            else KF_CALL0(fc_true, &F->out[F->n].guard);
        } else {
            /* a term local used freely by this node (bound by an enclosing
             * constructor or scope): its image is checked against the
             * declaration it was stored under */
            F->l = F->slot - F->np;
            if (F->env.def->lsort[F->l] != PS_REF || !F->env.def->ltype[F->l]) continue;
            F->out[F->n].slot = F->slot; F->out[F->n].sort = PS_REF; F->out[F->n].sig = 0;
            KF_CALL(interp, &F->v, F->env.def->ltype[F->l], &F->env); F->out[F->n].type = F->v.id;
            F->out[F->n].level = LEVEL_NONE; if (F->env.def->llevel[F->l]) { KF_CALL(interp, &F->v, F->env.def->llevel[F->l], &F->env); F->out[F->n].level = F->v.id; }
            if (F->env.def->lreq[F->l]) { KF_CALL(interp, &F->v, F->env.def->lreq[F->l], &F->env); F->out[F->n].guard = F->v.id; }
            else KF_CALL0(fc_true, &F->out[F->n].guard);
        }
        F->n++;
    }
    KF_RET(F->n);
    KF_END;
}
KF_SYNC_DEF(tnode_signature, size_t, tnode_signature_PARAMS, tnode_signature(RefId t, ParamSig *out, size_t max))
KF_DECL_EXT(tnode_result, bool, tnode_result_PARAMS, TNodeId Q; Env env; TVal v;)
KF_STEP(tnode_result) {
    KF_BEGIN(tnode_result);
    F->Q = ref_tnode(F->t); env_from_tenv(&F->env, F->Q, ref_tenv(F->t));
    if (!F->env.def->rtype || F->env.def->root_node != F->Q) KF_RET(false);
    KF_CALL(interp, &F->v, F->env.def->rtype, &F->env); *F->type = F->v.id;
    *F->level = LEVEL_NONE;
    if (F->env.def->rlevel) { KF_CALL(interp, &F->v, F->env.def->rlevel, &F->env); *F->level = F->v.id; }
    KF_RET(true);
    KF_END;
}
KF_SYNC_DEF(tnode_result, bool, tnode_result_PARAMS, tnode_result(RefId t, RefId *type, uint64_t *level))

/* ------------------------------------------------------------------ */
/* registration DSL                                                      */

static TDefId cur; static TDef *cd;
static ExprId under_face;         /* the `under` faces in force (0 = none) */

static ExprId P(size_t k) { return x1(X_PARAM, k + 1); }            /* user parameter k (κ is slot 0) */
static ExprId KAPPA(void) { return x1(X_PARAM, 0); }
static ExprId L(size_t l) { return x1(X_LOCAL, l); }
static ExprId LV(uint64_t n) { return x1(X_LEVEL, n); }
static ExprId LSUCC(ExprId a) { return x1(X_LSUCC, a); }
static ExprId LMAX(ExprId a, ExprId b) { return x2(X_LMAX, a, b); }
static ExprId LEVELS(ExprId m, ExprId n) { return x2(X_LEVELS, m, n); }
static ExprId IV0(void) { return x0(X_IV0); }
static ExprId IV1(void) { return x0(X_IV1); }
static ExprId IVNOT(ExprId a) { return x1(X_IVNOT, a); }
static ExprId IVAND(ExprId a, ExprId b) { return x2(X_IVAND, a, b); }
static ExprId IVOR(ExprId a, ExprId b) { return x2(X_IVOR, a, b); }
static ExprId FCF(void) { return x0(X_FCF); }
static ExprId FCT(void) { return x0(X_FCT); }
static ExprId FCAND(ExprId a, ExprId b) { return x2(X_FCAND, a, b); }
static ExprId FCOR(ExprId a, ExprId b) { return x2(X_FCOR, a, b); }
static ExprId FCEND(ExprId a, int eps) { return x2(X_FCEND, a, (uint64_t)eps); }
static ExprId FORALL(ExprId s) { return x1(X_FORALL, s); }
static ExprId AP1(ExprId s, ExprId a) { uint64_t w[4] = { X_APPLY, s, 1, a }; return xi(4, w); }
static ExprId AP2(ExprId s, ExprId a, ExprId b) { uint64_t w[5] = { X_APPLY, s, 2, a, b }; return xi(5, w); }
static ExprId CALLn(TDefKind f, size_t n, const ExprId *args) { uint64_t w[3 + MAXP]; w[0] = X_CALL; w[1] = f; w[2] = n; memcpy(w + 3, args, n * sizeof(ExprId)); return xi(3 + n, w); }
#define CALL(f, ...) ({ ExprId _a[] = { __VA_ARGS__ }; CALLn(f, sizeof _a / sizeof _a[0], _a); })

static size_t newlocal(PSort s) { require(cd->nlocals < MAXL, "too many template locals"); cd->lsort[cd->nlocals] = s; return cd->nlocals++; }

/* close a slot set under the declarations of the current definition: the
 * declared types / levels / guards / signatures of retained parameters and
 * the declarations of retained term locals (constructor binders and scope
 * locals). A retained slot keeps its typed dependency closure (§51.1). */
static void decl_closure(SlotSet *fsl) {
    size_t np = cd->nparams;
    for (bool changed = true; changed; ) {
        changed = false;
        SlotSet add; memset(&add, 0, sizeof add);
        for (size_t k = 0; k < np; k++) if (ss_has(fsl, k)) {
            if (cd->ptype[k]) expr_free(cd->ptype[k], np, &add);
            if (cd->plevel[k]) expr_free(cd->plevel[k], np, &add);
            if (cd->psig[k]) expr_free(cd->psig[k], np, &add);
            if (cd->pguard[k]) expr_free(cd->pguard[k], np, &add);
        }
        for (size_t l = 0; l < cd->nlocals; l++) if (ss_has(fsl, np + l)) {
            if (cd->ltype[l]) expr_free(cd->ltype[l], np, &add);
            if (cd->llevel[l]) expr_free(cd->llevel[l], np, &add);
            if (cd->lreq[l]) expr_free(cd->lreq[l], np, &add);
        }
        for (size_t k = 0; k < MAXSLOT; k++) if (ss_has(&add, k) && !ss_has(fsl, k)) { ss_set(fsl, k); changed = true; }
    }
}
/* the syntactic free slots of a node: fields, payload, levels, required
 * face, minus its own binder locals (child nodes contribute their current
 * free sets) */
static void node_syntactic_free(TNodeId Q, SlotSet *fsl) {
    size_t np = cd->nparams;
    size_t nf = tnode_nfields(Q);
    for (size_t k = 0; k < nf; k++) { FieldKind kd; BinderSlot bs; ExprId e; node_field(Q, k, &kd, &bs, &e); expr_free(e, np, fsl); }
    if (node_payload_e(Q)) expr_free(node_payload_e(Q), np, fsl);
    if (node_levels_e(Q)) expr_free(node_levels_e(Q), np, fsl);
    expr_free(node_required_e(Q), np, fsl);
    size_t nb = tnode_nbinders(Q);
    for (size_t b = 0; b < nb; b++) { Sort so; FieldIndex df; size_t ls; node_binder(Q, (BinderSlot)b, &so, &df, &ls); ss_clear(fsl, np + ls); }
}
static void set_free_slots(TNodeId Q, const SlotSet *fsl) {
    Words fl; words_init(&fl);
    for (size_t k = 0; k < MAXSLOT; k++) if (ss_has(fsl, k)) words_push(&fl, k);
    TNSIDE(Q)->free_slots = interner_intern(&M.keys, fl.w, fl.n, NULL);
    words_free(&fl);
}

typedef struct { FieldKind kind; BinderSlot bslot; ExprId e; } FS;
typedef struct { Sort sort; FieldIndex domfield; size_t lslot; } BS;
static ExprId NODE_req(Tag tag, ExprId payload, ExprId levels, size_t nf, const FS *fs, size_t nb, const BS *bs, ExprId req);
static ExprId NODE(Tag tag, ExprId payload, ExprId levels, size_t nf, const FS *fs, size_t nb, const BS *bs) {
    return NODE_req(tag, payload, levels, nf, fs, nb, bs, under_face ? FCAND(KAPPA(), under_face) : KAPPA());
}
static ExprId NODE_req(Tag tag, ExprId payload, ExprId levels, size_t nf, const FS *fs, size_t nb, const BS *bs, ExprId req) {
    Words w; words_init(&w);
    words_push(&w, cur); words_push(&w, TPL.index_counter[cur]++); words_push(&w, tag); words_push(&w, payload); words_push(&w, levels); words_push(&w, nf);
    for (size_t k = 0; k < nf; k++) { words_push(&w, fs[k].kind); words_push(&w, fs[k].bslot); words_push(&w, fs[k].e); }
    words_push(&w, nb);
    for (size_t k = 0; k < nb; k++) { words_push(&w, bs[k].sort); words_push(&w, bs[k].domfield); words_push(&w, bs[k].lslot); }
    words_push(&w, req);
    /* a term binder declares its local: the domain field, the first level, the node's required face */
    for (size_t k = 0; k < nb; k++) if (bs[k].sort == S_TERM && bs[k].domfield != NO_FIELD) {
        cd->ltype[bs[k].lslot] = fs[bs[k].domfield].e;
        cd->llevel[bs[k].lslot] = levels ? x1(X_LFIRST, levels) : 0;
        cd->lreq[bs[k].lslot] = req;
    }
    bool created;
    TNodeId Q = interner_intern(&M.tnodes, w.w, w.n, &created);
    words_free(&w);
    require(created, "duplicate template node");
    /* free slots: fields, payload, levels, required, minus own binder
     * locals, closed under the declared types / levels / signatures of the
     * retained parameters (§51.1, §59.1): a retained parameter keeps its
     * typed dependency closure */
    SlotSet fsl; memset(&fsl, 0, sizeof fsl);
    node_syntactic_free(Q, &fsl);
    set_free_slots(Q, &fsl);             /* provisional: finish() recomputes the typed closure over the complete declaration table */
    words_push(&cd->nodes, Q);
    return x1(X_NODE, Q);
}

/* constructor helpers; a binder takes the local slot it binds */
static ExprId nPI(ExprId m, ExprId n, size_t xl, ExprId A, ExprId B) { FS f[2] = { { F_REF, NO_SLOT, A }, { F_REF, 0, B } }; BS b[1] = { { S_TERM, 0, xl } }; return NODE(T_PI, 0, LEVELS(m, n), 2, f, 1, b); }
static ExprId nSIGMA(ExprId m, ExprId n, size_t xl, ExprId A, ExprId B) { FS f[2] = { { F_REF, NO_SLOT, A }, { F_REF, 0, B } }; BS b[1] = { { S_TERM, 0, xl } }; return NODE(T_SIGMA, 0, LEVELS(m, n), 2, f, 1, b); }
static ExprId nLAM(ExprId m, size_t xl, ExprId A, ExprId body) { FS f[2] = { { F_REF, NO_SLOT, A }, { F_REF, 0, body } }; BS b[1] = { { S_TERM, 0, xl } }; return NODE(T_LAM, 0, LEVELS(m, LV(LEVEL_NONE)), 2, f, 1, b); }
static ExprId nAPP(ExprId fn, ExprId a) { FS f[2] = { { F_REF, NO_SLOT, fn }, { F_REF, NO_SLOT, a } }; return NODE(T_APP, 0, 0, 2, f, 0, NULL); }
static ExprId nPAIR_AT(ExprId l, ExprId S, ExprId a, ExprId b) { FS f[3] = { { F_REF, NO_SLOT, a }, { F_REF, NO_SLOT, b }, { F_REF, NO_SLOT, S } }; return NODE(T_PAIR, 0, LEVELS(l, LV(LEVEL_NONE)), 3, f, 0, NULL); }
static ExprId nFST(ExprId p) { FS f[1] = { { F_REF, NO_SLOT, p } }; return NODE(T_FST, 0, 0, 1, f, 0, NULL); }
static ExprId nSND(ExprId p) { FS f[1] = { { F_REF, NO_SLOT, p } }; return NODE(T_SND, 0, 0, 1, f, 0, NULL); }
static ExprId nPATH(ExprId n, size_t jl, ExprId B, ExprId l, ExprId r) { FS f[3] = { { F_REF, 0, B }, { F_REF, NO_SLOT, l }, { F_REF, NO_SLOT, r } }; BS b[1] = { { S_DIM, NO_FIELD, jl } }; return NODE(T_PATH, 0, LEVELS(n, LV(LEVEL_NONE)), 3, f, 1, b); }
static ExprId nPLAM(size_t jl, ExprId body) { FS f[1] = { { F_REF, 0, body } }; BS b[1] = { { S_DIM, NO_FIELD, jl } }; return NODE(T_PLAM, 0, 0, 1, f, 1, b); }
static ExprId nPAPP(ExprId n, size_t jl, ExprId B, ExprId l, ExprId r, ExprId p, ExprId s) { FS f[5] = { { F_REF, 0, B }, { F_REF, NO_SLOT, l }, { F_REF, NO_SLOT, r }, { F_REF, NO_SLOT, p }, { F_INTERVAL, NO_SLOT, s } }; BS b[1] = { { S_DIM, NO_FIELD, jl } }; return NODE(T_PAPP, 0, LEVELS(n, LV(LEVEL_NONE)), 5, f, 1, b); }
static ExprId nGLUE(ExprId n, ExprId A, ExprId alpha, ExprId T, ExprId e) { FS f[4] = { { F_REF, NO_SLOT, A }, { F_FACE, NO_SLOT, alpha }, { F_REF, NO_SLOT, T }, { F_REF, NO_SLOT, e } }; return NODE(T_GLUE_TYPE, 0, LEVELS(n, LV(LEVEL_NONE)), 4, f, 0, NULL); }
static ExprId nGLUEINTRO(ExprId n, ExprId A, ExprId alpha, ExprId T, ExprId e, ExprId t, ExprId a) { FS f[6] = { { F_REF, NO_SLOT, A }, { F_FACE, NO_SLOT, alpha }, { F_REF, NO_SLOT, T }, { F_REF, NO_SLOT, e }, { F_REF, NO_SLOT, t }, { F_REF, NO_SLOT, a } }; return NODE(T_GLUE_INTRO, 0, LEVELS(n, LV(LEVEL_NONE)), 6, f, 0, NULL); }
static ExprId nUNGLUE(ExprId n, ExprId A, ExprId alpha, ExprId T, ExprId e, ExprId v) { FS f[5] = { { F_REF, NO_SLOT, A }, { F_FACE, NO_SLOT, alpha }, { F_REF, NO_SLOT, T }, { F_REF, NO_SLOT, e }, { F_REF, NO_SLOT, v } }; return NODE(T_UNGLUE, 0, LEVELS(n, LV(LEVEL_NONE)), 5, f, 0, NULL); }
static ExprId nCOMP(ExprId n, size_t jl, ExprId A, ExprId phi, ExprId u, ExprId cap) { FS f[4] = { { F_REF, 0, A }, { F_FACE, NO_SLOT, phi }, { F_REF, 0, u }, { F_REF, NO_SLOT, cap } }; BS b[1] = { { S_DIM, NO_FIELD, jl } }; return NODE(T_COMP, 0, LEVELS(n, LV(LEVEL_NONE)), 4, f, 1, b); }
static ExprId nSYSTEM(size_t nb, const ExprId *faces, const ExprId *terms) {
    FS f[8]; require(nb <= 4, "system arity");
    for (size_t k = 0; k < nb; k++) { f[2 * k] = (FS){ F_FACE, NO_SLOT, faces[k] }; f[2 * k + 1] = (FS){ F_REF, NO_SLOT, terms[k] }; }
    return NODE(T_SYSTEM, LV(nb), 0, 2 * nb, f, 0, NULL);
}
static ExprId nUNIV(ExprId l) { return NODE(T_UNIVERSE, l, 0, 0, NULL, 0, NULL); }

/* scope literals: locals are allocated here; the body is built by a
 * callback that receives the local slots */
static ExprId guard_now(void) { return under_face ? FCAND(KAPPA(), under_face) : KAPPA(); }
typedef struct { Sort sort; ExprId type, level, req; } LS;
static ExprId SCOPE(size_t nl, const LS *ls, size_t *slots, ExprId body, ExprId type, ExprId level, ExprId guard) {
    for (size_t k = 0; k < nl; k++) if (ls[k].sort == S_TERM) { cd->ltype[slots[k]] = ls[k].type; cd->llevel[slots[k]] = ls[k].level; cd->lreq[slots[k]] = ls[k].req; }
    uint64_t w[8 + 5 * 8]; size_t n = 0;
    w[n++] = X_SCOPE; w[n++] = nl;
    for (size_t k = 0; k < nl; k++) { w[n++] = ls[k].sort; w[n++] = slots[k]; w[n++] = ls[k].type; w[n++] = ls[k].level; w[n++] = ls[k].req; }
    w[n++] = body; w[n++] = type; w[n++] = level; w[n++] = guard;
    return xi(n, w);
}
/* unary dimension scope [j]. body, with its result type as a function of j */
typedef ExprId (*JFn)(ExprId j, void *ctx);
static ExprId DSCOPE1(JFn body, JFn type, void *ctx, ExprId level, ExprId guard) {
    size_t s = newlocal(PS_INTERVAL);
    LS ls[1] = { { S_DIM, 0, 0, 0 } };
    size_t slots[1] = { s };
    ExprId b = body(L(s), ctx);
    ExprId t = type ? type(L(s), ctx) : 0;
    return SCOPE(1, ls, slots, b, t, level, guard);
}


/* ---- contextual signatures of scope parameters (§51.4): a scope whose
 * locals are the expected telescope, whose body is the expected result type,
 * with the expected level and guard ---- */
typedef struct { ExprId a, b, c, d, e, f, t; } Cx;
static ExprId t_univ(ExprId j, void *c); static ExprId t_fam_at(ExprId j, void *c); static ExprId t_const(ExprId j, void *c);
typedef ExprId (*J2Fn)(ExprId a, ExprId b, void *ctx);
static ExprId SIG_DIM1(JFn result, void *ctx, ExprId level, ExprId guard) { return DSCOPE1(result, NULL, ctx, level, guard); }
static ExprId SIG_FACE1(ExprId guard) {
    size_t s = newlocal(PS_INTERVAL); LS ls[1] = { { S_DIM, 0, 0, 0 } }; size_t sl[1] = { s };
    return SCOPE(1, ls, sl, FCT(), 0, 0, guard);
}
static ExprId SIG_DIM2(J2Fn result, void *ctx, ExprId level, ExprId guard) {
    size_t i = newlocal(PS_INTERVAL), j = newlocal(PS_INTERVAL);
    LS ls[2] = { { S_DIM, 0, 0, 0 }, { S_DIM, 0, 0, 0 } }; size_t sl[2] = { i, j };
    return SCOPE(2, ls, sl, result(L(i), L(j), ctx), 0, level, guard);
}
/* [i, x : dom(i)]. result(i, x) */
static ExprId SIG_DIM_TERM(JFn dom, ExprId domlevel, J2Fn result, void *ctx, ExprId level, ExprId guard) {
    size_t i = newlocal(PS_INTERVAL), x = newlocal(PS_REF);
    LS ls[2] = { { S_DIM, 0, 0, 0 }, { S_TERM, dom(L(i), ctx), domlevel, 0 } }; size_t sl[2] = { i, x };
    return SCOPE(2, ls, sl, result(L(i), L(x), ctx), 0, level, guard);
}
/* [x : A, e : etype(x)]. result(x, e) */
static ExprId SIG_TERM2(ExprId A, ExprId lA, JFn etype, ExprId elevel, J2Fn result, void *ctx, ExprId level, ExprId guard) {
    size_t x = newlocal(PS_REF), e = newlocal(PS_REF);
    LS ls[2] = { { S_TERM, A, lA, 0 }, { S_TERM, etype(L(x), ctx), elevel, 0 } }; size_t sl[2] = { x, e };
    return SCOPE(2, ls, sl, result(L(x), L(e), ctx), 0, level, guard);
}
/* result-type recipes used by the signatures */
static ExprId r_pi_at(ExprId i, void *c) { Cx *x = c; /* a=m b=n c=D d=E */ size_t xl = newlocal(PS_REF); return nPI(x->a, x->b, xl, AP1(x->c, i), AP2(x->d, i, L(xl))); }
static ExprId r_sigma_at(ExprId i, void *c) { Cx *x = c; size_t xl = newlocal(PS_REF); return nSIGMA(x->a, x->b, xl, AP1(x->c, i), AP2(x->d, i, L(xl))); }
static ExprId r_E_dom(ExprId i, void *c) { Cx *x = c; return AP1(x->c, i); }
static ExprId r_univ2(ExprId i, ExprId x, void *c) { (void)i; (void)x; return nUNIV(((Cx *)c)->t); }
static ExprId r_path_at(ExprId i, void *c) { Cx *x = c; /* a=n b=B c=left d=right */ size_t k = newlocal(PS_INTERVAL); return nPATH(x->a, k, AP2(x->b, i, L(k)), AP1(x->c, i), AP1(x->d, i)); }
static ExprId r_B_at0(ExprId i, void *c) { return AP2(((Cx *)c)->b, i, IV0()); }
static ExprId r_B_at1(ExprId i, void *c) { return AP2(((Cx *)c)->b, i, IV1()); }
static ExprId r_glue_at(ExprId i, void *c) { Cx *x = c; /* a=n b=A c=alpha d=T e=e */ return nGLUE(x->a, AP1(x->b, i), AP1(x->c, i), AP1(x->d, i), AP1(x->e, i)); }
static ExprId r_equiv_TA(ExprId i, void *c) { Cx *x = c; return CALL(TD_EQUIV, x->a, x->a, AP1(x->d, i), AP1(x->b, i)); }
static ExprId r_guard_alpha(ExprId i, void *c) { return FCAND(KAPPA(), AP1(((Cx *)c)->c, i)); }
static ExprId r_down_etype(ExprId xl, void *c) { Cx *x = c; /* a=lA b=A c=t */ return CALL(TD_PATHCONST, x->a, x->b, x->c, xl); }
static ExprId r_down_res(ExprId xl, ExprId el, void *c) { (void)xl; (void)el; return nUNIV(((Cx *)c)->t); }
/* a unary dimension scope signature whose guard depends on the local */
static ExprId SIG_DIM1_G(JFn result, JFn guard, void *ctx, ExprId level) {
    size_t s = newlocal(PS_INTERVAL); LS ls[1] = { { S_DIM, 0, 0, 0 } }; size_t sl[1] = { s };
    return SCOPE(1, ls, sl, result(L(s), ctx), 0, level, guard(L(s), ctx));
}

static void begin(TDefKind k, const char *name, size_t n, const PSort *sorts) {
    cur = k; cd = &TPL.defs[k]; memset(cd, 0, sizeof *cd); words_init(&cd->nodes);
    cd->name = name; cd->nparams = n + 1; cd->sorts[0] = PS_FACE;
    for (size_t i = 0; i < n; i++) cd->sorts[i + 1] = sorts[i];
    under_face = 0;
}
static void ptype(size_t k, ExprId type, ExprId level) { cd->ptype[k + 1] = type; cd->plevel[k + 1] = level; }
static void ptype_on(size_t k, ExprId type, ExprId level, ExprId guard) { ptype(k, type, level); cd->pguard[k + 1] = guard; }
static void psig(size_t k, ExprId sig) { cd->psig[k + 1] = sig; }
static void rtype(ExprId type, ExprId level) { cd->rtype = type; cd->rlevel = level; }
/* ---- integration of a call-root (§51.1, review F2) ----
 * The callee's root recipe is remapped into caller-owned nodes: callee
 * parameters become the call's argument recipes (κ stays the caller's κ),
 * callee locals become fresh caller locals with their declarations, callee
 * nodes become caller nodes with the substituted field, payload, level and
 * required-face recipes. Done once at registration. */
typedef struct { const TDef *callee; ExprId arg[MAXP]; size_t lmap[MAXL]; bool lmapped[MAXL]; } Inl;
static ExprId inl_expr(ExprId e, Inl *in);
static size_t inl_local(size_t l, Inl *in) {
    if (!in->lmapped[l]) {
        size_t nl = newlocal(in->callee->lsort[l]);
        in->lmap[l] = nl; in->lmapped[l] = true;
        /* the local's declaration follows it (its recipes mention earlier locals: mapped on demand) */
        if (in->callee->ltype[l]) cd->ltype[nl] = inl_expr(in->callee->ltype[l], in);
        if (in->callee->llevel[l]) cd->llevel[nl] = inl_expr(in->callee->llevel[l], in);
        if (in->callee->lreq[l]) cd->lreq[nl] = inl_expr(in->callee->lreq[l], in);
    }
    return in->lmap[l];
}
static ExprId inl_expr(ExprId e, Inl *in) {
    if (!e) return 0;
    size_t n; const uint64_t *w = xw(e, &n);
    switch (w[0]) {
    case X_PARAM: return w[1] == 0 ? KAPPA() : in->arg[w[1]];
    case X_LOCAL: return x1(X_LOCAL, inl_local((size_t)w[1], in));
    case X_LEVEL: case X_IV0: case X_IV1: case X_FCF: case X_FCT: return e;
    case X_LSUCC: case X_LFIRST: case X_IVNOT: case X_FORALL: case X_APPLY_TYPE: case X_APPLY_GUARD: return x1(w[0], inl_expr(w[1], in));
    case X_LMAX: case X_LEVELS: case X_IVAND: case X_IVOR: case X_FCAND: case X_FCOR: return x2(w[0], inl_expr(w[1], in), inl_expr(w[2], in));
    case X_FCEND: return x2(X_FCEND, inl_expr(w[1], in), w[2]);
    case X_CALL: { uint64_t o[3 + MAXP]; o[0] = X_CALL; o[1] = w[1]; o[2] = w[2]; for (size_t k = 0; k < w[2]; k++) o[3 + k] = inl_expr(w[3 + k], in); return xi(3 + w[2], o); }
    case X_APPLY: { uint64_t o[3 + MAXP]; o[0] = X_APPLY; o[1] = inl_expr(w[1], in); o[2] = w[2]; for (size_t k = 0; k < w[2]; k++) o[3 + k] = inl_expr(w[3 + k], in); return xi(3 + w[2], o); }
    case X_SCOPE: {
        size_t nl = w[1]; const uint64_t *l = w + 2; const uint64_t *t = l + 5 * nl;
        uint64_t o[8 + 5 * 8]; size_t m = 0; o[m++] = X_SCOPE; o[m++] = nl;
        for (size_t k = 0; k < nl; k++) {
            size_t ns = inl_local((size_t)l[5 * k + 1], in);
            o[m++] = l[5 * k]; o[m++] = ns; o[m++] = inl_expr(l[5 * k + 2], in); o[m++] = inl_expr(l[5 * k + 3], in); o[m++] = inl_expr(l[5 * k + 4], in);
            if (l[5 * k] == S_TERM) { cd->ltype[ns] = o[m - 3]; cd->llevel[ns] = o[m - 2]; cd->lreq[ns] = o[m - 1]; }
        }
        o[m++] = inl_expr(t[0], in); o[m++] = inl_expr(t[1], in); o[m++] = inl_expr(t[2], in); o[m++] = inl_expr(t[3], in);
        return xi(m, o);
    }
    case X_NODE: {
        TNodeId Q = w[1];
        size_t nf = tnode_nfields(Q), nb = tnode_nbinders(Q);
        FS fs[12]; BS bs[4]; require(nf <= 12 && nb <= 4, "inline: node arity");
        for (size_t k = 0; k < nf; k++) { ExprId fe; node_field(Q, k, &fs[k].kind, &fs[k].bslot, &fe); fs[k].e = inl_expr(fe, in); }
        for (size_t b = 0; b < nb; b++) { size_t ls; node_binder(Q, (BinderSlot)b, &bs[b].sort, &bs[b].domfield, &ls); bs[b].lslot = inl_local(ls, in); }
        return NODE_req(tnode_tag(Q), inl_expr(node_payload_e(Q), in), inl_expr(node_levels_e(Q), in), nf, fs, nb, bs, inl_expr(node_required_e(Q), in));
    }
    default: die("inline: bad expression kind");
    }
}
static ExprId inline_root(ExprId e) {
    for (;;) {
        size_t n; const uint64_t *w = xw(e, &n);
        if (w[0] != X_CALL) return e;
        Inl in; memset(&in, 0, sizeof in);
        in.callee = &TPL.defs[w[1]];
        require(in.callee->root, "inline: callee not registered (%s)", in.callee->name);
        require(w[2] + 1 == in.callee->nparams, "inline: call arity");
        for (size_t k = 0; k < w[2]; k++) in.arg[k + 1] = w[3 + k];
        e = inl_expr(in.callee->root, &in);
    }
}

static void finish(ExprId root) {
    /* a root that calls another program is integrated into a caller-owned
     * constructor node (§51.1): the caller's parameter signature and result
     * type stay the retained, checkable boundary */
    root = inline_root(root);
    cd->root = root;
    size_t n; const uint64_t *w = xw(root, &n);
    require(w[0] == X_NODE, "template root is not a constructor node (%s)", cd->name);
    TNodeId Q = w[1]; cd->root_node = Q;
    /* the typed closure over the complete declaration table, children first,
     * to a fixpoint; the root node also retains the declared result type */
    for (bool changed = true; changed; ) {
        changed = false;
        for (size_t k = 0; k < cd->nodes.n; k++) {
            TNodeId N = (TNodeId)cd->nodes.w[k];
            SlotSet fsl; memset(&fsl, 0, sizeof fsl);
            node_syntactic_free(N, &fsl);
            if (N == Q) { if (cd->rtype) expr_free(cd->rtype, cd->nparams, &fsl); if (cd->rlevel) expr_free(cd->rlevel, cd->nparams, &fsl); }
            decl_closure(&fsl);
            uint64_t before = TNSIDE(N)->free_slots;
            set_free_slots(N, &fsl);
            if (TNSIDE(N)->free_slots != before) changed = true;
        }
    }
}
#define SORTS(...) ((const PSort[]){ __VA_ARGS__ })

/* ---- §52 programs ---- */

static ExprId b_pappnot(ExprId i, void *c) { Cx *x = c; return CALL(TD_PAPPCONST, x->a, x->b, x->c, x->d, x->e, IVNOT(i)); }
static ExprId b_concat(ExprId i, void *c) {
    Cx *x = c;   /* a=l b=A c=x d=y e=z (p, q in f? use two) */
    ExprId l = x->a, A = x->b, xx = x->c, y = x->d, z = x->e;
    ExprId p = P(5), q = P(6);
    size_t jl = newlocal(PS_INTERVAL);
    ExprId faces[2] = { FCEND(i, 0), FCEND(i, 1) };
    ExprId terms[2] = { xx, CALL(TD_PAPPCONST, l, A, y, z, q, L(jl)) };
    return nCOMP(l, jl, A, FCOR(faces[0], faces[1]), nSYSTEM(2, faces, terms), CALL(TD_PAPPCONST, l, A, xx, y, p, i));
}

static ExprId b_ideq_inner(ExprId i, void *c) {
    Cx *x = c; /* a=l b=X c=fx d=y e=p f=fib */
    size_t jl = newlocal(PS_INTERVAL);
    ExprId first = CALL(TD_PAPPCONST, x->a, x->b, x->c, x->d, x->e, IVNOT(i));
    ExprId second = nPLAM(jl, CALL(TD_PAPPCONST, x->a, x->b, x->c, x->d, x->e, IVOR(IVNOT(i), L(jl))));
    return nPAIR_AT(x->a, x->f, first, second);
}
static ExprId b_ext_tube(ExprId j, void *c) { Cx *x = c; return CALL(TD_PAPPCONST, x->a, x->b, x->c, x->d, nAPP(x->e, x->d), j); }
static ExprId b_lineeq_fam(ExprId i, void *c) { Cx *x = c; return CALL(TD_EQUIV, x->a, x->a, x->b, AP1(x->c, i)); }
static ExprId b_ua(ExprId i, void *c) {
    Cx *x = c; /* a=l b=X c=Y d=e */
    ExprId faces[2] = { FCEND(i, 0), FCEND(i, 1) };
    ExprId Ts[2] = { x->b, x->c }, es[2] = { x->d, CALL(TD_IDEQUIV, x->a, x->c) };
    return nGLUE(x->a, x->c, FCOR(faces[0], faces[1]), nSYSTEM(2, faces, Ts), nSYSTEM(2, faces, es));
}
/* composition clause helpers */
static ExprId b_pi_Dneg(ExprId j, void *c) { Cx *x = c; return AP1(x->a, IVNOT(j)); }
static ExprId t_univ(ExprId j, void *c) { (void)j; return nUNIV(((Cx *)c)->t); }
static ExprId b_empty(ExprId j, void *c) { (void)j; (void)c; return nSYSTEM(0, NULL, NULL); }
static ExprId t_fam_at(ExprId j, void *c) { return AP1(((Cx *)c)->t, j); }
static ExprId t_const(ExprId j, void *c) { (void)j; return ((Cx *)c)->t; }
static ExprId t_fam_neg(ExprId j, void *c) { return AP1(((Cx *)c)->t, IVNOT(j)); }
static ExprId b_pi_V(ExprId r, void *c) {
    Cx *x = c; /* a=m b=D c=x1 */
    Cx d = { x->b, 0, 0, 0, 0, 0, x->a };
    ExprId Dneg = DSCOPE1(b_pi_Dneg, t_univ, &d, LSUCC(x->a), guard_now());
    Cx e0 = { Dneg, 0, 0, 0, 0, 0, Dneg };
    ExprId empty = DSCOPE1(b_empty, t_fam_at, &e0, x->a, FCF());          /* the empty tube: family D<¬j> under false */
    return CALL(TD_FILL, x->a, Dneg, FCF(), empty, x->c, IVNOT(r));
}
static ExprId b_sig_fstu(ExprId i, void *c) { Cx *x = c; return nFST(AP1(x->a, i)); }
static ExprId b_sig_Afill(ExprId r, void *c) {
    Cx *x = c; /* a=m b=D c=phi d=u e=cap */
    Cx both = { x->d, 0, 0, 0, 0, 0, x->b };
    ExprId fstu = DSCOPE1(b_sig_fstu, t_fam_at, &both, x->a, FCAND(KAPPA(), x->c));
    return CALL(TD_FILL, x->a, x->b, x->c, fstu, nFST(x->e), r);
}
static ExprId b_glue_base(ExprId i, void *c) { Cx *x = c; /* a=n b=A c=alpha d=T e=e f=u */ return nUNGLUE(x->a, AP1(x->b, i), AP1(x->c, i), AP1(x->d, i), AP1(x->e, i), AP1(x->f, i)); }
static ExprId b_glue_Afill(ExprId r, void *c) { Cx *x = c; /* a=n b=A c=psi d=baseTube e=a0 */ return CALL(TD_FILL, x->a, x->b, x->c, x->d, x->e, r); }
static ExprId b_glue_Tfill(ExprId r, void *c) { Cx *x = c; /* a=n b=T c=psi d=u e=cap */ return CALL(TD_FILL, x->a, x->b, x->c, x->d, x->e, r); }
static ExprId b_glue_omega(ExprId q, void *c) {
    Cx *x = c; /* a=n b=A c=psi d=Afill e=e f=Tfill ; a0 via P? pass through extra: use P(6) cap? we need a0: stored in x->... */
    size_t il = newlocal(PS_INTERVAL);
    ExprId i = L(il);
    ExprId faces[3] = { x->c, FCEND(q, 0), FCEND(q, 1) };
    ExprId terms[3] = { AP1(x->d, i), nAPP(CALL(TD_EQUIVMAP, x->a, x->a, AP1(x->t, i), AP1(x->b, i), AP1(x->e, i)), AP1(x->f, i)), AP1(x->d, i) };
    extern ExprId glue_a0_expr;
    return nCOMP(x->a, il, AP1(x->b, i), FCOR(x->c, FCOR(faces[1], faces[2])), nSYSTEM(3, faces, terms), glue_a0_expr);
}
ExprId glue_a0_expr;
static ExprId b_glue_repair(ExprId q, void *c) {
    Cx *x = c; /* a=n b=A1 c=alpha1 d=psi e=f1t1 (App(EquivMap(e1),t1)) f=a1 ; p via global */
    extern ExprId glue_p_expr;
    ExprId faces[2] = { x->c, x->d };
    ExprId terms[2] = { CALL(TD_PAPPCONST, x->a, x->b, x->e, x->f, glue_p_expr, IVNOT(q)), x->f };
    return nSYSTEM(2, faces, terms);
}
ExprId glue_p_expr;
static ExprId b_univ_rev(ExprId j, void *c) { Cx *x = c; return AP1(x->a, IVNOT(j)); }
static ExprId b_down_fam(ExprId i, void *c) {
    Cx *x = c; /* a=lA b=A c=t d=D e=x f=e ; z separately */
    size_t jl = newlocal(PS_INTERVAL);
    ExprId xi_ = CALL(TD_PAPPCONST, x->a, x->b, x->c, x->e, x->f, IVNOT(i));
    ExprId ei = nPLAM(jl, CALL(TD_PAPPCONST, x->a, x->b, x->c, x->e, x->f, IVAND(IVNOT(i), L(jl))));
    return AP2(x->d, xi_, ei);
}

static void register_library(void) {
    /* PathConst(l, A, lft, r) = PathP(j. A, lft, r) */
    begin(TD_PATHCONST, "PathConst", 4, SORTS(PS_LEVEL, PS_REF, PS_REF, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(2, P(1), P(0)); ptype(3, P(1), P(0));
    rtype(nUNIV(P(0)), LSUCC(P(0)));
    { size_t j = newlocal(PS_INTERVAL); finish(nPATH(P(0), j, P(1), P(2), P(3))); }
    /* Refl(l, A, a) = PLam(j. a) */
    begin(TD_REFL, "Refl", 3, SORTS(PS_LEVEL, PS_REF, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(2, P(1), P(0));
    rtype(CALL(TD_PATHCONST, P(0), P(1), P(2), P(2)), P(0));
    { size_t j = newlocal(PS_INTERVAL); finish(nPLAM(j, P(2))); }
    /* PAppConst(l, A, lft, r, p, s) */
    begin(TD_PAPPCONST, "PAppConst", 6, SORTS(PS_LEVEL, PS_REF, PS_REF, PS_REF, PS_REF, PS_INTERVAL));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(2, P(1), P(0)); ptype(3, P(1), P(0)); ptype(4, CALL(TD_PATHCONST, P(0), P(1), P(2), P(3)), P(0));
    rtype(P(1), P(0));
    { size_t j = newlocal(PS_INTERVAL); finish(nPAPP(P(0), j, P(1), P(2), P(3), P(4), P(5))); }
    /* Reverse(l, A, lft, r, p) = PLam(i. PAppConst(A,l,r,p,not i)) */
    begin(TD_REVERSE, "Reverse", 5, SORTS(PS_LEVEL, PS_REF, PS_REF, PS_REF, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(2, P(1), P(0)); ptype(3, P(1), P(0)); ptype(4, CALL(TD_PATHCONST, P(0), P(1), P(2), P(3)), P(0));
    rtype(CALL(TD_PATHCONST, P(0), P(1), P(3), P(2)), P(0));
    { size_t i = newlocal(PS_INTERVAL); Cx c = { P(0), P(1), P(2), P(3), P(4), 0 }; finish(nPLAM(i, b_pappnot(L(i), &c))); }
    /* Concat(l, A, x, y, z, p, q) */
    begin(TD_CONCAT, "Concat", 7, SORTS(PS_LEVEL, PS_REF, PS_REF, PS_REF, PS_REF, PS_REF, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(2, P(1), P(0)); ptype(3, P(1), P(0)); ptype(4, P(1), P(0));
    ptype(5, CALL(TD_PATHCONST, P(0), P(1), P(2), P(3)), P(0)); ptype(6, CALL(TD_PATHCONST, P(0), P(1), P(3), P(4)), P(0));
    rtype(CALL(TD_PATHCONST, P(0), P(1), P(2), P(4)), P(0));
    { size_t i = newlocal(PS_INTERVAL); Cx c = { P(0), P(1), P(2), P(3), P(4), 0 }; finish(nPLAM(i, b_concat(L(i), &c))); }
    /* Fun(l, m, X, Y) = Pi(x:X. Y) */
    begin(TD_FUN, "Fun", 4, SORTS(PS_LEVEL, PS_LEVEL, PS_REF, PS_REF));
    ptype(2, nUNIV(P(0)), LSUCC(P(0))); ptype(3, nUNIV(P(1)), LSUCC(P(1)));
    rtype(nUNIV(LMAX(P(0), P(1))), LSUCC(LMAX(P(0), P(1))));
    { size_t x = newlocal(PS_REF); finish(nPI(P(0), P(1), x, P(2), P(3))); }
    /* Contr(l, X) = Sigma(c:X. Pi(x:X. PathConst(X,c,x))) */
    begin(TD_CONTR, "Contr", 2, SORTS(PS_LEVEL, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0)));
    rtype(nUNIV(P(0)), LSUCC(P(0)));
    { size_t c = newlocal(PS_REF), x = newlocal(PS_REF); finish(nSIGMA(P(0), P(0), c, P(1), nPI(P(0), P(0), x, P(1), CALL(TD_PATHCONST, P(0), P(1), L(c), L(x))))); }
    /* Fib(l, m, X, Y, f, y) = Sigma(x:X. PathConst(Y, App(f,x), y)) */
    begin(TD_FIB, "Fib", 6, SORTS(PS_LEVEL, PS_LEVEL, PS_REF, PS_REF, PS_REF, PS_REF));
    ptype(2, nUNIV(P(0)), LSUCC(P(0))); ptype(3, nUNIV(P(1)), LSUCC(P(1))); ptype(4, CALL(TD_FUN, P(0), P(1), P(2), P(3)), LMAX(P(0), P(1))); ptype(5, P(3), P(1));
    rtype(nUNIV(LMAX(P(0), P(1))), LSUCC(LMAX(P(0), P(1))));
    { size_t x = newlocal(PS_REF); finish(nSIGMA(P(0), P(1), x, P(2), CALL(TD_PATHCONST, P(1), P(3), nAPP(P(4), L(x)), P(5)))); }
    /* Equiv(l, m, X, Y) = Sigma(f:Fun(X,Y). Pi(y:Y. Contr(Fib(X,Y,f,y)))) */
    begin(TD_EQUIV, "Equiv", 4, SORTS(PS_LEVEL, PS_LEVEL, PS_REF, PS_REF));
    ptype(2, nUNIV(P(0)), LSUCC(P(0))); ptype(3, nUNIV(P(1)), LSUCC(P(1)));
    rtype(nUNIV(LMAX(P(0), P(1))), LSUCC(LMAX(P(0), P(1))));
    { size_t f = newlocal(PS_REF), y = newlocal(PS_REF); ExprId mx = LMAX(P(0), P(1));
      finish(nSIGMA(mx, mx, f, CALL(TD_FUN, P(0), P(1), P(2), P(3)), nPI(P(1), mx, y, P(3), CALL(TD_CONTR, mx, CALL(TD_FIB, P(0), P(1), P(2), P(3), L(f), L(y)))))); }
    /* IdFun(l, X) = Lam(x:X. x) */
    begin(TD_IDFUN, "IdFun", 2, SORTS(PS_LEVEL, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0)));
    rtype(CALL(TD_FUN, P(0), P(0), P(1), P(1)), P(0));
    { size_t x = newlocal(PS_REF); finish(nLAM(P(0), x, P(1), L(x))); }
    /* EquivMap(l, m, X, Y, e) = Fst(e) ; EquivContr(l, m, X, Y, e, y) = App(Snd(e), y) */
    begin(TD_EQUIVMAP, "EquivMap", 5, SORTS(PS_LEVEL, PS_LEVEL, PS_REF, PS_REF, PS_REF));
    ptype(2, nUNIV(P(0)), LSUCC(P(0))); ptype(3, nUNIV(P(1)), LSUCC(P(1))); ptype(4, CALL(TD_EQUIV, P(0), P(1), P(2), P(3)), LMAX(P(0), P(1)));
    rtype(CALL(TD_FUN, P(0), P(1), P(2), P(3)), LMAX(P(0), P(1)));
    finish(nFST(P(4)));
    begin(TD_EQUIVCONTR, "EquivContr", 6, SORTS(PS_LEVEL, PS_LEVEL, PS_REF, PS_REF, PS_REF, PS_REF));
    ptype(2, nUNIV(P(0)), LSUCC(P(0))); ptype(3, nUNIV(P(1)), LSUCC(P(1))); ptype(4, CALL(TD_EQUIV, P(0), P(1), P(2), P(3)), LMAX(P(0), P(1))); ptype(5, P(3), P(1));
    rtype(CALL(TD_CONTR, LMAX(P(0), P(1)), CALL(TD_FIB, P(0), P(1), P(2), P(3), CALL(TD_EQUIVMAP, P(0), P(1), P(2), P(3), P(4)), P(5))), LMAX(P(0), P(1)));
    finish(nAPP(nSND(P(4)), P(5)));
    /* IdEquiv(l, X) */
    begin(TD_IDEQUIV, "IdEquiv", 2, SORTS(PS_LEVEL, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0)));
    rtype(CALL(TD_EQUIV, P(0), P(0), P(1), P(1)), P(0));
    { ExprId l = P(0), X = P(1);
      ExprId f = CALL(TD_IDFUN, l, X);
      size_t y = newlocal(PS_REF), w = newlocal(PS_REF), i = newlocal(PS_INTERVAL);
      ExprId fib = CALL(TD_FIB, l, l, X, X, f, L(y));
      ExprId p = nSND(L(w)), fx = nAPP(f, nFST(L(w)));
      Cx c = { l, X, fx, L(y), p, fib };
      ExprId contraction = nLAM(l, w, fib, nPLAM(i, b_ideq_inner(L(i), &c)));
      ExprId centre = nPAIR_AT(l, fib, L(y), CALL(TD_REFL, l, X, L(y)));
      finish(nPAIR_AT(l, CALL(TD_EQUIV, l, l, X, X), f, nLAM(l, y, X, nPAIR_AT(l, CALL(TD_CONTR, l, fib), centre, contraction)))); }
    /* Fill(l, A:[i]U_l, phi, u:[i]A<i> on phi, cap:A<0>, r) */
    begin(TD_FILL, "Fill", 6, SORTS(PS_LEVEL, PS_SCOPE, PS_FACE, PS_SCOPE, PS_REF, PS_INTERVAL));
    ptype(4, AP1(P(1), IV0()), P(0));
    { Cx cu = { 0, 0, 0, 0, 0, 0, P(0) }, ca = { 0, 0, 0, 0, 0, 0, P(1) };
      psig(1, SIG_DIM1(t_univ, &cu, LSUCC(P(0)), KAPPA())); psig(3, SIG_DIM1(t_fam_at, &ca, P(0), FCAND(KAPPA(), P(2))));
      rtype(AP1(P(1), P(5)), P(0)); }
    { size_t j = newlocal(PS_INTERVAL); ExprId rj = IVAND(P(5), L(j)); ExprId r0 = FCEND(P(5), 0);
      ExprId faces[2] = { P(2), r0 }, terms[2] = { AP1(P(3), rj), P(4) };
      finish(nCOMP(P(0), j, AP1(P(1), rj), FCOR(P(2), r0), nSYSTEM(2, faces, terms), P(4))); }
    /* HComp(l, X, phi, u:[j]X on phi, cap) */
    begin(TD_HCOMP, "HComp", 5, SORTS(PS_LEVEL, PS_REF, PS_FACE, PS_SCOPE, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(4, P(1), P(0));
    { Cx cx = { 0, 0, 0, 0, 0, 0, P(1) }; psig(3, SIG_DIM1(t_const, &cx, P(0), FCAND(KAPPA(), P(2)))); rtype(P(1), P(0)); }
    { size_t j = newlocal(PS_INTERVAL); finish(nCOMP(P(0), j, P(1), P(2), AP1(P(3), L(j)), P(4))); }
    /* Coe(l, A:[i]U_l, cap:A<0>) */
    begin(TD_COE, "Coe", 3, SORTS(PS_LEVEL, PS_SCOPE, PS_REF));
    ptype(2, AP1(P(1), IV0()), P(0));
    { Cx cu = { 0, 0, 0, 0, 0, 0, P(0) }; psig(1, SIG_DIM1(t_univ, &cu, LSUCC(P(0)), KAPPA())); rtype(AP1(P(1), IV1()), P(0)); }
    { size_t i = newlocal(PS_INTERVAL); finish(nCOMP(P(0), i, AP1(P(1), L(i)), FCF(), nSYSTEM(0, NULL, NULL), P(2))); }
    /* ExtendContr(l, X, c, k, theta, v on theta) */
    begin(TD_EXTENDCONTR, "ExtendContr", 6, SORTS(PS_LEVEL, PS_REF, PS_REF, PS_REF, PS_FACE, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(2, P(1), P(0)); ptype_on(5, P(1), P(0), FCAND(KAPPA(), P(4)));
    { size_t xk = newlocal(PS_REF); ptype(3, nPI(P(0), P(0), xk, P(1), CALL(TD_PATHCONST, P(0), P(1), P(2), L(xk))), P(0)); }
    rtype(P(1), P(0));
    { Cx c = { P(0), P(1), P(2), P(5), P(3), 0, P(1) };
      ExprId tube = DSCOPE1(b_ext_tube, t_const, &c, P(0), FCAND(KAPPA(), P(4)));
      finish(CALL(TD_HCOMP, P(0), P(1), P(4), tube, P(2))); }
    /* LineEquiv(l, X:[i]U_l) = Coe([i]. Equiv(X<0>, X<i>), IdEquiv(X<0>)) */
    begin(TD_LINEEQUIV, "LineEquiv", 2, SORTS(PS_LEVEL, PS_SCOPE));
    { Cx cu = { 0, 0, 0, 0, 0, 0, P(0) }; psig(1, SIG_DIM1(t_univ, &cu, LSUCC(P(0)), KAPPA())); rtype(CALL(TD_EQUIV, P(0), P(0), AP1(P(1), IV0()), AP1(P(1), IV1())), P(0)); }
    { ExprId X0 = AP1(P(1), IV0()); Cx c = { P(0), X0, P(1), 0, 0, 0, 0 };
      c.t = P(0);
      ExprId fam = DSCOPE1(b_lineeq_fam, t_univ, &c, LSUCC(P(0)), guard_now());
      finish(CALL(TD_COE, P(0), fam, CALL(TD_IDEQUIV, P(0), X0))); }
    /* Ua(l, X, Y, e) */
    begin(TD_UA, "Ua", 4, SORTS(PS_LEVEL, PS_REF, PS_REF, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(2, nUNIV(P(0)), LSUCC(P(0))); ptype(3, CALL(TD_EQUIV, P(0), P(0), P(1), P(2)), P(0));
    rtype(CALL(TD_PATHCONST, LSUCC(P(0)), nUNIV(P(0)), P(1), P(2)), LSUCC(P(0)));
    { size_t i = newlocal(PS_INTERVAL); Cx c = { P(0), P(1), P(2), P(3), 0, 0 }; finish(nPLAM(i, b_ua(L(i), &c))); }

    /* ---- §53 composition clauses ---- */
    /* PiComp(m, n, D:[i]U_m, E:[i,x:D<i>]U_n, phi, u:[i]Pi on phi, cap) */
    begin(TD_PICOMP, "PiComp", 7, SORTS(PS_LEVEL, PS_LEVEL, PS_SCOPE, PS_SCOPE, PS_FACE, PS_SCOPE, PS_REF));
    { Cx sg = { P(0), P(1), P(2), P(3), 0, 0, P(0) }, sn = { 0, 0, P(2), 0, 0, 0, P(1) };
      psig(2, SIG_DIM1(t_univ, &sg, LSUCC(P(0)), KAPPA()));
      psig(3, SIG_DIM_TERM(r_E_dom, P(0), r_univ2, &sn, LSUCC(P(1)), KAPPA()));
      psig(5, SIG_DIM1(r_pi_at, &sg, LMAX(P(0), P(1)), FCAND(KAPPA(), P(4))));
      ptype(6, r_pi_at(IV0(), &sg), LMAX(P(0), P(1)));
      rtype(r_pi_at(IV1(), &sg), LMAX(P(0), P(1))); }
    { ExprId m = P(0), n = P(1), D = P(2), E = P(3), phi = P(4), u = P(5), cap = P(6);
      size_t x1 = newlocal(PS_REF), i = newlocal(PS_INTERVAL);
      Cx c = { m, D, L(x1), 0, 0, 0, D };
      ExprId V = DSCOPE1(b_pi_V, t_fam_neg, &c, m, guard_now());
      ExprId Vi = AP1(V, L(i)), V0 = AP1(V, IV0());
      finish(nLAM(m, x1, AP1(D, IV1()), nCOMP(n, i, AP2(E, L(i), Vi), phi, nAPP(AP1(u, L(i)), Vi), nAPP(cap, V0)))); }
    /* SigmaComp(m, n, D, E, phi, u, cap) */
    begin(TD_SIGMACOMP, "SigmaComp", 7, SORTS(PS_LEVEL, PS_LEVEL, PS_SCOPE, PS_SCOPE, PS_FACE, PS_SCOPE, PS_REF));
    { Cx sg = { P(0), P(1), P(2), P(3), 0, 0, P(0) }, sn = { 0, 0, P(2), 0, 0, 0, P(1) };
      psig(2, SIG_DIM1(t_univ, &sg, LSUCC(P(0)), KAPPA()));
      psig(3, SIG_DIM_TERM(r_E_dom, P(0), r_univ2, &sn, LSUCC(P(1)), KAPPA()));
      psig(5, SIG_DIM1(r_sigma_at, &sg, LMAX(P(0), P(1)), FCAND(KAPPA(), P(4))));
      ptype(6, r_sigma_at(IV0(), &sg), LMAX(P(0), P(1)));
      rtype(r_sigma_at(IV1(), &sg), LMAX(P(0), P(1))); }
    { ExprId m = P(0), n = P(1), D = P(2), E = P(3), phi = P(4), u = P(5), cap = P(6);
      size_t i = newlocal(PS_INTERVAL), x1 = newlocal(PS_REF);
      Cx c = { m, D, phi, u, cap, 0, D };
      ExprId Afill = DSCOPE1(b_sig_Afill, t_fam_at, &c, m, guard_now());
      ExprId second = nCOMP(n, i, AP2(E, L(i), AP1(Afill, L(i))), phi, nSND(AP1(u, L(i))), nSND(cap));
      ExprId Sg1 = nSIGMA(m, n, x1, AP1(D, IV1()), AP2(E, IV1(), L(x1)));
      finish(nPAIR_AT(LMAX(m, n), Sg1, AP1(Afill, IV1()), second)); }
    /* PathComp(n, B:[i,j]U_n, left:[i]B<i,0>, right:[i]B<i,1>, phi, u, cap) */
    begin(TD_PATHCOMP, "PathComp", 7, SORTS(PS_LEVEL, PS_SCOPE, PS_SCOPE, PS_SCOPE, PS_FACE, PS_SCOPE, PS_REF));
    { Cx sg = { P(0), P(1), P(2), P(3), 0, 0, P(0) };
      psig(1, SIG_DIM2(r_univ2, &sg, LSUCC(P(0)), KAPPA()));
      psig(2, SIG_DIM1(r_B_at0, &sg, P(0), KAPPA()));
      psig(3, SIG_DIM1(r_B_at1, &sg, P(0), KAPPA()));
      psig(5, SIG_DIM1(r_path_at, &sg, P(0), FCAND(KAPPA(), P(4))));
      ptype(6, r_path_at(IV0(), &sg), P(0));
      rtype(r_path_at(IV1(), &sg), P(0)); }
    { ExprId n = P(0), B = P(1), left = P(2), right = P(3), phi = P(4), u = P(5), cap = P(6);
      size_t j = newlocal(PS_INTERVAL), i = newlocal(PS_INTERVAL), k1 = newlocal(PS_INTERVAL), k2 = newlocal(PS_INTERVAL);
      ExprId faces[3] = { phi, FCEND(L(j), 0), FCEND(L(j), 1) };
      ExprId terms[3] = { nPAPP(n, k1, AP2(B, L(i), L(k1)), AP1(left, L(i)), AP1(right, L(i)), AP1(u, L(i)), L(j)), AP1(left, L(i)), AP1(right, L(i)) };
      ExprId capj = nPAPP(n, k2, AP2(B, IV0(), L(k2)), AP1(left, IV0()), AP1(right, IV0()), cap, L(j));
      finish(nPLAM(j, nCOMP(n, i, AP2(B, L(i), L(j)), FCOR(phi, FCOR(faces[1], faces[2])), nSYSTEM(3, faces, terms), capj))); }
    /* GlueComp(n, A:[i]U_n, alpha:[i]Face, T:[i]U_n on alpha, e:[i]Equiv(T,A) on alpha, psi, u, cap) */
    begin(TD_GLUECOMP, "GlueComp", 8, SORTS(PS_LEVEL, PS_SCOPE, PS_SCOPE, PS_SCOPE, PS_SCOPE, PS_FACE, PS_SCOPE, PS_REF));
    { Cx sg = { P(0), P(1), P(2), P(3), P(4), 0, P(0) };
      psig(1, SIG_DIM1(t_univ, &sg, LSUCC(P(0)), KAPPA()));
      psig(2, SIG_FACE1(KAPPA()));
      psig(3, SIG_DIM1_G(t_univ, r_guard_alpha, &sg, LSUCC(P(0))));
      psig(4, SIG_DIM1_G(r_equiv_TA, r_guard_alpha, &sg, P(0)));
      psig(6, SIG_DIM1(r_glue_at, &sg, P(0), FCAND(KAPPA(), P(5))));
      ptype(7, r_glue_at(IV0(), &sg), P(0));
      rtype(r_glue_at(IV1(), &sg), P(0)); }
    { ExprId n = P(0), A = P(1), alpha = P(2), T = P(3), e = P(4), psi = P(5), u = P(6), cap = P(7);
      ExprId A0 = AP1(A, IV0()), A1 = AP1(A, IV1()), T0 = AP1(T, IV0()), T1 = AP1(T, IV1()), e0 = AP1(e, IV0()), e1 = AP1(e, IV1());
      ExprId alpha0 = AP1(alpha, IV0()), alpha1 = AP1(alpha, IV1()), u1 = AP1(u, IV1());
      ExprId a0 = nUNGLUE(n, A0, alpha0, T0, e0, cap);
      glue_a0_expr = a0;
      Cx bt = { n, A, alpha, T, e, u, A };
      ExprId baseTube = DSCOPE1(b_glue_base, t_fam_at, &bt, n, FCAND(KAPPA(), psi));
      Cx af = { n, A, psi, baseTube, a0, 0, A };
      ExprId Afill = DSCOPE1(b_glue_Afill, t_fam_at, &af, n, guard_now());
      ExprId a1 = AP1(Afill, IV1());
      ExprId delta = FORALL(alpha);
      /* under delta */
      ExprId saved = under_face; under_face = delta;
      Cx tf = { n, T, psi, u, cap, 0, T };
      ExprId Tfill = DSCOPE1(b_glue_Tfill, t_fam_at, &tf, n, guard_now());
      ExprId t1prime = AP1(Tfill, IV1());
      size_t q = newlocal(PS_INTERVAL);
      Cx om = { n, A, psi, Afill, e, Tfill, T };
      ExprId omega = nPLAM(q, b_glue_omega(L(q), &om));
      under_face = saved;
      /* under alpha1 */
      saved = under_face; under_face = alpha1;
      ExprId f1 = CALL(TD_EQUIVMAP, n, n, T1, A1, e1);
      ExprId fibre = CALL(TD_FIB, n, n, T1, A1, f1, a1);
      ExprId pf[2] = { delta, psi };
      ExprId pt[2] = { nPAIR_AT(n, fibre, t1prime, omega), nPAIR_AT(n, fibre, u1, CALL(TD_REFL, n, A1, a1)) };
      ExprId partial = nSYSTEM(2, pf, pt);
      ExprId contraction = CALL(TD_EQUIVCONTR, n, n, T1, A1, e1, a1);
      ExprId extension = CALL(TD_EXTENDCONTR, n, fibre, nFST(contraction), nSND(contraction), FCOR(delta, psi), partial);
      ExprId t1 = nFST(extension), p = nSND(extension);
      under_face = saved;
      glue_p_expr = p;
      Cx rp = { n, A1, alpha1, psi, nAPP(f1, t1), a1, A1 };
      ExprId repairTube = DSCOPE1(b_glue_repair, t_const, &rp, n, FCAND(KAPPA(), FCOR(alpha1, psi)));
      ExprId repaired = CALL(TD_HCOMP, n, A1, FCOR(alpha1, psi), repairTube, a1);
      finish(nGLUEINTRO(n, A1, alpha1, T1, e1, t1, repaired)); }
    /* UniverseComp(l, phi, types:[i]U_l on phi, cap:U_l) */
    begin(TD_UNIVERSECOMP, "UniverseComp", 4, SORTS(PS_LEVEL, PS_FACE, PS_SCOPE, PS_REF));
    ptype(3, nUNIV(P(0)), LSUCC(P(0)));
    { Cx cu = { 0, 0, 0, 0, 0, 0, P(0) }; psig(2, SIG_DIM1(t_univ, &cu, LSUCC(P(0)), FCAND(KAPPA(), P(1)))); rtype(nUNIV(P(0)), LSUCC(P(0))); }
    { ExprId l = P(0), phi = P(1), types = P(2), cap = P(3);
      ExprId saved = under_face; under_face = phi;
      Cx c = { types, 0, 0, 0, 0, 0, l };
      ExprId reversed = DSCOPE1(b_univ_rev, t_univ, &c, LSUCC(l), guard_now());
      ExprId equivalence = CALL(TD_LINEEQUIV, l, reversed);
      under_face = saved;
      finish(nGLUE(l, cap, phi, AP1(types, IV1()), equivalence)); }
    /* Down(l, lA, A, t, D:[x:A, e:Path(A,t,x)]U_l, x, e, z) = Coe([i]. D<e@¬i, ⟨j⟩e@(¬i∧j)>, z) */
    begin(TD_DOWN, "Down", 8, SORTS(PS_LEVEL, PS_LEVEL, PS_REF, PS_REF, PS_SCOPE, PS_REF, PS_REF, PS_REF));
    ptype(2, nUNIV(P(1)), LSUCC(P(1))); ptype(3, P(2), P(1)); ptype(5, P(2), P(1)); ptype(6, CALL(TD_PATHCONST, P(1), P(2), P(3), P(5)), P(1));
    ptype(7, AP2(P(4), P(5), P(6)), P(0));
    { Cx sd = { P(1), P(2), P(3), 0, 0, 0, P(0) };
      psig(4, SIG_TERM2(P(2), P(1), r_down_etype, P(1), r_down_res, &sd, LSUCC(P(0)), KAPPA()));
      rtype(AP2(P(4), P(3), CALL(TD_REFL, P(1), P(2), P(3))), P(0)); }
    { ExprId l = P(0), lA = P(1), A = P(2), t = P(3), D = P(4), x = P(5), e = P(6), z = P(7);
      Cx c = { lA, A, t, D, x, e, l };
      ExprId fam = DSCOPE1(b_down_fam, t_univ, &c, LSUCC(l), guard_now());
      finish(CALL(TD_COE, l, fam, z)); }
}

/* the fixed library is registered once per machine lifetime, eagerly at
 * machine initialization (machine_init → templates_init, under the service
 * owner): no engine step ever performs or waits for the registration, and the
 * check in template_call is one bounded flag test. A concurrent first caller
 * outside machine initialization (none in the machine's own paths) waits on
 * the condition: it is never inside an engine step. */
void templates_init(void) {
    static pthread_mutex_t once = PTHREAD_MUTEX_INITIALIZER;
    static pthread_cond_t done_cv = PTHREAD_COND_INITIALIZER;
    static int registering;
    if (__atomic_load_n(&TPL.init, __ATOMIC_ACQUIRE)) return;
    pthread_mutex_lock(&once);
    while (!TPL.init && registering) kf_wait_plain(&done_cv, &once);
    if (TPL.init) { pthread_mutex_unlock(&once); return; }
    registering = 1; memset(&TPL, 0, sizeof TPL); pthread_mutex_init(&TPL.mu, NULL);
    pthread_mutex_unlock(&once);
    register_library();
    pthread_mutex_lock(&once); __atomic_store_n(&TPL.init, true, __ATOMIC_RELEASE); registering = 0; pthread_cond_broadcast(&done_cv); pthread_mutex_unlock(&once);
}
void templates_free(void) {
    if (!TPL.init) return;
    for (size_t k = 0; k < TD_COUNT; k++) words_free(&TPL.defs[k].nodes);
    pthread_mutex_destroy(&TPL.mu);
    memset(&TPL, 0, sizeof TPL);
}

KF_DECL_EXT(template_call, TVal, template_call_PARAMS, Env env; const TDef *d; TVal r;)
KF_STEP(template_call) {
    KF_BEGIN(template_call);
    templates_init();   /* a flag test: the library was registered at machine initialization */
    F->d = &TPL.defs[F->def];
    require(F->nargs + 1 == F->d->nparams, "template_call arity (%s)", F->d->name);
    memset(&F->env, 0, sizeof F->env); F->env.defid = F->def; F->env.def = F->d;
    KF_CALL0(template_kappa, &F->env.val[0].id); F->env.val[0].sort = PS_FACE; F->env.has[0] = true;
    for (size_t k = 0; k < F->nargs; k++) { require(F->args[k].sort == F->d->sorts[k + 1], "template_call sort (%s, %zu)", F->d->name, k); F->env.val[k + 1] = F->args[k]; F->env.has[k + 1] = true; }
    KF_CALL(interp, &F->r, F->d->root, &F->env);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(template_call, TVal, template_call_PARAMS, template_call(TDefKind def, size_t nargs, const TVal *args))
