#include "template.h"
#include "eval.h"

/* ------------------------------------------------------------------ */
/* definitions                                                           */

#define MAXP 16
#define MAXL 48
#define MAXSLOT (MAXP + MAXL)

typedef struct {
    const char *name;
    size_t nparams;
    PSort sorts[MAXP];
    ExprId ptype[MAXP];            /* reference parameters: declared type expression (0 = none) */
    ExprId plevel[MAXP];           /* its level expression */
    ExprId psig[MAXP];             /* scope parameters: the expected contextual signature (a scope expression whose body is the result type) */
    ExprId pguard[MAXP];           /* a partial reference parameter's declared availability (0 = none) */
    size_t nlocals;
    PSort lsort[MAXL];
    ExprId ltype[MAXL], llevel[MAXL], lreq[MAXL];   /* declarations of term locals (constructor binders and scope locals) */
    Words nodes;                   /* every constructor node of the definition, in construction order */
    ExprId root;
    ExprId rtype, rlevel;          /* the declared result type of the program and its level */
    TNodeId root_node;             /* the root constructor node when the root is a node (0 when the root is a call) */
} TDef;

static struct { TDef defs[TD_COUNT]; uint64_t index_counter[TD_COUNT]; bool init; pthread_mutex_t mu; } TPL;

/* ------------------------------------------------------------------ */
/* expressions: interned records [kind, words...]                        */

enum {
    X_PARAM = 1, X_LOCAL, X_LEVEL, X_LSUCC, X_LMAX, X_LEVELS, X_LFIRST, X_NODE, X_CALL, X_SCOPE, X_APPLY, X_APPLY_TYPE, X_APPLY_GUARD,
    X_IV0, X_IV1, X_IVNOT, X_IVAND, X_IVOR, X_FCF, X_FCT, X_FCAND, X_FCOR, X_FCEND, X_FORALL,
    X_CONST            /* [X_CONST, sort, id]: a construction's closed field constant */
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
ExprId tnode_head_expr(TNodeId Q, int levels) { return levels ? node_levels_e(Q) : node_payload_e(Q); }
static void node_field(TNodeId Q, size_t k, FieldKind *kind, BinderSlot *bslot, ExprId *e);
ExprId tnode_field_expr(TNodeId Q, size_t k) { FieldKind kd; BinderSlot bs; ExprId e; node_field(Q, k, &kd, &bs, &e); return e; }
static void node_binder(TNodeId Q, BinderSlot s, Sort *sort, FieldIndex *domfield, size_t *lslot);
/* a template node's binder field: the environment slot of the binder's local
 * and the field's recipe */
/* a node's binder field (a construction or a template program alike): the
 * environment slot of the binder's local — after the node's parameters — and
 * the field's expression */
static size_t node_param_count(TNodeId Q);
void tnode_template_binder(TNodeId Q, BinderSlot slot, FieldIndex field, uint64_t *env_slot, ExprId *body_e) {
    Sort so; FieldIndex df; size_t lslot; node_binder(Q, slot, &so, &df, &lslot);
    FieldKind kd; BinderSlot bs; node_field(Q, field, &kd, &bs, body_e);
    require(bs == slot, "field is not under this binder");
    *env_slot = node_param_count(Q) + lslot;
}
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
    case X_LEVEL: case X_IV0: case X_IV1: case X_FCF: case X_FCT: case X_CONST: break;
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
static size_t node_param_count(TNodeId Q);
static bool node_construction(TNodeId Q);
/* the free slots of a node: a construction's are its parameters; a template
 * node's were closed at registration */
static void node_free_list(TNodeId Q, size_t *n, const uint64_t **w) {
    if (!node_construction(Q)) { *w = interner_get(&M.keys, TNSIDE(Q)->free_slots, n); return; }
    Words s; words_init(&s); size_t np = node_param_count(Q);
    for (size_t k = 0; k < np; k++) words_push(&s, k);
    *w = interner_get(&M.keys, interner_intern(&M.keys, s.w, s.n, NULL), n); words_free(&s);
}

/* ------------------------------------------------------------------ */
/* environments and interpretation (as families, below)                 */


/* a reference's environment is its interpretation record [def, (slot, sort,
 * id)*] restricted to the node's free slots */
static const uint64_t *tenv_words(TEnvId E, size_t *n) { const uint64_t *w = interner_get(&M.keys, E, n); (*n)--; return w + 1; }
size_t tenv_size(TEnvId E) { size_t n; (void)tenv_words(E, &n); return n / 3; }
void tenv_entry(TEnvId E, size_t k, uint64_t *slot, TVal *v) { size_t n; const uint64_t *w = tenv_words(E, &n); *slot = w[3 * k]; v->sort = (PSort)w[3 * k + 1]; v->id = w[3 * k + 2]; }

/* An interpretation environment: the interned record [def, (slot, sort, id)*]
 * in slot order. An interpreted value is the interned pair [sort, id]. */
static uint64_t tvrec(PSort sort, uint64_t id) { uint64_t w[2] = { sort, id }; return interner_intern(&M.keys, w, 2, NULL); }
static TVal tvget(uint64_t rec) { size_t n; const uint64_t *w = interner_get(&M.keys, rec, &n); TVal v = { (PSort)w[0], w[1] }; return v; }
static uint64_t envrec_host(TDefId def, size_t n, const uint64_t *slots, const TVal *vals) {
    /* slots in increasing order */
    Words w; words_init(&w); words_push(&w, def);
    for (size_t k = 0; k < n; k++) { words_push(&w, slots[k]); words_push(&w, vals[k].sort); words_push(&w, vals[k].id); }
    uint64_t er = interner_intern(&M.keys, w.w, w.n, NULL);
    words_free(&w);
    return er;
}

/* ------------------------------------------------------------------ */
/* constructions: nodes with closed constant fields (template.h)          */

ExprId expr_const(PSort sort, uint64_t id) { uint64_t w[3] = { X_CONST, sort, id }; return xi(3, w); }
ExprId expr_level(uint64_t n) { return x1(X_LEVEL, n); }
static bool node_construction(TNodeId Q) { return tnode_def(Q) == 0; }
bool tnode_is_construction(TNodeId Q) { return node_construction(Q); }
static size_t node_param_count(TNodeId Q) { size_t n; return node_construction(Q) ? (size_t)nw(Q, &n)[1] : TPL.defs[tnode_def(Q)].nparams; }
bool tview_is_construction(RefId t) { return node_construction(ref_tnode(t)); }
size_t tnode_nparams(TNodeId Q) { require(node_construction(Q), "not a construction node"); size_t n; return (size_t)nw(Q, &n)[1]; }
static const uint64_t *node_ptab(TNodeId Q) { const uint64_t *b = node_btab(Q); return b + 1 + 3 * b[0] + 2; }
static ExprId node_declared_e(TNodeId Q) { const uint64_t *b = node_btab(Q); return b[2 + 3 * b[0]]; }
static uint64_t xconst(ExprId e) { size_t n; const uint64_t *w = xw(e, &n); require(w[0] == X_CONST, "construction field is not a constant"); return w[2]; }
static uint64_t xlevel(ExprId e) { size_t n; const uint64_t *w = xw(e, &n); require(w[0] == X_LEVEL, "construction annotation is not a constant"); return w[1]; }
bool expr_is_level(ExprId e) { size_t n; return xw(e, &n)[0] == X_LEVEL; }
uint64_t expr_level_value(ExprId e) { return xlevel(e); }
void tnode_param(TNodeId Q, size_t k, PSort *sort, RefId *closed_type, FaceId *closed_guard) {
    require(k < tnode_nparams(Q), "construction parameter out of range");
    const uint64_t *p = node_ptab(Q) + 3 * k;
    *sort = (PSort)p[0];
    *closed_type = p[1] ? xconst(p[1]) : 0;
    *closed_guard = p[2] ? xconst(p[2]) : 0;
}
uint64_t tnode_const_field(TNodeId Q, size_t k) { FieldKind kd; BinderSlot bs; ExprId e; node_field(Q, k, &kd, &bs, &e); return xconst(e); }
FaceId tnode_const_required(TNodeId Q) { return xconst(node_required_e(Q)); }
FaceId tnode_const_declared(TNodeId Q) { ExprId e = node_declared_e(Q); return e ? xconst(e) : 0; }
uint64_t tnode_const_payload(TNodeId Q) { ExprId e = node_payload_e(Q); return e ? xlevel(e) : 0; }



/* a binder opened at its keyed fresh name: the domain field, then the body
 * with the binder's local ↦ that name (the field and binder families, one
 * interpretation for both node kinds) */
TermOpen tview_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field) {
    TNodeId Q = ref_tnode(owner);
    Sort sort; FieldIndex domf; size_t lslot; node_binder(Q, slot, &sort, &domf, &lslot);
    require(sort == S_TERM, "sort mismatch: expected term binder");
    TermOpen o;
    o.type = construction_field(owner, domf);
    o.x = binder_term_var(owner, slot, o.type);
    o.body = construction_binder(owner, S_TERM, slot, body_field, ref_var(o.x));
    return o;
}
DimOpen tview_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field) {
    TNodeId Q = ref_tnode(owner);
    require(tnode_binder_sort(Q, slot) == S_DIM, "sort mismatch: expected dimension binder");
    DimOpen o;
    o.j = binder_dim_var(owner, slot);
    o.body = construction_binder(owner, S_DIM, slot, body_field, iv_var(o.j));
    return o;
}

/* generic instance: parameter k at a fresh name keyed by (node, k), its type
 * the closed type instantiated by the earlier fresh names */

/* ------------------------------------------------------------------ */
/* interpretation families                                               */
/* INTERP(e, env) interprets one expression; TVMAKE(Q, env) is the view of a
 * node (§51.1: restricted to the node's free slots, its required face the
 * instantiated recipe strengthened by its images'); ISCOPE(e, env) a scope
 * literal (fresh keyed locals, then capture); ENVLOOK(env, slot) the position
 * of a slot; ENVSET(env, [slot, sort, id]) an environment with one slot set.
 * A view's environment is an interpretation record. Each step does a
 * constant amount of work. */

static Family F_INTERP, F_TVMAKE, F_ISCOPE, F_ENVLOOK, F_ENVSET;
static Family F_TREF, F_TIV, F_TFC, F_TSCOPE, F_CAPTURE, F_REFVAR, F_SETFREE, F_DSUNION, F_VSUNION, F_IVDIMS, F_FCDIMS;
static Family F_IVNEG, F_IVMEET, F_IVJOIN, F_FCEND, F_FCMEET, F_FCJOIN, F_FCFORALL, F_REINDEX, F_IVRE, F_FCRE, F_FCENT;

/* position of slot w[1] in environment w[0], plus one (0: absent); one probe per step */
typedef struct { const uint64_t *w; size_t n, lo, hi; } LookLoc;
static void envlook_step(Cont *k, uint64_t v) {
    LookLoc *L = FR_LOC(k, LookLoc);
    FR_BEGIN(k);
    L->w = interner_get(&M.keys, k->w[0], &L->n);
    L->lo = 0; L->hi = (L->n - 1) / 3;
    while (L->lo < L->hi) {
        size_t mid = (L->lo + L->hi) / 2; uint64_t s = L->w[1 + 3 * mid];
        if (s == k->w[1]) FR_FINISH(k, mid + 1);
        if (s < k->w[1]) L->lo = mid + 1; else L->hi = mid;
        FR_YIELD(k);
    }
    FR_FINISH(k, 0);
    FR_END(k);
}
/* environment w[0] with the slot of entry w[1] = [slot, sort, id] set */
typedef struct { const uint64_t *w, *e; size_t n, q; bool placed; WordBuf out; bool created; } SetLoc;
static void envset_step(Cont *k, uint64_t v) {
    SetLoc *L = FR_LOC(k, SetLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    L->w = interner_get(&M.keys, k->w[0], &L->n);
    { size_t m; L->e = interner_get(&M.keys, k->w[1], &m); }
    wordbuf_init(&L->out); wordbuf_push(&L->out, L->w[0]); L->placed = false;
    for (L->q = 1; L->q < L->n; L->q += 3) {
        if (!L->placed && L->w[L->q] >= L->e[0]) {
            wordbuf_push(&L->out, L->e[0]); wordbuf_push(&L->out, L->e[1]); wordbuf_push(&L->out, L->e[2]);
            L->placed = true;
            if (L->w[L->q] == L->e[0]) { FR_YIELD(k); continue; }
        }
        wordbuf_push(&L->out, L->w[L->q]); wordbuf_push(&L->out, L->w[L->q + 1]); wordbuf_push(&L->out, L->w[L->q + 2]);
        FR_YIELD(k);
    }
    if (!L->placed) { wordbuf_push(&L->out, L->e[0]); wordbuf_push(&L->out, L->e[1]); wordbuf_push(&L->out, L->e[2]); }
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}
static uint64_t env_entry(uint64_t er, uint64_t slot, PSort sort, uint64_t id) { (void)er; uint64_t w[3] = { slot, sort, id }; return interner_intern(&M.keys, w, 3, NULL); }
/* env.map(er): an environment record as the substitution of its atoms —
 * slot k is atom k; terms first, then dimensions (a map record). The
 * interpretation of a construction's closed constant is its substitution by
 * this map: a constant field is one case of the common interpretation. */
static Family F_ENVMAP;
typedef struct { const uint64_t *w; size_t n, q, kept; bool dims; WordBuf out; bool created; } EmLoc;
static void envmap_step(Cont *k, uint64_t v) {
    EmLoc *L = FR_LOC(k, EmLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    L->w = interner_get(&M.keys, k->w[0], &L->n); L->kept = 0;
    wordbuf_init(&L->out);
    for (L->dims = false;; L->dims = true) {
        for (L->q = 1; L->q < L->n; L->q += 3) {
            {   uint64_t slot = L->w[L->q], sort = L->w[L->q + 1], val = L->w[L->q + 2], atom = obound_id((uint32_t)slot);
                if ((sort == PS_INTERVAL && L->dims) || (sort == PS_REF && !L->dims)) {
                    bool ident = L->dims ? val == iv_var(atom) : (ref_is_var(val) && ref_var_id(val) == atom);
                    if (!ident) { wordbuf_push(&L->out, atom); wordbuf_push(&L->out, val); if (!L->dims) L->kept++; }
                } }
            FR_YIELD(k);
        }
        if (L->dims) break;
    }
    wordbuf_push(&L->out, L->kept);
    FR_CALL(k, id, intern_sub(k, &M.maps, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}

static Family trav_of(PSort s) { return s == PS_REF ? F_TREF : s == PS_INTERVAL ? F_TIV : F_TFC; }
static PSort psort_of_val(ValSort s) { return s == VS_REF ? PS_REF : s == VS_INTERVAL ? PS_INTERVAL : PS_FACE; }

typedef struct { const uint64_t *w; size_t n, q; uint64_t a, b, er, S, tk; TVal t; WordBuf out; bool created; Join *J; } InLoc;
static void interp_step(Cont *k, uint64_t v) {
    InLoc *L = FR_LOC(k, InLoc);
    ExprId e = k->w[0]; uint64_t er = k->w[1];
    uint64_t r = 0, id = 0;
    FR_BEGIN(k);
    L->w = xw(e, &L->n);
    if (L->w[0] == X_PARAM || L->w[0] == X_LOCAL) {
        {   size_t m; const uint64_t *ew = interner_get(&M.keys, er, &m);
            uint64_t slot = L->w[0] == X_PARAM ? L->w[1] : TPL.defs[ew[0]].nparams + L->w[1];
            FR_AWAIT(k, r, F_ENVLOOK, er, slot); }
        require(r, "template: slot %llu unset", (unsigned long long)L->w[1]);
        {   size_t m; const uint64_t *ew = interner_get(&M.keys, er, &m);
            FR_FINISH(k, tvrec((PSort)ew[1 + 3 * (r - 1) + 1], ew[1 + 3 * (r - 1) + 2])); }
    }
    if (L->w[0] == X_LEVEL) FR_FINISH(k, tvrec(PS_LEVEL, L->w[1]));
    if (L->w[0] == X_IV0) FR_FINISH(k, tvrec(PS_INTERVAL, iv_zero()));
    if (L->w[0] == X_IV1) FR_FINISH(k, tvrec(PS_INTERVAL, iv_one()));
    if (L->w[0] == X_FCF) FR_FINISH(k, tvrec(PS_FACE, fc_false()));
    if (L->w[0] == X_FCT) FR_FINISH(k, tvrec(PS_FACE, fc_true()));
    if (L->w[0] == X_CONST) {
        /* a closed constant: substituted by the environment's atoms */
        FR_AWAIT(k, L->a, F_ENVMAP, er, 0);
        L->t.sort = (PSort)L->w[1];
        if (L->t.sort == PS_REF) FR_AWAIT(k, r, F_REINDEX, L->w[2], L->a);
        else if (L->t.sort == PS_INTERVAL) FR_AWAIT(k, r, F_IVRE, L->w[2], L->a);
        else if (L->t.sort == PS_FACE) FR_AWAIT(k, r, F_FCRE, L->w[2], L->a);
        else r = L->w[2];
        FR_FINISH(k, tvrec(L->t.sort, r));
    }
    if (L->w[0] == X_NODE) { FR_AWAIT(k, r, F_TVMAKE, L->w[1], er); FR_FINISH(k, tvrec(PS_REF, r)); }
    if (L->w[0] == X_SCOPE) { FR_AWAIT(k, r, F_ISCOPE, e, er); FR_FINISH(k, tvrec(PS_SCOPE, r)); }
    if (L->w[0] == X_CALL) {
        /* the callee's environment: the arguments, independent demands in one join */
        require(L->w[2] == TPL.defs[L->w[1]].nparams, "template call arity (%s)", TPL.defs[L->w[1]].name);
        L->J = join_new(k, L->w[2]);
        for (L->q = 0; L->q < L->w[2]; L->q++) { if (L->q) FR_YIELD(k); join_request(L->J, L->q, F_INTERP, L->w[3 + L->q], er); }
        FR_JOIN(k, L->J);
        wordbuf_init(&L->out); wordbuf_push(&L->out, L->w[1]);
        for (L->q = 0; L->q < L->w[2]; L->q++) {
            L->t = tvget(join_value(L->J, L->q));
            require(L->t.sort == TPL.defs[L->w[1]].sorts[L->q], "template call sort (%s, %zu)", TPL.defs[L->w[1]].name, L->q);
            wordbuf_push(&L->out, L->q); wordbuf_push(&L->out, L->t.sort); wordbuf_push(&L->out, L->t.id);
            FR_YIELD(k);
        }
        join_free(L->J); L->J = NULL;
        FR_CALL(k, L->er, intern_sub(k, &M.keys, &L->out, &L->created));
        FR_AWAIT(k, r, F_INTERP, TPL.defs[L->w[1]].root, L->er);
        FR_FINISH(k, r);
    }
    if (L->w[0] == X_APPLY || L->w[0] == X_APPLY_TYPE || L->w[0] == X_APPLY_GUARD) {
        /* the scope and its arguments are independent demands: one join */
        L->J = join_new(k, 1 + L->w[2]);
        join_request(L->J, 0, F_INTERP, L->w[1], er);
        for (L->q = 0; L->q < L->w[2]; L->q++) { FR_YIELD(k); join_request(L->J, 1 + L->q, F_INTERP, L->w[3 + L->q], er); }
        FR_JOIN(k, L->J);
        L->t = tvget(join_value(L->J, 0)); require(L->t.sort == PS_SCOPE, "scope application of a non-scope");
        L->S = L->t.id;
        require(L->w[2] == scope_arity(L->S), "scope application arity");
        wordbuf_init(&L->out);
        for (L->q = 0; L->q < L->w[2]; L->q++) {
            L->t = tvget(join_value(L->J, 1 + L->q));
            wordbuf_push(&L->out, L->t.sort == PS_REF ? VS_REF : L->t.sort == PS_INTERVAL ? VS_INTERVAL : VS_FACE); wordbuf_push(&L->out, L->t.id);
            FR_YIELD(k);
        }
        join_free(L->J); L->J = NULL;
        FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
        L->tk = trav_key(TR_APPLY, 0, id);
        if (L->w[0] == X_APPLY_TYPE) { FR_AWAIT(k, r, F_TREF, scope_type(L->S), L->tk); FR_FINISH(k, tvrec(PS_REF, r)); }
        if (L->w[0] == X_APPLY_GUARD) { FR_AWAIT(k, r, F_TFC, scope_guard(L->S), L->tk); FR_FINISH(k, tvrec(PS_FACE, r)); }
        L->t.sort = psort_of_val(scope_body(L->S).sort);
        FR_AWAIT(k, r, trav_of(L->t.sort), scope_body(L->S).id, L->tk);
        FR_FINISH(k, tvrec(L->t.sort, r));
    }
    if (L->w[0] == X_FORALL) {
        FR_AWAIT(k, r, F_INTERP, L->w[1], er);
        L->t = tvget(r); require(L->t.sort == PS_SCOPE, "forall of a non-scope");
        require(scope_arity(L->t.id) == 1 && scope_local(L->t.id, 0).sort == S_DIM && scope_body(L->t.id).sort == VS_FACE, "forall of a non-unary face scope");
        FR_AWAIT(k, r, F_FCFORALL, scope_body(L->t.id).id, bound_id(0, 0));
        FR_AWAIT(k, r, F_TFC, r, trav_key(TR_LOWER, 0, 0));
        FR_FINISH(k, tvrec(PS_FACE, r));
    }
    /* unary and binary operators on levels, intervals and faces */
    FR_AWAIT(k, r, F_INTERP, L->w[1], er);
    L->a = tvget(r).id;
    if (L->w[0] == X_LSUCC) FR_FINISH(k, tvrec(PS_LEVEL, level_succ(L->a)));
    if (L->w[0] == X_LFIRST) FR_FINISH(k, tvrec(PS_LEVEL, levels_first(L->a)));
    if (L->w[0] == X_IVNOT) { FR_AWAIT(k, r, F_IVNEG, L->a, 0); FR_FINISH(k, tvrec(PS_INTERVAL, r)); }
    if (L->w[0] == X_FCEND) { FR_AWAIT(k, r, F_FCEND, L->a, L->w[2]); FR_FINISH(k, tvrec(PS_FACE, r)); }
    FR_AWAIT(k, r, F_INTERP, L->w[2], er);
    L->b = tvget(r).id;
    if (L->w[0] == X_LMAX) FR_FINISH(k, tvrec(PS_LEVEL, level_max(L->a, L->b)));
    if (L->w[0] == X_LEVELS) FR_FINISH(k, tvrec(PS_LEVEL, levels_pack(L->a, L->b)));
    if (L->w[0] == X_IVAND) { FR_AWAIT(k, r, F_IVMEET, L->a, L->b); FR_FINISH(k, tvrec(PS_INTERVAL, r)); }
    if (L->w[0] == X_IVOR) { FR_AWAIT(k, r, F_IVJOIN, L->a, L->b); FR_FINISH(k, tvrec(PS_INTERVAL, r)); }
    if (L->w[0] == X_FCAND) { FR_AWAIT(k, r, F_FCMEET, L->a, L->b); FR_FINISH(k, tvrec(PS_FACE, r)); }
    if (L->w[0] == X_FCOR) { FR_AWAIT(k, r, F_FCJOIN, L->a, L->b); FR_FINISH(k, tvrec(PS_FACE, r)); }
    die("bad expression kind %llu", (unsigned long long)L->w[0]);
    FR_END(k);
}

/* the template view of node w[0] in environment w[1] */
typedef struct { const uint64_t *fl; size_t nf, q; uint64_t sup, fv, ds, E, req, slot, g; TVal t; WordBuf out; bool created; } MkLoc;
/* the declared guard of a node's slot: a construction parameter's closed
 * guard; a template parameter's or term local's declared availability */
static const uint64_t *node_ptab(TNodeId Q);
static ExprId slot_guard_e(TNodeId Q, size_t s) {
    if (node_construction(Q)) return node_ptab(Q)[3 * s + 2];
    const TDef *d = &TPL.defs[tnode_def(Q)];
    return s < d->nparams ? d->pguard[s] : d->lreq[s - d->nparams];
}
static void tvmake_step(Cont *k, uint64_t v) {
    MkLoc *L = FR_LOC(k, MkLoc);
    TNodeId Q = k->w[0]; uint64_t er = k->w[1];
    uint64_t r = 0;
    FR_BEGIN(k);
    node_free_list(Q, &L->nf, &L->fl);
    L->sup = dimset_make(NULL, 0); L->fv = varset_make(NULL, 0);
    wordbuf_init(&L->out); wordbuf_push(&L->out, tnode_def(Q));
    for (L->q = 0; L->q < L->nf; L->q++) {
        FR_AWAIT(k, r, F_ENVLOOK, er, L->fl[L->q]);
        require(r, "template view: a required slot has no value (%s slot %zu)", TPL.defs[tnode_def(Q)].name, (size_t)L->fl[L->q]);
        {   size_t m; const uint64_t *ew = interner_get(&M.keys, er, &m);
            L->t.sort = (PSort)ew[1 + 3 * (r - 1) + 1]; L->t.id = ew[1 + 3 * (r - 1) + 2]; }
        wordbuf_push(&L->out, L->fl[L->q]); wordbuf_push(&L->out, L->t.sort); wordbuf_push(&L->out, L->t.id);
        if (L->t.sort == PS_REF) {
            FR_AWAIT(k, L->sup, F_DSUNION, L->sup, ref_support(L->t.id));
            FR_AWAIT(k, L->fv, F_VSUNION, L->fv, ref_freevars(L->t.id));
        } else if (L->t.sort == PS_SCOPE) {
            FR_AWAIT(k, L->sup, F_DSUNION, L->sup, scope_support(L->t.id));
            FR_AWAIT(k, L->fv, F_VSUNION, L->fv, scope_freevars(L->t.id));
        } else if (L->t.sort == PS_INTERVAL || L->t.sort == PS_FACE) {
            FR_AWAIT(k, L->ds, L->t.sort == PS_INTERVAL ? F_IVDIMS : F_FCDIMS, L->t.id, 0);
            FR_AWAIT(k, L->sup, F_DSUNION, L->sup, L->ds);
        }
    }
    FR_CALL(k, L->E, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_AWAIT(k, r, F_INTERP, node_required_e(Q), er);
    L->req = tvget(r).id;
    /* each reference image's requirement, except where the slot's declared
     * guard entails it (a partial formal is used under its guard only) */
    for (L->q = 0; L->q < L->nf; L->q++) {
        tenv_entry(L->E, L->q, &L->slot, &L->t);
        if (L->t.sort != PS_REF) { FR_YIELD(k); continue; }
        L->g = slot_guard_e(Q, L->slot);
        if (L->g) { FR_AWAIT(k, r, F_INTERP, L->g, er); L->g = tvget(r).id; } else L->g = fc_true();
        FR_AWAIT(k, r, F_FCENT, L->g, ref_required(L->t.id));
        if (r != 2) FR_AWAIT(k, L->req, F_FCMEET, L->req, ref_required(L->t.id));
    }
    FR_AWAIT(k, L->sup, F_SETFREE, L->sup, 0);
    FR_AWAIT(k, L->fv, F_SETFREE, L->fv, 1);
    FR_FINISH(k, ref_intern_tview(Q, L->E, L->sup, L->fv, L->req));
    FR_END(k);
}

/* a scope literal: [X_SCOPE, nloc, (sort, lslot, type_e, level_e, req_e)*, body, type, level, guard];
 * its locals are fresh names keyed by (expression, environment, slot), the
 * records interpreted over them, then captured */
typedef struct { const uint64_t *w; size_t n, nl, q; uint64_t inner, ty, lv, rq, id, bsort, body, rtype, rlevel; WordBuf out; bool created; } ScLoc;
static void iscope_step(Cont *k, uint64_t v) {
    ScLoc *L = FR_LOC(k, ScLoc);
    ExprId e = k->w[0]; uint64_t er = k->w[1];
    uint64_t r = 0;
    FR_BEGIN(k);
    L->w = xw(e, &L->n); L->nl = (size_t)L->w[1];
    L->inner = er;
    wordbuf_init(&L->out); wordbuf_push(&L->out, L->nl);
    for (L->q = 0; L->q < L->nl; L->q++) {
        {   const uint64_t *l = L->w + 2 + 5 * L->q;
            KeyWord bk[5] = { { KW_CONST, 9100 }, { KW_CONST, e }, { KW_CONST, er }, { KW_CONST, L->q }, { KW_CONST, l[0] } };
            if (l[0] == S_DIM) {
                DimVarId j = fresh_dim_keyed(bk, 5);
                wordbuf_push(&L->out, S_DIM); wordbuf_push(&L->out, j); wordbuf_push(&L->out, 0); wordbuf_push(&L->out, LEVEL_NONE); wordbuf_push(&L->out, fc_true());
                L->id = j; L->ty = 0;
            } else L->id = 0; }
        if (L->id) {
            size_t m; const uint64_t *ew = interner_get(&M.keys, er, &m);
            FR_AWAIT(k, L->inner, F_ENVSET, L->inner, env_entry(L->inner, TPL.defs[ew[0]].nparams + L->w[2 + 5 * L->q + 1], PS_INTERVAL, iv_var(L->id)));
            continue;
        }
        FR_AWAIT(k, r, F_INTERP, L->w[2 + 5 * L->q + 2], L->inner);
        L->ty = tvget(r).id; L->lv = LEVEL_NONE; L->rq = fc_true();
        if (L->w[2 + 5 * L->q + 3]) { FR_AWAIT(k, r, F_INTERP, L->w[2 + 5 * L->q + 3], L->inner); L->lv = tvget(r).id; }
        if (L->w[2 + 5 * L->q + 4]) { FR_AWAIT(k, r, F_INTERP, L->w[2 + 5 * L->q + 4], L->inner); L->rq = tvget(r).id; }
        {   KeyWord bk[5] = { { KW_CONST, 9100 }, { KW_CONST, e }, { KW_CONST, er }, { KW_CONST, L->q }, { KW_CONST, S_TERM } };
            L->id = fresh_term_keyed_req(bk, 5, L->ty, L->rq); }
        wordbuf_push(&L->out, S_TERM); wordbuf_push(&L->out, L->id); wordbuf_push(&L->out, L->ty); wordbuf_push(&L->out, L->lv); wordbuf_push(&L->out, L->rq);
        FR_AWAIT(k, r, F_REFVAR, L->id, 0);
        {   size_t m; const uint64_t *ew = interner_get(&M.keys, er, &m);
            FR_AWAIT(k, L->inner, F_ENVSET, L->inner, env_entry(L->inner, TPL.defs[ew[0]].nparams + L->w[2 + 5 * L->q + 1], PS_REF, r)); }
    }
    {   const uint64_t *t = L->w + 2 + 5 * L->nl;          /* body, type, level, guard */
        FR_AWAIT(k, r, F_INTERP, t[0], L->inner); }
    {   TVal b = tvget(r); L->bsort = b.sort == PS_REF ? VS_REF : b.sort == PS_INTERVAL ? VS_INTERVAL : VS_FACE; L->body = b.id; }
    L->rtype = 0; L->rlevel = LEVEL_NONE;
    if (L->w[2 + 5 * L->nl + 1]) { FR_AWAIT(k, r, F_INTERP, L->w[2 + 5 * L->nl + 1], L->inner); L->rtype = tvget(r).id; }
    if (L->w[2 + 5 * L->nl + 2]) { FR_AWAIT(k, r, F_INTERP, L->w[2 + 5 * L->nl + 2], L->inner); L->rlevel = tvget(r).id; }
    FR_AWAIT(k, r, F_INTERP, L->w[2 + 5 * L->nl + 3], L->inner);
    wordbuf_push(&L->out, L->bsort); wordbuf_push(&L->out, L->body); wordbuf_push(&L->out, L->rtype); wordbuf_push(&L->out, L->rlevel); wordbuf_push(&L->out, tvget(r).id);
    FR_CALL(k, L->id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_AWAIT(k, r, F_CAPTURE, L->id, 0);
    FR_FINISH(k, r);
    FR_END(k);
}

void template_families_init(void) {
    F_TREF = family_lookup("trav.ref"); F_TIV = family_lookup("trav.interval"); F_TFC = family_lookup("trav.face"); F_TSCOPE = family_lookup("trav.scope");
    F_CAPTURE = family_lookup("scope.capture"); F_REFVAR = family_lookup("ref.var"); F_SETFREE = family_lookup("set.free");
    F_DSUNION = family_lookup("dimset.union"); F_VSUNION = family_lookup("varset.union"); F_IVDIMS = family_lookup("iv.dims"); F_FCDIMS = family_lookup("fc.dims");
    F_IVNEG = family_lookup("iv.negate"); F_IVMEET = family_lookup("iv.meet"); F_IVJOIN = family_lookup("iv.join");
    F_FCEND = family_lookup("fc.endpoint"); F_FCMEET = family_lookup("fc.meet"); F_FCJOIN = family_lookup("fc.join"); F_FCFORALL = family_lookup("fc.forall"); F_FCENT = family_lookup("fc.entails");
    F_REINDEX = family_lookup("reindex"); F_IVRE = family_lookup("iv.reindex"); F_FCRE = family_lookup("fc.reindex");
    require(F_TREF && F_CAPTURE && F_REFVAR && F_FCRE, "the scope, construction and substitution families are registered first");
    F_ENVLOOK = family_define("template.envlook", envlook_step, sizeof(LookLoc), true);
    F_ENVSET = family_define("template.envset", envset_step, sizeof(SetLoc), true);
    F_INTERP = family_define("template.interp", interp_step, sizeof(InLoc), true);
    F_ENVMAP = family_define("env.map", envmap_step, sizeof(EmLoc), true);
    F_TVMAKE = family_define("template.view", tvmake_step, sizeof(MkLoc), true);
    F_ISCOPE = family_define("template.scope", iscope_step, sizeof(ScLoc), true);
    construct_bind_template_families();
}

/* ------------------------------------------------------------------ */
/* TVIEW operations (synchronous driver over the families)               */

static TVal interp_at(ExprId e, uint64_t er) { return tvget(family_call(F_INTERP, e, er)); }
RefId tview_make(TNodeId Q, uint64_t er) { return family_call(F_TVMAKE, Q, er); }

static Family F_HEADANN;
void tview_open(RefId t, Head *h) {
    TNodeId Q = ref_tnode(t);
    h->tnode = Q; h->tenv = ref_tenv(t);
    h->tag = tnode_tag(Q);
    h->n = tnode_nfields(Q);
    if (!F_HEADANN) F_HEADANN = family_lookup("head.annotation");
    h->payload = family_call(F_HEADANN, t, 0);
    h->levels = family_call(F_HEADANN, t, 1);
}


/* the boundary signature of a template node as expressions (interpreted by
 * the caller in the view's environment, one awaited interpretation each):
 * entry k of the node's free slots; false when the slot carries no checked
 * declaration */
size_t tnode_sig_count(TNodeId Q) { size_t nf; const uint64_t *fl; node_free_list(Q, &nf, &fl); return nf; }
bool tnode_sig_exprs(TNodeId Q, size_t k, size_t *slot, PSort *sort, ExprId *type_e, ExprId *level_e, ExprId *sig_e, ExprId *guard_e) {
    size_t nf; const uint64_t *fl; node_free_list(Q, &nf, &fl);
    size_t s = (size_t)fl[k];
    *slot = s;
    if (node_construction(Q)) {
        /* a construction parameter: its closed type and guard over the earlier atoms */
        const uint64_t *p = node_ptab(Q) + 3 * s;
        *sort = (PSort)p[0]; *type_e = p[1]; *level_e = 0; *sig_e = 0; *guard_e = p[2];
        return *sort == PS_REF;
    }
    const TDef *def = &TPL.defs[tnode_def(Q)];
    size_t np = def->nparams;
    if (s < np) { *sort = def->sorts[s]; *type_e = def->ptype[s]; *level_e = def->plevel[s]; *sig_e = def->psig[s]; *guard_e = def->pguard[s]; return true; }
    size_t l = s - np;
    if (def->lsort[l] != PS_REF || !def->ltype[l]) return false;
    *sort = PS_REF; *type_e = def->ltype[l]; *level_e = def->llevel[l]; *sig_e = 0; *guard_e = def->lreq[l];
    return true;
}
bool tnode_result_exprs(TNodeId Q, ExprId *type_e, ExprId *level_e) {
    if (node_construction(Q)) return false;
    const TDef *def = &TPL.defs[tnode_def(Q)];
    if (!def->rtype || def->root_node != Q) return false;
    *type_e = def->rtype; *level_e = def->rlevel;
    return true;
}

/* ------------------------------------------------------------------ */
/* registration DSL                                                      */

static TDefId cur; static TDef *cd;
static ExprId under_face;         /* the `under` faces in force (0 = none) */

static ExprId P(size_t k) { return x1(X_PARAM, k); }
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
    return NODE_req(tag, payload, levels, nf, fs, nb, bs, under_face ? under_face : FCT());
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
static ExprId guard_now(void) { return under_face ? under_face : FCT(); }
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
static ExprId r_guard_alpha(ExprId i, void *c) { return AP1(((Cx *)c)->c, i); }
static ExprId r_down_etype(ExprId xl, void *c) { Cx *x = c; /* a=lA b=A c=t */ return CALL(TD_PATHCONST, x->a, x->b, x->c, xl); }
static ExprId r_down_res(ExprId xl, ExprId el, void *c) { (void)xl; (void)el; return nUNIV(((Cx *)c)->t); }
/* a unary dimension scope signature whose guard depends on the local */
static ExprId SIG_DIM1_G(JFn result, JFn guard, void *ctx, ExprId level) {
    size_t s = newlocal(PS_INTERVAL); LS ls[1] = { { S_DIM, 0, 0, 0 } }; size_t sl[1] = { s };
    return SCOPE(1, ls, sl, result(L(s), ctx), 0, level, guard(L(s), ctx));
}

static void begin(TDefKind k, const char *name, size_t n, const PSort *sorts) {
    cur = k; cd = &TPL.defs[k]; memset(cd, 0, sizeof *cd); words_init(&cd->nodes);
    cd->name = name; cd->nparams = n;
    for (size_t i = 0; i < n; i++) cd->sorts[i] = sorts[i];
    under_face = 0;
}
static void ptype(size_t k, ExprId type, ExprId level) { cd->ptype[k] = type; cd->plevel[k] = level; }
static void ptype_on(size_t k, ExprId type, ExprId level, ExprId guard) { ptype(k, type, level); cd->pguard[k] = guard; }
static void psig(size_t k, ExprId sig) { cd->psig[k] = sig; }
static void rtype(ExprId type, ExprId level) { cd->rtype = type; cd->rlevel = level; }
/* ---- integration of a call-root (§51.1, review F2) ----
 * The callee's root recipe is remapped into caller-owned nodes: callee
 * parameters become the call's argument recipes,
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
    case X_PARAM: return in->arg[w[1]];
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
        require(w[2] == in.callee->nparams, "inline: call arity");
        for (size_t k = 0; k < w[2]; k++) in.arg[k] = w[3 + k];
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
    ExprId fstu = DSCOPE1(b_sig_fstu, t_fam_at, &both, x->a, x->c);
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
      psig(1, SIG_DIM1(t_univ, &cu, LSUCC(P(0)), FCT())); psig(3, SIG_DIM1(t_fam_at, &ca, P(0), P(2)));
      rtype(AP1(P(1), P(5)), P(0)); }
    { size_t j = newlocal(PS_INTERVAL); ExprId rj = IVAND(P(5), L(j)); ExprId r0 = FCEND(P(5), 0);
      ExprId faces[2] = { P(2), r0 }, terms[2] = { AP1(P(3), rj), P(4) };
      finish(nCOMP(P(0), j, AP1(P(1), rj), FCOR(P(2), r0), nSYSTEM(2, faces, terms), P(4))); }
    /* HComp(l, X, phi, u:[j]X on phi, cap) */
    begin(TD_HCOMP, "HComp", 5, SORTS(PS_LEVEL, PS_REF, PS_FACE, PS_SCOPE, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(4, P(1), P(0));
    { Cx cx = { 0, 0, 0, 0, 0, 0, P(1) }; psig(3, SIG_DIM1(t_const, &cx, P(0), P(2))); rtype(P(1), P(0)); }
    { size_t j = newlocal(PS_INTERVAL); finish(nCOMP(P(0), j, P(1), P(2), AP1(P(3), L(j)), P(4))); }
    /* Coe(l, A:[i]U_l, cap:A<0>) */
    begin(TD_COE, "Coe", 3, SORTS(PS_LEVEL, PS_SCOPE, PS_REF));
    ptype(2, AP1(P(1), IV0()), P(0));
    { Cx cu = { 0, 0, 0, 0, 0, 0, P(0) }; psig(1, SIG_DIM1(t_univ, &cu, LSUCC(P(0)), FCT())); rtype(AP1(P(1), IV1()), P(0)); }
    { size_t i = newlocal(PS_INTERVAL); finish(nCOMP(P(0), i, AP1(P(1), L(i)), FCF(), nSYSTEM(0, NULL, NULL), P(2))); }
    /* ExtendContr(l, X, c, k, theta, v on theta) */
    begin(TD_EXTENDCONTR, "ExtendContr", 6, SORTS(PS_LEVEL, PS_REF, PS_REF, PS_REF, PS_FACE, PS_REF));
    ptype(1, nUNIV(P(0)), LSUCC(P(0))); ptype(2, P(1), P(0)); ptype_on(5, P(1), P(0), P(4));
    { size_t xk = newlocal(PS_REF); ptype(3, nPI(P(0), P(0), xk, P(1), CALL(TD_PATHCONST, P(0), P(1), P(2), L(xk))), P(0)); }
    rtype(P(1), P(0));
    { Cx c = { P(0), P(1), P(2), P(5), P(3), 0, P(1) };
      ExprId tube = DSCOPE1(b_ext_tube, t_const, &c, P(0), P(4));
      finish(CALL(TD_HCOMP, P(0), P(1), P(4), tube, P(2))); }
    /* LineEquiv(l, X:[i]U_l) = Coe([i]. Equiv(X<0>, X<i>), IdEquiv(X<0>)) */
    begin(TD_LINEEQUIV, "LineEquiv", 2, SORTS(PS_LEVEL, PS_SCOPE));
    { Cx cu = { 0, 0, 0, 0, 0, 0, P(0) }; psig(1, SIG_DIM1(t_univ, &cu, LSUCC(P(0)), FCT())); rtype(CALL(TD_EQUIV, P(0), P(0), AP1(P(1), IV0()), AP1(P(1), IV1())), P(0)); }
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
      psig(2, SIG_DIM1(t_univ, &sg, LSUCC(P(0)), FCT()));
      psig(3, SIG_DIM_TERM(r_E_dom, P(0), r_univ2, &sn, LSUCC(P(1)), FCT()));
      psig(5, SIG_DIM1(r_pi_at, &sg, LMAX(P(0), P(1)), P(4)));
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
      psig(2, SIG_DIM1(t_univ, &sg, LSUCC(P(0)), FCT()));
      psig(3, SIG_DIM_TERM(r_E_dom, P(0), r_univ2, &sn, LSUCC(P(1)), FCT()));
      psig(5, SIG_DIM1(r_sigma_at, &sg, LMAX(P(0), P(1)), P(4)));
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
      psig(1, SIG_DIM2(r_univ2, &sg, LSUCC(P(0)), FCT()));
      psig(2, SIG_DIM1(r_B_at0, &sg, P(0), FCT()));
      psig(3, SIG_DIM1(r_B_at1, &sg, P(0), FCT()));
      psig(5, SIG_DIM1(r_path_at, &sg, P(0), P(4)));
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
      psig(1, SIG_DIM1(t_univ, &sg, LSUCC(P(0)), FCT()));
      psig(2, SIG_FACE1(FCT()));
      psig(3, SIG_DIM1_G(t_univ, r_guard_alpha, &sg, LSUCC(P(0))));
      psig(4, SIG_DIM1_G(r_equiv_TA, r_guard_alpha, &sg, P(0)));
      psig(6, SIG_DIM1(r_glue_at, &sg, P(0), P(5)));
      ptype(7, r_glue_at(IV0(), &sg), P(0));
      rtype(r_glue_at(IV1(), &sg), P(0)); }
    { ExprId n = P(0), A = P(1), alpha = P(2), T = P(3), e = P(4), psi = P(5), u = P(6), cap = P(7);
      ExprId A0 = AP1(A, IV0()), A1 = AP1(A, IV1()), T0 = AP1(T, IV0()), T1 = AP1(T, IV1()), e0 = AP1(e, IV0()), e1 = AP1(e, IV1());
      ExprId alpha0 = AP1(alpha, IV0()), alpha1 = AP1(alpha, IV1()), u1 = AP1(u, IV1());
      ExprId a0 = nUNGLUE(n, A0, alpha0, T0, e0, cap);
      glue_a0_expr = a0;
      Cx bt = { n, A, alpha, T, e, u, A };
      ExprId baseTube = DSCOPE1(b_glue_base, t_fam_at, &bt, n, psi);
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
      ExprId repairTube = DSCOPE1(b_glue_repair, t_const, &rp, n, FCOR(alpha1, psi));
      ExprId repaired = CALL(TD_HCOMP, n, A1, FCOR(alpha1, psi), repairTube, a1);
      finish(nGLUEINTRO(n, A1, alpha1, T1, e1, t1, repaired)); }
    /* UniverseComp(l, phi, types:[i]U_l on phi, cap:U_l) */
    begin(TD_UNIVERSECOMP, "UniverseComp", 4, SORTS(PS_LEVEL, PS_FACE, PS_SCOPE, PS_REF));
    ptype(3, nUNIV(P(0)), LSUCC(P(0)));
    { Cx cu = { 0, 0, 0, 0, 0, 0, P(0) }; psig(2, SIG_DIM1(t_univ, &cu, LSUCC(P(0)), P(1))); rtype(nUNIV(P(0)), LSUCC(P(0))); }
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
      psig(4, SIG_TERM2(P(2), P(1), r_down_etype, P(1), r_down_res, &sd, LSUCC(P(0)), FCT()));
      rtype(AP2(P(4), P(3), CALL(TD_REFL, P(1), P(2), P(3))), P(0)); }
    { ExprId l = P(0), lA = P(1), A = P(2), t = P(3), D = P(4), x = P(5), e = P(6), z = P(7);
      Cx c = { lA, A, t, D, x, e, l };
      ExprId fam = DSCOPE1(b_down_fam, t_univ, &c, LSUCC(l), guard_now());
      finish(CALL(TD_COE, l, fam, z)); }
}

void templates_init(void) {
    static pthread_mutex_t once = PTHREAD_MUTEX_INITIALIZER;
    pthread_mutex_lock(&once);
    if (!TPL.init) { memset(&TPL, 0, sizeof TPL); pthread_mutex_init(&TPL.mu, NULL); register_library(); TPL.init = true; }
    pthread_mutex_unlock(&once);
}
void templates_free(void) {
    if (!TPL.init) return;
    for (size_t k = 0; k < TD_COUNT; k++) words_free(&TPL.defs[k].nodes);
    pthread_mutex_destroy(&TPL.mu);
    memset(&TPL, 0, sizeof TPL);
}

/* the environment and root of a definition's program at arguments args (for
 * a frame that awaits its interpretation) */
void template_call_env(TDefKind def, size_t nargs, const TVal *args, WordBuf *er, ExprId *root) {
    /* the environment record [def, (k, sort, arg)*] into a buffer (a fixed
     * library arity: bounded), interned by the caller's stepped subroutine */
    templates_init();
    const TDef *d = &TPL.defs[def];
    require(nargs == d->nparams && nargs < 16, "template call arity (%s)", d->name);
    wordbuf_init(er); wordbuf_push(er, def);
    for (size_t k = 0; k < nargs; k++) {
        require(args[k].sort == d->sorts[k], "template call sort (%s, %zu)", d->name, k);
        wordbuf_push(er, k); wordbuf_push(er, args[k].sort); wordbuf_push(er, args[k].id);
    }
    *root = d->root;
}

TVal template_call(TDefKind def, size_t nargs, const TVal *args) {
    templates_init();
    const TDef *d = &TPL.defs[def];
    require(nargs == d->nparams, "template_call arity (%s)", d->name);
    uint64_t *sl = malloc((nargs ? nargs : 1) * sizeof(uint64_t)); TVal *vl = malloc((nargs ? nargs : 1) * sizeof(TVal));
    require(sl && vl, "out of memory");
    for (size_t k = 0; k < nargs; k++) { require(args[k].sort == d->sorts[k], "template_call sort (%s, %zu)", d->name, k); sl[k] = k; vl[k] = args[k]; }
    uint64_t er = envrec_host(def, nargs, sl, vl);
    free(sl); free(vl);
    return interp_at(d->root, er);
}
