#include "template.h"
#include "eval.h"

/* ------------------------------------------------------------------ */
/* expressions: interned records [kind, words...]                        */

enum {
    X_LEVEL = 3,       /* [X_LEVEL, n]: a closed payload or annotation */
    X_CONST = 25       /* [X_CONST, sort, id]: a construction's closed field constant */
};

static ExprId xi(size_t n, const uint64_t *w) { return interner_intern(&M.keys, w, n, NULL); }
static ExprId x1(uint64_t k, uint64_t a) { uint64_t w[2] = { k, a }; return xi(2, w); }

/* ------------------------------------------------------------------ */
/* nodes: [def, np, tag, payload_e, levels_e, nf, (kind, bslot, e)*, nb, (sort, domfield, lslot)*, (sort, type_e)*np] */

TDefId tnode_def(TNodeId Q) { return rword(Q, 0); }
Tag tnode_tag(TNodeId Q) { return (Tag)rword(Q, 2); }
static ExprId node_payload_e(TNodeId Q) { return rword(Q, 3); }
static ExprId node_levels_e(TNodeId Q) { return rword(Q, 4); }
size_t tnode_nfields(TNodeId Q) { return (size_t)rword(Q, 5); }
static void node_field(TNodeId Q, size_t k, FieldKind *kind, BinderSlot *bslot, ExprId *e) {
    size_t n; const uint64_t *w = rget(Q, &n);
    *kind = (FieldKind)w[6 + 3 * k]; *bslot = (BinderSlot)w[7 + 3 * k]; *e = w[8 + 3 * k];
}
FieldKind tnode_field_kind(TNodeId Q, size_t k) { FieldKind kd; BinderSlot s; ExprId e; node_field(Q, k, &kd, &s, &e); return kd; }
BinderSlot tnode_field_slot(TNodeId Q, size_t k) { FieldKind kd; BinderSlot s; ExprId e; node_field(Q, k, &kd, &s, &e); return s; }
static const uint64_t *node_btab(TNodeId Q) { size_t n; const uint64_t *w = rget(Q, &n); return w + 6 + 3 * w[5]; }
static void node_binder(TNodeId Q, BinderSlot s, Sort *sort, FieldIndex *domfield, size_t *lslot) {
    const uint64_t *b = node_btab(Q);
    require(s < b[0], "template binder slot");
    *sort = (Sort)b[1 + 3 * s]; *domfield = (FieldIndex)b[2 + 3 * s]; *lslot = (size_t)b[3 + 3 * s];
}
Sort tnode_binder_sort(TNodeId Q, BinderSlot s) { Sort so; FieldIndex f; size_t l; node_binder(Q, s, &so, &f, &l); return so; }
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

/* a construction's free slots are its parameters 0..np-1 */
static size_t node_param_count(TNodeId Q);
static size_t node_free_count(TNodeId Q) { return node_param_count(Q); }
static size_t node_free_slot(TNodeId Q, size_t q) { (void)Q; return q; }

/* ------------------------------------------------------------------ */
/* environments and interpretation (as families, below)                 */


/* a reference's environment is its interpretation record [(slot, sort, id)*,
 * def] (a substitution record, subst.c) restricted to the node's free slots */

/* An interpreted value is the interned pair [sort, id]. */
static uint64_t tvrec(PSort sort, uint64_t id) { return RQ(sort, id); }
static TVal tvget(uint64_t rec) { size_t n; const uint64_t *w = rget(rec, &n); TVal v = { (PSort)w[0], w[1] }; return v; }

/* ------------------------------------------------------------------ */
/* constructions: nodes with closed constant fields (template.h)          */

ExprId expr_const(PSort sort, uint64_t id) { uint64_t w[3] = { X_CONST, sort, id }; return xi(3, w); }
ExprId expr_level(uint64_t n) { return x1(X_LEVEL, n); }
static size_t node_param_count(TNodeId Q) { return (size_t)rword(Q, 1); }
static uint64_t xlevel(ExprId e) { size_t n; const uint64_t *w = rget(e, &n); require(w[0] == X_LEVEL, "construction annotation is not a constant"); return w[1]; }
bool expr_is_level(ExprId e) { return rword(e, 0) == X_LEVEL; }
uint64_t expr_level_value(ExprId e) { return xlevel(e); }



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


/* ------------------------------------------------------------------ */
/* interpretation families                                               */
/* INTERP(e, env) interprets one expression; TVMAKE(Q, env) is the view of a
 * node in an environment (its support and free variables those of its
 * images). An environment is read and set by the substitution record's
 * lookup and set (subst.c). Each step does a constant amount of work. */


static Family trav_of(PSort s) { return s == PS_REF ? F_TREF : s == PS_INTERVAL ? F_TIV : F_TFC; }

/* INTERP(e, env): a closed constant with its atoms read from the
 * environment (APPLY), or a closed level */
static void interp_step(Cont *k, uint64_t v) {
    ExprId e = k->w[0]; uint64_t er = k->w[1];
    uint64_t r = 0;
    FR_BEGIN(k);
    {   size_t n; const uint64_t *w = rget(e, &n);
        if (w[0] == X_LEVEL) FR_FINISH(k, tvrec(PS_LEVEL, w[1]));
        require(w[0] == X_CONST, "bad expression kind %llu", (unsigned long long)w[0]);
        k->w[2] = w[1]; k->w[3] = w[2]; }
    if (k->w[2] == PS_REF || k->w[2] == PS_INTERVAL || k->w[2] == PS_FACE) FR_AWAIT(k, r, trav_of((PSort)k->w[2]), k->w[3], apply_key(er));
    else r = k->w[3];
    FR_FINISH(k, tvrec((PSort)k->w[2], r));
    FR_END(k);
}

/* the template view of node w[0] in environment w[1] */
typedef struct { size_t nf, q; uint64_t sup, fv, ds, E; TVal t; WordBuf out; bool created; } MkLoc;
static void tvmake_step(Cont *k, uint64_t v) {
    MkLoc *L = FR_LOC(k, MkLoc);
    TNodeId Q = k->w[0]; uint64_t er = k->w[1];
    uint64_t r = 0;
    FR_BEGIN(k);
    L->nf = node_free_count(Q);
    L->sup = set_make(NULL, 0); L->fv = set_make(NULL, 0);
    wordbuf_init(&L->out);
    for (L->q = 0; L->q < L->nf; L->q++) {
        FR_AWAIT(k, r, F_LOOKUP, er, node_free_slot(Q, L->q));
        require(r, "construction view: parameter %zu has no value", node_free_slot(Q, L->q));
        { uint64_t sl; subst_get(er, r - 1, &sl, &L->t); }
        wordbuf_push(&L->out, node_free_slot(Q, L->q)); wordbuf_push(&L->out, L->t.sort); wordbuf_push(&L->out, L->t.id);
        if (L->t.sort == PS_REF) {
            FR_AWAIT(k, L->sup, F_SUNION, L->sup, ref_support(L->t.id));
            FR_AWAIT(k, L->fv, F_SUNION, L->fv, ref_freevars(L->t.id));
        } else if (L->t.sort == PS_INTERVAL || L->t.sort == PS_FACE) {
            FR_AWAIT(k, L->ds, F_DIMS, L->t.id, 0);
            FR_AWAIT(k, L->sup, F_SUNION, L->sup, L->ds);
        }
    }
    wordbuf_push(&L->out, tnode_def(Q));
    FR_CALL(k, L->E, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_AWAIT(k, L->sup, F_SETFREE, L->sup, 0);
    FR_AWAIT(k, L->fv, F_SETFREE, L->fv, 0);
    FR_FINISH(k, ref_intern_tview(Q, L->E, L->sup, L->fv));
    FR_END(k);
}

void template_families_init(void) {
    family_define(F_INTERP, "node.interp", interp_step, 0);
    family_define(F_TVMAKE, "template.view", tvmake_step, sizeof(MkLoc));
}

/* ------------------------------------------------------------------ */
/* TVIEW operations (synchronous driver over the families)               */


void tview_open(RefId t, Head *h) {
    TNodeId Q = ref_tnode(t);
    h->tnode = Q; h->tenv = ref_tenv(t);
    h->tag = tnode_tag(Q);
    h->n = tnode_nfields(Q);
    h->payload = family_call(F_HEAD, t, 0);
    h->levels = family_call(F_HEAD, t, 1);
}


