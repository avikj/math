/* construct.c — constructions, field opening, binder application and
 * variable references as pure producer families.
 *
 * CONSTRUCT(request) builds the construction node of a request record
 *   [tag, payload, levels, declared, ft, fd, nf, (kind, slot, id)*, nb, (sort, formal, domain)*]
 * (ft/fd = 0: the boundary is computed from the fields): its typed free
 * boundary, required face, the closing substitution Φ (parameter k ↦ atom k,
 * dimensions first), the field constants closed by Φ (a field under binder s
 * also closes the formal into atom np+s), the closed parameter declarations,
 * the node record, the environment of the boundary itself and the instance.
 * FIELD(t, k) opens one field; BINDER(t, [sort, slot, field, image]) is a
 * binder field with its atom ↦ image; REFVAR(x) is VAR(x) with its typed
 * boundary. Every step does a constant amount of work; every intermediate is
 * awaited from its family. */
#include "eval.h"
#include "template.h"

static Family F_REFVAR, F_FCDIMS, F_FIELD, F_BINDER, F_CONSTRUCT;
static Family F_INTERP, F_ENVSET;   /* template families (bound after their registration) */
static Family F_REINDEX, F_IVRE, F_FCRE, F_TVMAKE, F_IVDIMS, F_OVERRIDE;
static Family F_DSUNION, F_VSUNION, F_DSREMOVE, F_VSREMOVE, F_FCMEET, F_FCJOIN, F_FCFORALL;

/* ---------------- VAR(x) ---------------- */
typedef struct { uint64_t fv, sup, req, ds; } VarLoc;
static void refvar_step(Cont *k, uint64_t v) {
    VarLoc *L = FR_LOC(k, VarLoc);
    TermVarId x = k->w[0];
    FR_BEGIN(k);
    { uint64_t w[2] = { 1, x }; RefId id = ref_lookup(w, 2); if (id) FR_FINISH(k, id); }
    if (is_local_atom(x)) FR_FINISH(k, ref_var(x));          /* an atom: constant side data */
    {   RefId type = term_var_type(x);
        uint64_t xs[1] = { x }; L->fv = varset_make(xs, 1); L->sup = ref_support(type); L->req = term_var_required(x); }
    FR_AWAIT(k, L->fv, F_VSUNION, L->fv, ref_freevars(term_var_type(x)));
    FR_AWAIT(k, L->req, F_FCMEET, L->req, ref_required(term_var_type(x)));
    FR_AWAIT(k, L->ds, F_FCDIMS, L->req, 0);
    FR_AWAIT(k, L->sup, F_DSUNION, L->sup, L->ds);
    FR_FINISH(k, ref_var_publish(x, L->sup, L->fv, L->req));
    FR_END(k);
}

/* the dimensions of a face as a set */
typedef struct { const uint64_t *x; size_t nx, i; uint64_t acc; } DimsLoc;
static void fcdims_step(Cont *k, uint64_t v) {
    DimsLoc *L = FR_LOC(k, DimsLoc);
    FR_BEGIN(k);
    L->x = interner_get(&M.faces, k->w[0], &L->nx);
    L->acc = dimset_make(NULL, 0);
    for (L->i = 0; L->i < L->nx; L->i++) {
        if (L->x[L->i] == DNF_SEP) continue;
        { uint64_t d = FC_LIT_DIM(L->x[L->i]); FR_AWAIT(k, L->acc, F_DSUNION, L->acc, dimset_make(&d, 1)); }
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
static Family dims_family(FieldKind kind) { return kind == F_INTERVAL ? F_IVDIMS : F_FCDIMS; }

/* ---------------- field opening ---------------- */
typedef struct { uint64_t m; } FieldLoc;
static void field_step(Cont *k, uint64_t v) {
    FieldLoc *L = FR_LOC(k, FieldLoc);
    RefId t = k->w[0]; size_t q = (size_t)k->w[1];
    uint64_t r = 0;
    FR_BEGIN(k);
    /* field q's own expression in the node's environment (a construction's
     * closed constant and a template program's recipe alike); fields 0..q-1
     * are not opened */
    require(tnode_field_slot(ref_tnode(t), q) == NO_SLOT, "a binder field is opened through its binder");
    L->m = ref_tenv(t);
    FR_AWAIT(k, r, F_INTERP, tnode_field_expr(ref_tnode(t), q), L->m);
    { size_t n; const uint64_t *w = interner_get(&M.keys, r, &n); FR_FINISH(k, w[1]); }
    FR_END(k);
}

/* ---------------- binder fields: the binder's atom ↦ image ---------------- */
typedef struct { uint64_t m, sort, slot, field, image; } BindLoc;
static void binder_step(Cont *k, uint64_t v) {
    BindLoc *L = FR_LOC(k, BindLoc);
    RefId t = k->w[0];
    uint64_t r = 0;
    FR_BEGIN(k);
    { size_t n; const uint64_t *e = interner_get(&M.keys, k->w[1], &n); L->sort = e[0]; L->slot = e[1]; L->field = e[2]; L->image = e[3]; }
    /* the binder's local set to the image in the node's environment, the
     * body's expression interpreted (both node kinds) */
    require(tnode_binder_sort(ref_tnode(t), (BinderSlot)L->slot) == (Sort)L->sort, "binder sort");
    L->m = ref_tenv(t);
    {   uint64_t es; ExprId be; tnode_template_binder(ref_tnode(t), (BinderSlot)L->slot, (FieldIndex)L->field, &es, &be);
        uint64_t e[3] = { es, L->sort == S_TERM ? PS_REF : PS_INTERVAL, L->image };
        FR_AWAIT(k, L->m, F_ENVSET, L->m, interner_intern(&M.keys, e, 3, NULL)); }
    {   uint64_t es; ExprId be; tnode_template_binder(ref_tnode(t), (BinderSlot)L->slot, (FieldIndex)L->field, &es, &be);
        FR_AWAIT(k, r, F_INTERP, be, L->m); }
    { size_t n; const uint64_t *w = interner_get(&M.keys, r, &n); FR_FINISH(k, w[1]); }
    FR_END(k);
}

/* ---------------- constructions ---------------- */
typedef struct {
    const uint64_t *rq; size_t nrq;
    uint64_t tag, payload, levels, declared; size_t nf, nb;
    const uint64_t *fields, *binders;
    uint64_t ft, fd, req, phi, mq, fv, ds, c, ty, g, E, Q;
    const uint64_t *xs, *dset; size_t nt, nd, np, q;
    WordBuf w; bool created;
} ConLoc;
static uint64_t con_field_kind(const ConLoc *L, size_t q) { return L->fields[3 * q]; }
static uint64_t con_field_slot(const ConLoc *L, size_t q) { return L->fields[3 * q + 1]; }
static uint64_t con_field_id(const ConLoc *L, size_t q) { return L->fields[3 * q + 2]; }
static uint64_t con_binder_sort(const ConLoc *L, size_t s) { return L->binders[3 * s]; }
static uint64_t con_binder_formal(const ConLoc *L, size_t s) { return L->binders[3 * s + 1]; }
static uint64_t con_binder_domain(const ConLoc *L, size_t s) { return L->binders[3 * s + 2]; }
static bool partial_position(uint64_t tag, size_t q) {
    return (tag == T_COMP && q == 2) || (tag == T_GLUE_TYPE && (q == 2 || q == 3)) ||
           (tag == T_GLUE_INTRO && (q == 2 || q == 3 || q == 4)) || (tag == T_UNGLUE && (q == 2 || q == 3));
}
static PSort psort_of(uint64_t kind) { return kind == F_REF ? PS_REF : kind == F_INTERVAL ? PS_INTERVAL : PS_FACE; }
static Family reindex_family(uint64_t kind) { return kind == F_REF ? F_REINDEX : kind == F_INTERVAL ? F_IVRE : F_FCRE; }

static void construct_step(Cont *k, uint64_t v) {
    ConLoc *L = FR_LOC(k, ConLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->rq = interner_get(&M.keys, k->w[0], &L->nrq);
    L->tag = L->rq[0]; L->payload = L->rq[1]; L->levels = L->rq[2]; L->declared = L->rq[3];
    L->ft = L->rq[4]; L->fd = L->rq[5]; L->nf = (size_t)L->rq[6]; L->fields = L->rq + 7;
    L->nb = (size_t)L->rq[7 + 3 * L->nf]; L->binders = L->rq + 8 + 3 * L->nf;
    /* the typed free boundary: field boundaries (closed through declaration
     * types) minus the formal bound at the field's binder */
    if (!L->ft) {
        L->ft = varset_make(NULL, 0); L->fd = dimset_make(NULL, 0);
        for (L->q = 0; L->q < L->nf; L->q++) {
            if (con_field_kind(L, L->q) == F_REF) { L->fv = ref_freevars(con_field_id(L, L->q)); L->ds = ref_support(con_field_id(L, L->q)); }
            else { L->fv = varset_make(NULL, 0); FR_AWAIT(k, L->ds, dims_family((FieldKind)con_field_kind(L, L->q)), con_field_id(L, L->q), 0); }
            if (con_field_slot(L, L->q) != NO_SLOT) {
                require(con_field_slot(L, L->q) < L->nb, "field refers to a missing binder");
                if (con_binder_sort(L, con_field_slot(L, L->q)) == S_TERM) FR_AWAIT(k, L->fv, F_VSREMOVE, L->fv, con_binder_formal(L, con_field_slot(L, L->q)));
                else FR_AWAIT(k, L->ds, F_DSREMOVE, L->ds, con_binder_formal(L, con_field_slot(L, L->q)));
            }
            FR_AWAIT(k, L->ft, F_VSUNION, L->ft, L->fv);
            FR_AWAIT(k, L->fd, F_DSUNION, L->fd, L->ds);
        }
    }
    for (L->q = 0; L->q < L->nb; L->q++) {
        if (con_binder_sort(L, L->q) == S_TERM) require(con_binder_domain(L, L->q) < L->nf, "term binder without domain field");
        FR_YIELD(k);                                        /* one binder per step */
    }
    /* the required face: a system requires the join of its guards; another
     * construction what its total reference fields require (a field under a
     * dimension binder along the whole line); partial positions are used
     * under their guards only */
    if (L->tag == T_SYSTEM) {
        L->req = fc_false();
        for (L->q = 0; L->q < L->nf; L->q += 2) FR_AWAIT(k, L->req, F_FCJOIN, L->req, con_field_id(L, L->q));
    } else {
        L->req = fc_true();
        for (L->q = 0; L->q < L->nf; L->q++) {
            if (con_field_kind(L, L->q) != F_REF || partial_position(L->tag, L->q)) {
                FR_YIELD(k);                                /* a skipped field is still one step */
                continue;
            }
            L->g = ref_required(con_field_id(L, L->q));
            if (con_field_slot(L, L->q) != NO_SLOT && con_binder_sort(L, con_field_slot(L, L->q)) == S_DIM)
                FR_AWAIT(k, L->g, F_FCFORALL, L->g, con_binder_formal(L, con_field_slot(L, L->q)));
            FR_AWAIT(k, L->req, F_FCMEET, L->req, L->g);
        }
    }
    if (L->declared) {
        FR_AWAIT(k, L->req, F_FCMEET, L->req, L->declared);
        FR_AWAIT(k, L->ds, F_FCDIMS, L->declared, 0);
        FR_AWAIT(k, L->fd, F_DSUNION, L->fd, L->ds);
    }
    L->dset = interner_get(&M.dimsets, L->fd, &L->nd);
    L->xs = interner_get(&M.varsets, L->ft, &L->nt);
    L->np = L->nd + L->nt;
    /* Φ: term variable k ↦ atom nd+k, dimension k ↦ atom k (a map record:
     * terms, then dimensions, then the term count) */
    wordbuf_init(&L->w);
    for (L->q = 0; L->q < L->nt; L->q++) {
        require(!is_local_atom(L->xs[L->q]), "a construction's boundary contains a bound atom");
        wordbuf_push(&L->w, L->xs[L->q]); wordbuf_push(&L->w, ref_var(obound_id((uint32_t)(L->nd + L->q))));
        FR_YIELD(k);
    }
    for (L->q = 0; L->q < L->nd; L->q++) {
        require(!is_local_atom(L->dset[L->q]), "a construction's boundary contains a bound atom");
        wordbuf_push(&L->w, L->dset[L->q]); wordbuf_push(&L->w, iv_var(obound_id((uint32_t)L->q)));
        FR_YIELD(k);
    }
    wordbuf_push(&L->w, L->nt);
    FR_CALL(k, L->phi, intern_sub(k, &M.maps, &L->w, &L->created));
    /* the node record */
    wordbuf_init(&L->w);
    wordbuf_push(&L->w, 0); wordbuf_push(&L->w, L->np); wordbuf_push(&L->w, L->tag);
    wordbuf_push(&L->w, L->payload ? expr_level(L->payload) : 0);
    wordbuf_push(&L->w, L->levels != LEVELS_NONE ? expr_level(L->levels) : 0);
    wordbuf_push(&L->w, L->nf);
    for (L->q = 0; L->q < L->nf; L->q++) {
        L->mq = L->phi;
        if (con_field_slot(L, L->q) != NO_SLOT) {
            uint64_t s = con_field_slot(L, L->q), atom = obound_id((uint32_t)(L->np + s));
            uint64_t img = con_binder_sort(L, s) == S_TERM ? ref_var(atom) : iv_var(atom);
            uint64_t e[3] = { con_binder_sort(L, s), con_binder_formal(L, s), img };
            FR_AWAIT(k, L->mq, F_OVERRIDE, L->phi, interner_intern(&M.keys, e, 3, NULL));
        }
        FR_AWAIT(k, L->c, reindex_family(con_field_kind(L, L->q)), con_field_id(L, L->q), L->mq);
        wordbuf_push(&L->w, con_field_kind(L, L->q)); wordbuf_push(&L->w, con_field_slot(L, L->q));
        wordbuf_push(&L->w, expr_const(psort_of(con_field_kind(L, L->q)), L->c));
    }
    wordbuf_push(&L->w, L->nb);
    for (L->q = 0; L->q < L->nb; L->q++) { wordbuf_push(&L->w, con_binder_sort(L, L->q)); wordbuf_push(&L->w, con_binder_domain(L, L->q)); wordbuf_push(&L->w, L->q); FR_YIELD(k); }
    FR_AWAIT(k, L->c, F_FCRE, L->req, L->phi);
    wordbuf_push(&L->w, expr_const(PS_FACE, L->c));
    if (L->declared) { FR_AWAIT(k, L->c, F_FCRE, L->declared, L->phi); wordbuf_push(&L->w, expr_const(PS_FACE, L->c)); }
    else wordbuf_push(&L->w, 0);
    for (L->q = 0; L->q < L->nd; L->q++) { wordbuf_push(&L->w, PS_INTERVAL); wordbuf_push(&L->w, 0); wordbuf_push(&L->w, 0); FR_YIELD(k); }
    for (L->q = 0; L->q < L->nt; L->q++) {
        FR_AWAIT(k, L->ty, F_REINDEX, term_var_type(L->xs[L->q]), L->phi);
        FR_AWAIT(k, L->g, F_FCRE, term_var_required(L->xs[L->q]), L->phi);
        wordbuf_push(&L->w, PS_REF); wordbuf_push(&L->w, expr_const(PS_REF, L->ty)); wordbuf_push(&L->w, expr_const(PS_FACE, L->g));
    }
    FR_CALL(k, L->Q, intern_sub(k, &M.tnodes, &L->w, &L->created));
    /* the environment of the boundary itself (its interpretation record) */
    wordbuf_init(&L->w); wordbuf_push(&L->w, 0);
    for (L->q = 0; L->q < L->nd; L->q++) { wordbuf_push(&L->w, L->q); wordbuf_push(&L->w, PS_INTERVAL); wordbuf_push(&L->w, iv_var(L->dset[L->q])); FR_YIELD(k); }
    for (L->q = 0; L->q < L->nt; L->q++) {
        FR_AWAIT(k, r, F_REFVAR, L->xs[L->q], 0);
        wordbuf_push(&L->w, L->nd + L->q); wordbuf_push(&L->w, PS_REF); wordbuf_push(&L->w, r);
    }
    FR_CALL(k, L->E, intern_sub(k, &M.keys, &L->w, &L->created));
    FR_AWAIT(k, r, F_TVMAKE, L->Q, L->E);
    FR_FINISH(k, r);
    FR_END(k);
}

/* a head's payload (w[1] = 0) or formation levels (w[1] = 1): constants of a
 * construction node, interpreted for a template node */
static Family F_HEAD;
static void head_step(Cont *k, uint64_t v) {
    RefId t = k->w[0];
    uint64_t r = 0;
    FR_BEGIN(k);
    {   TNodeId Q = ref_tnode(t); ExprId e = tnode_head_expr(Q, (int)k->w[1]);
        if (!e) FR_FINISH(k, k->w[1] ? LEVELS_NONE : 0);
        if (expr_is_level(e)) FR_FINISH(k, expr_level_value(e)); }     /* a closed expression needs no environment */
    r = ref_tenv(t);
    FR_AWAIT(k, r, F_INTERP, tnode_head_expr(ref_tnode(t), (int)k->w[1]), r);
    { size_t n; const uint64_t *w = interner_get(&M.keys, r, &n); FR_FINISH(k, w[1]); }
    FR_END(k);
}

/* a global reference unfolded: the definition body under the substitution of
 * the definition's parameters by the reference's environment (the map record
 * is written directly: parameters are sorted, images are the entries) */
typedef struct { const uint64_t *xs, *ds; size_t nt, nd, q, kept; uint64_t s, m; WordBuf w; bool created; } UnfLoc;
static Family F_UNFOLD;
static bool unf_identity(bool dim, uint64_t key, uint64_t img) { return dim ? img == iv_var(key) : (ref_is_var(img) && ref_var_id(img) == key); }
/* global.args(t): the substitution of a global's parameters by the
 * reference's environment (identity entries dropped), written directly */
static Family F_GARGS;
static void gargs_step(Cont *k, uint64_t v) {
    UnfLoc *L = FR_LOC(k, UnfLoc);
    RefId t = k->w[0];
    FR_BEGIN(k);
    require(!ref_is_var(t) && ref_tag(t) == T_GLOBAL && tview_is_construction(t), "arguments of a non-global");
    L->s = tnode_const_payload(ref_tnode(t));
    L->xs = varset_get(global_params((SymbolId)L->s), &L->nt);
    L->ds = dimset_get(global_dims((SymbolId)L->s), &L->nd);
    require(tenv_size(ref_tenv(t)) == L->nd + L->nt, "global reference with a strengthened boundary");
    wordbuf_init(&L->w); L->kept = 0;
    for (L->q = 0; L->q < L->nt; L->q++) {
        {   uint64_t slot; TVal val; tenv_entry(ref_tenv(t), L->nd + L->q, &slot, &val);
            if (!unf_identity(false, L->xs[L->q], val.id)) { wordbuf_push(&L->w, L->xs[L->q]); wordbuf_push(&L->w, val.id); L->kept++; } }
        FR_YIELD(k);
    }
    for (L->q = 0; L->q < L->nd; L->q++) {
        {   uint64_t slot; TVal val; tenv_entry(ref_tenv(t), L->q, &slot, &val);
            if (!unf_identity(true, L->ds[L->q], val.id)) { wordbuf_push(&L->w, L->ds[L->q]); wordbuf_push(&L->w, val.id); } }
        FR_YIELD(k);
    }
    wordbuf_push(&L->w, L->kept);
    FR_CALL(k, L->m, intern_sub(k, &M.maps, &L->w, &L->created));
    FR_FINISH(k, L->m);
    FR_END(k);
}
static void unfold_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    FR_BEGIN(k);
    require(k->w[1] != 0, "unfold of a global at its opaque revision");   /* w[1]: the pinned body */
    FR_AWAIT(k, r, F_GARGS, k->w[0], 0);
    FR_AWAIT(k, r, F_REINDEX, k->w[1], r);
    FR_FINISH(k, r);
    FR_END(k);
}

/* globals.of(x, kind): the global symbols a reference (kind 0) or a scope
 * (kind 1) names directly — through its field constants, its environment
 * values and, for a global reference, its own symbol. Bodies are not entered (that is the closure of an
 * observation's premises, pins.c). A set of symbol ids (a varset). */
typedef struct { size_t n, q, nf; uint64_t acc, f, a, b, r; } GlLoc;
static Family F_GLOBALS;
/* the demand for item q of x (kind w[1]): a family key, or none (f = 0) */
static void gl_item(const Cont *k, size_t q, size_t nf, uint64_t *f, uint64_t *a, uint64_t *b) {
    uint64_t x = k->w[0]; *f = 0; *a = *b = 0;
    if (k->w[1] == 1) {
        size_t n = scope_arity(x);
        RefId r = q < n ? scope_local(x, q).type : q == n ? scope_type(x) : (scope_body(x).sort == VS_REF ? scope_body(x).id : 0);
        if (r) { *f = F_GLOBALS; *a = r; }
        return;
    }
    TNodeId Q = ref_tnode(x); uint64_t sort = PS_LEVEL, id = 0;
    if (q < nf) { if (tnode_field_kind(Q, q) == F_REF) { sort = PS_REF; id = tnode_const_field(Q, q); } }
    else { uint64_t slot; TVal val; tenv_entry(ref_tenv(x), q - nf, &slot, &val); sort = val.sort; id = val.id; }
    if (sort == PS_REF && id) { *f = F_GLOBALS; *a = id; }
    else if (sort == PS_SCOPE) { *f = F_GLOBALS; *a = id; *b = 1; }
}
static void globals_step(Cont *k, uint64_t v) {
    GlLoc *L = FR_LOC(k, GlLoc);
    uint64_t x = k->w[0];
    FR_BEGIN(k);
    L->acc = varset_make(NULL, 0);
    if (k->w[1] == 1) { L->nf = 0; L->n = scope_arity(x) + 2; }
    else {
        if (ref_is_var(x)) FR_FINISH(k, L->acc);
        {   TNodeId Q = ref_tnode(x);
            if (tnode_is_construction(Q)) {
                if (tnode_tag(Q) == T_GLOBAL) { uint64_t s = tnode_const_payload(Q); L->acc = varset_make(&s, 1); }
                L->nf = tnode_nfields(Q);
            } else L->nf = 0;                                  /* a template program names no symbol: its environment's values */
            L->n = L->nf + tenv_size(ref_tenv(x)); }
    }
    /* the items' symbol sets are independent demands: launched, then awaited in order */
    for (L->q = 0; L->q < L->n; L->q++) {
        gl_item(k, L->q, L->nf, &L->f, &L->a, &L->b);
        if (L->f) family_launch((Family)L->f, L->a, L->b);
        FR_YIELD(k);
    }
    for (L->q = 0; L->q < L->n; L->q++) {
        gl_item(k, L->q, L->nf, &L->f, &L->a, &L->b);
        if (!L->f) { FR_YIELD(k); continue; }
        FR_AWAIT(k, L->r, (Family)L->f, L->a, L->b);
        {   size_t m; (void)varset_get(L->r, &m); if (!m) { FR_YIELD(k); continue; } }
        FR_AWAIT(k, L->acc, F_VSUNION, L->acc, L->r);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

void construct_families_init(void) {
    F_REINDEX = family_lookup("reindex"); F_IVRE = family_lookup("iv.reindex"); F_FCRE = family_lookup("fc.reindex");
    F_IVDIMS = family_lookup("iv.dims");
    F_OVERRIDE = family_lookup("map.override");
    F_DSUNION = family_lookup("dimset.union"); F_VSUNION = family_lookup("varset.union");
    F_DSREMOVE = family_lookup("dimset.remove"); F_VSREMOVE = family_lookup("varset.remove");
    F_FCMEET = family_lookup("fc.meet"); F_FCJOIN = family_lookup("fc.join"); F_FCFORALL = family_lookup("fc.forall");
    require(F_REINDEX && F_FCFORALL, "the substitution families are registered first");
    F_REFVAR = family_define("ref.var", refvar_step, sizeof(VarLoc));
    F_FCDIMS = family_define("fc.dims", fcdims_step, sizeof(DimsLoc));
    F_FIELD = family_define("field", field_step, sizeof(FieldLoc));
    F_BINDER = family_define("binder", binder_step, sizeof(BindLoc));
    F_CONSTRUCT = family_define("construct", construct_step, sizeof(ConLoc));
    F_HEAD = family_define("head.annotation", head_step, 0);
    F_GARGS = family_define("global.args", gargs_step, sizeof(UnfLoc));
    F_UNFOLD = family_define("global.unfold", unfold_step, 0);    /* keyed by (reference, body revision) */
    F_GLOBALS = family_define("globals.of", globals_step, sizeof(GlLoc));
}
/* the template families register after the construction families; their ids are read lazily */
void construct_bind_template_families(void) { F_TVMAKE = family_lookup("template.view"); F_INTERP = family_lookup("template.interp"); F_ENVSET = family_lookup("template.envset"); require(F_INTERP && F_ENVSET, "template families"); }

/* ---------------- the operations (synchronous driver) ---------------- */
RefId construct_request(const uint64_t *req, size_t n) { return family_call(F_CONSTRUCT, interner_intern(&M.keys, req, n, NULL), 0); }
uint64_t construction_field(RefId t, size_t k) { return family_call(F_FIELD, t, k); }
RefId construction_binder(RefId t, Sort sort, BinderSlot slot, FieldIndex field, uint64_t image) {
    uint64_t e[4] = { sort, slot, field, image };
    return family_call(F_BINDER, t, interner_intern(&M.keys, e, 4, NULL));
}
RefId ref_var_family(TermVarId x) { return family_call(F_REFVAR, x, 0); }
