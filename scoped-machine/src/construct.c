/* construct.c — constructions, field opening, binder application and
 * variable references as pure producer families.
 *
 * CONSTRUCT(request) builds the construction node of a request record
 *   [tag, payload, levels, declared, ft, fd, nf, (kind, slot, id)*, nb, (sort, formal, domain)*]
 * (ft/fd = 0: the boundary is computed from the fields): its typed free
 * boundary, required face, its CLOSE context Φ (parameter k ↦ slot k,
 * dimensions first), the field constants closed by Φ (a field under binder s
 * also closes the formal into slot np+s), the closed parameter declarations,
 * the node record, the environment of the boundary itself and the instance.
 * FIELD(t, k) opens one field; BINDER(t, [sort, slot, field, image]) is a
 * binder field with its atom ↦ image; REFVAR(x) is VAR(x) with its typed
 * boundary. Every step does a constant amount of work; every intermediate is
 * awaited from its family. */
#include "eval.h"
#include "template.h"

/* ---------------- the constructor schema ---------------- */
#define R_ F_REF
#define I_ F_INTERVAL
#define F_ F_FACE
static const TagSchema SCHEMA[] = {
    [T_UNIVERSE]   = { 0, 0, ROLE_INTRO, 0, { 0 }, { 0 }, { 0 } },
    [T_PI]         = { 2, S_TERM, ROLE_INTRO, 0, { R_, R_ }, { 0, 1 }, { 0 } },
    [T_SIGMA]      = { 2, S_TERM, ROLE_INTRO, 0, { R_, R_ }, { 0, 1 }, { 0 } },
    [T_LAM]        = { 2, S_TERM, ROLE_INTRO, 0, { R_, R_ }, { 0, 1 }, { 0 } },
    [T_APP]        = { 2, 0, ROLE_ELIM, 0, { R_, R_ }, { 0 }, { 0 } },
    [T_PAIR]       = { 3, 0, ROLE_INTRO, 0, { R_, R_, R_ }, { 0 }, { 0 } },
    [T_FST]        = { 1, 0, ROLE_ELIM, 0, { R_ }, { 0 }, { 0 } },
    [T_SND]        = { 1, 0, ROLE_ELIM, 0, { R_ }, { 0 }, { 0 } },
    [T_PATH]       = { 3, S_DIM, ROLE_INTRO, 0, { R_, R_, R_ }, { 1, 0, 0 }, { 0 } },
    [T_PLAM]       = { 1, S_DIM, ROLE_INTRO, 0, { R_ }, { 1 }, { 0 } },
    [T_PAPP]       = { 5, S_DIM, ROLE_ELIM, 3, { R_, R_, R_, R_, I_ }, { 1, 0, 0, 0, 0 }, { 0 } },
    [T_GLUE_TYPE]  = { 4, 0, ROLE_OTHER, 0, { R_, F_, R_, R_ }, { 0 }, { 0, 0, 1, 1 } },
    [T_GLUE_INTRO] = { 6, 0, ROLE_OTHER, 0, { R_, F_, R_, R_, R_, R_ }, { 0 }, { 0, 0, 1, 1, 1 } },
    [T_UNGLUE]     = { 5, 0, ROLE_ELIM, 4, { R_, F_, R_, R_, R_ }, { 0 }, { 0, 0, 1, 1 } },
    [T_COMP]       = { 4, S_DIM, ROLE_OTHER, 0, { R_, F_, R_, R_ }, { 1, 0, 1, 0 }, { 0, 0, 1 } },
    [T_SYSTEM]     = { 0, 0, ROLE_OTHER, 0, { 0 }, { 0 }, { 0 } },
    [T_GLOBAL]     = { 0, 0, ROLE_OTHER, 0, { 0 }, { 0 }, { 0 } },
    [T_CODE]       = { 0, 0, ROLE_INTRO, 0, { 0 }, { 0 }, { 0 } },
    [T_QUOTE]      = { 1, 0, ROLE_INTRO, 0, { R_ }, { 0 }, { 1 } },   /* a code is total: the record it holds is data */
    [T_QIV]        = { 1, 0, ROLE_INTRO, 0, { I_ }, { 0 }, { 0 } },
    [T_QFC]        = { 1, 0, ROLE_INTRO, 0, { F_ }, { 0 }, { 0 } },
    [T_CMATCH]     = { 3, 0, ROLE_OTHER, 0, { R_, R_, R_ }, { 0 }, { 0 } },
    [T_CINST]      = { 2, 0, ROLE_OTHER, 0, { R_, R_ }, { 0 }, { 0 } },
    [T_CEQ]        = { 4, 0, ROLE_OTHER, 0, { R_, R_, R_, R_ }, { 0 }, { 0 } },
    [T_CENT]       = { 4, 0, ROLE_OTHER, 0, { R_, R_, R_, R_ }, { 0 }, { 0 } },
    [T_CFCEND]     = { 1, 0, ROLE_OTHER, 0, { R_ }, { 0 }, { 0 } },
    [T_CUNFOLD]    = { 3, 0, ROLE_OTHER, 0, { R_, R_, R_ }, { 0 }, { 0 } },
    [T_CSET]       = { 2, 0, ROLE_OTHER, 0, { R_, R_ }, { 0 }, { 0 } },
    [T_CLEVELS]    = { 2, 0, ROLE_OTHER, 0, { R_, R_ }, { 0 }, { 0 } },
    [T_CSETLV]     = { 3, 0, ROLE_OTHER, 0, { R_, R_, R_ }, { 0 }, { 0 } },
    [T_QLV]        = { 0, 0, ROLE_INTRO, 0, { 0 }, { 0 }, { 0 } },
    [T_CLSUCC]     = { 1, 0, ROLE_OTHER, 0, { R_ }, { 0 }, { 0 } },
    [T_CLMAX]      = { 2, 0, ROLE_OTHER, 0, { R_, R_ }, { 0 }, { 0 } },
    [T_COP]        = { 2, 0, ROLE_OTHER, 0, { R_, R_ }, { 0 }, { 0 } },
    [T_CSYSCONS]   = { 3, 0, ROLE_OTHER, 0, { R_, R_, R_ }, { 0 }, { 0 } },
    [T_CVAR]       = { 1, 0, ROLE_OTHER, 0, { R_ }, { 0 }, { 0 } },
    [T_CSUBST]     = { 3, 0, ROLE_OTHER, 0, { R_, R_, R_ }, { 0 }, { 0 } },
    [T_CTYPE]      = { 1, 0, ROLE_OTHER, 0, { R_ }, { 0 }, { 0 } },
};
#undef R_
#undef I_
#undef F_
const TagSchema *tag_schema(Tag tag) { require(tag >= T_UNIVERSE && tag <= T_LAST, "unknown tag %u", (unsigned)tag); return &SCHEMA[tag]; }
FieldKind schema_kind(Tag tag, size_t k) { return tag == T_SYSTEM ? (k % 2 ? F_REF : F_FACE) : (FieldKind)tag_schema(tag)->kind[k]; }
BinderSlot schema_slot(Tag tag, size_t k) { return tag != T_SYSTEM && tag_schema(tag)->under[k] ? 0 : NO_SLOT; }
static size_t creq_head(uint64_t *w, Tag tag, uint64_t payload, uint64_t levels, VarSetId ft, DimSetId fd, size_t nf) {
    w[0] = tag; w[1] = payload; w[2] = levels; w[3] = 0; w[4] = ft; w[5] = fd; w[6] = nf; return 7;
}
static void wb_words(WordBuf *b, const uint64_t *w, size_t n) { for (size_t q = 0; q < n; q++) wordbuf_push(b, w[q]); }
size_t creq_fixed(uint64_t *w, Tag tag, uint64_t payload, uint64_t levels, size_t n, const uint64_t *ids, uint64_t formal) {
    const TagSchema *s = tag_schema(tag);
    require(tag != T_SYSTEM && n <= s->nf, "a fixed-shape construction of %zu operands", n);
    size_t m = creq_head(w, tag, payload, levels, 0, 0, n);
    for (size_t k = 0; k < n; k++) { w[m++] = schema_kind(tag, k); w[m++] = schema_slot(tag, k); w[m++] = ids[k]; }
    w[m++] = s->bsort ? 1 : 0;
    if (s->bsort) { w[m++] = s->bsort; w[m++] = formal; w[m++] = s->bsort == S_TERM ? 0 : NO_FIELD; }
    return m;
}
void creq_begin(WordBuf *w, Tag tag, uint64_t payload, uint64_t levels, VarSetId ft, DimSetId fd, size_t nf) {
    uint64_t h[7]; wordbuf_init(w); wb_words(w, h, creq_head(h, tag, payload, levels, ft, fd, nf));
}
void creq_entry(WordBuf *w, uint64_t a, uint64_t b, uint64_t c) { wordbuf_push(w, a); wordbuf_push(w, b); wordbuf_push(w, c); }
void creq_tag(WordBuf *w, Tag tag, uint64_t payload, uint64_t levels, size_t n, const uint64_t *ids, uint64_t formal) {
    uint64_t r[CREQ_MAX]; wordbuf_init(w); wb_words(w, r, creq_fixed(r, tag, payload, levels, n, ids, formal));
}
void creq_system_begin(WordBuf *w, size_t n) { creq_begin(w, T_SYSTEM, n, LEVELS_NONE, 0, 0, 2 * n); }
void creq_system_branch(WordBuf *w, FaceId f, RefId t) { creq_entry(w, F_FACE, NO_SLOT, f); creq_entry(w, F_REF, NO_SLOT, t); }
RefId construct_buf(WordBuf *b) { return family_call(F_CONSTRUCT, wordbuf_intern(&M.keys, b), 0); }
RefId mk_tag(Tag tag, uint64_t payload, uint64_t levels, size_t n, const uint64_t *ids, uint64_t formal) {
    WordBuf w; creq_tag(&w, tag, payload, levels, n, ids, formal); return construct_buf(&w);
}


/* ---------------- VAR(x) ---------------- */
typedef struct { uint64_t fv, sup, req, ds; } VarLoc;
static void refvar_step(Cont *k, uint64_t v) {
    VarLoc *L = FR_LOC(k, VarLoc);
    TermVarId x = k->w[0];
    FR_BEGIN(k);
    if (is_bound_id(x)) FR_FINISH(k, ref_var(x));          /* an atom: constant side data */
    {   RefId type = term_var_type(x);
        uint64_t xs[1] = { x }; L->fv = set_make(xs, 1); L->sup = ref_support(type); L->req = term_var_required(x); }
    FR_AWAIT(k, L->fv, F_SUNION, L->fv, ref_freevars(term_var_type(x)));
    FR_AWAIT(k, L->req, F_FCMEET, L->req, ref_required(term_var_type(x)));
    FR_AWAIT(k, L->ds, F_DIMS, L->req, 0);
    FR_AWAIT(k, L->sup, F_SUNION, L->sup, L->ds);
    FR_FINISH(k, ref_var_publish(x, L->sup, L->fv, L->req));
    FR_END(k);
}

/* Φ(ft, fd): the CLOSE context of a boundary — dimension q ↦ slot q, term
 * variable q ↦ slot nd+q — its keys merged in order */
typedef struct { const uint64_t *xs, *ds; size_t nt, nd, i, j; WordBuf w; bool created; } PhiLoc;
static void phi_step(Cont *k, uint64_t v) {
    PhiLoc *L = FR_LOC(k, PhiLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    L->xs = set_get(k->w[0], &L->nt); L->ds = set_get(k->w[1], &L->nd);
    wordbuf_init(&L->w);
    for (L->i = 0, L->j = 0; L->i < L->nt || L->j < L->nd; ) {
        if (L->j == L->nd || (L->i < L->nt && L->xs[L->i] < L->ds[L->j])) {
            require(!is_bound_id(L->xs[L->i]), "a construction's boundary contains a bound atom");
            wordbuf_push(&L->w, L->xs[L->i]); wordbuf_push(&L->w, PS_REF); wordbuf_push(&L->w, L->nd + L->i); L->i++;
        } else {
            require(!is_bound_id(L->ds[L->j]), "a construction's boundary contains a bound atom");
            wordbuf_push(&L->w, L->ds[L->j]); wordbuf_push(&L->w, PS_INTERVAL); wordbuf_push(&L->w, L->j); L->j++;
        }
        FR_YIELD(k);
    }
    wordbuf_push(&L->w, 0);                                  /* total: no entry is dropped */
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->w, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}

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
    FR_FINISH(k, rword(r, 1));
    FR_END(k);
}

/* ---------------- binder fields: the binder's atom ↦ image ---------------- */
typedef struct { uint64_t m, sort, slot, field, image; } BindLoc;
static void binder_step(Cont *k, uint64_t v) {
    BindLoc *L = FR_LOC(k, BindLoc);
    RefId t = k->w[0];
    uint64_t r = 0;
    FR_BEGIN(k);
    { size_t n; const uint64_t *e = rget(k->w[1], &n); L->sort = e[0]; L->slot = e[1]; L->field = e[2]; L->image = e[3]; }
    /* the binder's local set to the image in the node's environment, the
     * body's expression interpreted (both node kinds) */
    require(tnode_binder_sort(ref_tnode(t), (BinderSlot)L->slot) == (Sort)L->sort, "binder sort");
    L->m = ref_tenv(t);
    {   uint64_t es; ExprId be; tnode_template_binder(ref_tnode(t), (BinderSlot)L->slot, (FieldIndex)L->field, &es, &be);
        FR_AWAIT(k, L->m, F_SET, L->m, subst_entry(es, L->sort == S_TERM ? PS_REF : PS_INTERVAL, L->image)); }
    {   uint64_t es; ExprId be; tnode_template_binder(ref_tnode(t), (BinderSlot)L->slot, (FieldIndex)L->field, &es, &be);
        FR_AWAIT(k, r, F_INTERP, be, L->m); }
    FR_FINISH(k, rword(r, 1));
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
static PSort psort_of(uint64_t kind) { return kind == F_REF ? PS_REF : kind == F_INTERVAL ? PS_INTERVAL : PS_FACE; }
static Family trav_family(uint64_t kind) { return kind == F_REF ? F_TREF : kind == F_INTERVAL ? F_TIV : F_TFC; }

static void construct_step(Cont *k, uint64_t v) {
    ConLoc *L = FR_LOC(k, ConLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->rq = rget(k->w[0], &L->nrq);
    L->tag = L->rq[0]; L->payload = L->rq[1]; L->levels = L->rq[2]; L->declared = L->rq[3];
    L->ft = L->rq[4]; L->fd = L->rq[5]; L->nf = (size_t)L->rq[6]; L->fields = L->rq + 7;
    L->nb = (size_t)L->rq[7 + 3 * L->nf]; L->binders = L->rq + 8 + 3 * L->nf;
    /* the typed free boundary: field boundaries (closed through declaration
     * types) minus the formal bound at the field's binder */
    if (!L->ft) {
        L->ft = set_make(NULL, 0); L->fd = set_make(NULL, 0);
        for (L->q = 0; L->q < L->nf; L->q++) {
            if (con_field_kind(L, L->q) == F_REF) { L->fv = ref_freevars(con_field_id(L, L->q)); L->ds = ref_support(con_field_id(L, L->q)); }
            else { L->fv = set_make(NULL, 0); FR_AWAIT(k, L->ds, F_DIMS, con_field_id(L, L->q), 0); }
            if (con_field_slot(L, L->q) != NO_SLOT) {
                require(con_field_slot(L, L->q) < L->nb, "field refers to a missing binder");
                if (con_binder_sort(L, con_field_slot(L, L->q)) == S_TERM) FR_AWAIT(k, L->fv, F_SREMOVE, L->fv, con_binder_formal(L, con_field_slot(L, L->q)));
                else FR_AWAIT(k, L->ds, F_SREMOVE, L->ds, con_binder_formal(L, con_field_slot(L, L->q)));
            }
            FR_AWAIT(k, L->ft, F_SUNION, L->ft, L->fv);
            FR_AWAIT(k, L->fd, F_SUNION, L->fd, L->ds);
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
        for (L->q = 0; L->q < L->nf; L->q += 2) FR_AWAIT(k, L->req, F_JOIN, L->req, con_field_id(L, L->q));
    } else {
        L->req = fc_true();
        for (L->q = 0; L->q < L->nf; L->q++) {
            if (con_field_kind(L, L->q) != F_REF || tag_schema((Tag)L->tag)->partial[L->q]) {
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
        FR_AWAIT(k, L->ds, F_DIMS, L->declared, 0);
        FR_AWAIT(k, L->fd, F_SUNION, L->fd, L->ds);
    }
    L->dset = rget(L->fd, &L->nd);
    L->xs = rget(L->ft, &L->nt);
    L->np = L->nd + L->nt;
    FR_AWAIT(k, L->phi, F_PHI, L->ft, L->fd);
    /* the node record */
    wordbuf_init(&L->w);
    wordbuf_push(&L->w, 0); wordbuf_push(&L->w, L->np); wordbuf_push(&L->w, L->tag);
    wordbuf_push(&L->w, L->payload ? expr_level(L->payload) : 0);
    wordbuf_push(&L->w, L->levels != LEVELS_NONE ? expr_level(L->levels) : 0);
    wordbuf_push(&L->w, L->nf);
    for (L->q = 0; L->q < L->nf; L->q++) {
        L->mq = L->phi;
        if (con_field_slot(L, L->q) != NO_SLOT) {                       /* the binder's formal ↦ slot np + s */
            uint64_t s = con_field_slot(L, L->q);
            FR_AWAIT(k, L->mq, F_SET, L->phi, subst_entry(con_binder_formal(L, s), con_binder_sort(L, s) == S_TERM ? PS_REF : PS_INTERVAL, L->np + s));
        }
        FR_AWAIT(k, L->c, trav_family(con_field_kind(L, L->q)), con_field_id(L, L->q), close_key(L->mq));
        wordbuf_push(&L->w, con_field_kind(L, L->q)); wordbuf_push(&L->w, con_field_slot(L, L->q));
        wordbuf_push(&L->w, expr_const(psort_of(con_field_kind(L, L->q)), L->c));
    }
    wordbuf_push(&L->w, L->nb);
    for (L->q = 0; L->q < L->nb; L->q++) { wordbuf_push(&L->w, con_binder_sort(L, L->q)); wordbuf_push(&L->w, con_binder_domain(L, L->q)); wordbuf_push(&L->w, L->q); FR_YIELD(k); }
    FR_AWAIT(k, L->c, F_TFC, L->req, close_key(L->phi));
    wordbuf_push(&L->w, expr_const(PS_FACE, L->c));
    if (L->declared) { FR_AWAIT(k, L->c, F_TFC, L->declared, close_key(L->phi)); wordbuf_push(&L->w, expr_const(PS_FACE, L->c)); }
    else wordbuf_push(&L->w, 0);
    for (L->q = 0; L->q < L->nd; L->q++) { wordbuf_push(&L->w, PS_INTERVAL); wordbuf_push(&L->w, 0); wordbuf_push(&L->w, 0); FR_YIELD(k); }
    for (L->q = 0; L->q < L->nt; L->q++) {
        FR_AWAIT(k, L->ty, F_TREF, term_var_type(L->xs[L->q]), close_key(L->phi));
        FR_AWAIT(k, L->g, F_TFC, term_var_required(L->xs[L->q]), close_key(L->phi));
        wordbuf_push(&L->w, PS_REF); wordbuf_push(&L->w, expr_const(PS_REF, L->ty)); wordbuf_push(&L->w, expr_const(PS_FACE, L->g));
    }
    FR_CALL(k, L->Q, intern_sub(k, &M.keys, &L->w, &L->created));
    /* the environment of the boundary itself (its interpretation record) */
    wordbuf_init(&L->w);
    for (L->q = 0; L->q < L->nd; L->q++) { wordbuf_push(&L->w, L->q); wordbuf_push(&L->w, PS_INTERVAL); wordbuf_push(&L->w, iv_var(L->dset[L->q])); FR_YIELD(k); }
    for (L->q = 0; L->q < L->nt; L->q++) {
        FR_AWAIT(k, r, F_REFVAR, L->xs[L->q], 0);
        wordbuf_push(&L->w, L->nd + L->q); wordbuf_push(&L->w, PS_REF); wordbuf_push(&L->w, r);
    }
    wordbuf_push(&L->w, 0);                                  /* a construction's definition word */
    FR_CALL(k, L->E, intern_sub(k, &M.keys, &L->w, &L->created));
    FR_AWAIT(k, r, F_TVMAKE, L->Q, L->E);
    FR_FINISH(k, r);
    FR_END(k);
}

/* a head's payload (w[1] = 0) or formation levels (w[1] = 1): constants of a
 * construction node, interpreted for a template node */
static void head_step(Cont *k, uint64_t v) {
    RefId t = k->w[0];
    uint64_t r = 0;
    FR_BEGIN(k);
    {   TNodeId Q = ref_tnode(t); ExprId e = tnode_head_expr(Q, (int)k->w[1]);
        if (!e) FR_FINISH(k, k->w[1] ? LEVELS_NONE : 0);
        if (expr_is_level(e)) FR_FINISH(k, expr_level_value(e)); }     /* a closed expression needs no environment */
    r = ref_tenv(t);
    FR_AWAIT(k, r, F_INTERP, tnode_head_expr(ref_tnode(t), (int)k->w[1]), r);
    FR_FINISH(k, rword(r, 1));
    FR_END(k);
}

/* unfold(t, X): a record X of t's definition (its body or type, over the
 * definition's parameters) at t's arguments — closed over the parameters
 * (once per definition), then applied to t's environment */
static void unfold_step(Cont *k, uint64_t v) {
    RefId t = k->w[0];
    uint64_t r = 0;
    FR_BEGIN(k);
    require(k->w[1] != 0, "unfold of a global without a body");   /* w[1]: its body */
    require(!ref_is_var(t) && ref_tag(t) == T_GLOBAL, "unfold of a non-global");
    {   SymbolId s = (SymbolId)expr_level_value(tnode_head_expr(ref_tnode(t), 0)); FR_AWAIT(k, r, F_PHI, global_params(s), global_dims(s)); }
    FR_AWAIT(k, r, F_TREF, k->w[1], close_key(r));
    FR_AWAIT(k, r, F_TREF, r, apply_key(ref_tenv(t)));
    FR_FINISH(k, r);
    FR_END(k);
}


void construct_families_init(void) {
    family_define(F_REFVAR, "ref.var", refvar_step, sizeof(VarLoc));
    family_define(F_FIELD, "field", field_step, sizeof(FieldLoc));
    family_define(F_BINDER, "binder", binder_step, sizeof(BindLoc));
    family_define(F_CONSTRUCT, "construct", construct_step, sizeof(ConLoc));
    family_define(F_HEAD, "head.annotation", head_step, 0);
    family_define(F_PHI, "boundary.close", phi_step, sizeof(PhiLoc));
    family_define(F_UNFOLD, "global.unfold", unfold_step, 0);    /* keyed by (reference, body) */
}
/* the template families register after the construction families; their ids are read lazily */

/* ---------------- the operations (synchronous driver) ---------------- */
uint64_t construction_field(RefId t, size_t k) { return family_call(F_FIELD, t, k); }
uint64_t binder_req(Sort sort, BinderSlot slot, FieldIndex field, uint64_t image) { return RQ(sort, slot, field, image); }
RefId construction_binder(RefId t, Sort sort, BinderSlot slot, FieldIndex field, uint64_t image) { return family_call(F_BINDER, t, binder_req(sort, slot, field, image)); }
RefId ref_var_family(TermVarId x) { return family_call(F_REFVAR, x, 0); }
