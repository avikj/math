/* scopefam.c — scoped traversal, scope records and capture as pure producer
 * families (§50).
 *
 * A traversal is named by an interned key [kind, depth, context]:
 *   CLOSE (context: [sort, id]* of the captured locals) — a captured
 *         identity becomes the (depth, slot) atom;
 *   APPLY (context: [sort, value]* arguments) — a depth atom becomes its
 *         argument, a deeper atom is lowered;
 *   RE    (context: a map) — free identities are substituted;
 *   ENV   (context: an environment) — a node's atom k becomes its slot k;
 *   LOWER — the single binder level after ∀ is removed.
 * TREF/TIV/TFC traverse a reference, interval or face at the key's depth; a
 * scope's records sit one level deeper (TSCOPE with depth+1). A scope record
 * ends with its side data (free support and variables, bound atoms excluded):
 * SCOPESIDE forms it from the words without it. Each step does a constant
 * amount of work. */
#include "eval.h"
#include "template.h"



uint64_t trav_key(unsigned kind, unsigned depth, uint64_t ctx) { return RQ(kind, depth, ctx); }
uint64_t re_key(uint64_t map) { return trav_key(TR_RE, 0, map); }
uint64_t env_key(uint64_t env) { return trav_key(TR_ENV, 0, env); }
static void tk_get(uint64_t tk, unsigned *kind, unsigned *depth, uint64_t *ctx) { size_t n; const uint64_t *w = interner_get(&M.keys, tk, &n); *kind = (unsigned)w[0]; *depth = (unsigned)w[1]; *ctx = w[2]; }

/* the substitution by the empty map moves nothing */
static bool trav_identity(uint64_t tk) {
    unsigned kind, depth; uint64_t ctx; tk_get(tk, &kind, &depth, &ctx);
    size_t n; return kind == TR_RE && (interner_get(&M.maps, ctx, &n), n == 0);
}

/* APPLY / LOWER images of a bound atom (constant work); false = keep */
static bool bound_image(unsigned kind, unsigned depth, uint64_t ctx, uint64_t x, bool dim, uint64_t *out) {
    if (!is_bound_id(x)) return false;
    uint32_t d = bound_depth(x), s = bound_slot(x);
    if (d < depth) return false;
    if (kind == TR_LOWER) require(d != depth, "forall: a local remained");
    else if (d == depth) {
        size_t n; const uint64_t *a = interner_get(&M.keys, ctx, &n);
        require(2 * (size_t)s + 1 < n && a[2 * s] == (uint64_t)(dim ? VS_INTERVAL : VS_REF) && a[2 * s + 1],
                dim ? "scope application: missing or ill-sorted interval argument" : "scope application: missing or ill-sorted term argument");
        *out = a[2 * s + 1];
        return true;
    }
    *out = dim ? iv_var(bound_id(d - 1, s)) : ref_var(bound_id(d - 1, s));
    return true;
}

/* ---------------- identity images ----------------
 * operand: the dimension (dim) or the VAR reference itself (kept when
 * unchanged); key: the traversal */
typedef struct { const uint64_t *c; size_t nc, q; } ImgLoc;
static void image_step(Cont *k, uint64_t v, bool dim) {
    ImgLoc *L = FR_LOC(k, ImgLoc);
    uint64_t r = 0;
    unsigned kind, depth; uint64_t ctx; tk_get(k->w[1], &kind, &depth, &ctx);
    uint64_t x = dim ? k->w[0] : ref_var_id(k->w[0]);
    uint64_t keep = dim ? iv_var(x) : k->w[0];
    FR_BEGIN(k);
    if (kind == TR_APPLY || kind == TR_LOWER) { uint64_t o = 0; FR_FINISH(k, bound_image(kind, depth, ctx, x, dim, &o) ? o : keep); }
    if (is_bound_id(x)) FR_FINISH(k, keep);
    if (kind == TR_RE || kind == TR_ENV) {
        /* the substitution record's entry for the identity (an environment's for an atom's slot) */
        if (kind == TR_ENV && !is_obound_id(x)) FR_FINISH(k, keep);
        FR_AWAIT(k, r, F_LOOKUP, ctx, kind == TR_ENV ? x & ~OBOUND_BIT : x);
        if (!r) FR_FINISH(k, keep);
        FR_FINISH(k, subst_value(ctx, r - 1));
    }
    /* CLOSE: the captured locals, one per step */
    L->c = interner_get(&M.keys, ctx, &L->nc);
    for (L->q = 0; 2 * L->q < L->nc; L->q++) {
        if (L->c[2 * L->q] == (uint64_t)(dim ? S_DIM : S_TERM) && L->c[2 * L->q + 1] == x)
            FR_FINISH(k, dim ? iv_var(bound_id(depth, (uint32_t)L->q)) : ref_var(bound_id(depth, (uint32_t)L->q)));
        FR_YIELD(k);
    }
    FR_FINISH(k, keep);
    FR_END(k);
}
static void timgt_step(Cont *k, uint64_t v) { image_step(k, v, false); }
static void timgd_step(Cont *k, uint64_t v) { image_step(k, v, true); }

/* ---------------- intervals and faces: each image inserted once ---------------- */
typedef struct { const uint64_t *x; size_t nx, px, i; uint64_t acc, cl; } SubLoc;
static void tiv_step(Cont *k, uint64_t v) {
    SubLoc *L = FR_LOC(k, SubLoc);
    uint64_t im = 0;
    FR_BEGIN(k);
    if (trav_identity(k->w[1])) FR_FINISH(k, k->w[0]);
    L->x = interner_get(&M.intervals, k->w[0], &L->nx);
    L->acc = iv_zero();
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        L->cl = iv_one();
        for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) {
            FR_AWAIT(k, im, F_TIMGD, IV_ATOM_DIM(L->x[L->i]), k->w[1]);
            if (IV_ATOM_NEG(L->x[L->i])) FR_AWAIT(k, im, F_IVNEG, im, 0);
            FR_AWAIT(k, L->cl, F_IVMEET, L->cl, im);
        }
        FR_AWAIT(k, L->acc, F_IVJOIN, L->acc, L->cl);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
static void tfc_step(Cont *k, uint64_t v) {
    SubLoc *L = FR_LOC(k, SubLoc);
    uint64_t im = 0;
    FR_BEGIN(k);
    if (trav_identity(k->w[1])) FR_FINISH(k, k->w[0]);
    L->x = interner_get(&M.faces, k->w[0], &L->nx);
    L->acc = fc_false();
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        L->cl = fc_true();
        for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) {
            FR_AWAIT(k, im, F_TIMGD, FC_LIT_DIM(L->x[L->i]), k->w[1]);
            FR_AWAIT(k, im, F_FCEND, im, (uint64_t)FC_LIT_EPS(L->x[L->i]));
            FR_AWAIT(k, L->cl, F_FCMEET, L->cl, im);
        }
        FR_AWAIT(k, L->acc, F_FCJOIN, L->acc, L->cl);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

/* ---------------- references: a variable's image, or the environment rebuilt ---------------- */
static void tref_step(Cont *k, uint64_t v) {
    RefId t = k->w[0];
    uint64_t r = 0;
    FR_BEGIN(k);
    if (trav_identity(k->w[1])) FR_FINISH(k, t);
    if (ref_is_var(t)) { FR_AWAIT(k, r, F_TIMGT, t, k->w[1]); FR_FINISH(k, r); }
    FR_AWAIT(k, r, F_ENVREBUILD, t, k->w[1]);
    FR_FINISH(k, r);
    FR_END(k);
}

/* ---------------- scopes ----------------
 * record: [n, (sort, type, level, required)*, body_sort, type, level, guard, body] */
static Family val_family(uint64_t sort) { return sort == VS_REF ? F_TREF : sort == VS_INTERVAL ? F_TIV : F_TFC; }
typedef struct {
    const uint64_t *s; size_t ns, n, q; uint64_t tk, r; bool changed; WordBuf out; bool created;
    uint64_t sup, fv, ds;
} ScLoc;
/* the records of scope w[0] under traversal w[1] (records at the key's depth) */
static void tscope_step(Cont *k, uint64_t v) {
    ScLoc *L = FR_LOC(k, ScLoc);
    uint64_t r = 0, id = 0;
    FR_BEGIN(k);
    if (trav_identity(k->w[1])) FR_FINISH(k, k->w[0]);
    L->s = interner_get(&M.scopes, k->w[0], &L->ns); L->n = (size_t)L->s[0]; L->changed = false;
    wordbuf_init(&L->out); wordbuf_push(&L->out, L->n);
    for (L->q = 0; L->q < L->n; L->q++) {
        r = 0;
        if (L->s[2 + 4 * L->q]) FR_AWAIT(k, r, F_TREF, L->s[2 + 4 * L->q], k->w[1]);
        if (r != L->s[2 + 4 * L->q]) L->changed = true;
        wordbuf_push(&L->out, L->s[1 + 4 * L->q]); wordbuf_push(&L->out, r); wordbuf_push(&L->out, L->s[3 + 4 * L->q]);
        FR_AWAIT(k, r, F_TFC, L->s[4 + 4 * L->q], k->w[1]);
        if (r != L->s[4 + 4 * L->q]) L->changed = true;
        wordbuf_push(&L->out, r);
    }
    {   const uint64_t *t = L->s + 1 + 4 * L->n;
        wordbuf_push(&L->out, t[0]); L->r = 0;
        if (t[1]) FR_AWAIT(k, L->r, F_TREF, t[1], k->w[1]); }
    {   const uint64_t *t = L->s + 1 + 4 * L->n;
        if (L->r != t[1]) L->changed = true;
        wordbuf_push(&L->out, L->r); wordbuf_push(&L->out, t[2]);
        FR_AWAIT(k, r, F_TFC, t[3], k->w[1]); }
    {   const uint64_t *t = L->s + 1 + 4 * L->n;
        if (r != t[3]) L->changed = true;
        wordbuf_push(&L->out, r);
        FR_AWAIT(k, r, val_family(t[0]), t[4], k->w[1]); }
    {   const uint64_t *t = L->s + 1 + 4 * L->n;
        if (r != t[4]) L->changed = true;
        wordbuf_push(&L->out, r); }
    if (!L->changed) { while (wordbuf_drain_one(&L->out)) FR_YIELD(k); FR_FINISH(k, k->w[0]); }
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_AWAIT(k, r, F_SCOPESIDE, id, 0);
    FR_FINISH(k, r);
    FR_END(k);
}

/* the side data of scope w[0]: the support and free variables of every
 * record, bound atoms excluded; written before the scope id is published */
static void scopeside_step(Cont *k, uint64_t v) {
    ScLoc *L = FR_LOC(k, ScLoc);
    FR_BEGIN(k);
    L->s = interner_get(&M.keys, k->w[0], &L->ns); L->n = (size_t)L->s[0];
    L->sup = dimset_make(NULL, 0); L->fv = varset_make(NULL, 0);
    /* the reference records: local types, result type, body (when a reference) */
    for (L->q = 0; L->q < L->n + 2; L->q++) {
        {   const uint64_t *t = L->s + 1 + 4 * L->n;
            L->r = L->q < L->n ? L->s[2 + 4 * L->q] : L->q == L->n ? t[1] : (t[0] == VS_REF ? t[4] : 0); }
        if (!L->r) continue;
        FR_AWAIT(k, L->sup, F_DSUNION, L->sup, ref_support(L->r));
        FR_AWAIT(k, L->fv, F_VSUNION, L->fv, ref_freevars(L->r));
    }
    /* the face and interval records: required faces, guard, body (when not a reference) */
    for (L->q = 0; L->q < L->n + 2; L->q++) {
        {   const uint64_t *t = L->s + 1 + 4 * L->n;
            if (L->q < L->n) { L->r = L->s[4 + 4 * L->q]; L->tk = 1; }
            else if (L->q == L->n) { L->r = t[3]; L->tk = 1; }
            else { L->r = t[0] == VS_REF ? 0 : t[4]; L->tk = t[0] == VS_FACE; } }
        if (!L->r) continue;
        FR_AWAIT(k, L->ds, F_DIMS, L->r, L->tk);
        FR_AWAIT(k, L->sup, F_DSUNION, L->sup, L->ds);
    }
    FR_AWAIT(k, L->sup, F_SETFREE, L->sup, 0);
    FR_AWAIT(k, L->fv, F_SETFREE, L->fv, 1);
    /* the record: the words, then the side data */
    wordbuf_init(&L->out);
    for (L->q = 0; L->q < L->ns; L->q++) { wordbuf_push(&L->out, L->s[L->q]); FR_YIELD(k); }
    wordbuf_push(&L->out, L->sup); wordbuf_push(&L->out, L->fv);
    FR_CALL(k, L->r, intern_sub(k, &M.scopes, &L->out, &L->created));
    FR_FINISH(k, L->r);
    FR_END(k);
}

/* the free (unbound) part of a dimension set (w[1] = 0) or variable set */
typedef struct { const uint64_t *x; size_t n, q; WordBuf out; bool created; } FreeLoc;
static void setfree_step(Cont *k, uint64_t v) {
    FreeLoc *L = FR_LOC(k, FreeLoc);
    Interner *t = k->w[1] ? &M.varsets : &M.dimsets;
    uint64_t id = 0;
    FR_BEGIN(k);
    L->x = interner_get(t, k->w[0], &L->n);
    wordbuf_init(&L->out);
    for (L->q = 0; L->q < L->n; L->q++) { if (!is_bound_id(L->x[L->q])) wordbuf_push(&L->out, L->x[L->q]); FR_YIELD(k); }
    if (L->out.n == L->n) { while (wordbuf_drain_one(&L->out)) FR_YIELD(k); FR_FINISH(k, k->w[0]); }
    FR_CALL(k, id, intern_sub(k, t, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}

/* capture: request [n, (sort, id, type, level, required)*, body_sort, body, type, level, guard];
 * the captured identities close into depth-0 atoms in every record */
typedef struct { const uint64_t *c; size_t nc, n, q; uint64_t tk, r; WordBuf out; bool created; } CapLoc;
static void capture_step(Cont *k, uint64_t v) {
    CapLoc *L = FR_LOC(k, CapLoc);
    uint64_t r = 0, id = 0;
    FR_BEGIN(k);
    L->c = interner_get(&M.keys, k->w[0], &L->nc); L->n = (size_t)L->c[0];
    wordbuf_init(&L->out);
    for (L->q = 0; L->q < L->n; L->q++) { wordbuf_push(&L->out, L->c[1 + 5 * L->q]); wordbuf_push(&L->out, L->c[2 + 5 * L->q]); FR_YIELD(k); }
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    L->tk = trav_key(TR_CLOSE, 0, id);
    wordbuf_init(&L->out); wordbuf_push(&L->out, L->n);
    for (L->q = 0; L->q < L->n; L->q++) {
        r = 0;
        if (L->c[3 + 5 * L->q]) FR_AWAIT(k, r, F_TREF, L->c[3 + 5 * L->q], L->tk);
        wordbuf_push(&L->out, L->c[1 + 5 * L->q]); wordbuf_push(&L->out, r); wordbuf_push(&L->out, L->c[4 + 5 * L->q]);
        FR_AWAIT(k, r, F_TFC, L->c[5 + 5 * L->q], L->tk);
        wordbuf_push(&L->out, r);
    }
    {   const uint64_t *t = L->c + 1 + 5 * L->n;          /* body_sort, body, type, level, guard */
        wordbuf_push(&L->out, t[0]); L->r = 0;
        if (t[2]) FR_AWAIT(k, L->r, F_TREF, t[2], L->tk); }
    {   const uint64_t *t = L->c + 1 + 5 * L->n;
        wordbuf_push(&L->out, L->r); wordbuf_push(&L->out, t[3]);
        FR_AWAIT(k, r, F_TFC, t[4], L->tk); }
    {   const uint64_t *t = L->c + 1 + 5 * L->n;
        wordbuf_push(&L->out, r);
        FR_AWAIT(k, r, val_family(t[0]), t[1], L->tk); }
    wordbuf_push(&L->out, r);
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_AWAIT(k, r, F_SCOPESIDE, id, 0);
    FR_FINISH(k, r);
    FR_END(k);
}

void scope_families_init(void) {
    family_define(F_TIMGT, "trav.term_image", timgt_step, sizeof(ImgLoc));
    family_define(F_TIMGD, "trav.dim_image", timgd_step, sizeof(ImgLoc));
    family_define(F_TREF, "trav.ref", tref_step, 0);
    family_define(F_TIV, "trav.interval", tiv_step, sizeof(SubLoc));
    family_define(F_TFC, "trav.face", tfc_step, sizeof(SubLoc));
    family_define(F_TSCOPE, "trav.scope", tscope_step, sizeof(ScLoc));
    family_define(F_SCOPESIDE, "scope.side", scopeside_step, sizeof(ScLoc));
    family_define(F_SETFREE, "set.free", setfree_step, sizeof(FreeLoc));
    family_define(F_CAPTURE, "scope.capture", capture_step, sizeof(CapLoc));
}

/* ---------------- the operations (synchronous driver) ---------------- */
ScopeId scope_with_side(uint64_t pre) { return family_call(F_SCOPESIDE, pre, 0); }
ScopeId capture_request(const uint64_t *req, size_t n) { return family_call(F_CAPTURE, interner_intern(&M.keys, req, n, NULL), 0); }
ScopeId scope_records_traverse(ScopeId S, uint64_t tk) { return family_call(F_TSCOPE, S, tk); }
