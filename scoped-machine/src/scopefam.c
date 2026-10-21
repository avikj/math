/* scopefam.c — scoped traversal as pure producer families (§50).
 *
 * A traversal is named by an interned key [kind, depth, context]:
 *   CLOSE (context: identity ↦ slot) — a captured identity becomes the
 *         (depth, slot) atom;
 *   APPLY (context: an environment slot ↦ value) — a depth atom becomes its
 *         value, a deeper atom is lowered;
 *   RE    (context: a map) — free identities are substituted;
 *   LOWER — the single binder level after ∀ is removed.
 * TREF/TIV/TFC traverse a reference, interval or face at the key's depth.
 * Each step does a constant amount of work. */
#include "eval.h"
#include "template.h"



uint64_t trav_key(unsigned kind, unsigned depth, uint64_t ctx) { return RQ(kind, depth, ctx); }
uint64_t re_key(uint64_t map) { return trav_key(TR_RE, 0, map); }
uint64_t close_key(uint64_t ctx) { return trav_key(TR_CLOSE, 0, ctx); }
uint64_t apply_key(uint64_t env) { return trav_key(TR_APPLY, 0, env); }
static void tk_get(uint64_t tk, unsigned *kind, unsigned *depth, uint64_t *ctx) { size_t n; const uint64_t *w = rget(tk, &n); *kind = (unsigned)w[0]; *depth = (unsigned)w[1]; *ctx = w[2]; }

/* the substitution by the empty map moves nothing */
static bool trav_identity(uint64_t tk) {
    unsigned kind, depth; uint64_t ctx; tk_get(tk, &kind, &depth, &ctx);
    size_t n; return kind == TR_RE && (rget(ctx, &n), n == 0);
}

/* ---------------- identity images ----------------
 * operand: the dimension (dim) or the VAR reference itself (kept when
 * unchanged); key: the traversal. RE and CLOSE read their record by the
 * free identity; APPLY and LOWER act on the atoms at or below the key's
 * depth: an atom of the key's depth is APPLY's environment value at its
 * slot, a deeper one is lowered. */
static uint64_t atom(bool dim, uint32_t depth, uint32_t slot) { return dim ? iv_var(bound_id(depth, slot)) : ref_var(bound_id(depth, slot)); }
static void image_step(Cont *k, uint64_t v, bool dim) {
    uint64_t r = 0;
    unsigned kind, depth; uint64_t ctx; tk_get(k->w[1], &kind, &depth, &ctx);
    uint64_t x = dim ? k->w[0] : ref_var_id(k->w[0]);
    uint64_t keep = dim ? iv_var(x) : k->w[0];
    FR_BEGIN(k);
    if (kind == TR_RE || kind == TR_CLOSE) {
        if (is_bound_id(x)) FR_FINISH(k, keep);
        FR_AWAIT(k, r, F_LOOKUP, ctx, x);
        if (!r) FR_FINISH(k, keep);
        FR_FINISH(k, kind == TR_RE ? subst_value(ctx, r - 1) : atom(dim, depth, (uint32_t)subst_value(ctx, r - 1)));
    }
    if (!is_bound_id(x) || bound_depth(x) < depth) FR_FINISH(k, keep);
    if (bound_depth(x) > depth) FR_FINISH(k, atom(dim, bound_depth(x) - 1, bound_slot(x)));
    require(kind == TR_APPLY, "forall: a local remained");
    FR_AWAIT(k, r, F_LOOKUP, ctx, bound_slot(x));
    {   uint64_t slot; TVal e = { 0, 0 }; if (r) subst_get(ctx, r - 1, &slot, &e);
        require(e.sort == (dim ? PS_INTERVAL : PS_REF), dim ? "application: missing or ill-sorted interval argument" : "application: missing or ill-sorted term argument");
        FR_FINISH(k, e.id); }
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
    L->x = rget(k->w[0], &L->nx);
    L->acc = iv_zero();
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        L->cl = iv_one();
        for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) {
            FR_AWAIT(k, im, F_TIMGD, IV_ATOM_DIM(L->x[L->i]), k->w[1]);
            if (IV_ATOM_NEG(L->x[L->i])) FR_AWAIT(k, im, F_IVNEG, im, 0);
            FR_AWAIT(k, L->cl, F_IVMEET, L->cl, im);
        }
        FR_AWAIT(k, L->acc, F_JOIN, L->acc, L->cl);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
static void tfc_step(Cont *k, uint64_t v) {
    SubLoc *L = FR_LOC(k, SubLoc);
    uint64_t im = 0;
    FR_BEGIN(k);
    if (trav_identity(k->w[1])) FR_FINISH(k, k->w[0]);
    L->x = rget(k->w[0], &L->nx);
    L->acc = fc_false();
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        L->cl = fc_true();
        for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) {
            FR_AWAIT(k, im, F_TIMGD, FC_LIT_DIM(L->x[L->i]), k->w[1]);
            FR_AWAIT(k, im, F_FCEND, im, (uint64_t)FC_LIT_EPS(L->x[L->i]));
            FR_AWAIT(k, L->cl, F_FCMEET, L->cl, im);
        }
        FR_AWAIT(k, L->acc, F_JOIN, L->acc, L->cl);
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
/* the free (unbound) part of a set of dimensions or variables */
typedef struct { const uint64_t *x; size_t n, q; WordBuf out; bool created; } FreeLoc;
static void setfree_step(Cont *k, uint64_t v) {
    FreeLoc *L = FR_LOC(k, FreeLoc);
    Interner *t = &M.keys;
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

void scope_families_init(void) {
    family_define(F_TIMGT, "trav.term_image", timgt_step, 0);
    family_define(F_TIMGD, "trav.dim_image", timgd_step, 0);
    family_define(F_TREF, "trav.ref", tref_step, 0);
    family_define(F_TIV, "trav.interval", tiv_step, sizeof(SubLoc));
    family_define(F_TFC, "trav.face", tfc_step, sizeof(SubLoc));
    family_define(F_SETFREE, "set.free", setfree_step, sizeof(FreeLoc));
}

