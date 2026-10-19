/* subst.c — maps and substitution as pure producer families.
 *
 * Image lookup (binary search, one probe per step), override, composition,
 * the substitution of intervals, faces and references, the environment map
 * of a construction and the construction instance (its support, free
 * variables and required face) are producers keyed by their interned
 * operands. Records are written one word per step and inserted by the
 * interning subroutine. A template instance (a node with program fields) is
 * still reindexed by the template layer (its interpretation is step 3). */
#include "eval.h"
#include "template.h"


static const uint64_t *mrec(MapId m, size_t *n) { return interner_get(&M.maps, m, n); }
/* an identity entry key ↦ VAR(key) / key, recognized without forming VAR(key) */
static bool identity_image(bool dims, uint64_t key, uint64_t img) { return dims ? img == iv_var(key) : (ref_is_var(img) && ref_var_id(img) == key); }

/* ---------------- image lookup ---------------- */
typedef struct { const uint64_t *w; size_t n, base, lo, hi; } LookLoc;
static void look_step(Cont *k, uint64_t v, bool dims) {
    LookLoc *L = FR_LOC(k, LookLoc);
    FR_BEGIN(k);
    L->w = mrec(k->w[0], &L->n);
    { size_t nt = (size_t)L->w[L->n - 1];
      if (dims) { L->base = 2 * nt; L->lo = 0; L->hi = (L->n - 1 - 2 * nt) / 2; }
      else { L->base = 0; L->lo = 0; L->hi = nt; } }
    while (L->lo < L->hi) {
        size_t mid = (L->lo + L->hi) / 2; uint64_t key = L->w[L->base + 2 * mid];
        if (key == k->w[1]) FR_FINISH(k, L->w[L->base + 2 * mid + 1]);
        if (key < k->w[1]) L->lo = mid + 1; else L->hi = mid;
        FR_YIELD(k);
    }
    if (dims) FR_FINISH(k, iv_var(k->w[1]));
    { uint64_t r = 0; FR_AWAIT(k, r, F_REFVAR, k->w[1], 0); FR_FINISH(k, r); }
    FR_END(k);
}
static void mapt_step(Cont *k, uint64_t v) { look_step(k, v, false); }
static void mapd_step(Cont *k, uint64_t v) { look_step(k, v, true); }

/* ---------------- override and composition ----------------
 * Both merge the sorted key sections of their operands. Override: the second
 * operand's entries replace the first's. Composition σ;τ (σ then τ): a key of
 * σ maps to σ(x)[τ], a key only of τ to τ(x). Identity entries are dropped. */
typedef struct {
    const uint64_t *x, *y; size_t nx, ny, tx, ty, i, j, kept; bool dims;
    uint64_t key, img; WordBuf out; bool created;
} MergeLoc;
static void merge_step(Cont *k, uint64_t v, bool compose) {
    MergeLoc *L = FR_LOC(k, MergeLoc);
    uint64_t id = 0, r = 0;
    FR_BEGIN(k);
    L->x = mrec(k->w[0], &L->nx); L->y = mrec(k->w[1], &L->ny);
    if (L->ny == 1) FR_FINISH(k, k->w[0]);                        /* the second operand is the identity */
    if (L->nx == 1 && compose) FR_FINISH(k, k->w[1]);
    L->tx = (size_t)L->x[L->nx - 1]; L->ty = (size_t)L->y[L->ny - 1];
    wordbuf_init(&L->out); L->kept = 0;
    for (L->dims = false;; L->dims = true) {
        L->i = L->dims ? 2 * L->tx : 0; L->j = L->dims ? 2 * L->ty : 0;
        for (;;) {
            size_t ex = L->dims ? L->nx - 1 : 2 * L->tx, ey = L->dims ? L->ny - 1 : 2 * L->ty;
            if (L->i == ex && L->j == ey) break;
            bool from_x = L->j == ey || (L->i < ex && L->x[L->i] <= L->y[L->j]);
            bool from_y = L->i == ex || (L->j < ey && L->y[L->j] <= L->x[L->i]);
            if (from_x && from_y) {                                   /* a key of both */
                L->key = L->x[L->i];
                if (compose) L->img = L->x[L->i + 1]; else L->img = L->y[L->j + 1];
                L->i += 2; L->j += 2;
                if (compose) {
                    if (L->dims) FR_AWAIT(k, r, F_IVRE, L->img, k->w[1]);
                    else FR_AWAIT(k, r, F_REINDEX, L->img, k->w[1]);
                    L->img = r;
                }
            } else if (from_x) {
                L->key = L->x[L->i]; L->img = L->x[L->i + 1]; L->i += 2;
                if (compose) {
                    if (L->dims) FR_AWAIT(k, r, F_IVRE, L->img, k->w[1]);
                    else FR_AWAIT(k, r, F_REINDEX, L->img, k->w[1]);
                    L->img = r;
                }
            } else { L->key = L->y[L->j]; L->img = L->y[L->j + 1]; L->j += 2; }
            if (!identity_image(L->dims, L->key, L->img)) {
                wordbuf_push(&L->out, L->key); wordbuf_push(&L->out, L->img);
                if (!L->dims) L->kept++;
            }
            FR_YIELD(k);
        }
        if (L->dims) break;
    }
    wordbuf_push(&L->out, L->kept);
    FR_CALL(k, id, intern_sub(k, &M.maps, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}
/* σ with key's entry replaced by key ↦ image (operand b: the interned
 * triple [sort, key, image]); an identity image removes the entry */
typedef struct { const uint64_t *x; size_t nx, tx, i, kept; uint64_t sort, key, img; bool placed, dims; WordBuf out; bool created; } OverLoc;
static void override_step(Cont *k, uint64_t v) {
    OverLoc *L = FR_LOC(k, OverLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    { size_t n; const uint64_t *e = interner_get(&M.keys, k->w[1], &n); L->sort = e[0]; L->key = e[1]; L->img = e[2]; }
    L->x = mrec(k->w[0], &L->nx); L->tx = (size_t)L->x[L->nx - 1];
    wordbuf_init(&L->out); L->kept = 0;
    for (L->dims = false;; L->dims = true) {
        L->placed = (L->sort == S_DIM) != L->dims;           /* the key belongs to the other section */
        for (L->i = L->dims ? 2 * L->tx : 0; L->i < (L->dims ? L->nx - 1 : 2 * L->tx); L->i += 2) {
            if (!L->placed && L->x[L->i] >= L->key) {
                L->placed = true;
                if (!identity_image(L->dims, L->key, L->img)) { wordbuf_push(&L->out, L->key); wordbuf_push(&L->out, L->img); if (!L->dims) L->kept++; }
                if (L->x[L->i] == L->key) { FR_YIELD(k); continue; }
            }
            wordbuf_push(&L->out, L->x[L->i]); wordbuf_push(&L->out, L->x[L->i + 1]); if (!L->dims) L->kept++;
            FR_YIELD(k);
        }
        if (!L->placed && !identity_image(L->dims, L->key, L->img)) { wordbuf_push(&L->out, L->key); wordbuf_push(&L->out, L->img); if (!L->dims) L->kept++; }
        if (L->dims) break;
    }
    wordbuf_push(&L->out, L->kept);
    FR_CALL(k, id, intern_sub(k, &M.maps, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}
static void compose_step(Cont *k, uint64_t v) { merge_step(k, v, true); }

/* ---------------- substitution of intervals and faces ----------------
 * r[σ] = ∨_c ∧_a a[σ] with (¬i)[σ] = ¬(σ i); φ[σ] = ∨_c ∧_(i=ε) (σ i = ε).
 * Each image is inserted once, combined by the original meets and joins. */
typedef struct { const uint64_t *x; size_t nx, px, i; uint64_t acc, cl; } SubLoc;
static void ivre_step(Cont *k, uint64_t v) {
    SubLoc *L = FR_LOC(k, SubLoc);
    uint64_t im = 0;
    FR_BEGIN(k);
    if (map_n_dims(k->w[1]) == 0) FR_FINISH(k, k->w[0]);
    L->x = interner_get(&M.intervals, k->w[0], &L->nx);
    L->acc = iv_zero();
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        L->cl = iv_one();
        for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) {
            FR_AWAIT(k, im, F_MAPD, k->w[1], IV_ATOM_DIM(L->x[L->i]));
            if (IV_ATOM_NEG(L->x[L->i])) FR_AWAIT(k, im, F_IVNEG, im, 0);
            FR_AWAIT(k, L->cl, F_IVMEET, L->cl, im);
        }
        FR_AWAIT(k, L->acc, F_IVJOIN, L->acc, L->cl);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
static void fcre_step(Cont *k, uint64_t v) {
    SubLoc *L = FR_LOC(k, SubLoc);
    uint64_t im = 0;
    FR_BEGIN(k);
    if (map_n_dims(k->w[1]) == 0) FR_FINISH(k, k->w[0]);
    L->x = interner_get(&M.faces, k->w[0], &L->nx);
    L->acc = fc_false();
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        L->cl = fc_true();
        for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) {
            FR_AWAIT(k, im, F_MAPD, k->w[1], FC_LIT_DIM(L->x[L->i]));
            FR_AWAIT(k, im, F_FCEND, im, (uint64_t)FC_LIT_EPS(L->x[L->i]));
            FR_AWAIT(k, L->cl, F_FCMEET, L->cl, im);
        }
        FR_AWAIT(k, L->acc, F_FCJOIN, L->acc, L->cl);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
/* the dimensions of an interval as a set */
static void ivdims_step(Cont *k, uint64_t v) {
    SubLoc *L = FR_LOC(k, SubLoc);
    FR_BEGIN(k);
    L->x = interner_get(&M.intervals, k->w[0], &L->nx);
    L->acc = dimset_make(NULL, 0);
    for (L->i = 0; L->i < L->nx; L->i++) {
        if (L->x[L->i] == DNF_SEP) continue;
        { uint64_t d = IV_ATOM_DIM(L->x[L->i]); L->cl = dimset_make(&d, 1); }
        FR_AWAIT(k, L->acc, F_DSUNION, L->acc, L->cl);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

/* ---------------- references ----------------
 * A variable is looked up; any other reference has its environment rebuilt:
 * one independent demand per entry (a join), then the instance of the same
 * node (a construction's instance, or a template view). Nothing in a node is
 * visited. */
static uint64_t deeper_key(uint64_t tk) { size_t n; const uint64_t *w = interner_get(&M.keys, tk, &n); return trav_key((unsigned)w[0], (unsigned)w[1] + 1, w[2]); }

static void reindex_step(Cont *k, uint64_t v) {
    RefId t = k->w[0]; MapId sigma = k->w[1];
    uint64_t r = 0;
    FR_BEGIN(k);
    if (map_is_identity(sigma)) FR_FINISH(k, t);
    if (ref_is_var(t)) { FR_AWAIT(k, r, F_MAPT, sigma, ref_var_id(t)); FR_FINISH(k, r); }
    { uint64_t op[2] = { 0, sigma }; FR_AWAIT(k, r, F_ENVREBUILD, t, interner_intern(&M.keys, op, 2, NULL)); }
    FR_FINISH(k, r);
    FR_END(k);
}

/* the environment of reference w[0] rebuilt by operation w[1] = [mode, arg]:
 * mode 0 substitutes the map arg, mode 1 traverses with the traversal key arg */
typedef struct { size_t n, q; uint64_t mode, arg, slot, f, a, b; TVal val; bool changed; WordBuf out; bool created; } ReLoc;
/* the demand rebuilding entry val under [mode, arg] (f = 0: kept as is) */
static void re_item(uint64_t mode, uint64_t arg, TVal val, uint64_t *f, uint64_t *a, uint64_t *b) {
    *f = 0; *a = val.id; *b = arg;
    if (val.sort == PS_LEVEL) return;
    if (mode == 0) {
        if (val.sort == PS_REF) *f = F_REINDEX;
        else if (val.sort == PS_INTERVAL) *f = F_IVRE;
        else if (val.sort == PS_FACE) *f = F_FCRE;
        else { *f = F_TSCOPE; *b = trav_key(TR_RE, 0, arg); }
    } else {
        if (val.sort == PS_REF) *f = F_TREF;
        else if (val.sort == PS_INTERVAL) *f = F_TIV;
        else if (val.sort == PS_FACE) *f = F_TFC;
        else { *f = F_TSCOPE; *b = deeper_key(arg); }
    }
}
static void envrebuild_step(Cont *k, uint64_t v) {
    ReLoc *L = FR_LOC(k, ReLoc);
    RefId t = k->w[0];
    uint64_t r = 0, id = 0;
    FR_BEGIN(k);
    { size_t m; const uint64_t *op = interner_get(&M.keys, k->w[1], &m); L->mode = op[0]; L->arg = op[1]; }
    L->n = tenv_size(ref_tenv(t));
    /* the entries are independent demands: launched, then awaited in order */
    for (L->q = 0; L->q < L->n; L->q++) {
        tenv_entry(ref_tenv(t), L->q, &L->slot, &L->val);
        re_item(L->mode, L->arg, L->val, &L->f, &L->a, &L->b);
        if (L->f) family_launch((Family)L->f, L->a, L->b);
        FR_YIELD(k);
    }
    L->changed = false;
    wordbuf_init(&L->out);
    wordbuf_push(&L->out, tnode_def(ref_tnode(t)));
    for (L->q = 0; L->q < L->n; L->q++) {
        tenv_entry(ref_tenv(t), L->q, &L->slot, &L->val);
        re_item(L->mode, L->arg, L->val, &L->f, &L->a, &L->b);
        r = L->val.id;
        if (L->f) FR_AWAIT(k, r, (Family)L->f, L->a, L->b);
        tenv_entry(ref_tenv(t), L->q, &L->slot, &L->val);
        if (r != L->val.id) L->changed = true;
        wordbuf_push(&L->out, L->slot); wordbuf_push(&L->out, L->val.sort); wordbuf_push(&L->out, r);
        FR_YIELD(k);
    }
    if (!L->changed) { while (wordbuf_drain_one(&L->out)) FR_YIELD(k); FR_FINISH(k, t); }
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_AWAIT(k, r, F_TVMAKE, ref_tnode(t), id);
    FR_FINISH(k, r);
    FR_END(k);
}

void subst_families_init(void) {
    
    
    
    family_define(F_MAPT, "map.term_image", mapt_step, sizeof(LookLoc));
    family_define(F_MAPD, "map.dim_image", mapd_step, sizeof(LookLoc));
    family_define(F_OVERRIDE, "map.override", override_step, sizeof(OverLoc));
    family_define(F_COMPOSE, "map.compose", compose_step, sizeof(MergeLoc));
    family_define(F_REINDEX, "reindex", reindex_step, 0);
    family_define(F_ENVREBUILD, "env.rebuild", envrebuild_step, sizeof(ReLoc));
    family_define(F_IVRE, "iv.reindex", ivre_step, sizeof(SubLoc));
    family_define(F_FCRE, "fc.reindex", fcre_step, sizeof(SubLoc));
    family_define(F_IVDIMS, "iv.dims", ivdims_step, sizeof(SubLoc));
}

/* ---------------- the operations (synchronous driver) ---------------- */
RefId map_term_image(MapId m, TermVarId x) { return family_call(F_MAPT, m, x); }
IntervalId map_dim_image(MapId m, DimVarId i) { return family_call(F_MAPD, m, i); }
MapId compose(MapId sigma, MapId tau) { return family_call(F_COMPOSE, sigma, tau); }
MapId map_override(MapId sigma, Sort sort, uint64_t key, uint64_t image) {
    uint64_t e[3] = { sort, key, image };
    return family_call(F_OVERRIDE, sigma, interner_intern(&M.keys, e, 3, NULL));
}
RefId reindex(RefId t, MapId sigma) { return family_call(F_REINDEX, t, sigma); }
IntervalId iv_reindex(IntervalId r, MapId m) { return family_call(F_IVRE, r, m); }
FaceId fc_reindex(FaceId phi, MapId m) { return family_call(F_FCRE, phi, m); }
