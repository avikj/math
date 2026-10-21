/* subst.c — substitution records and their operations as pure producer
 * families.
 *
 * A substitution record is [(key, sort, value)*] sorted by key, followed for
 * an environment by its definition word:
 *   a map         keys are variables and dimensions (and construction atoms);
 *                 an absent key is its own image, so identity entries are
 *                 never stored (the record is canonical);
 *   an environment keys are the parameter and local slots of a node; it is
 *                 total over the slots it assigns (its values live in the
 *                 enclosing space, so no entry is an identity).
 * One lookup (binary search, one probe per step) and one set serve both;
 * composition is of maps. Applying a record is the one traversal
 * (scopefam.c) with the map (RE) or environment (ENV) as its image source;
 * a reference's environment is rebuilt here under any traversal. */
#include "eval.h"
#include "template.h"

/* an identity entry key ↦ VAR(key) / key, recognized without forming VAR(key) */
bool subst_identity(uint64_t sort, uint64_t key, uint64_t img) {
    return sort == PS_INTERVAL ? img == iv_var(key) : sort == PS_REF && ref_is_var(img) && ref_var_id(img) == key;
}
static const uint64_t *srec(uint64_t m, size_t *n) { return rget(m, n); }

/* ---------------- lookup: the position of key w[1] in record w[0], plus one (0: absent) ---------------- */
typedef struct { const uint64_t *w; size_t n, lo, hi, at; } LookLoc;
static void look_step(Cont *k, uint64_t v) {
    LookLoc *L = FR_LOC(k, LookLoc);
    FR_BEGIN(k);
    L->w = srec(k->w[0], &L->n);
    L->lo = 0; L->hi = L->n / 3;
    while (!sorted_probe(L->w, 3, k->w[1], &L->lo, &L->hi, &L->at)) FR_YIELD(k);
    FR_FINISH(k, L->at);
    FR_END(k);
}

/* ---------------- set: record w[0] with the entry w[1] = [key, sort, value] ----------------
 * placed or replaced; in a map an identity entry removes the key */
typedef struct { const uint64_t *x, *e; size_t nx, q, ne; bool placed, map; WordBuf out; bool created; } SetLoc;
static void set_push(SetLoc *L, const uint64_t *t) {
    if (L->map && subst_identity(t[1], t[0], t[2])) return;
    wordbuf_push(&L->out, t[0]); wordbuf_push(&L->out, t[1]); wordbuf_push(&L->out, t[2]);
}
static void set_step(Cont *k, uint64_t v) {
    SetLoc *L = FR_LOC(k, SetLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    L->x = srec(k->w[0], &L->nx); L->e = rget(k->w[1], &L->ne);
    L->map = L->nx % 3 == 0; L->placed = false;
    wordbuf_init(&L->out);
    for (L->q = 0; L->q + 3 <= L->nx; L->q += 3) {
        if (!L->placed && L->x[L->q] >= L->e[0]) {
            set_push(L, L->e); L->placed = true;
            if (L->x[L->q] == L->e[0]) { FR_YIELD(k); continue; }
        }
        set_push(L, L->x + L->q);
        FR_YIELD(k);
    }
    if (!L->placed) set_push(L, L->e);
    if (!L->map) wordbuf_push(&L->out, L->x[L->nx - 1]);              /* an environment's definition word */
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}


/* ---------------- the dimensions of an interval or face as a set ----------------
 * atoms and literals both carry the dimension in their high bits */
typedef struct { const uint64_t *x; size_t nx, i; uint64_t acc, d; } DimsLoc;
static void dims_step(Cont *k, uint64_t v) {
    DimsLoc *L = FR_LOC(k, DimsLoc);
    FR_BEGIN(k);
    L->x = rget(k->w[0], &L->nx);
    L->acc = set_make(NULL, 0);
    for (L->i = 0; L->i < L->nx; L->i++) {
        if (L->x[L->i] == DNF_SEP) { FR_YIELD(k); continue; }
        L->d = L->x[L->i] >> 1;
        FR_AWAIT(k, L->acc, F_SUNION, L->acc, set_make(&L->d, 1));
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

/* ---------------- a reference's environment rebuilt under traversal w[1] ----------------
 * the entries are independent demands: launched, then awaited in order */
typedef struct { size_t n, q; uint64_t slot, f, b; TVal val; bool changed; WordBuf out; bool created; } ReLoc;
static void re_item(uint64_t tk, TVal val, uint64_t *f, uint64_t *b) {
    *b = tk;
    *f = val.sort == PS_LEVEL ? 0 : val.sort == PS_REF ? F_TREF : val.sort == PS_INTERVAL ? F_TIV : F_TFC;
}
static void envrebuild_step(Cont *k, uint64_t v) {
    ReLoc *L = FR_LOC(k, ReLoc);
    RefId t = k->w[0];
    uint64_t r = 0, id = 0;
    FR_BEGIN(k);
    L->n = subst_size(ref_tenv(t));
    for (L->q = 0; L->q < L->n; L->q++) {
        subst_get(ref_tenv(t), L->q, &L->slot, &L->val);
        re_item(k->w[1], L->val, &L->f, &L->b);
        if (L->f) family_launch((Family)L->f, L->val.id, L->b);
        FR_YIELD(k);
    }
    L->changed = false;
    wordbuf_init(&L->out);
    for (L->q = 0; L->q < L->n; L->q++) {
        subst_get(ref_tenv(t), L->q, &L->slot, &L->val);
        re_item(k->w[1], L->val, &L->f, &L->b);
        if (L->f) FR_AWAIT(k, r, (Family)L->f, L->val.id, L->b);
        else { FR_YIELD(k); r = L->val.id; }                     /* a level: kept */
        if (r != L->val.id) L->changed = true;
        wordbuf_push(&L->out, L->slot); wordbuf_push(&L->out, L->val.sort); wordbuf_push(&L->out, r);
    }
    if (!L->changed) { while (wordbuf_drain_one(&L->out)) FR_YIELD(k); FR_FINISH(k, t); }
    wordbuf_push(&L->out, tnode_def(ref_tnode(t)));
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_AWAIT(k, r, F_TVMAKE, ref_tnode(t), id);
    FR_FINISH(k, r);
    FR_END(k);
}

void subst_families_init(void) {
    family_define(F_LOOKUP, "subst.lookup", look_step, sizeof(LookLoc));
    family_define(F_SET, "subst.set", set_step, sizeof(SetLoc));
    family_define(F_ENVREBUILD, "env.rebuild", envrebuild_step, sizeof(ReLoc));
    family_define(F_DIMS, "dnf.dims", dims_step, sizeof(DimsLoc));
}

/* ---------------- records and the operations (synchronous driver) ---------------- */
size_t subst_size(uint64_t rec) { size_t n; (void)srec(rec, &n); return n / 3; }
void subst_get(uint64_t rec, size_t k, uint64_t *key, TVal *v) {
    size_t n; const uint64_t *w = srec(rec, &n);
    require(k < n / 3, "substitution entry out of range");
    *key = w[3 * k]; v->sort = (PSort)w[3 * k + 1]; v->id = w[3 * k + 2];
}
uint64_t subst_value(uint64_t rec, size_t k) { uint64_t key; TVal v; subst_get(rec, k, &key, &v); return v.id; }
uint64_t subst_entry(uint64_t key, uint64_t sort, uint64_t value) { return RQ(key, sort, value); }
uint64_t env_empty(uint64_t def) { return interner_intern(&M.keys, &def, 1, NULL); }

/* a host map: its triples sorted (insertion; inside a counted step only a
 * fixed handful), conflicting keys rejected, identities dropped */
void mapb_init(MapBuilder *b) { words_init(&b->w); }
void mapb_term(MapBuilder *b, TermVarId x, RefId image) { words_push(&b->w, x); words_push(&b->w, PS_REF); words_push(&b->w, image); }
void mapb_dim(MapBuilder *b, DimVarId i, IntervalId image) { words_push(&b->w, i); words_push(&b->w, PS_INTERVAL); words_push(&b->w, image); }
MapId mapb_finish(MapBuilder *b) {
    size_t n = b->w.n / 3; uint64_t *w = b->w.w;
    require(!intern_in_step || n <= 4, "a map of %zu entries finished synchronously inside a counted step", n);
    for (size_t i = 1; i < n; i++)
        for (size_t j = i; j > 0 && w[3 * (j - 1)] > w[3 * j]; j--)
            for (size_t c = 0; c < 3; c++) { uint64_t t = w[3 * j + c]; w[3 * j + c] = w[3 * (j - 1) + c]; w[3 * (j - 1) + c] = t; }
    Words out; words_init(&out);
    for (size_t k = 0; k < n; k++) {
        if (k > 0 && w[3 * (k - 1)] == w[3 * k]) { require(w[3 * (k - 1) + 2] == w[3 * k + 2], "conflicting key in map"); continue; }
        if (subst_identity(w[3 * k + 1], w[3 * k], w[3 * k + 2])) continue;
        for (size_t c = 0; c < 3; c++) words_push(&out, w[3 * k + c]);
    }
    MapId id = interner_intern(&M.keys, out.w, out.n, NULL);
    words_free(&out); words_free(&b->w);
    return id;
}
MapId map_identity(void) { return interner_intern(&M.keys, NULL, 0, NULL); }
bool map_is_identity(MapId m) { size_t n; (void)srec(m, &n); return n == 0; }
MapId map_single_term(TermVarId x, RefId a) { MapBuilder b; mapb_init(&b); mapb_term(&b, x, a); return mapb_finish(&b); }
MapId map_single_dim(DimVarId i, IntervalId r) { MapBuilder b; mapb_init(&b); mapb_dim(&b, i, r); return mapb_finish(&b); }

static uint64_t lookup_value(uint64_t rec, uint64_t key, uint64_t absent) {
    uint64_t r = family_call(F_LOOKUP, rec, key);
    return r ? subst_value(rec, r - 1) : absent;
}
RefId map_term_image(MapId m, TermVarId x) { uint64_t v = lookup_value(m, x, 0); return v ? v : ref_var(x); }
IntervalId map_dim_image(MapId m, DimVarId i) { return lookup_value(m, i, iv_var(i)); }
RefId reindex(RefId t, MapId sigma) { return family_call(F_TREF, t, re_key(sigma)); }
IntervalId iv_reindex(IntervalId r, MapId m) { return family_call(F_TIV, r, re_key(m)); }
FaceId fc_reindex(FaceId phi, MapId m) { return family_call(F_TFC, phi, re_key(m)); }
