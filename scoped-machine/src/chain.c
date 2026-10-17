/* chain.c — see chain.h and CUBICAL-STOKES-ADDENDUM §§1–10. */
#include "chain.h"
#include "intern.h"
#include "radix.h"
#include "fine.h"
#include "eval.h"
#include <string.h>
#include <sched.h>
#include <stdio.h>

#define COMPUTING UINT64_MAX
struct Cochain { uint64_t id; int kind; size_t degree; uint64_t signature; ChAct act; void *ctx; Cochain *inner; LocalSystem *ls; ChainMapT *F; Cochain *all_next; };
enum { CO_GEN = 1, CO_COB, CO_PULL };
struct ChainMapT { uint64_t id; ChMapAct act; void *ctx; int shift; ChainMapT *all_next; };
struct LocalSystem { uint64_t id; ChTransport T; ChSquare square; void *ctx; size_t nunits; uint64_t *units; LocalSystem *all_next; };

static struct {
    pthread_mutex_t mu;
    Interner cells, chains, mods;
    WordMap face, prodroot, coval, fmap, admit, lsadmit, law, coordix;
    DimVarId *coords; size_t ncoords, capcoords;
    uint64_t ids;
    Cochain *cochains; ChainMapT *maps; LocalSystem *lss;
    uint64_t st_ops, st_units, st_hits, st_law_pairs;
    bool live;
} C;

static uint64_t fresh(void) { return __atomic_add_fetch(&C.ids, 1, __ATOMIC_RELAXED); }
static void unit(void) { fine_bump(FC_CHAIN_STEPS); __atomic_add_fetch(&C.st_units, 1, __ATOMIC_RELAXED); }
static bool memo_get(WordMap *m, const uint64_t *k, size_t n, uint64_t *v) { return wordmap_get(m, k, n, v); }

void chain_init(void) {
    memset(&C, 0, sizeof C); pthread_mutex_init(&C.mu, NULL);
    interner_init(&C.cells); interner_init(&C.chains); interner_init(&C.mods);
    wordmap_init(&C.face); wordmap_init(&C.prodroot); wordmap_init(&C.coval); wordmap_init(&C.fmap);
    wordmap_init(&C.admit); wordmap_init(&C.lsadmit); wordmap_init(&C.law); wordmap_init(&C.coordix);
    C.live = true;
}
void chain_free(void) {
    if (!C.live) return;
    for (Cochain *a = C.cochains, *n; a; a = n) { n = a->all_next; free(a); }
    for (ChainMapT *f = C.maps, *n; f; f = n) { n = f->all_next; free(f); }
    for (LocalSystem *l = C.lss, *n; l; l = n) { n = l->all_next; free(l->units); free(l); }
    interner_free(&C.cells); interner_free(&C.chains); interner_free(&C.mods);
    wordmap_free(&C.face); wordmap_free(&C.prodroot); wordmap_free(&C.coval); wordmap_free(&C.fmap);
    wordmap_free(&C.admit); wordmap_free(&C.lsadmit); wordmap_free(&C.law); wordmap_free(&C.coordix);
    free(C.coords); pthread_mutex_destroy(&C.mu);
    memset(&C, 0, sizeof C);
}
ChainStats chain_stats(void) {
    ChainStats s; s.cells = interner_count(&C.cells); s.chains = interner_count(&C.chains); s.mods = interner_count(&C.mods);
    s.ops = __atomic_load_n(&C.st_ops, __ATOMIC_RELAXED); s.units = __atomic_load_n(&C.st_units, __ATOMIC_RELAXED);
    s.memo_hits = __atomic_load_n(&C.st_hits, __ATOMIC_RELAXED); s.law_pairs = __atomic_load_n(&C.st_law_pairs, __ATOMIC_RELAXED);
    return s;
}

/* ================= exact integers ================= */
Nat nat_mul_exact(Nat a, Nat b) {
    if (nat_is_small(a) && nat_is_small(b)) {
        unsigned __int128 p = (unsigned __int128)a * b; fine_bump(FC_NAT_LIMBS);
        uint64_t l[2] = { (uint64_t)p, (uint64_t)(p >> 64) };
        return nat_from_limbs(2, l);
    }
    size_t na, nb; uint64_t ta, tb; const uint64_t *la = nat_limbs(a, &na, &ta), *lb = nat_limbs(b, &nb, &tb);
    uint64_t *r = calloc(na + nb + 1, sizeof *r); require(r, "out of memory");
    for (size_t i = 0; i < na; i++) {
        uint64_t carry = 0;
        for (size_t j = 0; j < nb; j++) {
            unsigned __int128 p = (unsigned __int128)la[i] * lb[j] + r[i + j] + carry; fine_bump(FC_NAT_LIMBS);
            r[i + j] = (uint64_t)p; carry = (uint64_t)(p >> 64);
        }
        size_t k = i + nb; while (carry) { unsigned __int128 s = (unsigned __int128)r[k] + carry; r[k] = (uint64_t)s; carry = (uint64_t)(s >> 64); k++; fine_bump(FC_NAT_LIMBS); }
    }
    Nat out = nat_from_limbs(na + nb + 1, r); free(r); return out;
}
Zx zx_nat(int sign, Nat mag) { Zx z; z.mag = mag; z.sign = mag == 0 ? 0 : (sign < 0 ? -1 : 1); return z; }
Zx zx_i64(int64_t v) { if (v == 0) return zx_nat(0, 0); uint64_t m = v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v; return zx_nat(v < 0 ? -1 : 1, nat_from_word(m)); }
bool zx_is_zero(Zx a) { return a.sign == 0; }
bool zx_eq(Zx a, Zx b) { return a.sign == b.sign && a.mag == b.mag; }
Zx zx_neg(Zx a) { a.sign = -a.sign; return a; }
Zx zx_add(Zx a, Zx b) {
    if (!a.sign) return b;
    if (!b.sign) return a;
    if (a.sign == b.sign) return zx_nat(a.sign, nat_add(a.mag, b.mag));
    NatDiff d = nat_diff(a.mag, b.mag);                 /* |a| − |b| */
    if (d.sign == 0) return zx_nat(0, 0);
    return zx_nat(d.sign > 0 ? a.sign : b.sign, d.magnitude);
}
Zx zx_mul(Zx a, Zx b) { if (!a.sign || !b.sign) return zx_nat(0, 0); return zx_nat(a.sign * b.sign, nat_mul_exact(a.mag, b.mag)); }
size_t zx_decimal(Zx a, char *buf, size_t cap) {
    if (cap == 0) return 0;
    size_t o = 0; if (a.sign < 0 && cap > 1) buf[o++] = '-';
    return o + nat_decimal(a.mag, buf + o, cap - o);
}

/* ================= modules: [n, (unit, sign, mag)*] sorted by unit ================= */
static ModId mod_intern(const uint64_t *w, size_t n) { return interner_intern(&C.mods, w, n, NULL); }
static const uint64_t *modrec(ModId a, size_t *n) { return interner_get(&C.mods, a, n); }
ModId mod_zero(void) { uint64_t w[1] = { 0 }; return mod_intern(w, 1); }
ModId mod_unit(uint64_t u, Zx c) { if (!c.sign) return mod_zero(); uint64_t w[4] = { 1, u, (uint64_t)(int64_t)c.sign, c.mag }; return mod_intern(w, 4); }
ModId mod_int(Zx c) { return mod_unit(0, c); }
size_t mod_nterms(ModId a) { size_t n; return (size_t)modrec(a, &n)[0]; }
void mod_term(ModId a, size_t k, uint64_t *u, Zx *c) { size_t n; const uint64_t *r = modrec(a, &n); *u = r[1 + 3 * k]; *c = zx_nat((int)(int64_t)r[2 + 3 * k], r[3 + 3 * k]); }
bool mod_is_zero(ModId a) { return mod_nterms(a) == 0; }
Zx mod_coef(ModId a, uint64_t u) { size_t n = mod_nterms(a); for (size_t k = 0; k < n; k++) { uint64_t v; Zx c; mod_term(a, k, &v, &c); if (v == u) return c; } return zx_nat(0, 0); }
bool mod_scalar(ModId a, Zx *c) {
    size_t n = mod_nterms(a);
    if (n == 0) { *c = zx_nat(0, 0); return true; }
    uint64_t u; mod_term(a, 0, &u, c); return n == 1 && u == 0;
}
static ModId mod_build(Words *w) { w->w[0] = (w->n - 1) / 3; ModId m = mod_intern(w->w, w->n); words_free(w); return m; }
ModId mod_add(ModId a, ModId b) {
    if (mod_is_zero(a)) return b;
    if (mod_is_zero(b)) return a;
    size_t na = mod_nterms(a), nb = mod_nterms(b), i = 0, j = 0;
    Words w; words_init(&w); words_push(&w, 0);
    while (i < na || j < nb) {
        uint64_t ua = UINT64_MAX, ub = UINT64_MAX; Zx ca = {0, 0}, cb = {0, 0};
        if (i < na) mod_term(a, i, &ua, &ca);
        if (j < nb) mod_term(b, j, &ub, &cb);
        uint64_t u; Zx c;
        if (j >= nb || (i < na && ua < ub)) { u = ua; c = ca; i++; }
        else if (i >= na || ub < ua) { u = ub; c = cb; j++; }
        else { u = ua; c = zx_add(ca, cb); i++; j++; }
        fine_bump(FC_COPY_WORDS);
        if (c.sign) { words_push(&w, u); words_push(&w, (uint64_t)(int64_t)c.sign); words_push(&w, c.mag); }
    }
    return mod_build(&w);
}
ModId mod_scale(Zx s, ModId a) {
    if (!s.sign || mod_is_zero(a)) return mod_zero();
    if (s.sign == 1 && s.mag == 1) return a;
    size_t n = mod_nterms(a); Words w; words_init(&w); words_push(&w, 0);
    for (size_t k = 0; k < n; k++) { uint64_t u; Zx c; mod_term(a, k, &u, &c); Zx p = zx_mul(s, c); words_push(&w, u); words_push(&w, (uint64_t)(int64_t)p.sign); words_push(&w, p.mag); }
    return mod_build(&w);
}
ModId mod_neg(ModId a) { return mod_scale(zx_i64(-1), a); }
size_t mod_print(ModId a, char *buf, size_t cap) {
    size_t n = mod_nterms(a), o = 0; Zx c;
    if (mod_scalar(a, &c)) return zx_decimal(c, buf, cap);
    o += (size_t)snprintf(buf + o, o < cap ? cap - o : 0, "(");
    for (size_t k = 0; k < n && o < cap; k++) { uint64_t u; mod_term(a, k, &u, &c); o += (size_t)snprintf(buf + o, cap - o, "%su%llu:", k ? ", " : "", (unsigned long long)u); if (o < cap) o += zx_decimal(c, buf + o, cap - o); }
    if (o < cap) o += (size_t)snprintf(buf + o, cap - o, ")");
    return o;
}
static Zx scalar_of(ModId a) { Zx c; require(mod_scalar(a, &c), "a scalar coefficient was required"); return c; }

/* ================= coordinates ================= */
DimVarId cube_coord(size_t k) {
    require(k >= 1, "cube coordinates start at 1");
    pthread_mutex_lock(&C.mu);
    while (C.ncoords < k) {
        if (C.ncoords == C.capcoords) { C.capcoords = C.capcoords ? 2 * C.capcoords : 16; C.coords = realloc(C.coords, C.capcoords * sizeof *C.coords); require(C.coords, "out of memory"); }
        DimVarId d = declare_dim(); C.coords[C.ncoords++] = d;
        uint64_t key[1] = { d }; wordmap_put(&C.coordix, key, 1, C.ncoords);
    }
    DimVarId d = C.coords[k - 1];
    pthread_mutex_unlock(&C.mu);
    return d;
}
static size_t coord_index(DimVarId d) { uint64_t key[1] = { d }, v = 0; return wordmap_get(&C.coordix, key, 1, &v) ? (size_t)v : 0; }
static bool images_within(size_t n, const IntervalId *img, size_t m) {
    for (size_t j = 0; j < n; j++) {
        Words w; words_init(&w); iv_dims(img[j], &w);
        bool ok = true; for (size_t k = 0; k < w.n && ok; k++) { size_t c = coord_index(w.w[k]); ok = c >= 1 && c <= m; }
        words_free(&w); if (!ok) return false;
    }
    return true;
}
static MapId coord_map(size_t m, const IntervalId *sigma) {   /* c_k ↦ sigma[k−1], simultaneously */
    MapBuilder b; mapb_init(&b);
    for (size_t k = 1; k <= m; k++) mapb_dim(&b, cube_coord(k), sigma[k - 1]);
    return mapb_finish(&b);
}

/* ================= cells ================= */
static const uint64_t *cellrec(CellId x, size_t *n) { return interner_get(&C.cells, x, n); }
int cell_kind(CellId x) { size_t n; return x ? (int)cellrec(x, &n)[0] : 0; }
size_t cell_degree(CellId x) {
    size_t n; const uint64_t *r = cellrec(x, &n);
    if (r[0] == CK_PRODUCT) return cell_degree(r[1]) + cell_degree(r[2]);
    return (size_t)r[3];
}
uint64_t cell_tag(CellId x, uint64_t *ns) { size_t n; const uint64_t *r = cellrec(x, &n); if (r[0] == CK_PRESENTED || r[0] == CK_DECLARED) { if (ns) *ns = r[1]; return r[2]; } if (ns) *ns = 0; return 0; }
bool cell_cubical(CellId x) {
    size_t n; const uint64_t *r = cellrec(x, &n);
    if (r[0] == CK_PRODUCT) return cell_cubical(r[1]) && cell_cubical(r[2]);
    return r[0] != CK_DECLARED;
}
static bool root_dims(ScopeId root, size_t *n) {
    size_t a = scope_arity(root);
    for (size_t k = 0; k < a; k++) if (scope_local(root, k).sort != S_DIM) return false;
    *n = a; return true;
}
CheckStatus cell_admit_root(ContextId G, FaceId kappa, ScopeId root, const char **why) {
    size_t n; if (!root_dims(root, &n)) { if (why) *why = "a presented cell's locals are dimensions"; return CK_INVALID; }
    uint64_t *ids = calloc(n ? n : 1, sizeof *ids); require(ids, "out of memory");
    TypedPartial p = open_scope_fresh(root, 0xC0BE, ids);
    ContextId Gd = G; for (size_t k = 0; k < n; k++) Gd = context_extend_dim(Gd, ids[k]);
    free(ids);
    if (p.body.sort != VS_REF) { if (why) *why = "a presented cell's body is a term"; return CK_INVALID; }
    return check(Gd, fc_meet(kappa, p.guard), p.body.id, p.type, why);
}
CellId cell_view(ScopeId root, MapId params, size_t m, const IntervalId *images) {
    size_t n; require(root_dims(root, &n), "a cube view's root has dimension locals only");
    require(images_within(n, images, m), "a cube view's images use its own coordinates only");
    uint64_t *w = malloc((5 + n) * sizeof *w); require(w, "out of memory");
    w[0] = CK_VIEW; w[1] = root; w[2] = params ? params : map_identity(); w[3] = m; w[4] = n;
    for (size_t j = 0; j < n; j++) w[5 + j] = images[j];
    CellId x = interner_intern(&C.cells, w, 5 + n, NULL); free(w); return x;
}
CellId cell_root(ScopeId root, MapId params) {
    size_t n; require(root_dims(root, &n), "a cube view's root has dimension locals only");
    IntervalId *img = malloc((n ? n : 1) * sizeof *img); require(img, "out of memory");
    for (size_t k = 0; k < n; k++) img[k] = iv_var(cube_coord(k + 1));
    CellId x = cell_view(root, params, n, img); free(img); return x;
}
bool cell_view_parts(CellId x, ScopeId *root, MapId *params, size_t *n, const IntervalId **images) {
    size_t len; const uint64_t *r = cellrec(x, &len);
    if (r[0] != CK_VIEW) return false;
    if (root) *root = r[1];
    if (params) *params = r[2];
    if (n) *n = (size_t)r[4];
    if (images) *images = (const IntervalId *)(r + 5);
    return true;
}
RefId cell_body(CellId x) {
    ScopeId root; MapId params; size_t n; const IntervalId *img;
    require(cell_view_parts(x, &root, &params, &n, &img), "cell_body: a cube view");
    Val *args = malloc((n ? n : 1) * sizeof *args); require(args, "out of memory");
    for (size_t j = 0; j < n; j++) { args[j].sort = VS_INTERVAL; args[j].id = img[j]; }
    TypedPartial p = apply_scope(root, n, args); free(args);
    RefId b = p.body.id;
    return map_is_identity(params) ? b : reindex(b, params);
}
CellId cell_reindex(CellId x, size_t m2, const IntervalId *sigma) {
    size_t len; const uint64_t *r = cellrec(x, &len);
    require(r[0] == CK_VIEW, "CUBE_REINDEX by a general cube map acts on cube views");
    size_t m = (size_t)r[3], n = (size_t)r[4];
    require(images_within(m, sigma, m2), "a cube map's images use the target coordinates only");
    MapId s = coord_map(m, sigma);
    IntervalId *img = malloc((n ? n : 1) * sizeof *img); require(img, "out of memory");
    for (size_t j = 0; j < n; j++) img[j] = iv_reindex((IntervalId)r[5 + j], s);
    CellId y = cell_view(r[1], r[2], m2, img); free(img); return y;
}
void cube_map_compose(size_t m, const IntervalId *sigma, size_t m2, const IntervalId *tau, IntervalId *out) {
    MapId t = coord_map(m2, tau);
    for (size_t k = 0; k < m; k++) out[k] = iv_reindex(sigma[k], t);
}
static ScopeId eff_root(ScopeId root, MapId params) { return map_is_identity(params) ? root : reindex_scope(root, params); }
static ScopeId prod_root(ScopeId R1, ScopeId R2) {
    uint64_t key[2] = { R1, R2 }, v = 0;
    if (memo_get(&C.prodroot, key, 2, &v)) return v;
    size_t n1 = scope_arity(R1), n2 = scope_arity(R2);
    uint64_t *ids = calloc(n1 + n2 + 1, sizeof *ids); require(ids, "out of memory");
    TypedPartial p1 = open_scope_fresh(R1, 0x50524F44000001ULL ^ (R2 << 8), ids);
    TypedPartial p2 = open_scope_fresh(R2, 0x50524F44000002ULL ^ (R1 << 8), ids + n1);
    uint64_t l1 = p1.level, l2 = p2.level, l = nat_max(l1, l2);
    TermVarId z = declare_term(p1.type, fc_true());
    RefId Sg = mk_sigma_lv(l1, l2, z, p1.type, p2.type);
    RefId body = mk_pair_at_lv(l, Sg, p1.body.id, p2.body.id);
    CaptureDecl *d = calloc(n1 + n2 + 1, sizeof *d); require(d, "out of memory");
    for (size_t k = 0; k < n1 + n2; k++) { d[k].sort = S_DIM; d[k].id = ids[k]; d[k].type = 0; d[k].level = LEVEL_NONE; d[k].required = fc_true(); }
    Val b = { VS_REF, body };
    ScopeId S = capture_scope(n1 + n2, d, b, Sg, l, fc_meet(p1.guard, p2.guard));
    free(d); free(ids);
    wordmap_put(&C.prodroot, key, 2, S);
    return S;
}
CellId cell_product(CellId x, CellId y) {
    size_t lx, ly; const uint64_t *rx = cellrec(x, &lx), *ry = cellrec(y, &ly);
    if (rx[0] == CK_VIEW && ry[0] == CK_VIEW) {
        ScopeId R1 = eff_root(rx[1], rx[2]), R2 = eff_root(ry[1], ry[2]);
        size_t p = (size_t)rx[3], q = (size_t)ry[3], n1 = (size_t)rx[4], n2 = (size_t)ry[4];
        ScopeId R = prod_root(R1, R2);
        IntervalId *shift = malloc((q ? q : 1) * sizeof *shift), *img = malloc((n1 + n2 + 1) * sizeof *img); require(shift && img, "out of memory");
        for (size_t k = 1; k <= q; k++) shift[k - 1] = iv_var(cube_coord(k + p));
        MapId sh = coord_map(q, shift);
        for (size_t j = 0; j < n1; j++) img[j] = (IntervalId)rx[5 + j];
        for (size_t j = 0; j < n2; j++) img[n1 + j] = iv_reindex((IntervalId)ry[5 + j], sh);
        CellId c = cell_view(R, map_identity(), p + q, img); free(shift); free(img); return c;
    }
    uint64_t w[3] = { CK_PRODUCT, x, y };
    return interner_intern(&C.cells, w, 3, NULL);
}
CellId cell_face(CellId x, size_t i, int eps) {
    size_t len; const uint64_t *r = cellrec(x, &len);
    size_t m = cell_degree(x);
    require(i >= 1 && i <= m, "face coordinate out of range");
    uint64_t key[3] = { x, i, (uint64_t)(eps != 0) }, v = 0;
    if (memo_get(&C.face, key, 3, &v)) return v;
    CellId f = 0;
    switch (r[0]) {
    case CK_VIEW: {
        IntervalId *s = malloc(m * sizeof *s); require(s, "out of memory");
        for (size_t k = 1; k <= m; k++) s[k - 1] = k < i ? iv_var(cube_coord(k)) : k == i ? (eps ? iv_one() : iv_zero()) : iv_var(cube_coord(k - 1));
        f = cell_reindex(x, m - 1, s); free(s); break;
    }
    case CK_PRESENTED: f = r[4 + 2 * (i - 1) + (eps != 0)]; break;
    case CK_PRODUCT: {
        size_t p = cell_degree(r[1]);
        require(cell_cubical(x), "faces of a product with a declared-boundary factor are given by its boundary only");
        f = i <= p ? cell_product(cell_face(r[1], i, eps), r[2]) : cell_product(r[1], cell_face(r[2], i - p, eps));
        break;
    }
    default: die("a declared-boundary cell has no cubical faces");
    }
    wordmap_put(&C.face, key, 3, f);
    return f;
}
CellId cell_param(CellId x, MapId tau) {
    size_t len; const uint64_t *r = cellrec(x, &len);
    if (r[0] == CK_VIEW) return cell_view(r[1], compose(r[2], tau), (size_t)r[3], (const IntervalId *)(r + 5));
    if (r[0] == CK_PRODUCT) return cell_product(cell_param(r[1], tau), cell_param(r[2], tau));
    return x;
}
bool cell_degenerate(CellId x, size_t *coord) {
    size_t len; const uint64_t *r = cellrec(x, &len);
    if (r[0] == CK_PRODUCT) {
        size_t c; if (cell_degenerate(r[1], &c)) { if (coord) *coord = c; return true; }
        if (cell_degenerate(r[2], &c)) { if (coord) *coord = c + cell_degree(r[1]); return true; }
        return false;
    }
    if (r[0] != CK_VIEW) return false;
    size_t m = (size_t)r[3], n = (size_t)r[4];
    bool *used = calloc(m + 1, sizeof *used); require(used, "out of memory");
    for (size_t j = 0; j < n; j++) { Words w; words_init(&w); iv_dims((IntervalId)r[5 + j], &w); for (size_t k = 0; k < w.n; k++) { size_t c = coord_index(w.w[k]); if (c >= 1 && c <= m) used[c] = true; } words_free(&w); }
    size_t miss = 0; for (size_t k = 1; k <= m && !miss; k++) if (!used[k]) miss = k;
    free(used);
    if (miss && coord) *coord = miss;
    return miss != 0;
}
CellId cell_base_edge(CellId x, size_t i) {
    size_t m = cell_degree(x); require(i >= 1 && i <= m, "edge coordinate out of range");
    for (size_t k = m; k >= 1; k--) if (k != i) x = cell_face(x, k, 0);
    return x;
}
CellId cell_base_square(CellId x, size_t i, size_t j) {
    size_t m = cell_degree(x); require(i >= 1 && i < j && j <= m, "square coordinates out of range");
    for (size_t k = m; k >= 1; k--) if (k != i && k != j) x = cell_face(x, k, 0);
    return x;
}

/* ================= chains: [degree, n, (cell, mod)*] sorted by cell ================= */
static const uint64_t *chainrec(ChainId c, size_t *n) { return interner_get(&C.chains, c, n); }
ChainId chain_zero(size_t degree) { uint64_t w[2] = { degree, 0 }; return interner_intern(&C.chains, w, 2, NULL); }
size_t chain_degree(ChainId c) { size_t n; return (size_t)chainrec(c, &n)[0]; }
size_t chain_nterms(ChainId c) { size_t n; return (size_t)chainrec(c, &n)[1]; }
void chain_term(ChainId c, size_t k, CellId *x, ModId *m) { size_t n; const uint64_t *r = chainrec(c, &n); *x = r[2 + 2 * k]; *m = r[3 + 2 * k]; }
bool chain_is_zero(ChainId c) { return chain_nterms(c) == 0; }
ModId chain_coef(ChainId c, CellId x) {
    size_t n = chain_nterms(c), lo = 0, hi = n;
    while (lo < hi) { size_t mid = (lo + hi) / 2; CellId y; ModId m; chain_term(c, mid, &y, &m); if (y == x) return m; if (y < x) lo = mid + 1; else hi = mid; }
    return mod_zero();
}

/* the accumulator: a sparse index cell → slot; finished by a stepwise heap sort (one sift per step) */
typedef struct { size_t degree; Radix idx; CellId *cell; ModId *coef; size_t n, cap; size_t *ord; size_t no, phase, i, hn; } Acc;
static void acc_init(Acc *a, size_t degree) { memset(a, 0, sizeof *a); a->degree = degree; radix_init(&a->idx); }
static void acc_release(Acc *a) { radix_free(&a->idx, NULL, NULL); free(a->cell); free(a->coef); free(a->ord); memset(a, 0, sizeof *a); }
static void acc_add(Acc *a, CellId x, ModId m) {
    if (mod_is_zero(m)) return;
    void **slot = radix_slot(&a->idx, (size_t)x, true);
    size_t pos = (size_t)(uintptr_t)*slot;
    if (pos) { a->coef[pos - 1] = mod_add(a->coef[pos - 1], m); return; }
    if (a->n == a->cap) { a->cap = a->cap ? 2 * a->cap : 8; a->cell = realloc(a->cell, a->cap * sizeof *a->cell); a->coef = realloc(a->coef, a->cap * sizeof *a->coef); require(a->cell && a->coef, "out of memory"); }
    a->cell[a->n] = x; a->coef[a->n] = m; a->n++; *slot = (void *)(uintptr_t)a->n;
}
static void sift(Acc *a, size_t i, size_t n) {
    for (;;) {
        size_t l = 2 * i + 1, big = i; kernel_sort_step();
        if (l < n && a->cell[a->ord[l]] > a->cell[a->ord[big]]) big = l;
        if (l + 1 < n && a->cell[a->ord[l + 1]] > a->cell[a->ord[big]]) big = l + 1;
        if (big == i) return;
        size_t t = a->ord[i]; a->ord[i] = a->ord[big]; a->ord[big] = t; i = big;
    }
}
static bool acc_finish_step(Acc *a, ChainId *out) {
    switch (a->phase) {
    case 0: a->ord = malloc((a->n ? a->n : 1) * sizeof *a->ord); require(a->ord, "out of memory"); a->no = 0; a->i = 0; a->phase = 1; return false;
    case 1: if (a->i < a->n) { if (!mod_is_zero(a->coef[a->i])) a->ord[a->no++] = a->i; a->i++; return false; }   /* zero coefficients disappear from the reading */
            a->i = a->no / 2; a->phase = 2; return false;
    case 2: if (a->i > 0) { a->i--; sift(a, a->i, a->no); return false; }
            a->hn = a->no; a->phase = 3; return false;
    case 3: if (a->hn > 1) { size_t t = a->ord[0]; a->ord[0] = a->ord[a->hn - 1]; a->ord[a->hn - 1] = t; a->hn--; sift(a, 0, a->hn); return false; }
            a->phase = 4; return false;
    default: {
        uint64_t *w = malloc((2 + 2 * a->no) * sizeof *w); require(w, "out of memory");
        w[0] = a->degree; w[1] = a->no;
        for (size_t k = 0; k < a->no; k++) { w[2 + 2 * k] = a->cell[a->ord[k]]; w[3 + 2 * k] = a->coef[a->ord[k]]; fine_bump(FC_COPY_WORDS); }
        *out = interner_intern(&C.chains, w, 2 + 2 * a->no, NULL); free(w);
        acc_release(a); return true;
    }
    }
}
static ChainId acc_finish(Acc *a) { ChainId c; while (!acc_finish_step(a, &c)) unit(); return c; }
ChainId chain_from(size_t degree, size_t n, const CellId *cells, const ModId *coefs) {
    Acc a; acc_init(&a, degree);
    for (size_t k = 0; k < n; k++) { require(!cells[k] || cell_degree(cells[k]) == degree, "a chain's generators share its degree"); acc_add(&a, cells[k], coefs[k]); }
    return acc_finish(&a);
}
ChainId chain_gen(CellId x, ModId c) { return chain_from(cell_degree(x), 1, &x, &c); }
ChainId chain_genz(CellId x, int64_t c) { return chain_gen(x, mod_int(zx_i64(c))); }
static ChainId chain_lin(Zx sa, ChainId a, Zx sb, ChainId b) {
    size_t d = chain_nterms(a) ? chain_degree(a) : chain_degree(b);
    require(chain_is_zero(a) || chain_is_zero(b) || chain_degree(a) == chain_degree(b), "chains of one degree");
    Acc acc; acc_init(&acc, d);
    for (size_t k = 0; k < chain_nterms(a); k++) { CellId x; ModId m; chain_term(a, k, &x, &m); acc_add(&acc, x, mod_scale(sa, m)); }
    for (size_t k = 0; k < chain_nterms(b); k++) { CellId x; ModId m; chain_term(b, k, &x, &m); acc_add(&acc, x, mod_scale(sb, m)); }
    return acc_finish(&acc);
}
ChainId chain_add(ChainId a, ChainId b) { return chain_lin(zx_i64(1), a, zx_i64(1), b); }
ChainId chain_sub(ChainId a, ChainId b) { return chain_lin(zx_i64(1), a, zx_i64(-1), b); }
ChainId chain_scale(Zx s, ChainId a) { return chain_lin(s, a, zx_i64(0), chain_zero(chain_degree(a))); }
ChainId chain_product(ChainId a, ChainId b) {
    Acc acc; acc_init(&acc, chain_degree(a) + chain_degree(b));
    for (size_t i = 0; i < chain_nterms(a); i++) for (size_t j = 0; j < chain_nterms(b); j++) {
        CellId x, y; ModId mx, my; chain_term(a, i, &x, &mx); chain_term(b, j, &y, &my);
        acc_add(&acc, cell_product(x, y), mod_scale(scalar_of(mx), my));
    }
    return acc_finish(&acc);
}
ChainId chain_normalize(ChainId c) {
    Acc acc; acc_init(&acc, chain_degree(c));
    for (size_t k = 0; k < chain_nterms(c); k++) { CellId x; ModId m; chain_term(c, k, &x, &m); if (!cell_degenerate(x, NULL)) acc_add(&acc, x, m); }
    return acc_finish(&acc);
}
size_t chain_print(ChainId c, char *buf, size_t cap) {
    size_t o = 0, n = chain_nterms(c);
    if (n == 0) return (size_t)snprintf(buf, cap, "0");
    for (size_t k = 0; k < n && o < cap; k++) {
        CellId x; ModId m; chain_term(c, k, &x, &m);
        if (k) o += (size_t)snprintf(buf + o, cap - o, " + ");
        if (o < cap) o += mod_print(m, buf + o, cap - o);
        if (o < cap) o += (size_t)snprintf(buf + o, cap - o, "·#%llu", (unsigned long long)x);
    }
    return o;
}

/* ================= boundary streams ================= */
/* the k-th term of the uncombined boundary of a generator, with its scalar sign */
static size_t bstream_len(CellId x) {
    size_t len; const uint64_t *r = cellrec(x, &len);
    if (cell_cubical(x)) return 2 * cell_degree(x);
    if (r[0] == CK_DECLARED) return chain_nterms(r[4]);
    return bstream_len(r[1]) + bstream_len(r[2]);   /* a product with a declared factor: Leibniz */
}
static void bterm(CellId x, size_t k, CellId *face, Zx *s, size_t *coord, int *eps) {
    size_t len; const uint64_t *r = cellrec(x, &len);
    *coord = 0; *eps = 0;
    if (cell_cubical(x)) {
        size_t i = k / 2 + 1; int e = (int)(k & 1);
        *face = cell_face(x, i, e);
        int sg = ((i - 1) & 1) ? -1 : 1; if (!e) sg = -sg;
        *s = zx_i64(sg); *coord = i; *eps = e; return;
    }
    if (r[0] == CK_DECLARED) { ModId m; chain_term(r[4], k, face, &m); *s = scalar_of(m); return; }
    size_t lx = bstream_len(r[1]); size_t ci; int ce;
    if (k < lx) { CellId f; bterm(r[1], k, &f, s, &ci, &ce); *face = cell_product(f, r[2]); return; }
    CellId g; bterm(r[2], k - lx, &g, s, &ci, &ce);
    if (cell_degree(r[1]) & 1) *s = zx_neg(*s);
    *face = cell_product(r[1], g);
}

/* ================= cochains, maps, local systems ================= */
static Cochain *co_new(int kind, size_t degree) {
    Cochain *a = calloc(1, sizeof *a); require(a, "out of memory");
    a->id = fresh(); a->kind = kind; a->degree = degree;
    pthread_mutex_lock(&C.mu); a->all_next = C.cochains; C.cochains = a; pthread_mutex_unlock(&C.mu);
    return a;
}
Cochain *cochain_gen(size_t degree, uint64_t signature, ChAct act, void *ctx) { Cochain *a = co_new(CO_GEN, degree); a->signature = signature; a->act = act; a->ctx = ctx; return a; }
Cochain *cochain_cob(Cochain *in, LocalSystem *ls) { Cochain *a = co_new(CO_COB, in->degree + 1); a->signature = in->signature; a->inner = in; a->ls = ls; return a; }
Cochain *cochain_pull(Cochain *in, ChainMapT *F) { require(F->shift == 0, "pullback along a degree-preserving chain map"); Cochain *a = co_new(CO_PULL, in->degree); a->signature = in->signature; a->inner = in; a->F = F; return a; }
size_t cochain_degree(const Cochain *a) { return a->degree; }
ChainMapT *chainmap_new(ChMapAct act, void *ctx, int shift) {
    ChainMapT *F = calloc(1, sizeof *F); require(F, "out of memory");
    F->id = fresh(); F->act = act; F->ctx = ctx; F->shift = shift;
    pthread_mutex_lock(&C.mu); F->all_next = C.maps; C.maps = F; pthread_mutex_unlock(&C.mu);
    return F;
}
LocalSystem *localsys_new(ChTransport T, ChSquare square, void *ctx, size_t nunits, const uint64_t *units) {
    LocalSystem *l = calloc(1, sizeof *l); require(l, "out of memory");
    l->id = fresh(); l->T = T; l->square = square; l->ctx = ctx; l->nunits = nunits;
    l->units = malloc((nunits ? nunits : 1) * sizeof *l->units); require(l->units, "out of memory");
    memcpy(l->units, units, nunits * sizeof *units);
    pthread_mutex_lock(&C.mu); l->all_next = C.lss; C.lss = l; pthread_mutex_unlock(&C.mu);
    return l;
}
void localsys_free(LocalSystem *ls) { (void)ls; }   /* owned by the registry until chain_free */
/* claim a memo slot: 0 found (*v), 1 claimed by the caller, 2 being computed elsewhere */
static int claim(WordMap *m, const uint64_t *k, size_t n, uint64_t *v) {
    pthread_mutex_lock(&C.mu);
    uint64_t x = 0; int r;
    if (wordmap_get(m, k, n, &x)) r = x == COMPUTING ? 2 : 0;
    else { wordmap_put(m, k, n, COMPUTING); r = 1; }
    pthread_mutex_unlock(&C.mu);
    if (r == 0) { *v = x; __atomic_add_fetch(&C.st_hits, 1, __ATOMIC_RELAXED); }
    return r;
}
static void publish(WordMap *m, const uint64_t *k, size_t n, uint64_t v) { pthread_mutex_lock(&C.mu); wordmap_put(m, k, n, v); pthread_mutex_unlock(&C.mu); }
/* F(x), requested once per shared generator: 0 value, 1 pending */
static int fmap_get(ChainMapT *F, CellId x, ChainId *out) {
    uint64_t key[2] = { F->id, x }, v = 0;
    int r = claim(&C.fmap, key, 2, &v);
    if (r == 0) { *out = v; return 0; }
    if (r == 2) return 1;
    ChainId y = F->act(F->ctx, x);
    require(chain_is_zero(y) || chain_degree(y) == cell_degree(x) + (size_t)(ptrdiff_t)F->shift, "a chain map's generator image has the shifted degree");
    publish(&C.fmap, key, 2, y); *out = y; return 0;
}

/* ================= operations ================= */
enum { OK_BOUNDARY = 1, OK_PAIR, OK_MAP, OK_COVAL, OK_LAW };
struct ChOp {
    int kind, phase; uint64_t result; size_t units;
    ChOp *child;
    ChainId in; size_t t, k, L; bool have; CellId cur; ModId curm; LocalSystem *ls; Acc acc;
    Cochain *co; ModId sum;
    ChainMapT *F; ChainId img;
    CellId x; bool claimed; size_t fi, m;
    size_t i, j; int e1, e2; bool ok; uint64_t done_pairs;
};
static ChOp *op_new(int kind) { ChOp *o = calloc(1, sizeof *o); require(o, "out of memory"); o->kind = kind; __atomic_add_fetch(&C.st_ops, 1, __ATOMIC_RELAXED); return o; }
ChOp *op_boundary(ChainId c, LocalSystem *ls) {
    ChOp *o = op_new(OK_BOUNDARY); o->in = c; o->ls = ls;
    size_t d = chain_degree(c); acc_init(&o->acc, d ? d - 1 : 0);
    return o;
}
ChOp *op_pair(Cochain *a, ChainId c) {
    require(chain_is_zero(c) || chain_degree(c) == a->degree, "pairing a cochain with a chain of its degree");
    ChOp *o = op_new(OK_PAIR); o->co = a; o->in = c; o->sum = mod_zero(); return o;
}
ChOp *op_map_chain(ChainMapT *F, ChainId c) {
    ChOp *o = op_new(OK_MAP); o->F = F; o->in = c;
    acc_init(&o->acc, (size_t)((ptrdiff_t)chain_degree(c) + F->shift)); return o;
}
static ChOp *op_coval(Cochain *a, CellId x) {
    require(cell_degree(x) == a->degree, "a cochain is evaluated on generators of its degree");
    ChOp *o = op_new(OK_COVAL); o->co = a; o->x = x; o->sum = mod_zero(); return o;
}
ChOp *op_law_d2(CellId x) {
    require(cell_cubical(x), "the face-cancellation law acts on cubical cells");
    ChOp *o = op_new(OK_LAW); o->x = x; o->m = cell_degree(x); o->i = 1; o->j = 2; o->ok = true; return o;
}
void chop_free(ChOp *o) {
    if (!o) return;
    chop_free(o->child);
    if (o->kind == OK_BOUNDARY || o->kind == OK_MAP) acc_release(&o->acc);
    free(o);
}
uint64_t chop_result(const ChOp *o) { return o->result; }
size_t chop_units(const ChOp *o) { return o->units; }
/* one step of the child; on completion its result is returned and the child released */
static int child_step(ChOp *o, uint64_t *res) {
    int r = chop_step(o->child);
    if (r != CH_DONE) return r;
    *res = o->child->result; chop_free(o->child); o->child = NULL; return CH_DONE;
}
static int step_boundary(ChOp *o) {
    if (o->phase == 0) {
        if (o->t < chain_nterms(o->in)) {
            if (!o->have) {
                chain_term(o->in, o->t, &o->cur, &o->curm);
                require(!o->ls || cell_cubical(o->cur), "local coefficients transport along cubical edges");
                o->L = bstream_len(o->cur); o->k = 0; o->have = true;
            }
            if (o->k < o->L) {
                CellId f; Zx s; size_t ci; int e; bterm(o->cur, o->k, &f, &s, &ci, &e);
                ModId c = o->curm;
                if (o->ls && e) c = o->ls->T(o->ls->ctx, cell_base_edge(o->cur, ci), c, false);   /* the upper face's base vertex is shifted: T_i(m) */
                acc_add(&o->acc, f, mod_scale(s, c));
                o->k++; return CH_RUNNING;
            }
            o->t++; o->have = false; return CH_RUNNING;
        }
        o->phase = 1; return CH_RUNNING;
    }
    ChainId out; if (acc_finish_step(&o->acc, &out)) { o->result = out; return CH_DONE; }
    return CH_RUNNING;
}
static int step_pair(ChOp *o) {
    if (o->t >= chain_nterms(o->in)) { o->result = o->sum; return CH_DONE; }
    if (!o->child) { chain_term(o->in, o->t, &o->cur, &o->curm); o->child = op_coval(o->co, o->cur); }
    uint64_t v; int r = child_step(o, &v);
    if (r != CH_DONE) return r;
    o->sum = mod_add(o->sum, mod_scale(scalar_of(o->curm), v)); o->t++;
    return CH_RUNNING;
}
static int step_map(ChOp *o) {
    if (o->phase == 0) {
        if (o->t < chain_nterms(o->in)) {
            if (!o->have) { chain_term(o->in, o->t, &o->cur, &o->curm); if (fmap_get(o->F, o->cur, &o->img)) return CH_PENDING; o->k = 0; o->have = true; return CH_RUNNING; }
            if (o->k < chain_nterms(o->img)) { CellId y; ModId c; chain_term(o->img, o->k, &y, &c); acc_add(&o->acc, y, mod_scale(scalar_of(c), o->curm)); o->k++; return CH_RUNNING; }
            o->t++; o->have = false; return CH_RUNNING;
        }
        o->phase = 1; return CH_RUNNING;
    }
    ChainId out; if (acc_finish_step(&o->acc, &out)) { o->result = out; return CH_DONE; }
    return CH_RUNNING;
}
static int coval_publish(ChOp *o, ModId v) {
    uint64_t key[2] = { o->co->id, o->x };
    publish(&C.coval, key, 2, v); o->claimed = false; o->result = v; return CH_DONE;
}
static int step_coval(ChOp *o) {
    Cochain *a = o->co;
    if (o->phase == 0) {
        uint64_t key[2] = { a->id, o->x }, v;
        int r = claim(&C.coval, key, 2, &v);
        if (r == 0) { o->result = v; return CH_DONE; }
        if (r == 2) return CH_PENDING;                 /* being computed by another request: this one joins it */
        o->claimed = true; o->phase = 1; return CH_RUNNING;
    }
    uint64_t v;
    switch (a->kind) {
    case CO_GEN: {
        ModId out; if (a->act(a->ctx, o->x, &out)) return CH_PENDING;   /* the generator's value is still being computed */
        return coval_publish(o, out);
    }
    case CO_COB:
        if (!a->ls) {
            if (o->phase == 1) { o->child = op_boundary(chain_gen(o->x, mod_int(zx_i64(1))), NULL); o->phase = 2; return CH_RUNNING; }
            if (o->phase == 2) { int r = child_step(o, &v); if (r != CH_DONE) return r; o->child = op_pair(a->inner, v); o->phase = 3; return CH_RUNNING; }
            { int r = child_step(o, &v); if (r != CH_DONE) return r; return coval_publish(o, v); }
        }
        /* the twisted differential: Σ (−1)^(i−1) (T_i^{-1}(a(d_i^1 x)) − a(d_i^0 x)) */
        if (o->fi >= 2 * cell_degree(o->x)) return coval_publish(o, o->sum);
        {
            size_t i = o->fi / 2 + 1; int e = (int)(o->fi & 1);
            if (!o->child) o->child = op_coval(a->inner, cell_face(o->x, i, e));
            int r = child_step(o, &v); if (r != CH_DONE) return r;
            ModId t = e ? a->ls->T(a->ls->ctx, cell_base_edge(o->x, i), v, true) : v;
            int sg = ((i - 1) & 1) ? -1 : 1; if (!e) sg = -sg;
            o->sum = mod_add(o->sum, mod_scale(zx_i64(sg), t)); o->fi++;
            return CH_RUNNING;
        }
    case CO_PULL:
        if (o->phase == 1) { o->child = op_map_chain(a->F, chain_gen(o->x, mod_int(zx_i64(1)))); o->phase = 2; return CH_RUNNING; }
        if (o->phase == 2) { int r = child_step(o, &v); if (r != CH_DONE) return r; o->child = op_pair(a->inner, v); o->phase = 3; return CH_RUNNING; }
        { int r = child_step(o, &v); if (r != CH_DONE) return r; return coval_publish(o, v); }
    }
    die("unknown cochain kind");
}
static int step_law(ChOp *o) {
    if (o->m < 2 || o->i >= o->m) {
        uint64_t key[1] = { o->m }, n = 0;
        pthread_mutex_lock(&C.mu); wordmap_get(&C.law, key, 1, &n); wordmap_put(&C.law, key, 1, n + 1); pthread_mutex_unlock(&C.mu);
        o->result = o->ok; return CH_DONE;
    }
    /* the pair (d_i^ε d_j^η x, d_(j−1)^η d_i^ε x), i < j: equal faces, opposite signs */
    CellId L = cell_face(cell_face(o->x, o->j, o->e2), o->i, o->e1);
    CellId R = cell_face(cell_face(o->x, o->i, o->e1), o->j - 1, o->e2);
    int sL = (((o->j - 1) + (o->i - 1)) & 1) ? -1 : 1, sR = (((o->i - 1) + (o->j - 2)) & 1) ? -1 : 1;
    if (!o->e1) { sL = -sL; sR = -sR; } if (!o->e2) { sL = -sL; sR = -sR; }
    if (L != R || sL != -sR) o->ok = false;
    o->done_pairs++; __atomic_add_fetch(&C.st_law_pairs, 1, __ATOMIC_RELAXED);
    if (o->e2 == 0) o->e2 = 1; else { o->e2 = 0; if (o->e1 == 0) o->e1 = 1; else { o->e1 = 0; if (o->j < o->m) o->j++; else { o->i++; o->j = o->i + 1; } } }
    return CH_RUNNING;
}
int chop_step(ChOp *o) {
    o->units++; unit();
    switch (o->kind) {
    case OK_BOUNDARY: return step_boundary(o);
    case OK_PAIR: return step_pair(o);
    case OK_MAP: return step_map(o);
    case OK_COVAL: return step_coval(o);
    case OK_LAW: return step_law(o);
    }
    die("unknown chain operation");
}
LawD2 law_d2_record(size_t n) {
    LawD2 r; r.degree = n; r.pairs = n < 2 ? 0 : (uint64_t)2 * n * (n - 1);
    uint64_t key[1] = { n }, v = 0; pthread_mutex_lock(&C.mu); wordmap_get(&C.law, key, 1, &v); pthread_mutex_unlock(&C.mu);
    r.instances = v; return r;
}
/* direct drive (used inside admissions, which may run inside jobs) */
static uint64_t op_eval(ChOp *o) { int r; while ((r = chop_step(o)) != CH_DONE) if (r == CH_PENDING) sched_yield(); uint64_t v = o->result; chop_free(o); return v; }
typedef struct { ChOp *o; int done; uint64_t res; } RunBox;
static void run_job(void *p) {
    RunBox *b = p; int r = chop_step(b->o);
    if (r == CH_DONE) { b->res = b->o->result; __atomic_store_n(&b->done, 1, __ATOMIC_RELEASE); return; }
    if (r == CH_PENDING) sched_yield();
    eval_job(run_job, b, CH_TAG);
}
uint64_t ch_run(ChOp *o) {
    RunBox b = { o, 0, 0 };
    eval_job(run_job, &b, CH_TAG);
    while (!__atomic_load_n(&b.done, __ATOMIC_ACQUIRE)) { eval_run(); if (!__atomic_load_n(&b.done, __ATOMIC_ACQUIRE)) sched_yield(); }
    chop_free(o);
    return b.res;
}
ChainId chain_boundary(ChainId c, LocalSystem *ls) { return ch_run(op_boundary(c, ls)); }
ModId chain_pair(Cochain *a, ChainId c) { return ch_run(op_pair(a, c)); }
ChainId chain_map(ChainMapT *F, ChainId c) { return ch_run(op_map_chain(F, c)); }
ModId read_defect(Cochain *a, ChainId h, bool *agree) {
    ModId lhs = ch_run(op_pair(a, ch_run(op_boundary(h, NULL))));
    Cochain *da = cochain_cob(a, NULL);
    ModId rhs = ch_run(op_pair(da, h));
    if (agree) *agree = lhs == rhs;
    return lhs;
}

/* ================= admissions ================= */
CellId cell_presented(uint64_t ns, uint64_t tag, size_t m, const CellId *faces, const char **why) {
    for (size_t k = 0; k < 2 * m; k++) if (!faces[k] || cell_degree(faces[k]) != m - 1) { if (why) *why = "a presented cell's faces have one degree less"; return 0; }
    for (size_t i = 1; i <= m; i++) for (size_t j = i + 1; j <= m; j++) for (int e = 0; e < 2; e++) for (int h = 0; h < 2; h++) {
        CellId fj = faces[2 * (j - 1) + h], fi = faces[2 * (i - 1) + e];
        if (!cell_cubical(fj) || !cell_cubical(fi)) { if (why) *why = "a presented cell's faces are cubical"; return 0; }
        unit();
        if (cell_face(fj, i, e) != cell_face(fi, j - 1, h)) { if (why) *why = "the declared faces violate a cubical face identity"; return 0; }
    }
    uint64_t *w = malloc((4 + 2 * m) * sizeof *w); require(w, "out of memory");
    w[0] = CK_PRESENTED; w[1] = ns; w[2] = tag; w[3] = m; if (m) memcpy(w + 4, faces, 2 * m * sizeof *faces);
    CellId x = interner_intern(&C.cells, w, 4 + 2 * m, NULL); free(w); return x;
}
bool chain_is_cycle(ChainId z) { if (chain_degree(z) == 0) return true; return chain_is_zero(op_eval(op_boundary(z, NULL))); }
CellId cell_declared(uint64_t ns, uint64_t tag, size_t m, ChainId boundary, const char **why) {
    if (m == 0) { if (!chain_is_zero(boundary)) { if (why) *why = "a degree-0 generator has no boundary"; return 0; } }
    else {
        if (!chain_is_zero(boundary) && chain_degree(boundary) != m - 1) { if (why) *why = "a declared boundary has one degree less"; return 0; }
        if (!chain_is_zero(boundary) && !chain_is_cycle(boundary)) { if (why) *why = "a declared boundary must itself have no boundary"; return 0; }
    }
    uint64_t w[5] = { CK_DECLARED, ns, tag, m, chain_is_zero(boundary) ? chain_zero(m ? m - 1 : 0) : boundary };
    return interner_intern(&C.cells, w, 5, NULL);
}
bool chainmap_admit(ChainMapT *F, CellId x, const char **why) {
    uint64_t key[3] = { 1, F->id, x }, v = 0;
    if (memo_get(&C.admit, key, 3, &v)) { if (v != 2 && why) *why = "F∂ ≠ ∂F on this generator"; return v == 2; }
    ChainId gx = chain_gen(x, mod_int(zx_i64(1)));
    ChainId lhs = op_eval(op_map_chain(F, op_eval(op_boundary(gx, NULL))));
    ChainId rhs = op_eval(op_boundary(op_eval(op_map_chain(F, gx)), NULL));
    bool ok = (chain_is_zero(lhs) && chain_is_zero(rhs)) || lhs == rhs;
    wordmap_put(&C.admit, key, 3, ok ? 2 : 1);
    if (!ok && why) *why = "F∂ ≠ ∂F on this generator";
    return ok;
}
bool localsys_admit(LocalSystem *ls, CellId x, const char **why) {
    uint64_t key[2] = { ls->id, x }, v = 0;
    if (memo_get(&C.lsadmit, key, 2, &v)) { if (v != 2 && why) *why = "no flat interpretation on this cell"; return v == 2; }
    bool ok = cell_cubical(x); if (!ok && why) *why = "local coefficients need a cubical cell";
    size_t m = ok ? cell_degree(x) : 0;
    for (size_t i = 1; i <= m && ok; i++) {
        CellId e = cell_base_edge(x, i);
        for (size_t u = 0; u < ls->nunits && ok; u++) {
            ModId b = mod_unit(ls->units[u], zx_i64(1));
            if (ls->T(ls->ctx, e, ls->T(ls->ctx, e, b, false), true) != b) { ok = false; if (why) *why = "a transport and its inverse do not compose to the identity"; }
        }
    }
    for (size_t i = 1; i <= m && ok; i++) for (size_t j = i + 1; j <= m && ok; j++) {
        CellId s = cell_base_square(x, i, j);
        if (!ls->square) { ok = false; if (why) *why = "the square-coherence witness is absent"; break; }
        if (!ls->square(ls->ctx, s)) { ok = false; if (why) *why = "the square-coherence witness is not supplied for a base square"; break; }
        CellId bottom = cell_face(s, 2, 0), right = cell_face(s, 1, 1), left = cell_face(s, 1, 0), top = cell_face(s, 2, 1);
        for (size_t u = 0; u < ls->nunits && ok; u++) {
            ModId b = mod_unit(ls->units[u], zx_i64(1)); unit();
            if (ls->T(ls->ctx, right, ls->T(ls->ctx, bottom, b, false), false) != ls->T(ls->ctx, top, ls->T(ls->ctx, left, b, false), false)) { ok = false; if (why) *why = "the supplied square witness is invalid: the two transports to the corner differ"; }
        }
    }
    wordmap_put(&C.lsadmit, key, 2, ok ? 2 : 1);
    return ok;
}

/* ================= cycles, boundaries, relative chains, gluing, images ================= */
bool boundary_witness(ChainId z, ChainId h, BoundaryWitness *out, const char **why) {
    ChainId bh = op_eval(op_boundary(h, NULL));
    if (!(bh == z || (chain_is_zero(bh) && chain_is_zero(z)))) { if (why) *why = "the supplied chain does not bound z"; return false; }
    if (out) { out->z = z; out->h = h; }
    return true;
}
RelativeView relative_view(ChainId c, ChIn in_A, void *ctx) {
    RelativeView v; v.chain = c;
    Acc a; acc_init(&a, chain_degree(c));
    for (size_t k = 0; k < chain_nterms(c); k++) { CellId x; ModId m; chain_term(c, k, &x, &m); if (!in_A(ctx, x)) acc_add(&a, x, m); }
    v.relative = acc_finish(&a);
    v.absolute_boundary = op_eval(op_boundary(c, NULL));
    Acc b; acc_init(&b, chain_degree(v.absolute_boundary));
    for (size_t k = 0; k < chain_nterms(v.absolute_boundary); k++) { CellId x; ModId m; chain_term(v.absolute_boundary, k, &x, &m); if (!in_A(ctx, x)) acc_add(&b, x, m); }
    v.relative_boundary = acc_finish(&b);
    return v;
}
ChainId chain_glue(ChainId h1, ChainId h2, ChainId j, const char **why) {
    for (size_t k = 0; k < chain_nterms(j); k++) {
        CellId x; ModId m; chain_term(j, k, &x, &m);
        if (chain_coef(h1, x) != m || chain_coef(h2, x) != m) { if (why) *why = "the interface is not an actual common part of both histories"; return 0; }
    }
    return chain_sub(chain_add(h1, h2), j);
}
ChainId chain_pushforward(ChainId c, ChCellMap f, void *ctx) {
    Acc a; acc_init(&a, chain_degree(c));
    for (size_t k = 0; k < chain_nterms(c); k++) { CellId x; ModId m; chain_term(c, k, &x, &m); acc_add(&a, f(ctx, x), m); }
    return acc_finish(&a);
}
size_t chain_support_image(ChainId c, ChCellMap f, void *ctx, CellId **out) {
    size_t n = chain_nterms(c), no = 0; CellId *v = malloc((n ? n : 1) * sizeof *v); require(v, "out of memory");
    for (size_t k = 0; k < n; k++) {
        CellId x; ModId m; chain_term(c, k, &x, &m); CellId y = f(ctx, x);
        size_t pos = 0; while (pos < no && v[pos] < y) pos++;
        if (pos < no && v[pos] == y) continue;      /* Boolean image: membership only */
        memmove(v + pos + 1, v + pos, (no - pos) * sizeof *v); v[pos] = y; no++; fine_bump(FC_COPY_WORDS);
    }
    *out = v; return no;
}
bool publish_realization(CellId typed, ChainMapT *F, ChainId opb, ChOccurred occurred, void *ctx, Realization *out, const char **why) {
    if (!chainmap_admit(F, typed, why)) return false;
    ChainId img = op_eval(op_map_chain(F, chain_gen(typed, mod_int(zx_i64(1)))));
    for (size_t k = 0; k < chain_nterms(img); k++) { CellId y; ModId m; chain_term(img, k, &y, &m); if (!occurred(ctx, y)) { if (why) *why = "publication cannot invent an executed event"; return false; } }
    ChainId b = op_eval(op_boundary(img, NULL));
    if (!(b == opb || (chain_is_zero(b) && chain_is_zero(opb)))) { if (why) *why = "the operational boundary differs from the mapped boundary (no filler is invented)"; return false; }
    if (out) { out->typed = typed; out->image = img; out->operational_boundary = opb; out->nlinks = chain_nterms(img); }
    return true;
}
