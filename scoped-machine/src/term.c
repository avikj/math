#include <sched.h>
#include "term.h"
#include "template.h"   /* the TVIEW families (tview_open, tview_reindex, tview_*_binder) */
#include "nat.h"
#include "fine.h"

const char *tag_name(Tag t) {
    switch (t) {
    case T_UNIVERSE: return "U"; case T_PI: return "Π"; case T_SIGMA: return "Σ";
    case T_LAM: return "λ"; case T_APP: return "app"; case T_PAIR: return "pair";
    case T_FST: return "fst"; case T_SND: return "snd"; case T_PATH: return "PathP";
    case T_PLAM: return "plam"; case T_PAPP: return "papp"; case T_GLUE_TYPE: return "Glue";
    case T_GLUE_INTRO: return "glue"; case T_UNGLUE: return "unglue"; case T_COMP: return "comp";
    case T_SYSTEM: return "system"; case T_GLOBAL: return "global"; case T_TCALL: return "tcall";
    }
    return "?";
}

#define OSIDE(id) ((OriginSide *)chunked_at(&M.origin_side, (id) - 1))
#define RSIDE(id) ((RefSide *)chunked_at(&M.ref_side, (id) - 1))
#define TDECL(x) ((TermDecl *)chunked_at(&M.term_decl, (x) - 1))
#define DPROV(i) ((uint64_t *)chunked_at(&M.dim_prov, (i) - 1))
#define NVAL(id) ((uint64_t *)chunked_at(&M.nominal_val, (id) - 1))
#define DEF(s) ((Def *)chunked_at(&M.defs, (s) - 1))
#define term_lock() pthread_mutex_lock(&M.term_mu)      /* a macro: the lock-section audit attributes each section to its caller */
#define term_unlock() pthread_mutex_unlock(&M.term_mu)

/* ================= declarations ================= */

TermVarId declare_term(RefId type, FaceId required) {
    term_lock();
    TermVarId x = (TermVarId)(M.n_term_vars + 1);
    TermDecl *d = TDECL(x);
    d->type = type; d->required = required; d->prov = 0;
    __atomic_store_n(&M.n_term_vars, M.n_term_vars + 1, __ATOMIC_RELEASE);
    term_unlock();
    return x;
}
DimVarId declare_dim(void) {
    term_lock();
    DimVarId i = (DimVarId)(M.n_dim_vars + 1);
    *DPROV(i) = 0;
    __atomic_store_n(&M.n_dim_vars, M.n_dim_vars + 1, __ATOMIC_RELEASE);
    term_unlock();
    return i;
}
static size_t n_terms_now(void) { return __atomic_load_n(&M.n_term_vars, __ATOMIC_ACQUIRE); }
RefId term_var_type(TermVarId x) { require(x >= 1 && x <= n_terms_now(), "undeclared term variable"); return TDECL(x)->type; }
FaceId term_var_required(TermVarId x) { require(x >= 1 && x <= n_terms_now(), "undeclared term variable"); return TDECL(x)->required; }

/* ================= raw maps ================= */
/* record: [nt, (x,ref)*, nd, (i,intv)*], keys sorted, no identity entries */

void mapb_init(MapBuilder *b) { words_init(&b->t); words_init(&b->d); }
void mapb_term(MapBuilder *b, TermVarId x, RefId image) { words_push(&b->t, x); words_push(&b->t, image); }
void mapb_dim(MapBuilder *b, DimVarId i, IntervalId image) { words_push(&b->d, i); words_push(&b->d, image); }


/* Pair-key sorting must expose the same bounded sifts as word sorting.
 * A comparison examines one key word; a sift has at most the word-width
 * number of levels. Duplicate-key/image checking remains in mapb_finish. */
static void pair_sift(uint64_t *p, size_t n, size_t i) {
    for (;;) {
        size_t l = 2 * i + 1, r = l + 1, m = i;
        if (l < n && (p[2 * l] > p[2 * m] || (p[2 * l] == p[2 * m] && p[2 * l + 1] > p[2 * m + 1]))) m = l;   /* lexicographic on (key, image) */
        if (r < n && (p[2 * r] > p[2 * m] || (p[2 * r] == p[2 * m] && p[2 * r + 1] > p[2 * m + 1]))) m = r;
        if (m == i) return;
        uint64_t key = p[2 * i], image = p[2 * i + 1];
        p[2 * i] = p[2 * m]; p[2 * i + 1] = p[2 * m + 1];
        p[2 * m] = key; p[2 * m + 1] = image; i = m;
    }
}
KF_DECL_EXT(pair_sort, void, pair_sort_PARAMS, size_t i, e;)
KF_STEP(pair_sort) {
    KF_BEGIN(pair_sort);
    if (F->n < 2) KF_RETV();
    for (F->i = F->n / 2; F->i > 0; F->i--) {
        pair_sift(F->p, F->n, F->i - 1); fine_bump(FC_SORT_STEPS); KF_SAFE();
    }
    for (F->e = F->n - 1; F->e > 0; F->e--) {
        uint64_t *p = F->p, key = p[0], image = p[1];
        p[0] = p[2 * F->e]; p[1] = p[2 * F->e + 1];
        p[2 * F->e] = key; p[2 * F->e + 1] = image;
        pair_sift(p, F->e, 0); fine_bump(FC_SORT_STEPS); KF_SAFE();
    }
    KF_RETV();
    KF_END;
}

KF_DECL_EXT_DROP(mapb_finish, MapId, mapb_finish_PARAMS, mapb_finish_drop, size_t nt, nd, kept, k, ndpos; Words w; uint64_t x, img, rv; MapId id;)
static void mapb_finish_drop(mapb_finish_F *F) { words_free(&F->w); words_free(&F->b->t); words_free(&F->b->d); }
KF_STEP(mapb_finish) {
    KF_BEGIN(mapb_finish);
    F->nt = F->b->t.n / 2; F->nd = F->b->d.n / 2;
    KF_CALL(pair_sort, NULL, F->b->t.w, F->nt);
    KF_CALL(pair_sort, NULL, F->b->d.w, F->nd);
    words_init(&F->w); KF_CALL(words_reserve, NULL, &F->w, 2 + 2 * (F->nt + F->nd));   /* at most every entry kept */
    words_push(&F->w, 0);
    F->kept = 0;
    for (F->k = 0; F->k < F->nt; F->k++) {
        F->x = F->b->t.w[2 * F->k]; F->img = F->b->t.w[2 * F->k + 1];
        if (F->k > 0 && F->b->t.w[2 * (F->k - 1)] == F->x) {
            require(F->b->t.w[2 * (F->k - 1) + 1] == F->img, "duplicate term key in map");
            continue;
        }
        KF_CALL(ref_var, &F->rv, F->x);
        if (F->img == F->rv) continue;   /* identity entry */
        words_push(&F->w, F->x); words_push(&F->w, F->img); F->kept++;
    }
    F->w.w[0] = F->kept;
    F->ndpos = F->w.n;
    words_push(&F->w, 0);
    F->kept = 0;
    for (F->k = 0; F->k < F->nd; F->k++) {
        F->x = F->b->d.w[2 * F->k]; F->img = F->b->d.w[2 * F->k + 1];
        if (F->k > 0 && F->b->d.w[2 * (F->k - 1)] == F->x) {
            require(F->b->d.w[2 * (F->k - 1) + 1] == F->img, "duplicate dimension key in map");
            continue;
        }
        KF_CALL(iv_var, &F->rv, F->x);
        if (F->img == F->rv) continue;
        words_push(&F->w, F->x); words_push(&F->w, F->img); F->kept++;
    }
    F->w.w[F->ndpos] = F->kept;
    KF_CALL(interner_intern, &F->id, &M.maps, F->w.w, F->w.n, NULL);
    words_free(&F->w);
    words_free(&F->b->t); words_free(&F->b->d);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(mapb_finish, MapId, mapb_finish_PARAMS, mapb_finish(MapBuilder *b))

KF_DECL_EXT_DROP(map_identity, MapId, KF_NOPARAMS, map_identity_drop, MapBuilder b; MapId r;)
static void map_identity_drop(map_identity_F *F) { words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(map_identity) { KF_BEGIN(map_identity); mapb_init(&F->b); KF_CALL(mapb_finish, &F->r, &F->b); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(map_identity, MapId, KF_NOPARAMS, map_identity(void))
bool map_is_identity(MapId m) { size_t n; const uint64_t *w = interner_get(&M.maps, m, &n); return w[0] == 0 && w[1] == 0; }
size_t map_n_terms(MapId m) { size_t n; const uint64_t *w = interner_get(&M.maps, m, &n); return (size_t)w[0]; }
size_t map_n_dims(MapId m) { size_t n; const uint64_t *w = interner_get(&M.maps, m, &n); return (size_t)w[1 + 2 * w[0]]; }
void map_term_entry(MapId m, size_t k, TermVarId *x, RefId *img) {
    size_t n; const uint64_t *w = interner_get(&M.maps, m, &n);
    require(k < w[0], "map entry out of range");
    *x = w[1 + 2 * k]; *img = w[2 + 2 * k];
}
void map_dim_entry(MapId m, size_t k, DimVarId *i, IntervalId *img) {
    size_t n; const uint64_t *w = interner_get(&M.maps, m, &n);
    const uint64_t *d = w + 1 + 2 * w[0];
    require(k < d[0], "map entry out of range");
    *i = d[1 + 2 * k]; *img = d[2 + 2 * k];
}

static const uint64_t *pairs_find(const uint64_t *p, size_t n, uint64_t key) {
    size_t lo = 0, hi = n;
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        if (p[2 * mid] == key) return p + 2 * mid;
        if (p[2 * mid] < key) lo = mid + 1; else hi = mid;
    }
    return NULL;
}

KF_DECL_EXT(map_term_image, RefId, map_term_image_PARAMS, RefId r;)
KF_STEP(map_term_image) {
    KF_BEGIN(map_term_image);
    {
        size_t n; const uint64_t *w = interner_get(&M.maps, F->m, &n);
        const uint64_t *e = pairs_find(w + 1, (size_t)w[0], F->x);
        if (e) KF_RET(e[1]);
    }
    KF_CALL(ref_var, &F->r, F->x);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(map_term_image, RefId, map_term_image_PARAMS, map_term_image(MapId m, TermVarId x))
KF_DECL_EXT(map_dim_image, IntervalId, map_dim_image_PARAMS, IntervalId r;)
KF_STEP(map_dim_image) {
    KF_BEGIN(map_dim_image);
    {
        size_t n; const uint64_t *w = interner_get(&M.maps, F->m, &n);
        const uint64_t *d = w + 1 + 2 * w[0];
        const uint64_t *e = pairs_find(d + 1, (size_t)d[0], F->i);
        if (e) KF_RET(e[1]);
    }
    KF_CALL(iv_var, &F->r, F->i);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(map_dim_image, IntervalId, map_dim_image_PARAMS, map_dim_image(MapId m, DimVarId i))
KF_DECL_EXT_DROP(map_single_term, MapId, map_single_term_PARAMS, map_single_term_drop, MapBuilder b; MapId r;)
static void map_single_term_drop(map_single_term_F *F) { words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(map_single_term) { KF_BEGIN(map_single_term); mapb_init(&F->b); mapb_term(&F->b, F->x, F->a); KF_CALL(mapb_finish, &F->r, &F->b); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(map_single_term, MapId, map_single_term_PARAMS, map_single_term(TermVarId x, RefId a))
KF_DECL_EXT_DROP(map_single_dim, MapId, map_single_dim_PARAMS, map_single_dim_drop, MapBuilder b; MapId r;)
static void map_single_dim_drop(map_single_dim_F *F) { words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(map_single_dim) { KF_BEGIN(map_single_dim); mapb_init(&F->b); mapb_dim(&F->b, F->i, F->r0); KF_CALL(mapb_finish, &F->r, &F->b); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(map_single_dim, MapId, map_single_dim_PARAMS, map_single_dim(DimVarId i, IntervalId r0))

/* the image of a dimension under a map (a DimImagePush) */
#define map_img_PARAMS(X) X(DimVarId, i) X(void *, ctx)
KF_DECL(map_img, IntervalId, map_img_PARAMS, IntervalId r;)
KF_STEP(map_img) {
    KF_BEGIN(map_img);
    {
        size_t n; const uint64_t *w = interner_get(&M.maps, *(MapId *)F->ctx, &n);
        const uint64_t *d = w + 1 + 2 * w[0];
        const uint64_t *e = pairs_find(d + 1, (size_t)d[0], F->i);
        if (e) KF_RET(e[1]);
    }
    KF_CALL(iv_var, &F->r, F->i);
    KF_RET(F->r);
    KF_END;
}
KF_DECL_EXT(iv_reindex, IntervalId, iv_reindex_PARAMS, IntervalId o;)
KF_STEP(iv_reindex) {
    KF_BEGIN(iv_reindex);
    if (map_is_identity(F->m)) KF_RET(F->r);
    KF_CALL(iv_substitute, &F->o, F->r, map_img_push, &F->m);
    KF_RET(F->o);
    KF_END;
}
KF_SYNC_DEF(iv_reindex, IntervalId, iv_reindex_PARAMS, iv_reindex(IntervalId r, MapId m))
KF_DECL_EXT(fc_reindex, FaceId, fc_reindex_PARAMS, FaceId o;)
KF_STEP(fc_reindex) {
    KF_BEGIN(fc_reindex);
    fine_bump(FC_FACE_OPS);
    if (map_is_identity(F->m)) KF_RET(F->phi);
    KF_CALL(fc_substitute, &F->o, F->phi, map_img_push, &F->m);
    KF_RET(F->o);
    KF_END;
}
KF_SYNC_DEF(fc_reindex, FaceId, fc_reindex_PARAMS, fc_reindex(FaceId phi, MapId m))

KF_DECL_EXT_DROP(compose, MapId, compose_PARAMS, compose_drop, uint64_t key[2]; MapId out; bool have; MapBuilder b; Words keys; size_t ns, nt, k; RefId im; IntervalId iv;)
static void compose_drop(compose_F *F) { words_free(&F->b.t); words_free(&F->b.d); words_free(&F->keys); }
KF_STEP(compose) {
    KF_BEGIN(compose);
    if (map_is_identity(F->sigma)) KF_RET(F->tau);
    if (map_is_identity(F->tau)) KF_RET(F->sigma);
    F->key[0] = F->sigma; F->key[1] = F->tau;
    KF_CALL(wordmap_get, &F->have, &M.compose_memo, F->key, 2, &F->out);
    if (F->have) KF_RET(F->out);
    mapb_init(&F->b);
    /* keys of both maps; tau acts on sigma's images, sigma is identity on
     * keys present only in tau */
    words_init(&F->keys);
    F->ns = map_n_terms(F->sigma); F->nt = map_n_terms(F->tau);
    { size_t a = map_n_dims(F->sigma) + map_n_dims(F->tau); KF_CALL(words_reserve, NULL, &F->keys, F->ns + F->nt > a ? F->ns + F->nt : a); }
    fine_bump(FC_REINDEX_CALLS);   /* §94: one fine step per entry visited (the suspension points of the computation) */
    for (F->k = 0; F->k < F->ns; F->k++) { TermVarId x; RefId im; map_term_entry(F->sigma, F->k, &x, &im); words_push(&F->keys, x); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
    for (F->k = 0; F->k < F->nt; F->k++) { TermVarId x; RefId im; map_term_entry(F->tau, F->k, &x, &im); words_push(&F->keys, x); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
    KF_CALL(sort_unique_u64, &F->keys.n, F->keys.w, F->keys.n);
    KF_CALL(words_reserve, NULL, &F->b.t, 2 * F->keys.n);
    for (F->k = 0; F->k < F->keys.n; F->k++) {
        KF_CALL(map_term_image, &F->im, F->sigma, F->keys.w[F->k]);
        KF_CALL(reindex, &F->im, F->im, F->tau);
        mapb_term(&F->b, F->keys.w[F->k], F->im); fine_bump(FC_MAP_ENTRIES);
    }
    F->keys.n = 0;
    F->ns = map_n_dims(F->sigma); F->nt = map_n_dims(F->tau);
    for (F->k = 0; F->k < F->ns; F->k++) { DimVarId i; IntervalId im; map_dim_entry(F->sigma, F->k, &i, &im); words_push(&F->keys, i); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
    for (F->k = 0; F->k < F->nt; F->k++) { DimVarId i; IntervalId im; map_dim_entry(F->tau, F->k, &i, &im); words_push(&F->keys, i); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
    KF_CALL(sort_unique_u64, &F->keys.n, F->keys.w, F->keys.n);
    KF_CALL(words_reserve, NULL, &F->b.d, 2 * F->keys.n);
    for (F->k = 0; F->k < F->keys.n; F->k++) {
        KF_CALL(map_dim_image, &F->iv, F->sigma, F->keys.w[F->k]);
        KF_CALL(iv_reindex, &F->iv, F->iv, F->tau);
        mapb_dim(&F->b, F->keys.w[F->k], F->iv); fine_bump(FC_MAP_ENTRIES);
    }
    words_free(&F->keys);
    KF_CALL(mapb_finish, &F->out, &F->b);
    KF_CALL(wordmap_put, NULL, &M.compose_memo, F->key, 2, F->out);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(compose, MapId, compose_PARAMS, compose(MapId sigma, MapId tau))

/* ================= origins ================= */
/* record: [tag, payload, nfields, (kind,slot,id)*, nbinders, (sort,formal,domain_field)*] */

static const uint64_t *origin_words(OriginId c, size_t *n) { return interner_get(&M.origins, c, n); }
Tag origin_tag(OriginId c) { size_t n; return (Tag)origin_words(c, &n)[0]; }
uint64_t origin_payload(OriginId c) { size_t n; return origin_words(c, &n)[1]; }
size_t origin_nfields(OriginId c) { size_t n; return (size_t)origin_words(c, &n)[2]; }
Field origin_field(OriginId c, FieldIndex k) {
    size_t n; const uint64_t *w = origin_words(c, &n);
    require(k < w[2], "field index out of range");
    Field f = { (FieldKind)w[3 + 3 * k], (BinderSlot)w[4 + 3 * k], w[5 + 3 * k] };
    return f;
}
size_t origin_nbinders(OriginId c) { size_t n; const uint64_t *w = origin_words(c, &n); return (size_t)w[3 + 3 * w[2]]; }
Binder origin_binder(OriginId c, BinderSlot s) {
    size_t n; const uint64_t *w = origin_words(c, &n);
    const uint64_t *b = w + 3 + 3 * w[2];
    require(s < b[0], "binder slot out of range");
    Binder r = { (Sort)b[1 + 3 * s], b[2 + 3 * s], (FieldIndex)b[3 + 3 * s] };
    return r;
}
VarSetId origin_ft(OriginId c) { return OSIDE(c)->ft; }
DimSetId origin_fd(OriginId c) { return OSIDE(c)->fd; }
FaceId origin_required(OriginId c) { return OSIDE(c)->required; }

typedef struct RequiredScope { FaceId face; struct RequiredScope *prev; } RequiredScope;
/* the dynamic construction state (the declared-required scope stack and the
 * formation levels of the origin being built) belongs to the computation:
 * it is registered as computation-local (kframe.h), so a suspended stack
 * carries it to the thread that resumes it */
typedef struct { RequiredScope *scope; uint64_t gen; uint64_t levels; } TermDyn;
static __thread TermDyn tl_term = { NULL, 0, LEVELS_NONE };
#define tl_req_scope (tl_term.scope)
#define tl_req_generation (tl_term.gen)
#define tl_levels (tl_term.levels)   /* formation levels of the origin being built (§59.1) */
static void *term_dyn_addr(void) { return &tl_term; }
static const TermDyn term_dyn_init = { NULL, 0, LEVELS_NONE };
static void term_dyn_release(void *p) {   /* a discarded computation's scope list (only while its machine lives) */
    TermDyn *d = p;
    if (d->gen != machine_generation()) return;
    while (d->scope) { RequiredScope *q = d->scope; d->scope = q->prev; free(q); }
}
__attribute__((constructor)) static void term_dyn_register(void) { kf_ctx_register(term_dyn_addr, sizeof(TermDyn), &term_dyn_init, term_dyn_release); }
static void required_scope_current(void) {
    uint64_t g = machine_generation();
    if (tl_req_generation != g) {
        while (tl_req_scope) { RequiredScope *p = tl_req_scope; tl_req_scope = p->prev; free(p); }
        tl_req_generation = g;
    }
}
KF_DECL_EXT(term_require_push, void, term_require_push_PARAMS, FaceId f;)
KF_STEP(term_require_push) {
    KF_BEGIN(term_require_push);
    required_scope_current();
    F->f = F->phi;
    if (tl_req_scope) KF_CALL(fc_meet, &F->f, tl_req_scope->face, F->phi);
    {
        required_scope_current();
        RequiredScope *p = malloc(sizeof *p); require(p, "out of memory");
        p->face = F->f; p->prev = tl_req_scope; tl_req_scope = p;
    }
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(term_require_push, term_require_push_PARAMS, term_require_push(FaceId phi))
void term_require_pop(void) {
    required_scope_current(); require(tl_req_scope, "required-face scope underflow");
    RequiredScope *p = tl_req_scope; tl_req_scope = p->prev; free(p);
}
static FaceId current_declared_required(void) { required_scope_current(); return tl_req_scope ? tl_req_scope->face : 0; }
FaceId origin_declared_required(OriginId c) {
    size_t n; const uint64_t *w = interner_get(&M.origins, c, &n);
    return w[n - 2];
}
uint64_t origin_levels(OriginId c) {
    size_t n; const uint64_t *w = interner_get(&M.origins, c, &n);
    return w[n - 1];
}
/* §51.2 / §59.1, BOUNDS-COMPLETION §2: a level is an exact natural (nat.h)
 * or the absent tag LEVEL_NONE; a pair of formation levels is an interned
 * tuple of two optional levels (LEVELS_NONE when both are absent), read
 * through the accessors — no packing, no width limit */
static void level_check(uint64_t l) { require(l == LEVEL_NONE || nat_valid(l), "not an exact level (use nat_from_word for an external word)"); }
KF_DECL_EXT(levels_pack, uint64_t, levels_pack_PARAMS, uint64_t w[3]; uint64_t id;)
KF_STEP(levels_pack) {
    KF_BEGIN(levels_pack);
    level_check(F->m); level_check(F->n);
    if (F->m == LEVEL_NONE && F->n == LEVEL_NONE) KF_RET(LEVELS_NONE);
    F->w[0] = 0x1E7E15; F->w[1] = F->m; F->w[2] = F->n;
    KF_CALL(interner_intern, &F->id, &M.keys, F->w, 3, NULL);
    KF_RET(F->id);   /* a handle (never LEVELS_NONE) */
    KF_END;
}
KF_SYNC_DEF(levels_pack, uint64_t, levels_pack_PARAMS, levels_pack(uint64_t m, uint64_t n))
uint64_t levels_first(uint64_t lv) { if (lv == LEVELS_NONE) return LEVEL_NONE; size_t n; const uint64_t *w = interner_get(&M.keys, lv, &n); require(n == 3 && w[0] == 0x1E7E15, "not a level pair"); return w[1]; }
uint64_t levels_second(uint64_t lv) { if (lv == LEVELS_NONE) return LEVEL_NONE; size_t n; const uint64_t *w = interner_get(&M.keys, lv, &n); require(n == 3 && w[0] == 0x1E7E15, "not a level pair"); return w[2]; }
KF_DECL_EXT(level_max, uint64_t, level_max_PARAMS, uint64_t r;)
KF_STEP(level_max) { KF_BEGIN(level_max); if (F->a == LEVEL_NONE || F->b == LEVEL_NONE) KF_RET(LEVEL_NONE); KF_CALL(nat_max, &F->r, F->a, F->b); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(level_max, uint64_t, level_max_PARAMS, level_max(uint64_t a, uint64_t b))
KF_DECL_EXT(level_succ, uint64_t, level_succ_PARAMS, uint64_t r;)
KF_STEP(level_succ) { KF_BEGIN(level_succ); if (F->a == LEVEL_NONE) KF_RET(LEVEL_NONE); KF_CALL(nat_successor, &F->r, F->a); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(level_succ, uint64_t, level_succ_PARAMS, level_succ(uint64_t a))

#define origin_intern_PARAMS(X) X(Tag, tag) X(uint64_t, payload) X(const Field *, fields) X(size_t, nf) X(const Binder *, binders) X(size_t, nb) X(VarSetId, ft) X(DimSetId, fd) X(FaceId, req)
KF_DECL_DROP(origin_intern, OriginId, origin_intern_PARAMS, origin_intern_drop, FaceId declared; Words dd, w; DimSetId t; bool created; OriginId id; size_t k;)
static void origin_side_pub(uint64_t id, void *ctx) {   /* inside the insertion section: the side before the id is reachable */
    origin_intern_F *F = ctx; OriginSide *o = OSIDE(id);
    o->ft = F->ft; o->fd = F->fd; o->required = F->req; __atomic_store_n(&o->ready, 1, __ATOMIC_RELEASE);
}
static void origin_intern_drop(origin_intern_F *F) { words_free(&F->dd); words_free(&F->w); }
KF_STEP(origin_intern) {
    KF_BEGIN(origin_intern);
    F->declared = current_declared_required();
    if (F->declared) {
        KF_CALL(fc_meet, &F->req, F->req, F->declared);
        words_init(&F->dd); fc_dims(F->declared, &F->dd);
        KF_CALL(dimset_make, &F->t, F->dd.w, F->dd.n);
        KF_CALL(dimset_union, &F->fd, F->fd, F->t);
        words_free(&F->dd);
    }
    words_init(&F->w); KF_CALL(words_reserve, NULL, &F->w, 6 + 3 * F->nf + 3 * F->nb);   /* the record's exact length */
    words_push(&F->w, F->tag); words_push(&F->w, F->payload); words_push(&F->w, F->nf);
    for (F->k = 0; F->k < F->nf; F->k++) { words_push(&F->w, F->fields[F->k].kind); words_push(&F->w, F->fields[F->k].slot); words_push(&F->w, F->fields[F->k].id); fine_bump(FC_COPY_WORDS); KF_SAFE(); }
    words_push(&F->w, F->nb);
    for (F->k = 0; F->k < F->nb; F->k++) { words_push(&F->w, F->binders[F->k].sort); words_push(&F->w, F->binders[F->k].formal); words_push(&F->w, F->binders[F->k].domain_field); fine_bump(FC_COPY_WORDS); KF_SAFE(); }
    words_push(&F->w, F->declared);                 /* annotation is part of the record */
    words_push(&F->w, tl_levels);                   /* formation levels (§59.1), part of the record */
    /* the interner is internally synchronized (hashing, comparison and the
     * copy outside its lock); the side is written inside the insertion
     * section, before the id is reachable (no term lock, no wait) */
    KF_CALL(interner_intern_pub, &F->id, &M.origins, F->w.w, F->w.n, &F->created, origin_side_pub, F);
    words_free(&F->w);
    KF_RET(F->id);
    KF_END;
}

/* dependency-closed free boundary: union of field boundaries (which are
 * already closed through declaration types), minus formals bound at the
 * field's binder. */
KF_DECL_EXT_DROP(origin_make, OriginId, origin_make_PARAMS, origin_make_drop, VarSetId ft, fv; DimSetId fd, fdk; FaceId req, rk; Words dims; size_t k; OriginId id;)
static void origin_make_drop(origin_make_F *F) { words_free(&F->dims); }
KF_STEP(origin_make) {
    KF_BEGIN(origin_make);
    KF_CALL(varset_make, &F->ft, NULL, 0);
    KF_CALL(dimset_make, &F->fd, NULL, 0);
    KF_CALL0(fc_true, &F->req);
    words_init(&F->dims);
    for (F->k = 0; F->k < F->nf; F->k++) {
        KF_CALL(varset_make, &F->fv, NULL, 0);
        F->dims.n = 0;
        switch (F->fields[F->k].kind) {
        case F_REF: F->fv = ref_freevars(F->fields[F->k].id); F->fdk = ref_support(F->fields[F->k].id); break;
        case F_INTERVAL: iv_dims(F->fields[F->k].id, &F->dims); KF_CALL(dimset_make, &F->fdk, F->dims.w, F->dims.n); break;
        case F_FACE: fc_dims(F->fields[F->k].id, &F->dims); KF_CALL(dimset_make, &F->fdk, F->dims.w, F->dims.n); break;
        default: die("bad field kind");
        }
        if (F->fields[F->k].slot != NO_SLOT) {
            require(F->fields[F->k].slot < F->nb, "field refers to a missing binder");
            if (F->binders[F->fields[F->k].slot].sort == S_TERM) KF_CALL(varset_remove, &F->fv, F->fv, F->binders[F->fields[F->k].slot].formal);
            else KF_CALL(dimset_remove, &F->fdk, F->fdk, F->binders[F->fields[F->k].slot].formal);
        }
        KF_CALL(varset_union, &F->ft, F->ft, F->fv);
        KF_CALL(dimset_union, &F->fd, F->fd, F->fdk);
    }
    words_free(&F->dims);
    for (size_t k = 0; k < F->nb; k++)
        if (F->binders[k].sort == S_TERM) require(F->binders[k].domain_field < F->nf, "term binder without domain field");
    if (F->tag == T_SYSTEM) {
        KF_CALL0(fc_false, &F->req);
        for (F->k = 0; F->k < F->nf; F->k += 2) KF_CALL(fc_join, &F->req, F->req, F->fields[F->k].id);
    } else {
        /* a total construction requires what its total reference fields
         * require; partial positions (tube, Glue fibre data, glue fibre term)
         * are only used under their guards and do not propagate. A field under
         * a dimension binder must be available along the whole line. */
        for (F->k = 0; F->k < F->nf; F->k++) {
            if (F->fields[F->k].kind != F_REF) continue;
            {
                size_t k = F->k; Tag tag = F->tag;
                bool partial = (tag == T_COMP && k == 2) || (tag == T_GLUE_TYPE && (k == 2 || k == 3)) ||
                               (tag == T_GLUE_INTRO && (k == 2 || k == 3 || k == 4)) || (tag == T_UNGLUE && (k == 2 || k == 3));
                if (partial) continue;
            }
            F->rk = ref_required(F->fields[F->k].id);
            if (F->fields[F->k].slot != NO_SLOT && F->binders[F->fields[F->k].slot].sort == S_DIM) KF_CALL(fc_forall, &F->rk, F->binders[F->fields[F->k].slot].formal, F->rk);
            KF_CALL(fc_meet, &F->req, F->req, F->rk);
        }
    }
    KF_CALL(origin_intern, &F->id, F->tag, F->payload, F->fields, F->nf, F->binders, F->nb, F->ft, F->fd, F->req);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(origin_make, OriginId, origin_make_PARAMS, origin_make(Tag tag, uint64_t payload, const Field *fields, size_t nf, const Binder *binders, size_t nb))

/* Bound atoms retain both coordinates; the tag marks a table identity. */
KF_DECL_EXT(bound_id, uint64_t, bound_id_PARAMS, uint64_t w[2]; uint64_t id;)
KF_STEP(bound_id) {
    KF_BEGIN(bound_id);
    F->w[0] = F->depth; F->w[1] = F->slot;
    KF_CALL(interner_intern, &F->id, &M.bound_atoms, F->w, 2, NULL);
    require(F->id < BOUND_BIT, "bound atom address space exhausted");
    KF_RET(BOUND_BIT | F->id);
    KF_END;
}
KF_SYNC_DEF(bound_id, uint64_t, bound_id_PARAMS, bound_id(size_t depth, size_t slot))
size_t bound_depth(uint64_t id) { size_t n; require(is_bound_id(id), "not a bound atom"); return (size_t)interner_get(&M.bound_atoms, id & ~BOUND_BIT, &n)[0]; }
size_t bound_slot(uint64_t id) { size_t n; require(is_bound_id(id), "not a bound atom"); return (size_t)interner_get(&M.bound_atoms, id & ~BOUND_BIT, &n)[1]; }

/* ================= references ================= */
/* record: [1, x] for VAR ; [2, origin, map] for VIEW */

static void ref_side_set(RefId id, DimSetId support, VarSetId fv, FaceId req) {
    RefSide *r = RSIDE(id); r->support = support; r->freevars = fv; r->required = req;
}
/* a reference's side data, written inside the interner's insertion section (before the id is reachable) */
typedef struct { DimSetId sup; VarSetId fv; FaceId req; } RefSidePub;
static void ref_side_pub(uint64_t id, void *ctx) { RefSidePub *p = ctx; ref_side_set(id, p->sup, p->fv, p->req); }

KF_DECL_EXT_DROP(ref_var, RefId, ref_var_PARAMS, ref_var_drop, uint64_t w[2]; uint64_t xs[1]; RefId id, type; FaceId req; VarSetId fv, t; DimSetId sup, ts; Words d; RefSidePub pub;)
static void ref_var_drop(ref_var_F *F) { words_free(&F->d); }
KF_STEP(ref_var) {
    KF_BEGIN(ref_var);
    F->w[0] = 1; F->w[1] = F->x;
    if (is_bound_id(F->x)) {
        /* a bound local occurrence (§50): no declaration record; its type and
         * guard live in the enclosing scope's telescope (one locked section) */
        KF_CALL(interner_find, &F->id, &M.refs, F->w, 2);
        if (F->id) KF_RET(F->id);
        F->xs[0] = F->x;
        KF_CALL(dimset_make, &F->pub.sup, NULL, 0); KF_CALL(varset_make, &F->pub.fv, F->xs, 1); F->pub.req = fc_true();
        KF_CALL(interner_intern_pub, &F->id, &M.refs, F->w, 2, NULL, ref_side_pub, &F->pub);
        KF_RET(F->id);
    }
    require(F->x >= 1 && F->x <= n_terms_now(), "VAR of undeclared variable %llu", (unsigned long long)F->x);
    KF_CALL(interner_find, &F->id, &M.refs, F->w, 2);
    if (F->id) KF_RET(F->id);
    /* the side data is computed outside the term lock (it is the closed
     * boundary of the declaration type: input-sized); the record is created
     * and its side published under the lock, after a second find */
    F->type = TDECL(F->x)->type;
    KF_CALL(fc_meet, &F->req, TDECL(F->x)->required, ref_required(F->type));
    /* typed boundary: x itself plus the closed boundary of its declaration
     * type and the dimensions of its required face */
    F->xs[0] = F->x;
    KF_CALL(varset_make, &F->t, F->xs, 1);
    KF_CALL(varset_union, &F->fv, F->t, ref_freevars(F->type));
    words_init(&F->d); fc_dims(F->req, &F->d);
    KF_CALL(dimset_make, &F->ts, F->d.w, F->d.n);
    KF_CALL(dimset_union, &F->sup, ref_support(F->type), F->ts);
    words_free(&F->d);
    F->pub.sup = F->sup; F->pub.fv = F->fv; F->pub.req = F->req;   /* another creator of the same variable computes the same side */
    KF_CALL(interner_intern_pub, &F->id, &M.refs, F->w, 2, NULL, ref_side_pub, &F->pub);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(ref_var, RefId, ref_var_PARAMS, ref_var(TermVarId x))

bool ref_is_var(RefId t) { size_t n; return interner_get(&M.refs, t, &n)[0] == 1; }
bool ref_is_tview(RefId t) { size_t n; return interner_get(&M.refs, t, &n)[0] == 3; }
uint64_t ref_tnode(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] == 3, "not a TVIEW"); return w[1]; }
uint64_t ref_tenv(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] == 3, "not a TVIEW"); return w[2]; }
/* intern a TVIEW record with its computed side data (template layer) */
KF_DECL_EXT(ref_intern_tview, RefId, ref_intern_tview_PARAMS, uint64_t w[3]; RefSidePub pub; RefId id;)
KF_STEP(ref_intern_tview) {
    KF_BEGIN(ref_intern_tview);
    F->w[0] = 3; F->w[1] = F->node; F->w[2] = F->env;
    F->pub.sup = F->support; F->pub.fv = F->fv; F->pub.req = F->required;
    KF_CALL(interner_intern_pub, &F->id, &M.refs, F->w, 3, NULL, ref_side_pub, &F->pub);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(ref_intern_tview, RefId, ref_intern_tview_PARAMS, ref_intern_tview(uint64_t node, uint64_t env, DimSetId support, VarSetId fv, FaceId required))
TermVarId ref_var_id(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] == 1, "not a VAR"); return w[1]; }
Tag ref_tag(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] != 1, "ref_tag of a variable"); return w[0] == 3 ? tnode_tag(w[1]) : origin_tag(w[1]); }
OriginId ref_origin(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] == 2, "not a VIEW"); return w[1]; }
MapId ref_map(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] == 2, "not a VIEW"); return w[2]; }
DimSetId ref_support(RefId t) { return RSIDE(t)->support; }
VarSetId ref_freevars(RefId t) { return RSIDE(t)->freevars; }
FaceId ref_required(RefId t) { return RSIDE(t)->required; }

/* restrict keys to the complete typed free boundary of c, drop identity
 * entries (mapb_finish), intern */
KF_DECL_EXT_DROP(make_view, RefId, make_view_PARAMS, make_view_drop, VarSetId ft, fv; DimSetId fd, sup, t; MapBuilder b; size_t nt, nd, n, k; MapId m; uint64_t w[3]; RefId have, im, id; FaceId req, guard; bool ent; const uint64_t *xs; IntervalId iv; Words d; RefSidePub pub;)
static void make_view_drop(make_view_F *F) { words_free(&F->b.t); words_free(&F->b.d); words_free(&F->d); }
KF_STEP(make_view) {
    KF_BEGIN(make_view);
    F->ft = origin_ft(F->c);
    F->fd = origin_fd(F->c);
    mapb_init(&F->b);
    F->nt = map_n_terms(F->sigma); F->nd = map_n_dims(F->sigma);
    KF_MAPB_RESERVE(&F->b, F->nt, F->nd);
    fine_bump(FC_REINDEX_CALLS);
    for (F->k = 0; F->k < F->nt; F->k++) {
        TermVarId x; RefId im; map_term_entry(F->sigma, F->k, &x, &im); fine_bump(FC_MAP_ENTRIES);
        if (varset_contains(F->ft, x)) mapb_term(&F->b, x, im);
        KF_SAFE();
    }
    for (F->k = 0; F->k < F->nd; F->k++) {
        DimVarId i; IntervalId im; map_dim_entry(F->sigma, F->k, &i, &im); fine_bump(FC_MAP_ENTRIES);
        if (dimset_contains(F->fd, i)) mapb_dim(&F->b, i, im);
        KF_SAFE();
    }
    KF_CALL(mapb_finish, &F->m, &F->b);
    F->w[0] = 2; F->w[1] = F->c; F->w[2] = F->m;
    /* an existing view (its side was written before it was reachable) */
    KF_CALL(interner_find, &F->have, &M.refs, F->w, 3);
    if (F->have) KF_RET(F->have);
    /* instantiated support and free variables (§7), computed outside the
     * lock on immutable data (the loop's transitions are suspension points;
     * the lock is held only to intern and publish the side data, which
     * another creator of the same view would compute identically) */
    KF_CALL(varset_make, &F->fv, NULL, 0);
    KF_CALL(dimset_make, &F->sup, NULL, 0);
    KF_CALL(fc_reindex, &F->req, origin_required(F->c), F->m);
    F->xs = varset_get(F->ft, &F->n);
    for (F->k = 0; F->k < F->n; F->k++) {
        fine_bump(FC_MAP_ENTRIES);
        KF_CALL(map_term_image, &F->im, F->m, F->xs[F->k]);
        KF_CALL(varset_union, &F->fv, F->fv, ref_freevars(F->im));
        KF_CALL(dimset_union, &F->sup, F->sup, ref_support(F->im));
        /* a formal declared partial on phi_x is only used under phi_x
         * inside the origin, so its image need only be available there:
         * an image available on all of phi_x[m] adds no requirement */
        KF_CALL(fc_reindex, &F->guard, TDECL(F->xs[F->k])->required, F->m);
        KF_CALL(fc_entails, &F->ent, F->guard, ref_required(F->im));
        if (!F->ent) KF_CALL(fc_meet, &F->req, F->req, ref_required(F->im));
    }
    F->xs = dimset_get(F->fd, &F->n);
    words_init(&F->d);
    for (F->k = 0; F->k < F->n; F->k++) { KF_CALL(map_dim_image, &F->iv, F->m, F->xs[F->k]); iv_dims(F->iv, &F->d); }
    KF_CALL(dimset_make, &F->t, F->d.w, F->d.n);
    KF_CALL(dimset_union, &F->sup, F->sup, F->t);
    words_free(&F->d);
    F->pub.sup = F->sup; F->pub.fv = F->fv; F->pub.req = F->req;
    KF_CALL(interner_intern_pub, &F->id, &M.refs, F->w, 3, NULL, ref_side_pub, &F->pub);   /* the side, inside the insertion section */
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(make_view, RefId, make_view_PARAMS, make_view(OriginId c, MapId sigma))

void (*term_edge_hook)(RefId dest, RefId src, MapId sigma);
/* §78.4: edge lists are interned word lists [src0, map0, src1, map1, ...];
 * duplicates are interned away by the list identity */
#define record_edge_PARAMS(X) X(RefId, dest) X(RefId, src) X(MapId, sigma)
KF_DECL_DROP(record_edge, void, record_edge_PARAMS, record_edge_drop, uint64_t key[1]; uint64_t old, now, id, kid; uint64_t *slot; Words w; const uint64_t *l; size_t n, k;)
static void record_edge_drop(record_edge_F *F) { words_free(&F->w); }
KF_STEP(record_edge) {
    KF_BEGIN(record_edge);
    F->key[0] = F->dest;
    /* the destination's list slot: the key interned once, the value word then
     * replaced by compare-and-swap (no lock is held while a list is read or built) */
    KF_CALL(interner_intern, &F->kid, &M.edges.keys, F->key, 1, NULL);
    KF_CALL(chunked_prepare, NULL, &M.edges.vals, F->kid - 1);
    F->slot = (uint64_t *)chunked_at(&M.edges.vals, F->kid - 1);
    for (;;) {   /* §94: read, build and intern the new list (one transition per entry), publish it if the list is still the one read; else retry */
        F->old = __atomic_load_n(F->slot, __ATOMIC_ACQUIRE);
        words_init(&F->w);
        if (F->old) {
            F->l = interner_get(&M.edge_lists, F->old, &F->n);
            KF_CALL(words_reserve, NULL, &F->w, F->n + 2);
            for (F->k = 0; F->k + 1 < F->n; F->k += 2) { fine_bump(FC_MAP_ENTRIES); if (F->l[F->k] == F->src && F->l[F->k + 1] == F->sigma) { words_free(&F->w); KF_RETV(); } KF_SAFE(); }
            for (F->k = 0; F->k < F->n; F->k++) { words_push(&F->w, F->l[F->k]); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
        }
        words_push(&F->w, F->src); words_push(&F->w, F->sigma);
        KF_CALL(interner_intern, &F->id, &M.edge_lists, F->w.w, F->w.n, NULL);
        words_free(&F->w);
        {
            uint64_t expect = F->old; bool same = __atomic_compare_exchange_n(F->slot, &expect, F->id, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
            if (same) { void (*h)(RefId, RefId, MapId) = __atomic_load_n(&term_edge_hook, __ATOMIC_ACQUIRE); if (h) h(F->dest, F->src, F->sigma); KF_RETV(); }
        }
    }
    KF_END;
}

KF_DECL_EXT_DROP(reindex, RefId, reindex_PARAMS, reindex_drop, uint64_t key[2]; RefId out, im; bool have; OriginId c; MapId tau, m; MapBuilder b; const uint64_t *xs; size_t n, k; IntervalId iv;)
static void reindex_drop(reindex_F *F) { words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(reindex) {
    KF_BEGIN(reindex);
    if (map_is_identity(F->sigma)) KF_RET(F->t);
    if (ref_is_var(F->t)) { KF_CALL(map_term_image, &F->out, F->sigma, ref_var_id(F->t)); KF_RET(F->out); }
    F->key[0] = F->t; F->key[1] = F->sigma;
    KF_CALL(wordmap_get, &F->have, &M.reindex_memo, F->key, 2, &F->out);
    if (F->have) KF_RET(F->out);
    if (ref_is_tview(F->t)) {
        KF_CALL(tview_reindex, &F->out, F->t, F->sigma);
        KF_CALL(wordmap_put, NULL, &M.reindex_memo, F->key, 2, F->out);
        if (F->out != F->t) KF_CALL(record_edge, NULL, F->out, F->t, F->sigma);
        KF_RET(F->out);
    }
    F->c = ref_origin(F->t);
    F->tau = ref_map(F->t);
    mapb_init(&F->b);
    KF_MAPB_RESERVE(&F->b, varset_n(origin_ft(F->c)), dimset_n(origin_fd(F->c)));
    F->xs = varset_get(origin_ft(F->c), &F->n);
    fine_bump(FC_REINDEX_CALLS);
    for (F->k = 0; F->k < F->n; F->k++) {
        fine_bump(FC_MAP_ENTRIES);
        KF_CALL(map_term_image, &F->im, F->tau, F->xs[F->k]);
        KF_CALL(reindex, &F->im, F->im, F->sigma);
        mapb_term(&F->b, F->xs[F->k], F->im);
    }
    F->xs = dimset_get(origin_fd(F->c), &F->n);
    for (F->k = 0; F->k < F->n; F->k++) {
        fine_bump(FC_MAP_ENTRIES);
        KF_CALL(map_dim_image, &F->iv, F->tau, F->xs[F->k]);
        KF_CALL(iv_reindex, &F->iv, F->iv, F->sigma);
        mapb_dim(&F->b, F->xs[F->k], F->iv);
    }
    KF_CALL(mapb_finish, &F->m, &F->b);
    KF_CALL(make_view, &F->out, F->c, F->m);
    KF_CALL(wordmap_put, NULL, &M.reindex_memo, F->key, 2, F->out);
    if (F->out != F->t) KF_CALL(record_edge, NULL, F->out, F->t, F->sigma);
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(reindex, RefId, reindex_PARAMS, reindex(RefId t, MapId sigma))
/* the published list of a destination (a list is immutable; the slot is replaced whole) */
KF_DECL_EXT(instantiation_edges, size_t, instantiation_edges_PARAMS, uint64_t key[1]; uint64_t id; bool have;)
KF_STEP(instantiation_edges) {
    KF_BEGIN(instantiation_edges);
    F->key[0] = F->dest; F->id = 0;
    KF_CALL(wordmap_get, &F->have, &M.edges, F->key, 1, &F->id);
    if (!F->have) { *F->pairs = NULL; KF_RET(0); }
    { size_t n; *F->pairs = interner_get(&M.edge_lists, F->id, &n); KF_RET(n / 2); }
    KF_END;
}
KF_SYNC_DEF(instantiation_edges, size_t, instantiation_edges_PARAMS, instantiation_edges(RefId dest, const uint64_t **pairs))

KF_DECL_EXT(reindex1, RefId, reindex1_PARAMS, MapId m; RefId r;)
KF_STEP(reindex1) { KF_BEGIN(reindex1); KF_CALL(map_single_term, &F->m, F->x, F->a); KF_CALL(reindex, &F->r, F->t, F->m); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(reindex1, RefId, reindex1_PARAMS, reindex1(RefId t, TermVarId x, RefId a))
KF_DECL_EXT(reindex_dim, RefId, reindex_dim_PARAMS, MapId m; RefId o;)
KF_STEP(reindex_dim) { KF_BEGIN(reindex_dim); KF_CALL(map_single_dim, &F->m, F->i, F->r); KF_CALL(reindex, &F->o, F->t, F->m); KF_RET(F->o); KF_END; }
KF_SYNC_DEF(reindex_dim, RefId, reindex_dim_PARAMS, reindex_dim(RefId t, DimVarId i, IntervalId r))

/* ================= binders ================= */

/* a nominal variable: its key interned outside every lock; the variable is
 * declared inside the insertion section (interner_intern_pub), so a lookup
 * that finds the key finds its variable. Keys have a constant length. */
KF_DECL_EXT_DROP(nominal_var, uint64_t, nominal_var_PARAMS, nominal_var_drop, Words w; uint64_t id; bool created;)
static void nominal_var_drop(nominal_var_F *F) { words_free(&F->w); }
static void nominal_pub(uint64_t id, void *ctx) {
    nominal_var_F *F = ctx;
    if (F->sort == S_TERM) { TermVarId x = declare_term(F->type, F->req); *NVAL(id) = x; TDECL(x)->prov = id; }
    else { DimVarId i = declare_dim(); *NVAL(id) = i; *DPROV(i) = id; }
}
KF_STEP(nominal_var) {
    KF_BEGIN(nominal_var);
    words_init(&F->w); KF_CALL(words_reserve, NULL, &F->w, 2 * (F->n + 1));
    if (F->prefix) { words_push(&F->w, KW_CONST); words_push(&F->w, F->prefix); }
    for (size_t k = 0; k < F->n; k++) { words_push(&F->w, F->key[k].kind); words_push(&F->w, F->key[k].v); }
    KF_CALL(interner_intern_pub, &F->id, &M.nominal, F->w.w, F->w.n, &F->created, nominal_pub, F);
    words_free(&F->w);
    if (!F->created && F->check)
        require(term_var_type((TermVarId)*NVAL(F->id)) == F->type && term_var_required((TermVarId)*NVAL(F->id)) == F->req,
                "keyed fresh variable reused at a different type or required face");
    KF_RET(*NVAL(F->id));
    KF_END;
}
KF_SYNC_DEF(nominal_var, uint64_t, nominal_var_PARAMS, nominal_var(const KeyWord *key, size_t n, uint64_t prefix, Sort sort, RefId type, FaceId req, bool check))
const uint64_t *nominal_key(uint64_t nid, size_t *npairs) {
    size_t n; const uint64_t *w = interner_get(&M.nominal, nid, &n);
    *npairs = n / 2;
    return w;
}
uint64_t term_var_provenance(TermVarId x) { return TDECL(x)->prov; }
uint64_t dim_var_provenance(DimVarId i) { return *DPROV(i); }

/* the variable of a binder occurrence (owner, slot) */
KF_DECL_EXT(binder_var, uint64_t, binder_var_PARAMS, KeyWord key[4]; uint64_t v; FaceId req;)
KF_STEP(binder_var) {
    KF_BEGIN(binder_var);
    F->key[0] = (KeyWord){ KW_CONST, 1 }; F->key[1] = (KeyWord){ KW_REF, F->owner }; F->key[2] = (KeyWord){ KW_CONST, F->slot }; F->key[3] = (KeyWord){ KW_CONST, F->sort };
    F->req = 0; if (F->sort == S_TERM) KF_CALL0(fc_true, &F->req);
    KF_CALL(nominal_var, &F->v, F->key, 4, 0, F->sort, F->type, F->req, false);
    KF_RET(F->v);
    KF_END;
}
TermVarId binder_term_var(RefId owner, BinderSlot slot, RefId type) { KeyWord key[4] = { { KW_CONST, 1 }, { KW_REF, owner }, { KW_CONST, slot }, { KW_CONST, S_TERM } }; return (TermVarId)nominal_var(key, 4, 0, S_TERM, type, fc_true(), false); }
DimVarId binder_dim_var(RefId owner, BinderSlot slot) { KeyWord key[4] = { { KW_CONST, 1 }, { KW_REF, owner }, { KW_CONST, slot }, { KW_CONST, S_DIM } }; return (DimVarId)nominal_var(key, 4, 0, S_DIM, 0, 0, false); }
TermVarId fresh_term_keyed_req(const KeyWord *key, size_t n, RefId type, FaceId required) { return (TermVarId)nominal_var(key, n, 2, S_TERM, type, required, true); }
KF_DECL_EXT(fresh_term_keyed, TermVarId, fresh_term_keyed_PARAMS, FaceId req; uint64_t v;)
KF_STEP(fresh_term_keyed) { KF_BEGIN(fresh_term_keyed); KF_CALL0(fc_true, &F->req); KF_CALL(nominal_var, &F->v, F->key, F->n, 2, S_TERM, F->type, F->req, true); KF_RET(F->v); KF_END; }
KF_SYNC_DEF(fresh_term_keyed, TermVarId, fresh_term_keyed_PARAMS, fresh_term_keyed(const KeyWord *key, size_t n, RefId type))
DimVarId fresh_dim_keyed(const KeyWord *key, size_t n) { return (DimVarId)nominal_var(key, n, 3, S_DIM, 0, 0, false); }

/* lifted = sigma with the formal's entry removed, then formal ↦ fresh */
#define lift_map_PARAMS(X) X(MapId, sigma) X(Sort, sort) X(uint64_t, formal) X(uint64_t, fresh_image)
KF_DECL_DROP(lift_map, MapId, lift_map_PARAMS, lift_map_drop, MapBuilder b; MapId r; size_t nt, nd, k;)
static void lift_map_drop(lift_map_F *F) { words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(lift_map) {
    KF_BEGIN(lift_map);
    mapb_init(&F->b);
    F->nt = map_n_terms(F->sigma); F->nd = map_n_dims(F->sigma);
    KF_MAPB_RESERVE(&F->b, F->nt + 1, F->nd + 1);
    for (F->k = 0; F->k < F->nt; F->k++) {
        TermVarId x; RefId im; map_term_entry(F->sigma, F->k, &x, &im);
        if (!(F->sort == S_TERM && x == F->formal)) mapb_term(&F->b, x, im);
        fine_bump(FC_MAP_ENTRIES); KF_SAFE();
    }
    for (F->k = 0; F->k < F->nd; F->k++) {
        DimVarId i; IntervalId im; map_dim_entry(F->sigma, F->k, &i, &im);
        if (!(F->sort == S_DIM && i == F->formal)) mapb_dim(&F->b, i, im);
        fine_bump(FC_MAP_ENTRIES); KF_SAFE();
    }
    if (F->sort == S_TERM) mapb_term(&F->b, F->formal, F->fresh_image); else mapb_dim(&F->b, F->formal, F->fresh_image);
    KF_CALL(mapb_finish, &F->r, &F->b);
    KF_RET(F->r);
    KF_END;
}

KF_DECL_EXT(lifted_map, MapId, lifted_map_PARAMS, OriginId c; MapId sigma, r; Binder b; RefId dt, rv; TermVarId x; DimVarId j; IntervalId iv;)
KF_STEP(lifted_map) {
    KF_BEGIN(lifted_map);
    require(!ref_is_var(F->owner) && !ref_is_tview(F->owner), "lifted map of a variable or template view");
    F->c = ref_origin(F->owner);
    F->sigma = ref_map(F->owner);
    F->b = origin_binder(F->c, F->slot);
    if (F->b.sort == S_TERM) {
        KF_CALL(reindex, &F->dt, origin_field(F->c, F->b.domain_field).id, F->sigma);
        KF_CALL(binder_var, &F->x, F->owner, F->slot, S_TERM, F->dt);
        if (F->fresh) *F->fresh = F->x;
        KF_CALL(ref_var, &F->rv, F->x);
        KF_CALL(lift_map, &F->r, F->sigma, S_TERM, F->b.formal, F->rv);
        KF_RET(F->r);
    }
    KF_CALL(binder_var, &F->j, F->owner, F->slot, S_DIM, 0);
    if (F->fresh) *F->fresh = F->j;
    KF_CALL(iv_var, &F->iv, F->j);
    KF_CALL(lift_map, &F->r, F->sigma, S_DIM, F->b.formal, F->iv);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(lifted_map, MapId, lifted_map_PARAMS, lifted_map(RefId owner, BinderSlot slot, uint64_t *fresh))

KF_DECL_EXT(resolve_term_binder, TermOpen, resolve_term_binder_PARAMS, OriginId c; MapId sigma, m; Binder b; Field dom, body; TermOpen o; RefId rv;)
KF_STEP(resolve_term_binder) {
    KF_BEGIN(resolve_term_binder);
    require(!ref_is_var(F->owner), "binder of a variable");
    if (ref_is_tview(F->owner)) { KF_CALL(tview_term_binder, &F->o, F->owner, F->slot, F->body_field); KF_RET(F->o); }
    F->c = ref_origin(F->owner);
    F->sigma = ref_map(F->owner);
    F->b = origin_binder(F->c, F->slot);
    require(F->b.sort == S_TERM, "sort mismatch: expected term binder");
    F->dom = origin_field(F->c, F->b.domain_field);
    F->body = origin_field(F->c, F->body_field);
    require(F->body.slot == F->slot && F->body.kind == F_REF, "field is not under this binder");
    KF_CALL(reindex, &F->o.type, F->dom.id, F->sigma);
    KF_CALL(binder_var, &F->o.x, F->owner, F->slot, S_TERM, F->o.type);
    KF_CALL(ref_var, &F->rv, F->o.x);
    KF_CALL(lift_map, &F->m, F->sigma, S_TERM, F->b.formal, F->rv);
    KF_CALL(reindex, &F->o.body, F->body.id, F->m);
    KF_RET(F->o);
    KF_END;
}
KF_SYNC_DEF(resolve_term_binder, TermOpen, resolve_term_binder_PARAMS, resolve_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field))

KF_DECL_EXT(resolve_dim_binder, DimOpen, resolve_dim_binder_PARAMS, OriginId c; MapId sigma, m; Binder b; Field body; DimOpen o; IntervalId iv;)
KF_STEP(resolve_dim_binder) {
    KF_BEGIN(resolve_dim_binder);
    require(!ref_is_var(F->owner), "binder of a variable");
    if (ref_is_tview(F->owner)) { KF_CALL(tview_dim_binder, &F->o, F->owner, F->slot, F->body_field); KF_RET(F->o); }
    F->c = ref_origin(F->owner);
    F->sigma = ref_map(F->owner);
    F->b = origin_binder(F->c, F->slot);
    require(F->b.sort == S_DIM, "sort mismatch: expected dimension binder");
    F->body = origin_field(F->c, F->body_field);
    require(F->body.slot == F->slot && F->body.kind == F_REF, "field is not under this binder");
    KF_CALL(binder_var, &F->o.j, F->owner, F->slot, S_DIM, 0);
    KF_CALL(iv_var, &F->iv, F->o.j);
    KF_CALL(lift_map, &F->m, F->sigma, S_DIM, F->b.formal, F->iv);
    KF_CALL(reindex, &F->o.body, F->body.id, F->m);
    KF_RET(F->o);
    KF_END;
}
KF_SYNC_DEF(resolve_dim_binder, DimOpen, resolve_dim_binder_PARAMS, resolve_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field))

KF_DECL_EXT(apply_term_binder, RefId, apply_term_binder_PARAMS, TermOpen o; RefId r;)
KF_STEP(apply_term_binder) {
    KF_BEGIN(apply_term_binder);
    KF_CALL(resolve_term_binder, &F->o, F->owner, F->slot, F->body_field);
    KF_CALL(reindex1, &F->r, F->o.body, F->o.x, F->a);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(apply_term_binder, RefId, apply_term_binder_PARAMS, apply_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field, RefId a))
KF_DECL_EXT(apply_dim_binder, RefId, apply_dim_binder_PARAMS, DimOpen o; RefId r;)
KF_STEP(apply_dim_binder) {
    KF_BEGIN(apply_dim_binder);
    KF_CALL(resolve_dim_binder, &F->o, F->owner, F->slot, F->body_field);
    KF_CALL(reindex_dim, &F->r, F->o.body, F->o.j, F->iv);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(apply_dim_binder, RefId, apply_dim_binder_PARAMS, apply_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field, IntervalId iv))

/* ================= opening ================= */

KF_DECL_EXT(open_ref, void, open_ref_PARAMS, OriginId c; MapId sigma; size_t k; Field fl;)
KF_STEP(open_ref) {
    KF_BEGIN(open_ref);
    {
        Head *h = F->h;
        memset(h, 0, sizeof *h);
        h->owner = F->t;
        if (ref_is_var(F->t)) { h->is_var = true; h->var = ref_var_id(F->t); KF_RETV(); }
        if (ref_is_tview(F->t)) { KF_CALL(tview_open, NULL, F->t, F->h); KF_RETV(); }
        F->c = ref_origin(F->t);
        F->sigma = ref_map(F->t);
        h->origin = F->c; h->map = F->sigma;
        h->tag = origin_tag(F->c);
        h->payload = origin_payload(F->c);
        h->levels = origin_levels(F->c);
        h->n = origin_nfields(F->c);
        fine_bump(FC_HEAD_CELLS);
    }
    KF_CALL(k_zalloc, (void **)&F->h->f, F->h->n ? F->h->n : 1, sizeof(HField));   /* the field cells, cleared one word per transition */
    for (F->k = 0; F->k < F->h->n; F->k++) {
        fine_bump(FC_FIELDS_OPENED);
        KF_SAFE();
        F->fl = origin_field(F->c, (FieldIndex)F->k);
        F->h->f[F->k].kind = F->fl.kind;
        F->h->f[F->k].index = (FieldIndex)F->k;
        if (F->fl.slot != NO_SLOT) {
            F->h->f[F->k].is_binder = true;
            F->h->f[F->k].slot = F->fl.slot;
            F->h->f[F->k].sort = origin_binder(F->c, F->fl.slot).sort;
            F->h->f[F->k].id = F->fl.id;
        } else {
            F->h->f[F->k].slot = NO_SLOT;
            switch (F->fl.kind) {
            case F_REF: KF_CALL(reindex, &F->h->f[F->k].id, F->fl.id, F->sigma); break;
            case F_INTERVAL: KF_CALL(iv_reindex, &F->h->f[F->k].id, F->fl.id, F->sigma); break;
            case F_FACE: KF_CALL(fc_reindex, &F->h->f[F->k].id, F->fl.id, F->sigma); break;
            }
        }
    }
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(open_ref, open_ref_PARAMS, open_ref(RefId t, Head *h))

void head_free(Head *h) { free(h->f); h->f = NULL; h->n = 0; }

/* ================= occurrence contexts ================= */
/* record: [n, (sort, id, type)*, assumption] */

#define context_intern_PARAMS(X) X(Words *, w)
KF_DECL(context_intern, ContextId, context_intern_PARAMS, ContextId id;)
KF_STEP(context_intern) { KF_BEGIN(context_intern); KF_CALL(interner_intern, &F->id, &M.contexts, F->w->w, F->w->n, NULL); words_free(F->w); KF_RET(F->id); KF_END; }

KF_DECL_EXT_DROP(context_make, ContextId, context_make_PARAMS, context_make_drop, Words w; ContextId id;)
static void context_make_drop(context_make_F *F) { words_free(&F->w); }
KF_STEP(context_make) {
    KF_BEGIN(context_make);
    words_init(&F->w); KF_CALL(words_reserve, NULL, &F->w, 2 + 3 * F->n);
    {
        size_t n = F->n; const CtxDecl *decls = F->decls;
        /* well-formed: no duplicate declaration; a term declaration's type
         * depends only on earlier declarations */
        for (size_t k = 0; k < n; k++) {
            for (size_t j = 0; j < k; j++) require(!(decls[j].sort == decls[k].sort && decls[j].id == decls[k].id), "duplicate declaration in context");
            if (decls[k].sort != S_TERM) continue;
            size_t m; const uint64_t *xs = varset_get(ref_freevars(decls[k].type), &m);
            for (size_t q = 0; q < m; q++) { bool found = false; for (size_t j = 0; j < k; j++) if (decls[j].sort == S_TERM && decls[j].id == xs[q]) found = true; require(found, "context declaration type mentions a variable not declared earlier"); }
            const uint64_t *ds = dimset_get(ref_support(decls[k].type), &m);
            for (size_t q = 0; q < m; q++) { bool found = false; for (size_t j = 0; j < k; j++) if (decls[j].sort == S_DIM && decls[j].id == ds[q]) found = true; require(found, "context declaration type mentions a dimension not declared earlier"); }
        }
        words_push(&F->w, n);
        for (size_t k = 0; k < n; k++) { words_push(&F->w, decls[k].sort); words_push(&F->w, decls[k].id); words_push(&F->w, decls[k].sort == S_TERM ? decls[k].type : 0); }
        words_push(&F->w, F->assumption);
    }
    KF_CALL(context_intern, &F->id, &F->w);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(context_make, ContextId, context_make_PARAMS, context_make(size_t n, const CtxDecl *decls, FaceId assumption))
static const uint64_t *ctx_words(ContextId c, size_t *n) { return interner_get(&M.contexts, c, n); }
size_t context_size(ContextId c) { size_t n; return (size_t)ctx_words(c, &n)[0]; }
FaceId context_assumption(ContextId c) { size_t n; const uint64_t *w = ctx_words(c, &n); return w[1 + 3 * w[0]]; }
CtxDecl context_decl(ContextId c, size_t k) {
    size_t n; const uint64_t *w = ctx_words(c, &n);
    require(k < w[0], "context declaration out of range");
    CtxDecl d = { (Sort)w[1 + 3 * k], w[2 + 3 * k], w[3 + 3 * k] };
    return d;
}
#define context_with_PARAMS(X) X(ContextId, c) X(const CtxDecl *, extra) X(FaceId, assumption)
KF_DECL_DROP(context_with, ContextId, context_with_PARAMS, context_with_drop, CtxDecl *ds; size_t n; ContextId out;)
static void context_with_drop(context_with_F *F) { free(F->ds); F->ds = NULL; }
KF_STEP(context_with) {
    KF_BEGIN(context_with);
    F->n = context_size(F->c);
    F->ds = malloc((F->n + 1) * sizeof(CtxDecl));
    require(F->ds, "out of memory");
    for (size_t k = 0; k < F->n; k++) F->ds[k] = context_decl(F->c, k);
    if (F->extra) F->ds[F->n] = *F->extra;
    KF_CALL(context_make, &F->out, F->extra ? F->n + 1 : F->n, F->ds, F->assumption);
    free(F->ds); F->ds = NULL;
    KF_RET(F->out);
    KF_END;
}
KF_DECL_EXT(context_extend_term, ContextId, context_extend_term_PARAMS, CtxDecl d; ContextId r;)
KF_STEP(context_extend_term) { KF_BEGIN(context_extend_term); F->d.sort = S_TERM; F->d.id = F->x; F->d.type = F->type; KF_CALL(context_with, &F->r, F->c, &F->d, context_assumption(F->c)); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(context_extend_term, ContextId, context_extend_term_PARAMS, context_extend_term(ContextId c, TermVarId x, RefId type))
KF_DECL_EXT(context_extend_dim, ContextId, context_extend_dim_PARAMS, CtxDecl d; ContextId r;)
KF_STEP(context_extend_dim) { KF_BEGIN(context_extend_dim); F->d.sort = S_DIM; F->d.id = F->i; F->d.type = 0; KF_CALL(context_with, &F->r, F->c, &F->d, context_assumption(F->c)); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(context_extend_dim, ContextId, context_extend_dim_PARAMS, context_extend_dim(ContextId c, DimVarId i))
KF_DECL_EXT(context_restrict, ContextId, context_restrict_PARAMS, FaceId a; ContextId r;)
KF_STEP(context_restrict) { KF_BEGIN(context_restrict); KF_CALL(fc_meet, &F->a, context_assumption(F->c), F->phi); KF_CALL(context_with, &F->r, F->c, NULL, F->a); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(context_restrict, ContextId, context_restrict_PARAMS, context_restrict(ContextId c, FaceId phi))
bool context_declares_term(ContextId c, TermVarId x, RefId *type_out) {
    size_t n = context_size(c);
    for (size_t k = 0; k < n; k++) { CtxDecl d = context_decl(c, k); if (d.sort == S_TERM && d.id == x) { if (type_out) *type_out = d.type; return true; } }
    return false;
}
bool context_declares_dim(ContextId c, DimVarId i) {
    size_t n = context_size(c);
    for (size_t k = 0; k < n; k++) { CtxDecl d = context_decl(c, k); if (d.sort == S_DIM && d.id == i) return true; }
    return false;
}

OccStatus occurrence_validate(RefId t, ContextId ctx, uint64_t *culprit) {
    size_t n;
    const uint64_t *xs = varset_get(ref_freevars(t), &n);
    for (size_t k = 0; k < n; k++) {
        RefId ty;
        if (!context_declares_term(ctx, xs[k], &ty)) { if (culprit) *culprit = xs[k]; return OCC_UNDECLARED_TERM; }
        if (ty != term_var_type(xs[k])) { if (culprit) *culprit = xs[k]; return OCC_TYPE_MISMATCH; }
    }
    const uint64_t *ds = dimset_get(ref_support(t), &n);
    for (size_t k = 0; k < n; k++) if (!context_declares_dim(ctx, ds[k])) { if (culprit) *culprit = ds[k]; return OCC_UNDECLARED_DIM; }
    if (!fc_entails(context_assumption(ctx), ref_required(t))) return OCC_FACE_NOT_ENTAILED;
    return OCC_VALID;
}

/* ================= globals ================= */

/* the definition environment's version: every declaration or body
 * registration begins a new environment (§57 R1, §59.4) */
static uint64_t env_version_ctr;
uint64_t global_env_version(void) { return __atomic_load_n(&env_version_ctr, __ATOMIC_ACQUIRE); }
static void env_bump(void) { __atomic_add_fetch(&env_version_ctr, 1, __ATOMIC_ACQ_REL); }
/* §57 R1 / §59.4: the admitted environment is frozen; registration into a
 * frozen environment fails closed (a new candidate environment is opened by
 * the checker, which retires its caches) */
static bool env_frozen_flag;
/* a new machine starts with an open environment; the version counter is
 * never reused, so stale keys of a destroyed machine cannot alias */
void env_control_init(void) { __atomic_store_n(&env_frozen_flag, false, __ATOMIC_RELEASE); env_bump(); }
void env_freeze(void) { __atomic_store_n(&env_frozen_flag, true, __ATOMIC_RELEASE); }
void env_unfreeze(void) { __atomic_store_n(&env_frozen_flag, false, __ATOMIC_RELEASE); env_bump(); }
bool env_is_frozen(void) { return __atomic_load_n(&env_frozen_flag, __ATOMIC_ACQUIRE); }

SymbolId define_global(const char *name, VarSetId params, DimSetId dims, RefId type) {
    term_lock();
    if (env_is_frozen()) { term_unlock(); return 0; }
    SymbolId s = (SymbolId)(M.n_defs + 1);
    Def *d = DEF(s);
    d->body = 0; d->params = params; d->dims = dims; d->name = name; d->type = type; d->revision = 1;
    M.n_defs++;
    env_bump();
    term_unlock();
    return s;
}

bool set_global_body(SymbolId s, RefId body) {
    require(s >= 1 && s <= M.n_defs, "unknown symbol");
    Def *d = DEF(s);
    require(d->body == 0, "definition environment is immutable: %s already defined", d->name);
    if (env_is_frozen()) return false;
    size_t n; const uint64_t *xs = varset_get(ref_freevars(body), &n);
    for (size_t k = 0; k < n; k++) require(varset_contains(d->params, xs[k]), "global body has an undeclared free variable");
    const uint64_t *ds = dimset_get(ref_support(body), &n);
    for (size_t k = 0; k < n; k++) require(dimset_contains(d->dims, ds[k]), "global body has an undeclared free dimension");
    __atomic_store_n(&d->body, body, __ATOMIC_RELEASE);
    __atomic_add_fetch(&d->revision, 1, __ATOMIC_ACQ_REL);
    env_bump();
    return true;
}
uint64_t global_revision(SymbolId s) { require(s >= 1 && s <= M.n_defs, "unknown symbol"); return __atomic_load_n(&DEF(s)->revision, __ATOMIC_ACQUIRE); }

RefId global_type(SymbolId s) { return DEF(s)->type; }
RefId global_body(SymbolId s) { return __atomic_load_n(&DEF(s)->body, __ATOMIC_ACQUIRE); }
VarSetId global_params(SymbolId s) { return DEF(s)->params; }
DimSetId global_dims(SymbolId s) { return DEF(s)->dims; }
const char *global_name(SymbolId s) { return DEF(s)->name; }
size_t global_count(void) { return M.n_defs; }

KF_DECL_EXT(global_ref, RefId, global_ref_PARAMS, OriginId c; FaceId t; MapId m; RefId r;)
KF_STEP(global_ref) {
    KF_BEGIN(global_ref);
    require(F->s >= 1 && F->s <= M.n_defs, "unknown symbol");
    KF_CALL0(fc_true, &F->t);
    KF_CALL(origin_intern, &F->c, T_GLOBAL, F->s, NULL, 0, NULL, 0, DEF(F->s)->params, DEF(F->s)->dims, F->t);
    KF_CALL0(map_identity, &F->m);
    KF_CALL(make_view, &F->r, F->c, F->m);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(global_ref, RefId, global_ref_PARAMS, global_ref(SymbolId s))

KF_DECL_EXT(unfold_global, RefId, unfold_global_PARAMS, RefId r;)
KF_STEP(unfold_global) {
    KF_BEGIN(unfold_global);
    {
        require(!ref_is_var(F->t) && !ref_is_tview(F->t), "unfold of a variable");
        OriginId c = ref_origin(F->t);
        require(origin_tag(c) == T_GLOBAL, "unfold of a non-global");
        SymbolId s = origin_payload(c);
        RefId body = __atomic_load_n(&DEF(s)->body, __ATOMIC_ACQUIRE);
        require(body != 0, "global %s has no body", DEF(s)->name);
        KF_CALL(reindex, &F->r, body, ref_map(F->t));
    }
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(unfold_global, RefId, unfold_global_PARAMS, unfold_global(RefId t))

/* ================= constructors ================= */

#define view0_PARAMS(X) X(Tag, tag) X(uint64_t, payload) X(const Field *, f) X(size_t, nf) X(const Binder *, b) X(size_t, nb)
KF_DECL(view0, RefId, view0_PARAMS, OriginId c; MapId m; RefId r;)
KF_STEP(view0) {
    KF_BEGIN(view0);
    KF_CALL(origin_make, &F->c, F->tag, F->payload, F->f, F->nf, F->b, F->nb);
    KF_CALL0(map_identity, &F->m);
    KF_CALL(make_view, &F->r, F->c, F->m);
    KF_RET(F->r);
    KF_END;
}
/* a constructor frame: its fields and binders live in the frame */
#define MK_DECL(name, PARAMS, ...) KF_DECL_EXT(name, RefId, PARAMS, Field f[6]; Binder b[1]; RefId r; __VA_ARGS__)

MK_DECL(mk_universe, mk_universe_PARAMS)
KF_STEP(mk_universe) {
    KF_BEGIN(mk_universe);
    require(F->level != LEVEL_NONE && nat_valid(F->level), "a universe level is an exact natural (use nat_from_word for an external word)");
    KF_CALL(view0, &F->r, T_UNIVERSE, F->level, NULL, 0, NULL, 0);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_universe, RefId, mk_universe_PARAMS, mk_universe(uint64_t level))

#define mk_term_binder_form_PARAMS(X) X(Tag, tag) X(TermVarId, x) X(RefId, A) X(RefId, body)
KF_DECL(mk_term_binder_form, RefId, mk_term_binder_form_PARAMS, Field f[2]; Binder b[1]; RefId r;)
KF_STEP(mk_term_binder_form) {
    KF_BEGIN(mk_term_binder_form);
    require(term_var_type(F->x) == F->A, "binder formal declared at a different type");
    F->f[0] = (Field){ F_REF, NO_SLOT, F->A }; F->f[1] = (Field){ F_REF, 0, F->body };
    F->b[0] = (Binder){ S_TERM, F->x, 0 };
    KF_CALL(view0, &F->r, F->tag, 0, F->f, 2, F->b, 1);
    KF_RET(F->r);
    KF_END;
}
#define MK_BINDER(name, TAG) \
    MK_DECL(name, name##_PARAMS) \
    KF_STEP(name) { KF_BEGIN(name); KF_CALL(mk_term_binder_form, &F->r, TAG, F->x, F->A, F->B); KF_RET(F->r); KF_END; } \
    KF_SYNC_DEF(name, RefId, name##_PARAMS, name(TermVarId x, RefId A, RefId B))
MK_BINDER(mk_pi, T_PI)
MK_BINDER(mk_sigma, T_SIGMA)
MK_BINDER(mk_lam, T_LAM)
/* annotated forms (§59.1): the formation levels are set for the origin
 * being built and recorded in its record (the previous levels are restored) */
#define MK_BINDER_LV(name, TAG, NSECOND, SIG) \
    MK_DECL(name, name##_PARAMS, uint64_t lv, saved;) \
    KF_STEP(name) { \
        KF_BEGIN(name); \
        KF_CALL(levels_pack, &F->lv, F->m, NSECOND); \
        F->saved = tl_levels; tl_levels = F->lv; \
        KF_CALL(mk_term_binder_form, &F->r, TAG, F->x, F->A, F->B); \
        tl_levels = F->saved; \
        KF_RET(F->r); \
        KF_END; \
    } \
    KF_SYNC_DEF(name, RefId, name##_PARAMS, SIG)
MK_BINDER_LV(mk_pi_lv, T_PI, F->n, mk_pi_lv(uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B))
MK_BINDER_LV(mk_sigma_lv, T_SIGMA, F->n, mk_sigma_lv(uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B))
MK_BINDER_LV(mk_lam_lv, T_LAM, LEVEL_NONE, mk_lam_lv(uint64_t m, TermVarId x, RefId A, RefId B))

KF_DECL_EXT(term_levels_push, void, term_levels_push_PARAMS, uint64_t lv;)
KF_STEP(term_levels_push) { KF_BEGIN(term_levels_push); KF_CALL(levels_pack, &F->lv, F->m, F->n); tl_levels = F->lv; KF_RETV(); KF_END; }
KF_SYNC_VOID_DEF(term_levels_push, term_levels_push_PARAMS, term_levels_push(uint64_t m, uint64_t n))
void term_levels_pop(void) { tl_levels = LEVELS_NONE; }

MK_DECL(mk_app, mk_app_PARAMS)
KF_STEP(mk_app) { KF_BEGIN(mk_app); F->f[0] = (Field){ F_REF, NO_SLOT, F->fn }; F->f[1] = (Field){ F_REF, NO_SLOT, F->a }; KF_CALL(view0, &F->r, T_APP, 0, F->f, 2, NULL, 0); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(mk_app, RefId, mk_app_PARAMS, mk_app(RefId fn, RefId a))
MK_DECL(mk_pair, mk_pair_PARAMS)
KF_STEP(mk_pair) { KF_BEGIN(mk_pair); F->f[0] = (Field){ F_REF, NO_SLOT, F->a }; F->f[1] = (Field){ F_REF, NO_SLOT, F->b0 }; KF_CALL(view0, &F->r, T_PAIR, 0, F->f, 2, NULL, 0); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(mk_pair, RefId, mk_pair_PARAMS, mk_pair(RefId a, RefId b0))
/* a pair annotated with its Σ type (§33: a checking-only form synthesizes
 * from its stored annotation); the annotation is the third field */
MK_DECL(mk_pair_at, mk_pair_at_PARAMS)
KF_STEP(mk_pair_at) { KF_BEGIN(mk_pair_at); F->f[0] = (Field){ F_REF, NO_SLOT, F->a }; F->f[1] = (Field){ F_REF, NO_SLOT, F->b0 }; F->f[2] = (Field){ F_REF, NO_SLOT, F->S }; KF_CALL(view0, &F->r, T_PAIR, 0, F->f, 3, NULL, 0); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(mk_pair_at, RefId, mk_pair_at_PARAMS, mk_pair_at(RefId S, RefId a, RefId b0))
MK_DECL(mk_fst, mk_fst_PARAMS)
KF_STEP(mk_fst) { KF_BEGIN(mk_fst); F->f[0] = (Field){ F_REF, NO_SLOT, F->p }; KF_CALL(view0, &F->r, T_FST, 0, F->f, 1, NULL, 0); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(mk_fst, RefId, mk_fst_PARAMS, mk_fst(RefId p))
MK_DECL(mk_snd, mk_snd_PARAMS)
KF_STEP(mk_snd) { KF_BEGIN(mk_snd); F->f[0] = (Field){ F_REF, NO_SLOT, F->p }; KF_CALL(view0, &F->r, T_SND, 0, F->f, 1, NULL, 0); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(mk_snd, RefId, mk_snd_PARAMS, mk_snd(RefId p))
MK_DECL(mk_path, mk_path_PARAMS)
KF_STEP(mk_path) {
    KF_BEGIN(mk_path);
    F->f[0] = (Field){ F_REF, 0, F->B_j }; F->f[1] = (Field){ F_REF, NO_SLOT, F->l }; F->f[2] = (Field){ F_REF, NO_SLOT, F->r0 };
    F->b[0] = (Binder){ S_DIM, F->j, NO_FIELD };
    KF_CALL(view0, &F->r, T_PATH, 0, F->f, 3, F->b, 1);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_path, RefId, mk_path_PARAMS, mk_path(DimVarId j, RefId B_j, RefId l, RefId r0))
MK_DECL(mk_plam, mk_plam_PARAMS)
KF_STEP(mk_plam) {
    KF_BEGIN(mk_plam);
    F->f[0] = (Field){ F_REF, 0, F->body };
    F->b[0] = (Binder){ S_DIM, F->j, NO_FIELD };
    KF_CALL(view0, &F->r, T_PLAM, 0, F->f, 1, F->b, 1);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_plam, RefId, mk_plam_PARAMS, mk_plam(DimVarId j, RefId body))
MK_DECL(mk_papp, mk_papp_PARAMS)
KF_STEP(mk_papp) {
    KF_BEGIN(mk_papp);
    F->f[0] = (Field){ F_REF, 0, F->B_j }; F->f[1] = (Field){ F_REF, NO_SLOT, F->l }; F->f[2] = (Field){ F_REF, NO_SLOT, F->r0 };
    F->f[3] = (Field){ F_REF, NO_SLOT, F->p }; F->f[4] = (Field){ F_INTERVAL, NO_SLOT, F->s };
    F->b[0] = (Binder){ S_DIM, F->j, NO_FIELD };
    KF_CALL(view0, &F->r, T_PAPP, 0, F->f, 5, F->b, 1);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_papp, RefId, mk_papp_PARAMS, mk_papp(DimVarId j, RefId B_j, RefId l, RefId r0, RefId p, IntervalId s))
MK_DECL(mk_glue_type, mk_glue_type_PARAMS)
KF_STEP(mk_glue_type) {
    KF_BEGIN(mk_glue_type);
    F->f[0] = (Field){ F_REF, NO_SLOT, F->A }; F->f[1] = (Field){ F_FACE, NO_SLOT, F->alpha }; F->f[2] = (Field){ F_REF, NO_SLOT, F->T }; F->f[3] = (Field){ F_REF, NO_SLOT, F->e };
    KF_CALL(view0, &F->r, T_GLUE_TYPE, 0, F->f, 4, NULL, 0);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_glue_type, RefId, mk_glue_type_PARAMS, mk_glue_type(RefId A, FaceId alpha, RefId T, RefId e))
MK_DECL(mk_glue_intro, mk_glue_intro_PARAMS)
KF_STEP(mk_glue_intro) {
    KF_BEGIN(mk_glue_intro);
    F->f[0] = (Field){ F_REF, NO_SLOT, F->A }; F->f[1] = (Field){ F_FACE, NO_SLOT, F->alpha }; F->f[2] = (Field){ F_REF, NO_SLOT, F->T };
    F->f[3] = (Field){ F_REF, NO_SLOT, F->e }; F->f[4] = (Field){ F_REF, NO_SLOT, F->t }; F->f[5] = (Field){ F_REF, NO_SLOT, F->a };
    KF_CALL(view0, &F->r, T_GLUE_INTRO, 0, F->f, 6, NULL, 0);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_glue_intro, RefId, mk_glue_intro_PARAMS, mk_glue_intro(RefId A, FaceId alpha, RefId T, RefId e, RefId t, RefId a))
MK_DECL(mk_unglue, mk_unglue_PARAMS)
KF_STEP(mk_unglue) {
    KF_BEGIN(mk_unglue);
    F->f[0] = (Field){ F_REF, NO_SLOT, F->A }; F->f[1] = (Field){ F_FACE, NO_SLOT, F->alpha }; F->f[2] = (Field){ F_REF, NO_SLOT, F->T };
    F->f[3] = (Field){ F_REF, NO_SLOT, F->e }; F->f[4] = (Field){ F_REF, NO_SLOT, F->v };
    KF_CALL(view0, &F->r, T_UNGLUE, 0, F->f, 5, NULL, 0);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_unglue, RefId, mk_unglue_PARAMS, mk_unglue(RefId A, FaceId alpha, RefId T, RefId e, RefId v))
MK_DECL(mk_comp, mk_comp_PARAMS)
KF_STEP(mk_comp) {
    KF_BEGIN(mk_comp);
    F->f[0] = (Field){ F_REF, 0, F->A_j }; F->f[1] = (Field){ F_FACE, NO_SLOT, F->phi }; F->f[2] = (Field){ F_REF, 0, F->u_j }; F->f[3] = (Field){ F_REF, NO_SLOT, F->cap };
    F->b[0] = (Binder){ S_DIM, F->j, NO_FIELD };
    KF_CALL(view0, &F->r, T_COMP, 0, F->f, 4, F->b, 1);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_comp, RefId, mk_comp_PARAMS, mk_comp(DimVarId j, RefId A_j, FaceId phi, RefId u_j, RefId cap))
/* annotated forms (§59.1): n is the family's / type's universe level; the
 * levels are set for the construction and cleared after it */
#define MK_LV(name, base, ...) \
    MK_DECL(name, name##_PARAMS) \
    KF_STEP(name) { KF_BEGIN(name); KF_CALL(term_levels_push, NULL, F->n, LEVEL_NONE); KF_CALL(base, &F->r, __VA_ARGS__); term_levels_pop(); KF_RET(F->r); KF_END; }
MK_LV(mk_comp_lv, mk_comp, F->j, F->A_j, F->phi, F->u_j, F->cap)
KF_SYNC_DEF(mk_comp_lv, RefId, mk_comp_lv_PARAMS, mk_comp_lv(uint64_t n, DimVarId j, RefId A_j, FaceId phi, RefId u_j, RefId cap))
MK_LV(mk_path_lv, mk_path, F->j, F->B_j, F->l, F->r0)
KF_SYNC_DEF(mk_path_lv, RefId, mk_path_lv_PARAMS, mk_path_lv(uint64_t n, DimVarId j, RefId B_j, RefId l, RefId r0))
MK_LV(mk_papp_lv, mk_papp, F->j, F->B_j, F->l, F->r0, F->p, F->s)
KF_SYNC_DEF(mk_papp_lv, RefId, mk_papp_lv_PARAMS, mk_papp_lv(uint64_t n, DimVarId j, RefId B_j, RefId l, RefId r0, RefId p, IntervalId s))
MK_LV(mk_glue_type_lv, mk_glue_type, F->A, F->alpha, F->T, F->e)
KF_SYNC_DEF(mk_glue_type_lv, RefId, mk_glue_type_lv_PARAMS, mk_glue_type_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e))
MK_LV(mk_glue_intro_lv, mk_glue_intro, F->A, F->alpha, F->T, F->e, F->t, F->a)
KF_SYNC_DEF(mk_glue_intro_lv, RefId, mk_glue_intro_lv_PARAMS, mk_glue_intro_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId t, RefId a))
MK_LV(mk_unglue_lv, mk_unglue, F->A, F->alpha, F->T, F->e, F->v)
KF_SYNC_DEF(mk_unglue_lv, RefId, mk_unglue_lv_PARAMS, mk_unglue_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId v))
MK_LV(mk_pair_at_lv, mk_pair_at, F->S, F->a, F->b0)
KF_SYNC_DEF(mk_pair_at_lv, RefId, mk_pair_at_lv_PARAMS, mk_pair_at_lv(uint64_t n, RefId S, RefId a, RefId b0))

KF_DECL_EXT_DROP(mk_tcall, RefId, mk_tcall_PARAMS, mk_tcall_drop, Field *f; RefId out; bool pushed;)
static void mk_tcall_drop(mk_tcall_F *F) { free(F->f); F->f = NULL; if (F->pushed) term_require_pop(); }
KF_STEP(mk_tcall) {
    KF_BEGIN(mk_tcall);
    F->f = malloc((F->nparams + 3) * sizeof(Field)); require(F->f, "out of memory");
    for (size_t k = 0; k < F->nparams; k++) { F->f[k] = F->params[k]; F->f[k].slot = NO_SLOT; }
    F->f[F->nparams] = (Field){ F_REF, NO_SLOT, F->a };
    F->f[F->nparams + 1] = (Field){ F_REF, NO_SLOT, F->in_type };
    F->f[F->nparams + 2] = (Field){ F_REF, NO_SLOT, F->out_type };
    KF_CALL(term_require_push, NULL, F->required);
    F->pushed = true;
    KF_CALL(view0, &F->out, T_TCALL, 2 * F->id + (F->dir ? 1 : 0), F->f, F->nparams + 3, NULL, 0);
    term_require_pop(); F->pushed = false;
    free(F->f); F->f = NULL;
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(mk_tcall, RefId, mk_tcall_PARAMS, mk_tcall(uint64_t id, int dir, size_t nparams, const Field *params, RefId a, RefId in_type, RefId out_type, FaceId required))

KF_DECL_EXT_DROP(mk_system, RefId, mk_system_PARAMS, mk_system_drop, Field *f; RefId r;)
static void mk_system_drop(mk_system_F *F) { free(F->f); F->f = NULL; }
KF_STEP(mk_system) {
    KF_BEGIN(mk_system);
    F->f = malloc((F->n ? 2 * F->n : 1) * sizeof(Field));
    require(F->f, "out of memory");
    for (size_t k = 0; k < F->n; k++) {
        F->f[2 * k].kind = F_FACE; F->f[2 * k].slot = NO_SLOT; F->f[2 * k].id = F->faces[k];
        F->f[2 * k + 1].kind = F_REF; F->f[2 * k + 1].slot = NO_SLOT; F->f[2 * k + 1].id = F->terms[k];
    }
    KF_CALL(view0, &F->r, T_SYSTEM, F->n, F->f, 2 * F->n, NULL, 0);
    free(F->f); F->f = NULL;
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(mk_system, RefId, mk_system_PARAMS, mk_system(size_t n, const FaceId *faces, const RefId *terms))

/* ================= printing ================= */

static void pr(RefId t, FILE *f, int depth);

static void pr_field(const Head *h, size_t k, FILE *f, int depth) {
    const HField *x = &h->f[k];
    if (x->is_binder) {
        if (x->sort == S_TERM) {
            TermOpen o = resolve_term_binder(h->owner, x->slot, x->index);
            fprintf(f, "x%llu. ", (unsigned long long)o.x);
            pr(o.body, f, depth - 1);
        } else {
            DimOpen o = resolve_dim_binder(h->owner, x->slot, x->index);
            fprintf(f, "d%llu. ", (unsigned long long)o.j);
            pr(o.body, f, depth - 1);
        }
        return;
    }
    switch (x->kind) {
    case F_REF: pr(x->id, f, depth - 1); break;
    case F_INTERVAL: iv_print(x->id, f); break;
    case F_FACE: fc_print(x->id, f); break;
    }
}

static void pr(RefId t, FILE *f, int depth) {
    if (ref_is_var(t)) { fprintf(f, "x%llu", (unsigned long long)ref_var_id(t)); return; }
    if (depth <= 0) { fprintf(f, "#%llu", (unsigned long long)t); return; }
    Head h; open_ref(t, &h);
    if (h.tag == T_UNIVERSE) { char d[512]; nat_decimal(h.payload, d, sizeof d); fprintf(f, "U%s", d); head_free(&h); return; }
    if (h.tag == T_GLOBAL) {
        fprintf(f, "%s", DEF(h.payload)->name);
        if (!map_is_identity(h.map)) {
            fprintf(f, "[");
            size_t nt = map_n_terms(h.map), nd = map_n_dims(h.map);
            for (size_t k = 0; k < nt; k++) { TermVarId x; RefId im; map_term_entry(h.map, k, &x, &im); fprintf(f, "%sx%llu:=", k ? "," : "", (unsigned long long)x); pr(im, f, depth - 1); }
            for (size_t k = 0; k < nd; k++) { DimVarId i; IntervalId im; map_dim_entry(h.map, k, &i, &im); fprintf(f, "%sd%llu:=", (k || nt) ? "," : "", (unsigned long long)i); iv_print(im, f); }
            fprintf(f, "]");
        }
        head_free(&h); return;
    }
    fprintf(f, "(%s", tag_name(h.tag));
    for (size_t k = 0; k < h.n; k++) { fprintf(f, " "); pr_field(&h, k, f, depth); }
    fprintf(f, ")");
    head_free(&h);
}

void print_ref_depth(RefId t, FILE *f, int depth) { pr(t, f, depth); }
void print_ref(RefId t, FILE *f) { pr(t, f, 12); }
