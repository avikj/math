/* event.c — see event.h. Host allocations only: the stream must not record
 * itself through the instrumented allocator it accounts for. */
#include "event.h"
#include "radix.h"
#include "fine.h"
#include "reuse_stats.h"
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define CHUNK_WORDS ((size_t)1 << 15)
#define REC_TAG ((uint64_t)0xA << 60)
#define AMT_MAX ((((uint64_t)1) << 48) - 1)   /* one label word's amount; larger amounts span several words of the same dimension */

typedef struct EvStream {
    uint32_t id;
    Radix dir;                   /* chunk index → word array (non-moving) */
    uint64_t len;                /* published words (release) */
    uint64_t gen;                /* the session it belongs to */
    struct EvStream *next;
} EvStream;

typedef struct { const char *name; unsigned base, n; XCount *shadow; size_t nbase; uint32_t *bstream; uint64_t *blen; } Family;   /* the fold starts at the family's baseline: the stream lengths when its shadow was (re)initialized */
static struct {
    pthread_mutex_t mu;          /* stream registration, family registration */
    EvStream *streams; uint32_t nstreams;
    Family fam[64]; unsigned nfam, ndims;
    uint64_t gen; bool live;
    uint64_t st_records, st_words, st_segments, st_ambient;
} G = { PTHREAD_MUTEX_INITIALIZER, NULL, 0, { { 0 } }, 0, 0, 0, false, 0, 0, 0, 0 };

__thread uint64_t ev_cur[ED_MAX];
__thread uint64_t ev_touch[ED_MAX / 64];

typedef struct { int kind; uint64_t occ, cause, owner; uint32_t nsaved; uint32_t *sdim; uint64_t *sval; } Unit;
static __thread EvStream *tl_stream; static __thread uint64_t tl_gen;
static __thread Unit *tl_units; static __thread size_t tl_depth, tl_cap;
static __thread uint64_t tl_pos;   /* writer cursor (words) */
/* a thread's unit buffers are released when the thread exits */
static pthread_key_t units_key; static pthread_once_t units_once = PTHREAD_ONCE_INIT;
static void units_release(void *v) { Unit *u = v; for (size_t i = 0; i < tl_cap; i++) { (free)(u[i].sdim); (free)(u[i].sval); } (free)(u); }
static void units_key_init(void) { pthread_key_create(&units_key, units_release); }

/* the accounting owner: the client scope current on this thread, else the service owner of the unit kind */
extern __thread struct ReuseScope *reuse_tl_scope;
uint64_t reuse_scope_id(const struct ReuseScope *s);
static uint64_t service_owner(int kind) {
    switch (kind) { case EK_EVAL_TASK: return EO_EVAL; case EK_NET_PAIR: return EO_NET; case EK_ENGINE_UNIT: return EO_ENGINE; case EK_KERNEL_GRANT: return EO_KERNEL;
                    case EK_EFFECT_JOB: return EO_EFFECT; case EK_CHAIN_STEP: return EO_CHAIN; default: return EO_AMBIENT; }
}
uint64_t ev_owner_current(EvKind kind) { return reuse_tl_scope ? reuse_scope_id(reuse_tl_scope) : service_owner(kind); }

unsigned ev_family(const char *name, unsigned n, XCount *shadow) {
    ev_quiesce();
    pthread_mutex_lock(&G.mu);
    Family *f = NULL;
    for (unsigned i = 0; i < G.nfam && !f; i++) if (!strcmp(G.fam[i].name, name)) f = &G.fam[i];
    if (!f) {
        if (G.nfam == 64 || G.ndims + n > ED_MAX) { fprintf(stderr, "fatal: event: dimension space exhausted registering %s\n", name); abort(); }
        f = &G.fam[G.nfam++]; f->name = name; f->base = G.ndims; f->n = n; G.ndims += n;
    }
    f->shadow = shadow;
    /* baseline: every stream's published length now (the caller's ambient label was published first) */
    (free)(f->bstream); (free)(f->blen); f->nbase = G.nstreams;
    f->bstream = (malloc)((f->nbase ? f->nbase : 1) * sizeof *f->bstream); f->blen = (malloc)((f->nbase ? f->nbase : 1) * sizeof *f->blen);
    if (!f->bstream || !f->blen) abort();
    size_t i = 0; for (EvStream *st = G.streams; st && i < f->nbase; st = st->next, i++) { f->bstream[i] = st->id; f->blen[i] = __atomic_load_n(&st->len, __ATOMIC_ACQUIRE); }
    f->nbase = i;
    unsigned b = f->base; pthread_mutex_unlock(&G.mu); return b;
}
unsigned ev_family_base(const char *name) { unsigned b = (unsigned)-1; pthread_mutex_lock(&G.mu); for (unsigned i = 0; i < G.nfam; i++) if (!strcmp(G.fam[i].name, name)) b = G.fam[i].base; pthread_mutex_unlock(&G.mu); return b; }
unsigned ev_dims(void) { return G.ndims; }
const char *ev_dim_name(unsigned d, unsigned *index) {
    for (unsigned i = 0; i < G.nfam; i++) if (d >= G.fam[i].base && d < G.fam[i].base + G.fam[i].n) { if (index) *index = d - G.fam[i].base; return G.fam[i].name; }
    return "?";
}
bool ev_live(void) { return __atomic_load_n(&G.live, __ATOMIC_ACQUIRE); }

static void clear_cur(void) {
    for (unsigned w = 0; w < ED_MAX / 64; w++) { uint64_t m = ev_touch[w]; while (m) { unsigned b = (unsigned)__builtin_ctzll(m); m &= m - 1; ev_cur[w * 64 + b] = 0; } ev_touch[w] = 0; }
}
void ev_init(void) {
    pthread_mutex_lock(&G.mu); G.gen++; G.live = true; G.st_records = G.st_words = G.st_segments = G.st_ambient = 0;
    for (unsigned i = 0; i < G.nfam; i++) G.fam[i].nbase = 0;   /* a new session: every family's fold starts at its streams' beginning */
    pthread_mutex_unlock(&G.mu);
    clear_cur(); tl_depth = 0;    /* the initializing thread starts this session with an empty ambient label */
}
static void free_chunk(void *v, void *ctx) { (void)ctx; (free)(v); }
void ev_free(void) {
    pthread_mutex_lock(&G.mu);
    EvStream *s = G.streams; G.streams = NULL; G.nstreams = 0; G.live = false; G.gen++;
    pthread_mutex_unlock(&G.mu);
    while (s) { EvStream *n = s->next; radix_free(&s->dir, free_chunk, NULL); (free)(s); s = n; }
    clear_cur(); tl_depth = 0;
}
static EvStream *my_stream(void) {
    if (tl_stream && tl_gen == G.gen) return tl_stream;
    EvStream *s = (calloc)(1, sizeof *s); if (!s) abort();
    radix_init(&s->dir);
    pthread_mutex_lock(&G.mu);
    s->id = G.nstreams++; s->gen = G.gen; s->next = G.streams; G.streams = s;
    pthread_mutex_unlock(&G.mu);
    tl_stream = s; tl_gen = G.gen; tl_pos = 0;
    return s;
}
static uint64_t *slot(EvStream *s, uint64_t pos) {
    void **p = radix_slot(&s->dir, (size_t)(pos / CHUNK_WORDS), true);
    if (!*p) { *p = (calloc)(CHUNK_WORDS, sizeof(uint64_t)); if (!*p) abort(); }
    return (uint64_t *)*p + pos % CHUNK_WORDS;
}
static uint64_t *slot_ro(const EvStream *s, uint64_t pos) { uint64_t *c = radix_get(&s->dir, (size_t)(pos / CHUNK_WORDS)); return c ? c + pos % CHUNK_WORDS : NULL; }

/* publish the current label as one record; the label is cleared */
static EvRef publish(int kind, uint64_t owner, uint64_t occ, uint64_t cause) {
    EvRef r = { 0, 0 };
    if (!ev_live()) { clear_cur(); return r; }
    EvStream *s = my_stream();
    unsigned nd = 0;
    for (unsigned w = 0; w < ED_MAX / 64; w++) { uint64_t m = ev_touch[w]; while (m) { unsigned b = (unsigned)__builtin_ctzll(m); m &= m - 1; uint64_t v = ev_cur[w * 64 + b]; nd += (unsigned)((v + AMT_MAX - 1) / AMT_MAX); } }
    size_t need = 4 + nd;
    if (tl_pos % CHUNK_WORDS + need > CHUNK_WORDS) tl_pos += CHUNK_WORDS - tl_pos % CHUNK_WORDS;   /* the rest of this chunk stays zero: padding */
    r.stream = s->id; r.index = tl_pos;
    uint64_t *w0 = slot(s, tl_pos);
    w0[1] = owner; w0[2] = occ; w0[3] = cause;
    size_t k = 4;
    for (unsigned w = 0; w < ED_MAX / 64; w++) {
        uint64_t m = ev_touch[w];
        while (m) {
            unsigned b = (unsigned)__builtin_ctzll(m); m &= m - 1; unsigned d = w * 64 + b; uint64_t v = ev_cur[d];
            while (v) { uint64_t part = v > AMT_MAX ? AMT_MAX : v; w0[k++] = ((uint64_t)d << 48) | part; v -= part; }
            ev_cur[d] = 0;
        }
        ev_touch[w] = 0;
    }
    w0[0] = REC_TAG | ((uint64_t)(kind & 0xFF) << 52) | ((uint64_t)(k - 4) << 32);
    tl_pos += k;
    __atomic_store_n(&s->len, tl_pos, __ATOMIC_RELEASE);
    __atomic_add_fetch(&G.st_records, 1, __ATOMIC_RELAXED); __atomic_add_fetch(&G.st_words, k, __ATOMIC_RELAXED);
    return r;
}
static bool cur_empty(void) { for (unsigned w = 0; w < ED_MAX / 64; w++) if (ev_touch[w]) return false; return true; }
void ev_quiesce(void) {
    if (tl_depth || cur_empty()) return;
    publish(EK_AMBIENT, ev_owner_current(EK_AMBIENT), 0, 0); __atomic_add_fetch(&G.st_ambient, 1, __ATOMIC_RELAXED);
}
void ev_begin(EvKind kind, uint64_t occ, uint64_t cause) {
    if (tl_depth == tl_cap) { pthread_once(&units_once, units_key_init); size_t nc = tl_cap ? 2 * tl_cap : 8; Unit *u = (realloc)(tl_units, nc * sizeof *u); if (!u) abort(); memset(u + tl_cap, 0, (nc - tl_cap) * sizeof *u); tl_units = u; tl_cap = nc; pthread_setspecific(units_key, u); }
    Unit *u = &tl_units[tl_depth];
    /* the enclosing label is set aside (bounded: at most ED_MAX entries) */
    if (!u->sdim) { u->sdim = (malloc)(ED_MAX * sizeof *u->sdim); u->sval = (malloc)(ED_MAX * sizeof *u->sval); if (!u->sdim || !u->sval) abort(); }
    u->nsaved = 0;
    for (unsigned w = 0; w < ED_MAX / 64; w++) { uint64_t m = ev_touch[w]; while (m) { unsigned b = (unsigned)__builtin_ctzll(m); m &= m - 1; unsigned d = w * 64 + b; u->sdim[u->nsaved] = d; u->sval[u->nsaved++] = ev_cur[d]; ev_cur[d] = 0; } ev_touch[w] = 0; }
    u->kind = kind; u->occ = occ; u->cause = cause; u->owner = ev_owner_current(kind);
    tl_depth++;
}
EvRef ev_end(void) {
    if (!tl_depth) { EvRef z = { 0, 0 }; return z; }
    Unit *u = &tl_units[--tl_depth];
    EvRef r = publish(u->kind, u->owner, u->occ, u->cause);
    for (uint32_t i = 0; i < u->nsaved; i++) ev_add(u->sdim[i], u->sval[i]);   /* the enclosing label resumes */
    return r;
}
void ev_owner_switch(void) {
    if (!tl_depth) { if (!cur_empty()) { publish(EK_AMBIENT, ev_owner_current(EK_AMBIENT), 0, 0); __atomic_add_fetch(&G.st_ambient, 1, __ATOMIC_RELAXED); } return; }
    Unit *u = &tl_units[tl_depth - 1];
    if (!cur_empty()) { publish(u->kind, u->owner, u->occ, u->cause); __atomic_add_fetch(&G.st_segments, 1, __ATOMIC_RELAXED); }
}
size_t ev_depth(void) { return tl_depth; }
void ev_unwind_to(size_t depth) { while (tl_depth > depth) ev_end(); }
void ev_owner_refresh(void) { if (tl_depth) tl_units[tl_depth - 1].owner = ev_owner_current((EvKind)tl_units[tl_depth - 1].kind); }

EvPrefix ev_prefix(void) {
    EvPrefix p = { 0, NULL, NULL };
    pthread_mutex_lock(&G.mu);
    p.n = G.nstreams; p.s = (malloc)((p.n ? p.n : 1) * sizeof *p.s); p.len = (malloc)((p.n ? p.n : 1) * sizeof *p.len);
    if (!p.s || !p.len) abort();
    size_t i = 0; for (EvStream *s = G.streams; s && i < p.n; s = s->next, i++) { p.s[i] = s; p.len[i] = __atomic_load_n(&s->len, __ATOMIC_ACQUIRE); }
    p.n = i;
    pthread_mutex_unlock(&G.mu);
    return p;
}
void ev_prefix_free(EvPrefix *p) { (free)(p->s); (free)(p->len); memset(p, 0, sizeof *p); }
static bool match(const uint64_t *w, const EvFilter *f) {
    if (!f) return true;
    if (f->owner && w[1] != f->owner) return false;
    if (f->kind >= 0 && (int)((w[0] >> 52) & 0xFF) != f->kind) return false;
    if (f->occ && w[2] != f->occ) return false;
    if (f->occs) { size_t lo = 0, hi = f->nocc; while (lo < hi) { size_t m = (lo + hi) / 2; if (f->occs[m] < w[2]) lo = m + 1; else hi = m; } if (lo == f->nocc || f->occs[lo] != w[2]) return false; }
    return true;
}
static void fold_from(const EvPrefix *p, const EvFilter *f, XCount *out, const Family *fam) {
    for (size_t i = 0; i < p->n; i++) {
        uint64_t pos = 0, end = p->len[i];
        if (fam) for (size_t j = 0; j < fam->nbase; j++) if (fam->bstream[j] == p->s[i]->id) pos = fam->blen[j];
        while (pos < end) {
            const uint64_t *w = slot_ro(p->s[i], pos);
            if (!w || *w == 0) { pos += CHUNK_WORDS - pos % CHUNK_WORDS; continue; }
            unsigned nd = (unsigned)((w[0] >> 32) & 0xFFFFF);
            if (match(w, f)) for (unsigned k = 0; k < nd; k++) { uint64_t e = w[4 + k]; xc_add(&out[e >> 48], e & (((uint64_t)1 << 48) - 1)); }
            pos += 4 + nd;
        }
    }
}
void ev_fold_dims(const EvPrefix *p, const EvFilter *f, XCount *out) { fold_from(p, f, out, NULL); }
uint64_t ev_count_records(const EvPrefix *p, const EvFilter *f) {
    uint64_t n = 0;
    for (size_t i = 0; i < p->n; i++) {
        uint64_t pos = 0, end = p->len[i];
        while (pos < end) {
            const uint64_t *w = slot_ro(p->s[i], pos);
            if (!w || *w == 0) { pos += CHUNK_WORDS - pos % CHUNK_WORDS; continue; }
            unsigned nd = (unsigned)((w[0] >> 32) & 0xFFFFF);
            if (match(w, f)) n++;
            pos += 4 + nd;
        }
    }
    return n;
}
size_t ev_shadow_check(const EvPrefix *pin, bool verbose) {
    if (verbose && (tl_depth || !cur_empty())) fprintf(stderr, "event: shadow check with %zu open units on this thread\n", tl_depth);
    ev_quiesce();
    /* shadows and prefix captured together, before the fold performs any work */
    static XSnap shadow[ED_MAX]; static XCount folded[ED_MAX];   /* (test-time comparison: one caller at a time) */
    unsigned nf = G.nfam;
    for (unsigned i = 0; i < nf; i++) if (G.fam[i].shadow) for (unsigned j = 0; j < G.fam[i].n; j++) shadow[G.fam[i].base + j] = xc_snap(&G.fam[i].shadow[j]);
    EvPrefix own = pin ? *pin : ev_prefix();
    size_t bad = 0;
    for (unsigned i = 0; i < nf; i++) {
        if (!G.fam[i].shadow) continue;
        for (unsigned j = 0; j < G.fam[i].n; j++) xc_reset(&folded[G.fam[i].base + j]);
        fold_from(&own, NULL, folded, &G.fam[i]);
        for (unsigned j = 0; j < G.fam[i].n; j++) {
            unsigned d = G.fam[i].base + j; XSnap a = xc_snap(&folded[d]);
            if (!xs_eq(a, shadow[d])) {
                bad++;
                if (verbose) { uint64_t x = 0, y = 0; xs_u64(a, &x); xs_u64(shadow[d], &y); fprintf(stderr, "event shadow mismatch: %s[%u] stream=%llu shadow=%llu\n", G.fam[i].name, j, (unsigned long long)x, (unsigned long long)y); }
            }
        }
    }
    if (!pin) ev_prefix_free(&own);
    return bad;
}
EvStats ev_stats(void) {
    EvStats s; s.records = __atomic_load_n(&G.st_records, __ATOMIC_RELAXED); s.words = __atomic_load_n(&G.st_words, __ATOMIC_RELAXED);
    s.streams = G.nstreams; s.segments = __atomic_load_n(&G.st_segments, __ATOMIC_RELAXED); s.ambient = __atomic_load_n(&G.st_ambient, __ATOMIC_RELAXED);
    return s;
}

/* the fine transitions and the reuse markers are the first two families (fine_bump / reuse_bump add to them directly) */
extern XCount fine_counters[FC_COUNT];
_Static_assert(FC_COUNT == ED_REUSE, "ED_REUSE must equal FC_COUNT");
__attribute__((constructor)) static void ev_register_core(void) {
    unsigned f = ev_family("fine", FC_COUNT, fine_counters);
    unsigned r = ev_family("reuse", REUSE_COUNTER_COUNT, NULL);
    if (f != 0 || r != ED_REUSE) { fprintf(stderr, "fatal: event: core families out of order\n"); abort(); }
}

static int cmp_u64(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }
void ev_occ_sort(uint64_t *v, size_t *n) {
    qsort(v, *n, sizeof *v, cmp_u64);
    size_t k = 0; for (size_t i = 0; i < *n; i++) if (!k || v[k - 1] != v[i]) v[k++] = v[i];
    *n = k;
}
size_t ev_occ_union(const uint64_t *a, size_t na, const uint64_t *b, size_t nb, uint64_t **out) {
    uint64_t *v = (malloc)((na + nb + 1) * sizeof *v); if (!v) abort();
    size_t i = 0, j = 0, k = 0;
    while (i < na || j < nb) { if (j == nb || (i < na && a[i] < b[j])) v[k++] = a[i++]; else if (i == na || b[j] < a[i]) v[k++] = b[j++]; else { v[k++] = a[i++]; j++; } }
    *out = v; return k;
}
size_t ev_occ_intersection(const uint64_t *a, size_t na, const uint64_t *b, size_t nb, uint64_t **out) {
    uint64_t *v = (malloc)(((na < nb ? na : nb) + 1) * sizeof *v); if (!v) abort();
    size_t i = 0, j = 0, k = 0;
    while (i < na && j < nb) { if (a[i] < b[j]) i++; else if (b[j] < a[i]) j++; else { v[k++] = a[i++]; j++; } }
    *out = v; return k;
}
size_t ev_occ_difference(const uint64_t *a, size_t na, const uint64_t *b, size_t nb, uint64_t **out) {
    uint64_t *v = (malloc)((na + 1) * sizeof *v); if (!v) abort();
    size_t i = 0, j = 0, k = 0;
    while (i < na) { if (j < nb && b[j] < a[i]) j++; else if (j < nb && b[j] == a[i]) { i++; j++; } else v[k++] = a[i++]; }
    *out = v; return k;
}
