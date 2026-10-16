#include "intern.h"
#include "fine.h"
#include "arena.h"

/* ---- chunked arrays ---- */
void chunked_init(Chunked *c, size_t elem) { memset(c->dir, 0, sizeof c->dir); c->elem = elem; c->alloc = NULL; c->alloc_ctx = NULL; }
void chunked_set_alloc(Chunked *c, ChunkAlloc alloc, void *ctx) { c->alloc = alloc; c->alloc_ctx = ctx; }
void chunked_free(Chunked *c) { if (!c->alloc) for (size_t k = 0; k < MAX_CHUNKS; k++) if (c->dir[k]) arena_release(c->dir[k], (CHUNK_SIZE * c->elem + 7) / 8); memset(c->dir, 0, sizeof c->dir); }   /* engine chunks (hooked) belong to their spares' arena lists */
void *chunked_at(Chunked *c, size_t i) {
    size_t ch = i >> CHUNK_BITS;
    require(ch < MAX_CHUNKS, "chunked array exhausted");
    void *p = __atomic_load_n(&c->dir[ch], __ATOMIC_ACQUIRE);
    if (!p) {
        void *fresh = c->alloc ? c->alloc(CHUNK_SIZE * c->elem, c->alloc_ctx) : arena_alloc_zero((CHUNK_SIZE * c->elem + 7) / 8, NULL);   /* §94: a kernel chunk is a fresh zero block of the arena — no clearing, possibly under a lock */
        require(fresh, "out of memory");
        void *expected = NULL;
        if (__atomic_compare_exchange_n(&c->dir[ch], &expected, fresh, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) p = fresh;
        else { if (!c->alloc) arena_release(fresh, (CHUNK_SIZE * c->elem + 7) / 8); p = expected; }   /* an arena chunk lost the race: returned at teardown with the arena (the engine's tables are filled under one lock, so this does not occur there) */
    }
    return (char *)p + (i & (CHUNK_SIZE - 1)) * c->elem;
}
void *chunked_get(const Chunked *c, size_t i) {
    size_t ch = i >> CHUNK_BITS;
    void *p = __atomic_load_n(&c->dir[ch], __ATOMIC_ACQUIRE);
    require(p, "chunked read of a missing element");
    return (char *)p + (i & (CHUNK_SIZE - 1)) * c->elem;
}
void *chunked_peek(const Chunked *c, size_t i) {
    size_t ch = i >> CHUNK_BITS;
    if (ch >= MAX_CHUNKS) return NULL;
    void *p = __atomic_load_n(&c->dir[ch], __ATOMIC_ACQUIRE);
    if (!p) return NULL;
    return (char *)p + (i & (CHUNK_SIZE - 1)) * c->elem;
}

/* ---- interner ---- */
static uint64_t hash_words(const uint64_t *w, size_t n) {
    uint64_t h = 1469598103934665603ULL;
    for (size_t i = 0; i < n; i++) {
        uint64_t x = w[i]; fine_bump(FC_INTERN_WORDS_HASHED);   /* one transition per word (unlocked) */
        for (int b = 0; b < 8; b++) { h ^= (x & 0xff); h *= 1099511628211ULL; x >>= 8; }
    }
    h ^= (uint64_t)n; h *= 1099511628211ULL;
    return h ? h : 1;
}

void interner_init(Interner *t) {
    chunked_init(&t->recs, sizeof(Rec));
    t->n = 0;
    t->nslots = 1024;
    t->slots = arena_alloc_zero(t->nslots, NULL);   /* a fresh zero block: no clearing */
    t->old = NULL; t->old_n = t->cursor = 0;
    pthread_mutex_init(&t->mu, NULL);
}

void interner_free(Interner *t) {
    for (size_t i = 0; i < t->n; i++) free(((Rec *)chunked_get(&t->recs, i))->w);
    chunked_free(&t->recs);
    arena_release(t->slots, t->nslots); arena_release(t->old, t->old_n);
    pthread_mutex_destroy(&t->mu);
    memset(t, 0, sizeof *t);
}

static Rec *rec_of(const Interner *t, uint64_t id) { return (Rec *)chunked_get(&t->recs, id - 1); }

static bool rec_equal(const Interner *t, uint64_t id, uint64_t h, const uint64_t *w, size_t n) {
    Rec *r = rec_of(t, id);
    if (r->hash != h || r->n != n) return false;
    /* a hash hit is not equality: every word is compared (§89.2) */
    for (size_t i = 0; i < n; i++) { fine_bump(FC_INTERN_WORD_COMPARES); if (r->w[i] != w[i]) return false; }
    return true;
}

/* §94: growth is incremental. `grow_begin` takes a fresh zero array of twice
 * the size (one allocation, no clearing); every subsequent operation under
 * the lock migrates at most CHUNK_WORDS old slots (`migrate_chunk`); while the
 * old array exists, probes consult the new array and then the old one, and
 * insertions go to the new one. */
#define MIGRATE_CHUNK 32
static void place(uint64_t *slots, size_t nslots, const Interner *t, uint64_t id) {
    size_t p = rec_of(t, id)->hash & (nslots - 1);
    while (slots[p]) { p = (p + 1) & (nslots - 1); fine_bump(FC_INTERN_PROBES); }
    slots[p] = id;
}
static void grow_begin(Interner *t) {
    if (t->old) return;
    t->old = t->slots; t->old_n = t->nslots; t->cursor = 0;
    t->nslots *= 2; t->slots = arena_alloc_zero(t->nslots, NULL);
}
static void migrate_chunk(Interner *t) {
    if (!t->old) return;
    size_t end = t->cursor + MIGRATE_CHUNK; if (end > t->old_n) end = t->old_n;
    for (; t->cursor < end; t->cursor++) { uint64_t id = t->old[t->cursor]; if (id) { place(t->slots, t->nslots, t, id); fine_bump(FC_INTERN_SLOTS_RELOCATED); } }
    if (t->cursor >= t->old_n) { arena_release(t->old, t->old_n); t->old = NULL; t->old_n = t->cursor = 0; }
}
static uint64_t find_in(const Interner *t, const uint64_t *slots, size_t nslots, uint64_t h, const uint64_t *w, size_t n) {
    size_t p = h & (nslots - 1);
    while (slots[p]) {
        uint64_t id = slots[p]; fine_bump(FC_INTERN_PROBES);
        if (rec_equal(t, id, h, w, n)) return id;
        p = (p + 1) & (nslots - 1);
    }
    fine_bump(FC_INTERN_PROBES);
    return 0;
}
static uint64_t find_locked(const Interner *t, uint64_t h, const uint64_t *w, size_t n) {
    uint64_t id = find_in(t, t->slots, t->nslots, h, w, n);
    if (!id && t->old) id = find_in(t, t->old, t->old_n, h, w, n);
    return id;
}

/* §94: the lock is held for probes and the publication only. Hashing, the
 * word comparisons (records are immutable at stable addresses once
 * published) and the copy of a new record happen outside it, so a kernel
 * continuation suspends between words. Candidates found under the lock (equal
 * hash and length) are compared after it; a candidate published by another
 * thread between the two lock sections is compared under the second. The
 * slot-array growth (`grow_slots`) remains one locked relocation, amortized
 * and counted (FC_INTERN_SLOTS_RELOCATED). */
#define CAND_MAX 8
static size_t candidates_in(const Interner *t, const uint64_t *slots, size_t nslots, uint64_t h, size_t n, uint64_t *cand, size_t k, uint64_t above) {
    size_t p = h & (nslots - 1);
    while (slots[p]) {
        uint64_t id = slots[p]; fine_bump(FC_INTERN_PROBES);
        Rec *r = rec_of(t, id);
        if (r->hash == h && r->n == n && id > above) { if (k < CAND_MAX) cand[k++] = id; else return (size_t)-1; }   /* too many: compare under the lock */
        p = (p + 1) & (nslots - 1);
    }
    fine_bump(FC_INTERN_PROBES);
    return k;
}
static size_t candidates_locked(Interner *t, uint64_t h, size_t n, uint64_t *cand, uint64_t above) {
    migrate_chunk(t);   /* one bounded step of a growth in progress */
    size_t k = candidates_in(t, t->slots, t->nslots, h, n, cand, 0, above);
    if (k != (size_t)-1 && t->old) k = candidates_in(t, t->old, t->old_n, h, n, cand, k, above);
    return k;
}
static uint64_t match_unlocked(const Interner *t, const uint64_t *cand, size_t k, uint64_t h, const uint64_t *w, size_t n) {
    for (size_t i = 0; i < k; i++) if (rec_equal(t, cand[i], h, w, n)) return cand[i];
    return 0;
}
uint64_t interner_find(Interner *t, const uint64_t *w, size_t n) {
    uint64_t h = hash_words(w, n), cand[CAND_MAX];
    pthread_mutex_lock(&t->mu);
    size_t k = candidates_locked(t, h, n, cand, 0);
    if (k == (size_t)-1) { uint64_t id = find_locked(t, h, w, n); pthread_mutex_unlock(&t->mu); return id; }
    pthread_mutex_unlock(&t->mu);
    return match_unlocked(t, cand, k, h, w, n);
}

uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created) {
    uint64_t h = hash_words(w, n), cand[CAND_MAX];
    pthread_mutex_lock(&t->mu);
    size_t k = candidates_locked(t, h, n, cand, 0); uint64_t seen = t->n;
    if (k == (size_t)-1) { uint64_t id = find_locked(t, h, w, n); if (id) { pthread_mutex_unlock(&t->mu); if (created) *created = false; return id; } k = 0; }
    pthread_mutex_unlock(&t->mu);
    uint64_t id = match_unlocked(t, cand, k, h, w, n);
    if (id) { if (created) *created = false; return id; }
    /* a new record: prepared outside the lock, one transition per word; the
     * record chunk the new id will need is created outside the lock too (its
     * clearing is in transitions; a chunk created under the lock would not be) */
    uint64_t *copy = malloc((n ? n : 1) * sizeof(uint64_t)); require(copy, "out of memory");
    for (size_t i = 0; i < n; i++) { copy[i] = w[i]; fine_bump(FC_INTERN_WORDS_COPIED); }
    { size_t at = __atomic_load_n(&t->n, __ATOMIC_RELAXED); (void)chunked_at(&t->recs, at); (void)chunked_at(&t->recs, at + 1); }
    pthread_mutex_lock(&t->mu);
    if (t->n > seen) {   /* published meanwhile by another thread: compare the newcomers under the lock */
        size_t k2 = candidates_locked(t, h, n, cand, seen);
        uint64_t dup = k2 == (size_t)-1 ? find_locked(t, h, w, n) : match_unlocked(t, cand, k2, h, w, n);
        if (dup) { pthread_mutex_unlock(&t->mu); free(copy); if (created) *created = false; return dup; }
    }
    Rec *r = chunked_at(&t->recs, t->n);
    r->w = copy; r->n = n; r->hash = h;
    id = (uint64_t)__atomic_add_fetch(&t->n, 1, __ATOMIC_RELEASE);   /* the count is read unlocked (relaxed) by the chunk pre-creation */
    place(t->slots, t->nslots, t, id);
    if (t->n * 2 > t->nslots) grow_begin(t);   /* one fresh allocation; the migration proceeds a chunk per operation */
    pthread_mutex_unlock(&t->mu);
    if (created) *created = true;
    return id;
}

const uint64_t *interner_get(const Interner *t, uint64_t id, size_t *n) {
    require(id >= 1, "bad interned id 0");
    Rec *r = rec_of(t, id);
    if (n) *n = r->n;
    return r->w;
}

size_t interner_count(Interner *t) {
    pthread_mutex_lock(&t->mu);
    size_t n = t->n;
    pthread_mutex_unlock(&t->mu);
    return n;
}

/* ---- WordMap ---- */
void wordmap_init(WordMap *m) { interner_init(&m->keys); chunked_init(&m->vals, sizeof(uint64_t)); }
void wordmap_free(WordMap *m) { interner_free(&m->keys); chunked_free(&m->vals); }

bool wordmap_get(WordMap *m, const uint64_t *k, size_t n, uint64_t *out) {
    uint64_t id = interner_find(&m->keys, k, n);
    if (!id) return false;
    /* The key becomes discoverable before the writer stores its value: an
     * absent value chunk, like a zero value, means "not yet published". */
    uint64_t *slot = chunked_peek(&m->vals, id - 1);
    if (!slot) return false;
    uint64_t v = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
    if (!v) return false;            /* key created, value not yet published */
    *out = v;
    return true;
}

void wordmap_put(WordMap *m, const uint64_t *k, size_t n, uint64_t v) {
    require(v != 0, "wordmap values are non-zero handles");
    uint64_t id = interner_intern(&m->keys, k, n, NULL);
    __atomic_store_n((uint64_t *)chunked_at(&m->vals, id - 1), v, __ATOMIC_RELEASE);
}
