#include "intern.h"

/* ---- chunked arrays ---- */
void chunked_init(Chunked *c, size_t elem) { memset(c->dir, 0, sizeof c->dir); c->elem = elem; }
void chunked_free(Chunked *c) { for (size_t k = 0; k < MAX_CHUNKS; k++) free(c->dir[k]); memset(c->dir, 0, sizeof c->dir); }
void *chunked_at(Chunked *c, size_t i) {
    size_t ch = i >> CHUNK_BITS;
    require(ch < MAX_CHUNKS, "chunked array exhausted");
    void *p = __atomic_load_n(&c->dir[ch], __ATOMIC_ACQUIRE);
    if (!p) {
        void *fresh = calloc(CHUNK_SIZE, c->elem);
        require(fresh, "out of memory");
        void *expected = NULL;
        if (__atomic_compare_exchange_n(&c->dir[ch], &expected, fresh, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) p = fresh;
        else { free(fresh); p = expected; }
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
        uint64_t x = w[i];
        for (int b = 0; b < 8; b++) { h ^= (x & 0xff); h *= 1099511628211ULL; x >>= 8; }
    }
    h ^= (uint64_t)n; h *= 1099511628211ULL;
    return h ? h : 1;
}

void interner_init(Interner *t) {
    chunked_init(&t->recs, sizeof(Rec));
    t->n = 0;
    t->nslots = 1024;
    t->slots = calloc(t->nslots, sizeof(uint64_t));
    require(t->slots, "out of memory");
    pthread_mutex_init(&t->mu, NULL);
}

void interner_free(Interner *t) {
    for (size_t i = 0; i < t->n; i++) free(((Rec *)chunked_get(&t->recs, i))->w);
    chunked_free(&t->recs);
    free(t->slots);
    pthread_mutex_destroy(&t->mu);
    memset(t, 0, sizeof *t);
}

static Rec *rec_of(const Interner *t, uint64_t id) { return (Rec *)chunked_get(&t->recs, id - 1); }

static bool rec_equal(const Interner *t, uint64_t id, uint64_t h, const uint64_t *w, size_t n) {
    Rec *r = rec_of(t, id);
    if (r->hash != h || r->n != n) return false;
    return n == 0 || memcmp(r->w, w, n * sizeof(uint64_t)) == 0;
}

static void grow_slots(Interner *t) {
    size_t ns = t->nslots * 2;
    uint64_t *slots = calloc(ns, sizeof(uint64_t));
    require(slots, "out of memory");
    for (size_t s = 0; s < t->nslots; s++) {
        uint64_t id = t->slots[s];
        if (!id) continue;
        size_t p = rec_of(t, id)->hash & (ns - 1);
        while (slots[p]) p = (p + 1) & (ns - 1);
        slots[p] = id;
    }
    free(t->slots);
    t->slots = slots;
    t->nslots = ns;
}

static uint64_t find_locked(const Interner *t, uint64_t h, const uint64_t *w, size_t n) {
    size_t p = h & (t->nslots - 1);
    while (t->slots[p]) {
        uint64_t id = t->slots[p];
        if (rec_equal(t, id, h, w, n)) return id;
        p = (p + 1) & (t->nslots - 1);
    }
    return 0;
}

uint64_t interner_find(Interner *t, const uint64_t *w, size_t n) {
    uint64_t h = hash_words(w, n);
    pthread_mutex_lock(&t->mu);
    uint64_t id = find_locked(t, h, w, n);
    pthread_mutex_unlock(&t->mu);
    return id;
}

uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created) {
    uint64_t h = hash_words(w, n);
    pthread_mutex_lock(&t->mu);
    uint64_t id = find_locked(t, h, w, n);
    if (id) { pthread_mutex_unlock(&t->mu); if (created) *created = false; return id; }
    Rec *r = chunked_at(&t->recs, t->n);
    r->w = malloc((n ? n : 1) * sizeof(uint64_t));
    require(r->w, "out of memory");
    if (n) memcpy(r->w, w, n * sizeof(uint64_t));
    r->n = n; r->hash = h;
    id = (uint64_t)(++t->n);
    size_t p = h & (t->nslots - 1);
    while (t->slots[p]) p = (p + 1) & (t->nslots - 1);
    t->slots[p] = id;
    if (t->n * 2 > t->nslots) grow_slots(t);
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
