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
    return h;
}

void interner_init(Interner *t) {
    memset(t, 0, sizeof *t);
    chunked_init(&t->recs, sizeof(Rec));
    chunked_init(&t->nodes, sizeof(TrieNode));
    chunked_at(&t->nodes, 0);            /* the root, index 1, all slots empty */
    t->nnodes = 1;
    pthread_mutex_init(&t->mu, NULL);
}

void interner_free(Interner *t) {
    for (uint64_t *p = t->pages; p; ) { uint64_t *prev = (uint64_t *)(uintptr_t)p[0]; free(p); p = prev; }
    chunked_free(&t->recs);
    chunked_free(&t->nodes);
    pthread_mutex_destroy(&t->mu);
    memset(t, 0, sizeof *t);
}

static Rec *rec_of(const Interner *t, uint64_t id) { return (Rec *)chunked_get(&t->recs, id - 1); }
static TrieNode *node_of(const Interner *t, uint64_t idx) { return (TrieNode *)chunked_get(&t->nodes, idx - 1); }

/* nibble d of the stream (h, n, w[0..n-1]); d < 16·(n+2) */
static unsigned nib(uint64_t h, size_t n, const uint64_t *w, size_t d) {
    size_t i = d >> 4;
    uint64_t x = i == 0 ? h : i == 1 ? (uint64_t)n : w[i - 2];
    return (unsigned)(x >> (4 * (d & 15))) & 15;
}

static bool rec_equal(const Rec *r, uint64_t h, const uint64_t *w, size_t n) {
    return r->hash == h && r->n == n && (n == 0 || memcmp(r->w, w, n * sizeof(uint64_t)) == 0);
}

/* Lock-free descent. Returns the id when present. Otherwise *slot is the
 * empty slot or the slot holding the separating leaf, *depth its depth. */
static uint64_t descend(const Interner *t, uint64_t h, const uint64_t *w, size_t n, uint64_t **slot, size_t *depth) {
    uint64_t idx = 1;
    for (size_t d = 0;; d++) {
        uint64_t *s = &node_of(t, idx)->c[nib(h, n, w, d)];
        uint64_t x = __atomic_load_n(s, __ATOMIC_ACQUIRE);
        if (x == 0) { *slot = s; *depth = d; return 0; }
        if (x & 1) {
            uint64_t id = x >> 1;
            if (rec_equal(rec_of(t, id), h, w, n)) return id;
            *slot = s; *depth = d; return 0;
        }
        idx = x >> 1;
    }
}

uint64_t interner_find(Interner *t, const uint64_t *w, size_t n) {
    uint64_t *s; size_t d;
    return descend(t, hash_words(w, n), w, n, &s, &d);
}

static uint64_t *words_store(Interner *t, const uint64_t *w, size_t n) {
    if (n + 1 > WPAGE_WORDS) {                         /* oversized record: its own block */
        uint64_t *b = malloc((n + 1) * sizeof(uint64_t));
        require(b, "out of memory");
        b[0] = (uint64_t)(uintptr_t)t->pages; t->pages = b;
        memcpy(b + 1, w, n * sizeof(uint64_t));
        return b + 1;
    }
    if (!t->page || t->page_used + n > WPAGE_WORDS) {
        uint64_t *p = malloc(WPAGE_WORDS * sizeof(uint64_t));
        require(p, "out of memory");
        p[0] = (uint64_t)(uintptr_t)t->pages; t->pages = p;
        t->page = p; t->page_used = 1;
    }
    uint64_t *dst = t->page + t->page_used;
    if (n) memcpy(dst, w, n * sizeof(uint64_t));
    t->page_used += n;
    return dst;
}

static uint64_t new_node(Interner *t) {
    TrieNode *x = chunked_at(&t->nodes, t->nnodes);    /* zeroed on chunk creation; never reused */
    (void)x;
    return ++t->nnodes;
}

uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created) {
    uint64_t h = hash_words(w, n);
    uint64_t *slot; size_t d;
    uint64_t id = descend(t, h, w, n, &slot, &d);
    if (id) { if (created) *created = false; return id; }
    pthread_mutex_lock(&t->mu);
    id = descend(t, h, w, n, &slot, &d);               /* revalidate under the lock */
    if (id) { pthread_mutex_unlock(&t->mu); if (created) *created = false; return id; }
    /* the record, fully initialized before its leaf is published */
    size_t nid = __atomic_load_n(&t->n, __ATOMIC_RELAXED) + 1;
    Rec *r = chunked_at(&t->recs, nid - 1);
    r->w = words_store(t, w, n); r->n = n; r->hash = h;
    uint64_t leaf = ((uint64_t)nid << 1) | 1;
    uint64_t old = *slot;
    if (old == 0) {
        __atomic_store_n(slot, leaf, __ATOMIC_RELEASE);
    } else {
        /* split: inner nodes along the common nibbles, then both leaves,
         * built privately and published by one store into the slot */
        Rec *o = rec_of(t, old >> 1);
        uint64_t top = new_node(t), cur = top;
        size_t e = d + 1;
        while (nib(h, n, w, e) == nib(o->hash, o->n, o->w, e)) {
            uint64_t nx = new_node(t);
            node_of(t, cur)->c[nib(h, n, w, e)] = nx << 1;
            cur = nx; e++;
        }
        node_of(t, cur)->c[nib(h, n, w, e)] = leaf;
        node_of(t, cur)->c[nib(o->hash, o->n, o->w, e)] = old;
        __atomic_store_n(slot, top << 1, __ATOMIC_RELEASE);
    }
    __atomic_store_n(&t->n, nid, __ATOMIC_RELEASE);
    pthread_mutex_unlock(&t->mu);
    if (created) *created = true;
    return nid;
}

const uint64_t *interner_get(const Interner *t, uint64_t id, size_t *n) {
    require(id >= 1, "bad interned id 0");
    Rec *r = rec_of(t, id);
    if (n) *n = r->n;
    return r->w;
}

size_t interner_count(Interner *t) { return __atomic_load_n(&t->n, __ATOMIC_ACQUIRE); }

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
