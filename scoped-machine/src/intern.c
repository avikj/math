#include "intern.h"
#include "pool.h"

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

/* word storage for one record, reserved before its copy: a bump in the
 * current page (constant work under the storage mutex; a full page is
 * replaced by one fixed-size host allocation, an oversized record gets its
 * own block) */
static uint64_t *storage_reserve(Interner *t, size_t n) {
    pthread_mutex_lock(&t->mu);
    uint64_t *dst;
    if (n + 1 > WPAGE_WORDS) {
        uint64_t *b = malloc((n + 1) * sizeof(uint64_t));
        require(b, "out of memory");
        b[0] = (uint64_t)(uintptr_t)t->pages; t->pages = b;
        dst = b + 1;
    } else {
        if (!t->page || t->page_used + n > WPAGE_WORDS) {
            uint64_t *p = malloc(WPAGE_WORDS * sizeof(uint64_t));
            require(p, "out of memory");
            p[0] = (uint64_t)(uintptr_t)t->pages; t->pages = p;
            t->page = p; t->page_used = 1;
        }
        dst = t->page + t->page_used;
        t->page_used += n;
    }
    pthread_mutex_unlock(&t->mu);
    return dst;
}

/* a fresh trie node, zeroed (chunks are zeroed on creation; indices are
 * never reused); written privately and published by one release CAS */
static uint64_t new_node(Interner *t) {
    uint64_t idx = __atomic_add_fetch(&t->nnodes, 1, __ATOMIC_RELAXED);
    (void)chunked_at(&t->nodes, idx - 1);
    return idx;
}

/* ---- word buffers ---- */
static Pool wpage_pool; static pthread_once_t wpage_once = PTHREAD_ONCE_INIT;
static void wpage_init(void) { pool_init(&wpage_pool, sizeof(WPage)); }
static WPage *wpage_new(void) { pthread_once(&wpage_once, wpage_init); return pool_alloc(&wpage_pool); }
static void wpage_release(WPage *p) { pool_free(&wpage_pool, p); }
void wordbuf_init(WordBuf *b) { b->head = b->tail = NULL; b->n = 0; b->h = 1469598103934665603ULL; }
void wordbuf_push(WordBuf *b, uint64_t x) {
    size_t at = b->n % WB_PAGE;
    if (at == 0) { WPage *p = wpage_new(); if (b->tail) b->tail->next = p; else b->head = p; b->tail = p; }
    b->tail->w[at] = x;
    b->n++;
    uint64_t h = b->h;
    for (int k = 0; k < 8; k++) { h ^= (x & 0xff); h *= 1099511628211ULL; x >>= 8; }
    b->h = h;
}
bool wordbuf_drain_one(WordBuf *b) {
    WPage *p = b->head;
    if (!p) { wordbuf_init(b); return false; }
    b->head = p->next; wpage_release(p);
    if (!b->head) wordbuf_init(b);
    return true;
}
void wordbuf_clear(WordBuf *b) {
    for (WPage *p = b->head; p; ) { WPage *nx = p->next; wpage_release(p); p = nx; }
    wordbuf_init(b);
}

/* ---- the insertion state machine ---- */
enum { P_DESCEND = 0, P_COMPARE, P_INSERT, P_COPY, P_PUBLISH, P_SPLIT, P_DRAIN, P_DONE };

void intern_begin(InternState *s, Interner *t, const uint64_t *arr, WordBuf *buf, size_t n) {
    memset(s, 0, sizeof *s);
    s->t = t; s->arr = arr; s->buf = buf; s->n = n;
    if (buf) { require(buf->n == n, "word buffer length"); s->h = (buf->h ^ (uint64_t)n) * 1099511628211ULL; s->dpg = buf->head; }
    else s->h = hash_words(arr, n);
    s->idx = 1; s->phase = P_DESCEND;
}
/* word j of the source through a forward cursor */
static uint64_t src_word(const InternState *s, const WPage **pg, size_t *base, size_t j) {
    if (s->arr) return s->arr[j];
    while (j >= *base + WB_PAGE) { *pg = (*pg)->next; *base += WB_PAGE; }
    return (*pg)->w[j - *base];
}
static unsigned key_nib(InternState *s, size_t d) {
    size_t i = d >> 4;
    uint64_t x = i == 0 ? s->h : i == 1 ? (uint64_t)s->n : src_word(s, &s->dpg, &s->dbase, i - 2);
    return (unsigned)(x >> (4 * (d & 15))) & 15;
}
static unsigned rec_nib(const Rec *r, size_t d) { return nib(r->hash, r->n, r->w, d); }
/* a leaf was reached: compare its record, or record the separating slot */
static void at_leaf(InternState *s, uint64_t *slot, uint64_t leaf) {
    s->slot = slot; s->seen = leaf; s->cand = leaf >> 1;
    const Rec *r = rec_of(s->t, s->cand);
    if (r->hash == s->h && r->n == s->n) { s->ci = 0; s->cpg = s->buf ? s->buf->head : NULL; s->cbase = 0; s->phase = P_COMPARE; }
    else s->phase = s->id ? P_SPLIT : P_INSERT;
}
static void found(InternState *s, uint64_t id) {
    s->result = id; s->created = false;
    s->phase = s->buf && s->buf->head ? P_DRAIN : P_DONE;
}
static void begin_split(InternState *s) { s->top = new_node(s->t); s->cur = s->top; s->e = s->d + 1; }

bool intern_advance(InternState *s, size_t budget) {
    Interner *t = s->t;
    for (size_t u = 0; u < budget; u++) {
        switch (s->phase) {
        case P_DESCEND: {
            uint64_t *slot = &node_of(t, s->idx)->c[key_nib(s, s->d)];
            uint64_t x = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
            if (x == 0) { s->slot = slot; s->seen = 0; s->phase = s->id ? P_PUBLISH : P_INSERT; break; }
            if (x & 1) { at_leaf(s, slot, x); if (s->phase == P_SPLIT) begin_split(s); break; }
            s->idx = x >> 1; s->d++;
            break;
        }
        case P_COMPARE: {
            const Rec *r = rec_of(t, s->cand);
            if (s->ci == s->n) { found(s, s->cand); break; }
            if (src_word(s, &s->cpg, &s->cbase, s->ci) != r->w[s->ci]) {
                s->phase = s->id ? P_SPLIT : P_INSERT;
                if (s->phase == P_SPLIT) begin_split(s);
                break;
            }
            s->ci++;
            break;
        }
        case P_INSERT:
            s->id = __atomic_add_fetch(&t->n, 1, __ATOMIC_ACQ_REL);
            s->dst = storage_reserve(t, s->n);
            s->copied = 0; s->ppg = s->buf ? s->buf->head : NULL; s->pbase = 0;
            s->phase = P_COPY;
            break;
        case P_COPY:
            if (s->copied < s->n) {
                if (s->buf) {
                    if (s->copied >= s->pbase + WB_PAGE) { WPage *nx = s->ppg->next; wpage_release(s->ppg); s->ppg = nx; s->pbase += WB_PAGE; }
                    s->dst[s->copied] = s->ppg->w[s->copied - s->pbase];
                } else s->dst[s->copied] = s->arr[s->copied];
                s->copied++;
                break;
            }
            if (s->buf) { if (s->ppg) wpage_release(s->ppg); s->buf->head = s->buf->tail = NULL; s->buf->n = 0; s->buf = NULL; }
            s->arr = s->dst;                 /* every later read is of the stored copy */
            { Rec *r = chunked_at(&t->recs, s->id - 1); r->w = s->dst; r->n = s->n; r->hash = s->h; }
            if (s->seen == 0) s->phase = P_PUBLISH;
            else { s->phase = P_SPLIT; begin_split(s); }
            break;
        case P_PUBLISH: {
            uint64_t expect = 0, leaf = (s->id << 1) | 1;
            if (__atomic_compare_exchange_n(s->slot, &expect, leaf, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
                __atomic_store_n(&rec_of(t, s->id)->live, 1, __ATOMIC_RELEASE);
                s->result = s->id; s->created = true; s->phase = P_DONE; break;
            }
            if (expect & 1) { at_leaf(s, s->slot, expect); if (s->phase == P_SPLIT) begin_split(s); }
            else { s->idx = expect >> 1; s->d++; s->phase = P_DESCEND; }
            break;
        }
        case P_SPLIT: {
            const Rec *o = rec_of(t, s->seen >> 1);
            unsigned a = key_nib(s, s->e), b = rec_nib(o, s->e);
            if (a == b) { uint64_t nx = new_node(t); node_of(t, s->cur)->c[a] = nx << 1; s->cur = nx; s->e++; break; }
            node_of(t, s->cur)->c[a] = (s->id << 1) | 1;
            node_of(t, s->cur)->c[b] = s->seen;
            uint64_t expect = s->seen;
            if (__atomic_compare_exchange_n(s->slot, &expect, s->top << 1, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
                __atomic_store_n(&rec_of(t, s->id)->live, 1, __ATOMIC_RELEASE);
                s->result = s->id; s->created = true; s->phase = P_DONE; break;
            }
            /* the leaf was split by another insertion: the private chain is
             * abandoned and the descent continues below the slot */
            require((expect & 1) == 0, "a leaf slot changes only into an inner node");
            s->idx = expect >> 1; s->d++; s->phase = P_DESCEND;
            break;
        }
        case P_DRAIN: {
            WPage *p = s->buf->head;
            if (!p) { s->buf->tail = NULL; s->buf->n = 0; s->phase = P_DONE; break; }
            s->buf->head = p->next; wpage_release(p);
            break;
        }
        case P_DONE: return true;
        }
    }
    return s->phase == P_DONE;
}

uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created) {
    InternState s;
    intern_begin(&s, t, w, NULL, n);
    while (!intern_advance(&s, SIZE_MAX)) {}
    if (created) *created = s.created;
    return s.result;
}

const uint64_t *interner_get(const Interner *t, uint64_t id, size_t *n) {
    require(id >= 1, "bad interned id 0");
    Rec *r = rec_of(t, id);
    if (n) *n = r->n;
    return r->w;
}

size_t interner_count(Interner *t) { return __atomic_load_n(&t->n, __ATOMIC_ACQUIRE); }
bool interner_live(const Interner *t, uint64_t id) {
    Rec *r = chunked_peek(&t->recs, id - 1);
    return r && __atomic_load_n(&r->live, __ATOMIC_ACQUIRE);
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
