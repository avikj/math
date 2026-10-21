#include "intern.h"
#include "pool.h"
#include <sched.h>

/* ---- chunked arrays ---- */
void chunked_init(Chunked *c, size_t elem) { c->root = NULL; c->elem = elem; }
static void rnode_free(RNode *n) {
    for (size_t k = 0; k < ((size_t)1 << FAN_BITS); k++) if (n->slot[k]) { if (n->height > 1) rnode_free(n->slot[k]); else free(n->slot[k]); }
    free(n);
}
void chunked_free(Chunked *c) { if (c->root) rnode_free(c->root); c->root = NULL; }
static bool covers(unsigned h, size_t i) { unsigned b = CHUNK_BITS + FAN_BITS * h; return b >= 64 || (i >> b) == 0; }
static void *publish(void **slot, void *fresh) {
    void *expected = NULL;
    if (__atomic_compare_exchange_n(slot, &expected, fresh, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return fresh;
    free(fresh); return expected;
}
static RNode *rnode_new(unsigned h) { RNode *n = calloc(1, sizeof *n); require(n, "out of memory"); n->height = h; return n; }
/* the leaf element of index i under the root, creating nodes and the chunk when create */
static void *descend(const Chunked *c, size_t i, bool create) {
    RNode *n = __atomic_load_n(&c->root, __ATOMIC_ACQUIRE);
    if (!n || !covers(n->height, i)) return NULL;
    for (;;) {
        unsigned h = n->height;
        void **slot = &n->slot[(i >> (CHUNK_BITS + FAN_BITS * (h - 1))) & (((size_t)1 << FAN_BITS) - 1)];
        void *p = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
        if (!p) {
            if (!create) return NULL;
            void *fresh = h > 1 ? (void *)rnode_new(h - 1) : calloc(CHUNK_SIZE, c->elem);
            require(fresh, "out of memory");
            p = publish(slot, fresh);
        }
        if (h == 1) return (char *)p + (i & (CHUNK_SIZE - 1)) * c->elem;
        n = p;
    }
}
void *chunked_at(Chunked *c, size_t i) {
    for (;;) {                                        /* at most one new level per word-width step */
        RNode *r = __atomic_load_n(&c->root, __ATOMIC_ACQUIRE);
        if (r && covers(r->height, i)) return descend(c, i, true);
        RNode *up = rnode_new(r ? r->height + 1 : 1);
        up->slot[0] = r;
        if (!__atomic_compare_exchange_n(&c->root, &r, up, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) free(up);
    }
}
void *chunked_get(const Chunked *c, size_t i) { void *p = descend(c, i, false); require(p, "chunked read of a missing element"); return p; }
void *chunked_peek(const Chunked *c, size_t i) { return descend(c, i, false); }

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

__thread int intern_in_step;
static FlattenHook flatten_hook;
void interner_set_flatten_hook(FlattenHook h) { __atomic_store_n(&flatten_hook, h, __ATOMIC_RELEASE); }

/* registry: index → table (indices are never reused) */
static Chunked registry; static size_t registry_n; static pthread_once_t registry_once = PTHREAD_ONCE_INIT;
static void registry_init(void) { chunked_init(&registry, sizeof(Interner *)); }
Interner *interner_by_index(size_t index) { Interner **p = chunked_peek(&registry, index - 1); return p ? __atomic_load_n(p, __ATOMIC_ACQUIRE) : NULL; }

void interner_init(Interner *t) {
    memset(t, 0, sizeof *t);
    chunked_init(&t->recs, sizeof(Rec));
    chunked_init(&t->nodes, sizeof(TrieNode));
    chunked_at(&t->nodes, 0);            /* the root, index 1, all slots empty */
    t->nnodes = 1;
    pthread_once(&registry_once, registry_init);
    t->index = __atomic_add_fetch(&registry_n, 1, __ATOMIC_RELAXED);
    __atomic_store_n((Interner **)chunked_at(&registry, t->index - 1), t, __ATOMIC_RELEASE);
}

void interner_free(Interner *t) {
    if (t->index) __atomic_store_n((Interner **)chunked_at(&registry, t->index - 1), NULL, __ATOMIC_RELEASE);
    if (t->tree) { interner_free(t->tree); free(t->tree); }
    for (uint64_t *p = t->pages; p; ) { uint64_t *prev = (uint64_t *)(uintptr_t)p[0]; free(p); p = prev; }
    chunked_free(&t->recs);
    chunked_free(&t->nodes);
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

/* word storage for one record, constant work: each thread carves its own
 * current page of each table (cached by the table's never-reused index); a
 * full page is replaced by one fixed-size host allocation, linked into the
 * table's teardown list by one CAS; an oversized record — only the flatten
 * owner's — gets one host block, whose words are then written one leaf per
 * step */
#define TL_PAGES 16
static __thread struct { size_t index; uint64_t *page; size_t used; } tl_page[TL_PAGES];
static uint64_t *storage_block(Interner *t, size_t words) {
    uint64_t *b = malloc(words * sizeof(uint64_t));
    require(b, "out of memory");
    uint64_t *head = __atomic_load_n(&t->pages, __ATOMIC_RELAXED);
    do b[0] = (uint64_t)(uintptr_t)head;
    while (!__atomic_compare_exchange_n(&t->pages, &head, b, true, __ATOMIC_RELEASE, __ATOMIC_RELAXED));
    return b;
}
static uint64_t *storage_reserve(Interner *t, size_t n) {
    if (n + 1 > WPAGE_WORDS) return storage_block(t, n + 1) + 1;
    __typeof__(tl_page[0]) *c = &tl_page[t->index % TL_PAGES];
    if (c->index != t->index || c->used + n > WPAGE_WORDS) { c->index = t->index; c->page = storage_block(t, WPAGE_WORDS); c->used = 1; }
    uint64_t *dst = c->page + c->used;
    c->used += n;
    return dst;
}

/* a fresh trie node, zeroed (chunks are zeroed on creation; indices are
 * never reused); written privately and published by one release CAS */
static uint64_t new_node(Interner *t) {
    uint64_t idx = __atomic_add_fetch(&t->nnodes, 1, __ATOMIC_RELAXED);
    (void)chunked_at(&t->nodes, idx - 1);
    return idx;
}

/* ---- one unit: a small record ----
 * Descent of the compressed trie over (h, n, w); at an empty slot or a
 * separating leaf the record is reserved and copied privately (once), and
 * published by one CAS of a leaf or of a privately built split chain. A
 * failed CAS re-reads the same slot: a slot changes only empty → leaf →
 * inner node, so the work is bounded by the stream length (≤ 18 words). */
static uint64_t small_unit(Interner *t, const uint64_t *w, size_t n, bool *created, bool find_only) {
    require(n <= INTERN_SMALL, "a small record");
    uint64_t h = hash_words(w, n);
    uint64_t idx = 1, id = 0;
    for (size_t d = 0;;) {
        uint64_t *slot = &node_of(t, idx)->c[nib(h, n, w, d)];
        uint64_t x = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
        if (x && !(x & 1)) { idx = x >> 1; d++; continue; }
        if (x & 1) {
            uint64_t lid = x >> 1;
            if (rec_equal(rec_of(t, lid), h, w, n)) { if (created) *created = false; return lid; }
        }
        if (find_only) return 0;
        if (!id) {
            id = __atomic_add_fetch(&t->n, 1, __ATOMIC_ACQ_REL);
            uint64_t *dst = storage_reserve(t, n);
            if (n) memcpy(dst, w, n * sizeof(uint64_t));
            Rec *r = chunked_at(&t->recs, id - 1); r->w = dst; r->n = n; r->hash = h;
        }
        uint64_t put = (id << 1) | 1;
        if (x & 1) {
            /* split: a private chain from depth d+1 to the first nibble separating the two */
            const Rec *o = rec_of(t, x >> 1);
            uint64_t top = new_node(t), cur = top;
            size_t e = d + 1;
            for (;;) {
                unsigned a = nib(h, n, w, e), b = nib(o->hash, o->n, o->w, e);
                if (a != b) { node_of(t, cur)->c[a] = put; node_of(t, cur)->c[b] = x; break; }
                uint64_t nx = new_node(t); node_of(t, cur)->c[a] = nx << 1; cur = nx; e++;
            }
            put = top << 1;
        }
        uint64_t expect = x;
        if (__atomic_compare_exchange_n(slot, &expect, put, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
            __atomic_store_n(&rec_of(t, id)->live, 1, __ATOMIC_RELEASE);
            if (created) *created = true;
            return id;
        }
        /* the slot changed: re-read it at the same depth (the reserved id
         * and copy are kept for the next attempt, or stay unused) */
    }
}

/* ---- the canonical tree of a large record ---- */
static Interner *tree_of(Interner *t) {
    Interner *x = __atomic_load_n(&t->tree, __ATOMIC_ACQUIRE);
    if (x) return x;
    Interner *fresh = malloc(sizeof *fresh); require(fresh, "out of memory");
    interner_init(fresh);
    Interner *expect = NULL;
    if (__atomic_compare_exchange_n(&t->tree, &expect, fresh, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return fresh;
    interner_free(fresh); free(fresh);
    return expect;
}
const uint64_t *interner_tree_get(Interner *t, uint64_t id, size_t *n) { return interner_get(__atomic_load_n(&t->tree, __ATOMIC_ACQUIRE), id, n); }
uint64_t interner_flat_of(Interner *t, uint64_t root) {
    uint64_t f = __atomic_load_n(&rec_of(__atomic_load_n(&t->tree, __ATOMIC_ACQUIRE), root)->flat, __ATOMIC_ACQUIRE);
    return f == UINT64_MAX ? 0 : f;
}
uint64_t *interner_flat_reserve(Interner *t, size_t n) { return storage_reserve(t, n); }
uint64_t interner_flat_publish(Interner *t, uint64_t root, uint64_t *dst, size_t n) {
    uint64_t id = __atomic_add_fetch(&t->n, 1, __ATOMIC_ACQ_REL);
    Rec *r = chunked_at(&t->recs, id - 1); r->w = dst; r->n = n; r->hash = 0;
    __atomic_store_n(&r->live, 1, __ATOMIC_RELEASE);
    __atomic_store_n(&rec_of(__atomic_load_n(&t->tree, __ATOMIC_ACQUIRE), root)->flat, id, __ATOMIC_RELEASE);
    return id;
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
uint64_t wordbuf_intern(Interner *t, WordBuf *b) {
    uint64_t *w = malloc((b->n ? b->n : 1) * sizeof *w); require(w, "out of memory");
    size_t i = 0;
    for (WPage *p = b->head; p; p = p->next) for (size_t j = 0; j < WB_PAGE && i < b->n; j++) w[i++] = p->w[j];
    uint64_t id = interner_intern(t, w, i, NULL);
    free(w); wordbuf_clear(b);
    return id;
}
void wordbuf_clear(WordBuf *b) {
    for (WPage *p = b->head; p; ) { WPage *nx = p->next; wpage_release(p); p = nx; }
    wordbuf_init(b);
}

/* ---- the stepped construction ---- */
enum { P_SMALL = 0, P_LEAF, P_CARRY, P_FOLD, P_ROOT, P_FLAT, P_DONE };

void intern_begin(InternState *s, Interner *t, const uint64_t *arr, WordBuf *buf, size_t n) {
    memset(s, 0, sizeof *s);
    s->t = t; s->arr = arr; s->buf = buf; s->n = n;
    if (buf) { require(buf->n == n, "word buffer length"); s->pg = buf->head; }
    s->phase = n <= INTERN_SMALL ? P_SMALL : P_LEAF;
}
/* read the next m words of the source into out; a buffer page left behind is
 * released (at most one per read: m ≤ 16 < WB_PAGE) */
static void src_read(InternState *s, uint64_t *out, size_t m) {
    if (s->arr) { memcpy(out, s->arr + s->pos, m * sizeof(uint64_t)); s->pos += m; return; }
    for (size_t q = 0; q < m; q++, s->pos++) {
        if (s->pos >= s->pbase + WB_PAGE) { const WPage *nx = s->pg->next; wpage_release((WPage *)s->pg); s->pg = nx; s->pbase += WB_PAGE; }
        out[q] = s->pg->w[s->pos - s->pbase];
    }
    if (s->pos == s->n) {
        if (s->pg) wpage_release((WPage *)s->pg);
        s->pg = NULL; s->buf->head = s->buf->tail = NULL; s->buf->n = 0;
    }
}
static uint64_t tree_unit(InternState *s, const uint64_t *w, size_t n, bool *created) {
    return small_unit(tree_of(s->t), w, n, created, s->find);
}
static bool higher_levels(const InternState *s, unsigned i) { for (unsigned j = i + 1; j < TREE_LEVELS; j++) if (s->cnt[j]) return true; return false; }

int intern_advance(InternState *s, size_t budget) {
    for (size_t u = 0; u < budget; u++) {
        switch (s->phase) {
        case P_SMALL: {
            uint64_t w[INTERN_SMALL];
            if (s->n) src_read(s, w, s->n);
            else if (s->buf) { if (s->pg) wpage_release((WPage *)s->pg); s->pg = NULL; s->buf->head = s->buf->tail = NULL; s->buf->n = 0; }
            s->result = small_unit(s->t, w, s->n, &s->created, s->find);
            s->phase = P_DONE;
            return INTERN_DONE;
        }
        case P_LEAF: {
            uint64_t w[1 + TREE_FAN]; size_t m = s->n - s->pos < TREE_FAN ? s->n - s->pos : TREE_FAN;
            w[0] = TREE_LEAF; src_read(s, w + 1, m);
            uint64_t id = tree_unit(s, w, 1 + m, NULL);
            if (!id) { s->result = 0; s->phase = P_DONE; return INTERN_DONE; }      /* find: absent */
            s->lvl[0][s->cnt[0]++] = id;
            if (s->cnt[0] == TREE_FAN) { s->fi = 0; s->phase = P_CARRY; }
            else if (s->pos == s->n) { s->fi = 0; s->phase = P_FOLD; }
            break;
        }
        case P_CARRY: {
            /* level fi is full: one node one level up */
            unsigned i = s->fi; require(i + 1 < TREE_LEVELS, "record too long");
            uint64_t w[1 + TREE_FAN]; w[0] = TREE_NODE; memcpy(w + 1, s->lvl[i], TREE_FAN * sizeof(uint64_t));
            uint64_t id = tree_unit(s, w, 1 + TREE_FAN, NULL);
            if (!id) { s->result = 0; s->phase = P_DONE; return INTERN_DONE; }
            s->cnt[i] = 0; s->lvl[i + 1][s->cnt[i + 1]++] = id;
            if (s->cnt[i + 1] == TREE_FAN) s->fi = i + 1;
            else if (s->pos == s->n) { s->fi = 0; s->phase = P_FOLD; }
            else s->phase = P_LEAF;
            break;
        }
        case P_FOLD: {
            /* the partial levels bottom-up: each folds into one node carried
             * to the next level, until a level holds the only id left */
            for (;;) {
                unsigned i = s->fi;
                if (s->carry) { s->lvl[i][s->cnt[i]++] = s->carry; s->carry = 0; }
                if (!higher_levels(s, i) && s->cnt[i] == 1) { s->root = s->lvl[i][0]; s->phase = P_ROOT; break; }
                if (s->cnt[i]) break;
                s->fi++;
            }
            if (s->phase == P_ROOT) { u--; break; }          /* no unit was spent */
            {   unsigned i = s->fi;
                uint64_t w[1 + TREE_FAN]; w[0] = TREE_NODE; memcpy(w + 1, s->lvl[i], s->cnt[i] * sizeof(uint64_t));
                uint64_t id = tree_unit(s, w, 1 + s->cnt[i], NULL);
                if (!id) { s->result = 0; s->phase = P_DONE; return INTERN_DONE; }
                s->cnt[i] = 0; s->carry = id; s->fi = i + 1; }
            break;
        }
        case P_ROOT: {
            uint64_t w[3] = { TREE_ROOT, s->n, s->root };
            s->root = tree_unit(s, w, 3, &s->created);
            if (!s->root) { s->result = 0; s->phase = P_DONE; return INTERN_DONE; }
            if (s->find) { s->result = interner_flat_of(s->t, s->root); s->phase = P_DONE; return INTERN_DONE; }
            s->phase = P_FLAT;
            return INTERN_FLATTEN;
        }
        case P_FLAT: return INTERN_FLATTEN;
        case P_DONE: return INTERN_DONE;
        }
    }
    return s->phase == P_FLAT ? INTERN_FLATTEN : s->phase == P_DONE ? INTERN_DONE : INTERN_RUNNING;
}

uint64_t intern_complete(InternState *s) {
    require(s->phase == P_FLAT, "intern_complete before the tree is built");
    require(!intern_in_step, "a large record completed synchronously inside a counted step");
    Interner *t = s->t; uint64_t root = s->root;
    uint64_t id = interner_flat_of(t, root);
    if (!id) {
        FlattenHook h = __atomic_load_n(&flatten_hook, __ATOMIC_ACQUIRE);
        require(h, "a large record completed without the evaluator");
        id = h(t, root);                       /* the one owner: the intern.flatten producer keyed by (table, root) */
    }
    s->result = id; s->phase = P_DONE;
    return id;
}

uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created) {
    if (n <= INTERN_SMALL) return small_unit(t, w, n, created, false);
    require(!intern_in_step, "a record of %zu words interned synchronously inside a counted step (a stepped subroutine is required)", n);
    InternState s;
    intern_begin(&s, t, w, NULL, n);
    while (intern_advance(&s, SIZE_MAX) == INTERN_RUNNING) {}
    if (created) *created = s.created;
    return intern_complete(&s);
}

uint64_t interner_find(Interner *t, const uint64_t *w, size_t n) {
    if (n <= INTERN_SMALL) return small_unit(t, w, n, NULL, true);
    require(!intern_in_step, "a record of %zu words looked up synchronously inside a counted step", n);
    if (!__atomic_load_n(&t->tree, __ATOMIC_ACQUIRE)) return 0;
    InternState s;
    intern_begin(&s, t, w, NULL, n); s.find = true;
    while (intern_advance(&s, SIZE_MAX) == INTERN_RUNNING) {}
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



