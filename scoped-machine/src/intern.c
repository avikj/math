#include "intern.h"
#include "fine.h"
#include "arena.h"
#include "kcont.h"

/* ---- chunked arrays ---- */
void chunked_init(Chunked *c, size_t elem) { memset(c->dir, 0, sizeof c->dir); c->elem = elem; c->alloc = NULL; c->alloc_ctx = NULL; }
void chunked_set_alloc(Chunked *c, ChunkAlloc alloc, void *ctx) { c->alloc = alloc; c->alloc_ctx = ctx; }
void chunked_free(Chunked *c) {
    /* Both suppliers return owned arena chunks. A spare ceases to own its
     * chunk when it hands it to this table; release before dropping the directory. */
    for (size_t k = 0; k < MAX_CHUNKS; k++)
        if (c->dir[k]) arena_release(c->dir[k], (CHUNK_SIZE * c->elem + 7) / 8);
    memset(c->dir, 0, sizeof c->dir);
}
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
    t->old = NULL; t->old_n = t->cursor = 0; t->moving = 0; t->mprobe = 0; t->gen = 1; t->placed = 0;
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
static void grow_begin(Interner *t) {
    if (t->old) return;
    t->old = t->slots; t->old_n = t->nslots; t->cursor = 0;
    t->nslots *= 2; t->slots = arena_alloc_zero(t->nslots, NULL); t->gen++;
}
/* one migration step: at most MIGRATE_CHUNK source-slot visits plus probes in
 * total; the entry being placed and its probe position are retained between
 * steps (`moving`, `mprobe`), so a long collision chain spans several steps */
static void migrate_chunk(Interner *t) {
    if (!t->old) return;
    size_t budget = MIGRATE_CHUNK;
    while (budget) {
        if (!t->moving) {
            if (t->cursor >= t->old_n) break;
            uint64_t id = t->old[t->cursor++]; budget--;
            if (!id) continue;
            t->moving = id; t->mprobe = rec_of(t, id)->hash & (t->nslots - 1);
            continue;
        }
        fine_bump(FC_INTERN_PROBES); budget--;
        if (t->slots[t->mprobe]) { t->mprobe = (t->mprobe + 1) & (t->nslots - 1); continue; }
        t->slots[t->mprobe] = t->moving; t->moving = 0; t->placed++; fine_bump(FC_INTERN_SLOTS_RELOCATED);
    }
    if (t->cursor >= t->old_n && !t->moving) { arena_release(t->old, t->old_n); t->old = NULL; t->old_n = t->cursor = 0; t->gen++; }
}

/* §94: the lock is held for probes and the publication only. Hashing, the
 * word comparisons (records are immutable at stable addresses once
 * published) and the copy of a new record happen outside it, so a kernel
 * continuation suspends between words. Candidates found under the lock (equal
 * hash and length) are compared after it; a candidate published by another
 * thread between the two lock sections is compared under the second. The
 * slot-array growth (`grow_slots`) remains one locked relocation, amortized
 * and counted (FC_INTERN_SLOTS_RELOCATED). */
/* §94: a probe is a cursor. One locked section walks at most PROBE_CHUNK
 * slots of one array from the cursor (after one migration step of a growth
 * in progress), collecting the ids whose hash and length match; the words of
 * those candidates are compared outside the lock (records are immutable at
 * stable addresses). The cursor is valid for the table's generation
 * (`gen`: bumped when an array is replaced or released); a stale cursor
 * restarts the scan. A scan is complete when the chain's empty slot was
 * reached in the current array and, during a growth, in the old array too.
 * Insertion happens under the lock only after a complete scan during which no
 * record was published (`n` unchanged) and the generation did not change;
 * otherwise the scan resumes over the newcomers (ids above the last count),
 * again outside the lock. No section hashes, compares or copies a record. */
#define CAND_MAX 8
#define PROBE_CHUNK 32
typedef struct { unsigned arr; size_t p; uint64_t gen; bool started; size_t empty0; uint64_t seen0, placed0; } Cursor;   /* seen0/placed0: the count and placements in the section that found empty0 */   /* arr 0 = current array, 1 = old; empty0 = the chain's empty slot in the current array */
/* one locked section: ≤ PROBE_CHUNK probes; returns candidates in cand[0..k); *complete when the scan is finished */
static size_t probe_section(Interner *t, Cursor *cu, uint64_t h, size_t n, uint64_t above, uint64_t *cand, bool *complete) {
    migrate_chunk(t);
    if (!cu->started || cu->gen != t->gen) { cu->arr = 0; cu->p = h & (t->nslots - 1); cu->gen = t->gen; cu->started = true; }
    size_t k = 0; *complete = false;
    for (size_t steps = 0; steps < PROBE_CHUNK; steps++) {
        const uint64_t *slots = cu->arr == 0 ? t->slots : t->old; size_t nslots = cu->arr == 0 ? t->nslots : t->old_n;
        if (!slots) { *complete = true; return k; }
        uint64_t id = slots[cu->p]; fine_bump(FC_INTERN_PROBES);
        if (!id) {   /* the chain ends in this array */
            if (cu->arr == 0) { cu->empty0 = cu->p; cu->seen0 = t->n; cu->placed0 = t->placed; if (t->old) { cu->arr = 1; cu->p = h & (t->old_n - 1); continue; } }
            *complete = true; return k;
        }
        cu->p = (cu->p + 1) & (nslots - 1);
        Rec *r = rec_of(t, id);
        if (r->hash == h && r->n == n && id > above) { cand[k++] = id; if (k == CAND_MAX) return k; }   /* the section ends early: the candidates are compared first */
    }
    return k;
}
static uint64_t match_unlocked(const Interner *t, const uint64_t *cand, size_t k, uint64_t h, const uint64_t *w, size_t n) {
    for (size_t i = 0; i < k; i++) if (rec_equal(t, cand[i], h, w, n)) return cand[i];
    return 0;
}
/* scan the chain for w; 0 when absent. On return with 0, *seen_out is the
 * record count and *gen_out the generation of the completing section */
static uint64_t scan(Interner *t, uint64_t h, const uint64_t *w, size_t n, uint64_t above, uint64_t *seen_out, uint64_t *gen_out, size_t *empty_out, uint64_t *placed_out) {
    Cursor cu = { 0, 0, 0, false, 0, 0, 0 }; uint64_t cand[CAND_MAX];
    for (;;) {
        bool complete;
        pthread_mutex_lock(&t->mu);
        size_t k = probe_section(t, &cu, h, n, above, cand, &complete);
        uint64_t gen = t->gen;
        pthread_mutex_unlock(&t->mu);
        kc_safepoint();   /* between two locked sections: a spent grant yields here */
        uint64_t id = match_unlocked(t, cand, k, h, w, n);
        if (id) return id;
        if (complete) { *seen_out = cu.seen0; *gen_out = gen; if (empty_out) *empty_out = cu.empty0; if (placed_out) *placed_out = cu.placed0; return 0; }   /* the snapshot of the section that found the chain end: a record published after it is a newcomer */
    }
}
uint64_t interner_find(Interner *t, const uint64_t *w, size_t n) {
    uint64_t h = hash_words(w, n), seen, gen;
    return scan(t, h, w, n, 0, &seen, &gen, NULL, NULL);
}

uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created) {
    uint64_t h = hash_words(w, n), seen, gen, placed; size_t empty;
    uint64_t id = scan(t, h, w, n, 0, &seen, &gen, &empty, &placed);
    if (id) { if (created) *created = false; return id; }
    /* a new record: prepared outside the lock, one transition per word; the
     * record chunk the new id will need is created outside the lock too */
    uint64_t *copy = malloc((n ? n : 1) * sizeof(uint64_t)); require(copy, "out of memory");
    for (size_t i = 0; i < n; i++) { copy[i] = w[i]; fine_bump(FC_INTERN_WORDS_COPIED); }
    { size_t at = __atomic_load_n(&t->n, __ATOMIC_RELAXED); (void)chunked_at(&t->recs, at); (void)chunked_at(&t->recs, at + 1); }
    for (;;) {
        pthread_mutex_lock(&t->mu);
        if (t->n == seen && t->gen == gen && t->placed == placed) break;   /* nothing published or migrated since the complete scan: insert */
        uint64_t above = t->gen == gen ? seen : 0;   /* a new generation: rescan everything; else only the newcomers (a migrated record was
                                                        compared where the scan met it in the old array, which a migration does not clear) */
        pthread_mutex_unlock(&t->mu);
        uint64_t dup = scan(t, h, w, n, above, &seen, &gen, &empty, &placed);
        if (dup) { free(copy); if (created) *created = false; return dup; }
    }
    Rec *r = chunked_at(&t->recs, t->n);
    r->w = copy; r->n = n; r->hash = h;
    id = (uint64_t)__atomic_add_fetch(&t->n, 1, __ATOMIC_RELEASE);   /* the count is read unlocked (relaxed) by the chunk pre-creation */
    require(!t->slots[empty], "interner: the scanned chain end is taken");   /* nothing was published or migrated since the complete scan: the chain's empty slot is where the scan found it — one write */
    t->slots[empty] = id;
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
