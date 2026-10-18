#include "intern.h"
#include "fine.h"
#include "arena.h"

/* ---- chunked arrays ---- */
void chunked_init(Chunked *c, size_t elem) { radix_init(&c->dir); c->elem = elem; c->alloc = NULL; c->alloc_ctx = NULL; }
void chunked_set_alloc(Chunked *c, ChunkAlloc alloc, void *ctx) { c->alloc = alloc; c->alloc_ctx = ctx; }
void *chunk_uncleared(size_t bytes, void *ctx) { (void)ctx; return arena_alloc((bytes + 7) / 8, NULL); }
/* both suppliers return owned arena chunks: a spare ceases to own its chunk
 * when it hands it to this table; release before dropping the directory */
static void chunk_release(void *p, void *ctx) { Chunked *c = ctx; arena_release(p, (CHUNK_SIZE * c->elem + 7) / 8); }
void chunked_free(Chunked *c) { radix_free(&c->dir, chunk_release, c); }
void *chunked_at(Chunked *c, size_t i) {
    require(c->elem <= (SIZE_MAX - 7) / CHUNK_SIZE, "chunk allocation size overflow");
    void **slot = radix_slot(&c->dir, i >> CHUNK_BITS, true);
    void *p = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
    if (!p) {
        void *fresh = c->alloc ? c->alloc(CHUNK_SIZE * c->elem, c->alloc_ctx) : arena_alloc_zero((CHUNK_SIZE * c->elem + 7) / 8, NULL);   /* §94: a kernel chunk is a zero block of the arena — no clearing, possibly under a lock */
        require(fresh, "out of memory"); void *expected = NULL;
        if (__atomic_compare_exchange_n(slot, &expected, fresh, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) p = fresh;
        else { arena_release(fresh, (CHUNK_SIZE * c->elem + 7) / 8); p = expected; }   /* the losing candidate is retired */
    }
    return (char *)p + (i & (CHUNK_SIZE - 1)) * c->elem;
}
/* the chunk of element i created ahead of a locked section (outside every
 * lock): a reused block is cleared one word per transition (arena_zero) */
KF_DECL_EXT_DROP(chunked_prepare, void, chunked_prepare_PARAMS, chunked_prepare_drop, void **slot; uint64_t *fresh;)
static void chunked_prepare_drop(chunked_prepare_F *F) { if (F->fresh) arena_release(F->fresh, (CHUNK_SIZE * F->c->elem + 7) / 8); F->fresh = NULL; }
KF_STEP(chunked_prepare) {
    KF_BEGIN(chunked_prepare);
    if (F->c->alloc) { (void)chunked_at(F->c, F->i); KF_RETV(); }   /* a table with its own supplier */
    F->slot = radix_slot(&F->c->dir, F->i >> CHUNK_BITS, true);
    if (__atomic_load_n(F->slot, __ATOMIC_ACQUIRE)) KF_RETV();
    KF_CALL(arena_zero, &F->fresh, (CHUNK_SIZE * F->c->elem + 7) / 8);
    { void *expected = NULL;
      if (!__atomic_compare_exchange_n(F->slot, &expected, (void *)F->fresh, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) arena_release(F->fresh, (CHUNK_SIZE * F->c->elem + 7) / 8);   /* the losing candidate is retired */
      F->fresh = NULL; }
    KF_RETV();
    KF_END;
}
/* V21 R4: a consumed chunk of a monotone table (a queue's prefix) is retired:
 * one directory slot exchanged, one arena release */
void chunked_release_chunk(Chunked *c, size_t chunk) {
    void **slot = radix_slot(&c->dir, chunk, false); if (!slot) return;
    void *p = __atomic_exchange_n(slot, NULL, __ATOMIC_ACQ_REL);
    if (p) arena_release(p, (CHUNK_SIZE * c->elem + 7) / 8);
}
void *chunked_get(const Chunked *c, size_t i) {
    void *p = radix_get(&c->dir, i >> CHUNK_BITS);
    require(p, "chunked read of a missing element");
    return (char *)p + (i & (CHUNK_SIZE - 1)) * c->elem;
}
void *chunked_peek(const Chunked *c, size_t i) {
    void *p = radix_get(&c->dir, i >> CHUNK_BITS);
    return p ? (char *)p + (i & (CHUNK_SIZE - 1)) * c->elem : NULL;
}

/* ---- interner ---- */
/* the key-sized loops of the interner are frame families (kframe.h): one
 * transition per word, a suspension point after each */
#define hash_words_PARAMS(X) X(const uint64_t *, w) X(size_t, n)
KF_DECL(hash_words, uint64_t, hash_words_PARAMS, uint64_t h; size_t i;)
KF_STEP(hash_words) {
    KF_BEGIN(hash_words);
    F->h = 1469598103934665603ULL;
    for (F->i = 0; F->i < F->n; F->i++) {
        uint64_t x = F->w[F->i]; fine_bump(FC_INTERN_WORDS_HASHED);   /* one transition per word (unlocked) */
        for (int b = 0; b < 8; b++) { F->h ^= (x & 0xff); F->h *= 1099511628211ULL; x >>= 8; }
        KF_SAFE();
    }
    F->h ^= (uint64_t)F->n; F->h *= 1099511628211ULL;
    KF_RET(F->h ? F->h : 1);
    KF_END;
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

#define rec_equal_PARAMS(X) X(const Interner *, t) X(uint64_t, id) X(uint64_t, h) X(const uint64_t *, w) X(size_t, n)
KF_DECL(rec_equal, bool, rec_equal_PARAMS, Rec *r; size_t i;)
KF_STEP(rec_equal) {
    KF_BEGIN(rec_equal);
    F->r = rec_of(F->t, F->id);
    if (F->r->hash != F->h || F->r->n != F->n) KF_RET(false);
    /* a hash hit is not equality: every word is compared (§89.2) */
    for (F->i = 0; F->i < F->n; F->i++) { fine_bump(FC_INTERN_WORD_COMPARES); if (F->r->w[F->i] != F->w[F->i]) KF_RET(false); KF_SAFE(); }
    KF_RET(true);
    KF_END;
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
#define match_unlocked_PARAMS(X) X(const Interner *, t) X(const uint64_t *, cand) X(size_t, k) X(uint64_t, h) X(const uint64_t *, w) X(size_t, n)
KF_DECL(match_unlocked, uint64_t, match_unlocked_PARAMS, size_t i; bool eq;)
KF_STEP(match_unlocked) {
    KF_BEGIN(match_unlocked);
    for (F->i = 0; F->i < F->k; F->i++) { KF_CALL(rec_equal, &F->eq, F->t, F->cand[F->i], F->h, F->w, F->n); if (F->eq) KF_RET(F->cand[F->i]); }
    KF_RET(0);
    KF_END;
}
/* scan the chain for w; 0 when absent. On return with 0, *seen_out is the
 * record count and *gen_out the generation of the completing section */
#define scan_PARAMS(X) X(Interner *, t) X(uint64_t, h) X(const uint64_t *, w) X(size_t, n) X(uint64_t, above) X(uint64_t *, seen_out) X(uint64_t *, gen_out) X(size_t *, empty_out) X(uint64_t *, placed_out)
KF_DECL(scan, uint64_t, scan_PARAMS, Cursor cu; uint64_t cand[CAND_MAX]; bool complete; size_t k; uint64_t gen, id;)
KF_STEP(scan) {
    KF_BEGIN(scan);
    for (;;) {
        pthread_mutex_lock(&F->t->mu);
        F->k = probe_section(F->t, &F->cu, F->h, F->n, F->above, F->cand, &F->complete);
        F->gen = F->t->gen;
        pthread_mutex_unlock(&F->t->mu);
        KF_SAFE();   /* between two locked sections: a spent grant suspends here */
        KF_CALL(match_unlocked, &F->id, F->t, F->cand, F->k, F->h, F->w, F->n);
        if (F->id) KF_RET(F->id);
        if (F->complete) {   /* the snapshot of the section that found the chain end: a record published after it is a newcomer */
            *F->seen_out = F->cu.seen0; *F->gen_out = F->gen; if (F->empty_out) *F->empty_out = F->cu.empty0; if (F->placed_out) *F->placed_out = F->cu.placed0;
            KF_RET(0);
        }
    }
    KF_END;
}
KF_DECL_EXT(interner_find, uint64_t, interner_find_PARAMS, uint64_t h, seen, gen, id;)
KF_STEP(interner_find) {
    KF_BEGIN(interner_find);
    KF_CALL(hash_words, &F->h, F->w, F->n);
    KF_CALL(scan, &F->id, F->t, F->h, F->w, F->n, 0, &F->seen, &F->gen, NULL, NULL);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(interner_find, uint64_t, interner_find_PARAMS, interner_find(Interner *t, const uint64_t *w, size_t n))

KF_DECL_EXT(interner_intern_pub, uint64_t, interner_intern_pub_PARAMS, uint64_t h, seen, gen, placed, id, above, dup; size_t empty; uint64_t *copy; size_t i;)
KF_STEP(interner_intern_pub) {
    KF_BEGIN(interner_intern_pub);
    KF_CALL(hash_words, &F->h, F->w, F->n);
    KF_CALL(scan, &F->id, F->t, F->h, F->w, F->n, 0, &F->seen, &F->gen, &F->empty, &F->placed);
    if (F->id) { if (F->created) *F->created = false; KF_RET(F->id); }
    /* a new record: prepared outside the lock, one transition per word; the
     * record chunk the new id will need is created outside the lock too */
    F->copy = malloc((F->n ? F->n : 1) * sizeof(uint64_t)); require(F->copy, "out of memory");
    for (F->i = 0; F->i < F->n; F->i++) { F->copy[F->i] = F->w[F->i]; fine_bump(FC_INTERN_WORDS_COPIED); KF_SAFE(); }
    F->i = __atomic_load_n(&F->t->n, __ATOMIC_RELAXED); KF_CALL(chunked_prepare, NULL, &F->t->recs, F->i); KF_CALL(chunked_prepare, NULL, &F->t->recs, F->i + 1);
    for (;;) {
        pthread_mutex_lock(&F->t->mu);
        if (F->t->n == F->seen && F->t->gen == F->gen && F->t->placed == F->placed) break;   /* nothing published or migrated since the complete scan: insert */
        F->above = F->t->gen == F->gen ? F->seen : 0;   /* a new generation: rescan everything; else only the newcomers (a migrated record was
                                                           compared where the scan met it in the old array, which a migration does not clear) */
        pthread_mutex_unlock(&F->t->mu);
        KF_CALL(scan, &F->dup, F->t, F->h, F->w, F->n, F->above, &F->seen, &F->gen, &F->empty, &F->placed);
        if (F->dup) { free(F->copy); F->copy = NULL; if (F->created) *F->created = false; KF_RET(F->dup); }
    }
    {
        Interner *t = F->t;
        Rec *r = chunked_at(&t->recs, t->n);
        r->w = F->copy; r->n = F->n; r->hash = F->h; F->copy = NULL;
        F->id = (uint64_t)__atomic_add_fetch(&t->n, 1, __ATOMIC_RELEASE);   /* the count is read unlocked (relaxed) by the chunk pre-creation */
        if (F->pub) F->pub(F->id, F->pub_ctx);   /* the side data, before the slot write publishes the id */
        require(!t->slots[F->empty], "interner: the scanned chain end is taken");   /* nothing was published or migrated since the complete scan: the chain's empty slot is where the scan found it — one write */
        t->slots[F->empty] = F->id;
        if (t->n * 2 > t->nslots) grow_begin(t);   /* one fresh allocation; the migration proceeds a chunk per operation */
        pthread_mutex_unlock(&t->mu);
    }
    if (F->created) *F->created = true;
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(interner_intern_pub, uint64_t, interner_intern_pub_PARAMS, interner_intern_pub(Interner *t, const uint64_t *w, size_t n, bool *created, InternPub pub, void *pub_ctx))
KF_DECL_EXT(interner_intern, uint64_t, interner_intern_PARAMS, uint64_t id;)
KF_STEP(interner_intern) { KF_BEGIN(interner_intern); KF_CALL(interner_intern_pub, &F->id, F->t, F->w, F->n, F->created, NULL, NULL); KF_RET(F->id); KF_END; }
KF_SYNC_DEF(interner_intern, uint64_t, interner_intern_PARAMS, interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created))

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

KF_DECL_EXT(wordmap_get, bool, wordmap_get_PARAMS, uint64_t id;)
KF_STEP(wordmap_get) {
    KF_BEGIN(wordmap_get);
    KF_CALL(interner_find, &F->id, &F->m->keys, F->k, F->n);
    if (!F->id) KF_RET(false);
    {
        /* The key becomes discoverable before the writer stores its value: an
         * absent value chunk, like a zero value, means "not yet published". */
        uint64_t *slot = chunked_peek(&F->m->vals, F->id - 1);
        if (!slot) KF_RET(false);
        uint64_t v = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
        if (!v) KF_RET(false);            /* key created, value not yet published */
        *F->out = v;
    }
    KF_RET(true);
    KF_END;
}
KF_SYNC_DEF(wordmap_get, bool, wordmap_get_PARAMS, wordmap_get(WordMap *m, const uint64_t *k, size_t n, uint64_t *out))
KF_DECL_EXT(wordmap_put, void, wordmap_put_PARAMS, uint64_t id;)
KF_STEP(wordmap_put) {
    KF_BEGIN(wordmap_put);
    require(F->v != 0, "wordmap values are non-zero handles");
    KF_CALL(interner_intern, &F->id, &F->m->keys, F->k, F->n, NULL);
    KF_CALL(chunked_prepare, NULL, &F->m->vals, F->id - 1);
    __atomic_store_n((uint64_t *)chunked_at(&F->m->vals, F->id - 1), F->v, __ATOMIC_RELEASE);
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(wordmap_put, wordmap_put_PARAMS, wordmap_put(WordMap *m, const uint64_t *k, size_t n, uint64_t v))
