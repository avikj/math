/* intern.h — structural interning of immutable word records.
 *
 * A record is a finite sequence of 64-bit words. Two records are equal
 * exactly when their word sequences are equal; hash equality alone is never
 * taken as equality (collisions are resolved by comparing the words).
 * Ids are dense, start at 1, and are never reused.
 *
 * Concurrency: find-or-insert is atomic (one mutex per table), so two threads
 * interning the same record obtain the same id. Record storage never moves:
 * a pointer returned by interner_get stays valid for the table's lifetime,
 * and a reader that has obtained an id through any synchronized channel may
 * read its record without taking the lock.
 */
#ifndef CUBICAL_INTERN_H
#define CUBICAL_INTERN_H

#include "common.h"
#include <pthread.h>

#define CHUNK_BITS 11
#define CHUNK_SIZE ((size_t)1 << CHUNK_BITS)
#define MAX_CHUNKS ((size_t)1 << 15)

/* Non-moving, lazily chunked array of fixed-size elements. Element i lives
 * at a stable address once created. Creation of a chunk is done under the
 * caller's lock; the chunk pointer is published with release semantics so a
 * reader that learned of index i through a synchronized channel can read it
 * without the lock. */
typedef void *(*ChunkAlloc)(size_t bytes, void *ctx);   /* §94: an arena-backed, pre-cleared chunk supplier (work.c) */
typedef struct {
    void *dir[MAX_CHUNKS];
    size_t elem;
    ChunkAlloc alloc; void *alloc_ctx;   /* NULL: calloc (the kernel's own tables) */
} Chunked;
void chunked_set_alloc(Chunked *c, ChunkAlloc alloc, void *ctx);

void chunked_init(Chunked *c, size_t elem);
void chunked_free(Chunked *c);
void *chunked_at(Chunked *c, size_t i);           /* creates the chunk if needed (zeroed) */
void *chunked_get(const Chunked *c, size_t i);    /* read-only: chunk must exist */
void *chunked_peek(const Chunked *c, size_t i);   /* read-only: NULL when the chunk does not exist yet */

typedef struct { uint64_t *w; size_t n; uint64_t hash; } Rec;

typedef struct {
    Chunked recs;             /* Rec per id (index id-1) */
    size_t n;                 /* records so far (read under lock, or as a snapshot) */
    uint64_t *slots;          /* open addressing table of ids (0 = empty), under lock */
    size_t nslots;
    uint64_t *old; size_t old_n, cursor;   /* §94: a growth in progress — the previous array, migrated CHUNK_WORDS slots per operation */
    pthread_mutex_t mu;
} Interner;

void interner_init(Interner *t);
void interner_free(Interner *t);
/* returns id; *created set to true when the record did not exist before */
uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created);
/* lookup without creating; returns 0 when absent */
uint64_t interner_find(Interner *t, const uint64_t *w, size_t n);
const uint64_t *interner_get(const Interner *t, uint64_t id, size_t *n);
size_t interner_count(Interner *t);

/* Small key→value hash map on word tuples (memo tables); thread-safe. */
typedef struct {
    Interner keys;
    Chunked vals;             /* uint64_t per key id */
} WordMap;

void wordmap_init(WordMap *m);
void wordmap_free(WordMap *m);
bool wordmap_get(WordMap *m, const uint64_t *k, size_t n, uint64_t *out);
void wordmap_put(WordMap *m, const uint64_t *k, size_t n, uint64_t v);

#endif
