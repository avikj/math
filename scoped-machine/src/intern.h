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
#include "radix.h"
#include "kframe.h"

#define CHUNK_BITS 11
#define CHUNK_SIZE ((size_t)1 << CHUNK_BITS)
/* The pointer index covers size_t; there is no fixed chunk count. */

/* Non-moving, lazily chunked array of fixed-size elements over a full-width
 * sparse directory; there is no fixed maximum chunk count. Element i lives
 * at a stable address once created. Creation of a chunk is done under the
 * caller's lock; the chunk pointer is published with release semantics so a
 * reader that learned of index i through a synchronized channel can read it
 * without the lock. */
typedef void *(*ChunkAlloc)(size_t bytes, void *ctx);   /* Returns an owned arena block; chunked_free releases it. */
typedef struct {
    Radix dir;
    size_t elem;
    ChunkAlloc alloc; void *alloc_ctx;   /* NULL: calloc (the kernel's own tables) */
} Chunked;
void chunked_set_alloc(Chunked *c, ChunkAlloc alloc, void *ctx);
void *chunk_uncleared(size_t bytes, void *ctx);   /* a supplier for tables whose slots are written before they are published: one arena block, never cleared */

void chunked_init(Chunked *c, size_t elem);
void chunked_free(Chunked *c);
void chunked_release_chunk(Chunked *c, size_t chunk);   /* retire one consumed chunk (index >> CHUNK_BITS) */
void *chunked_at(Chunked *c, size_t i);           /* creates the chunk if needed (zeroed) */
#define chunked_prepare_PARAMS(X) X(Chunked *, c) X(size_t, i)
KF_PROTO(chunked_prepare, void, chunked_prepare_PARAMS);   /* the chunk of i created outside every lock, a reused block cleared one word per transition */
void *chunked_get(const Chunked *c, size_t i);    /* read-only: chunk must exist */
void *chunked_peek(const Chunked *c, size_t i);   /* read-only: NULL when the chunk does not exist yet */

typedef struct { uint64_t *w; size_t n; uint64_t hash; } Rec;

typedef struct {
    Chunked recs;             /* Rec per id (index id-1) */
    size_t n;                 /* records so far (read under lock, or as a snapshot) */
    uint64_t *slots;          /* open addressing table of ids (0 = empty), under lock */
    size_t nslots;
    uint64_t *old; size_t old_n, cursor;   /* §94: a growth in progress — the previous array, migrated CHUNK_WORDS slots per operation */
    uint64_t gen;                          /* bumped when an array is replaced or released: a probe cursor is valid for one generation */
    uint64_t placed;                       /* migration placements into the current array (a scanned chain end may have been filled) */
    uint64_t moving; size_t mprobe;        /* the old entry being placed by the migration and its probe position */
    pthread_mutex_t mu;
} Interner;

void interner_init(Interner *t);
void interner_free(Interner *t);
/* returns id; *created set to true when the record did not exist before */
uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created);
/* lookup without creating; returns 0 when absent */
uint64_t interner_find(Interner *t, const uint64_t *w, size_t n);
const uint64_t *interner_get(const Interner *t, uint64_t id, size_t *n);
/* frame families (kframe.h): the same procedures as resumable frames */
#define interner_find_PARAMS(X) X(Interner *, t) X(const uint64_t *, w) X(size_t, n)
#define interner_intern_PARAMS(X) X(Interner *, t) X(const uint64_t *, w) X(size_t, n) X(bool *, created)
KF_PROTO(interner_find, uint64_t, interner_find_PARAMS);
KF_PROTO(interner_intern, uint64_t, interner_intern_PARAMS);
/* interning with a publication: pub(id, ctx) runs inside the insertion's
 * locked section, before the new id becomes reachable by any probe (its
 * writes — the record's side data — happen before every lookup that finds
 * the id); constant work, never a suspension */
typedef void (*InternPub)(uint64_t id, void *ctx);
#define interner_intern_pub_PARAMS(X) X(Interner *, t) X(const uint64_t *, w) X(size_t, n) X(bool *, created) X(InternPub, pub) X(void *, pub_ctx)
KF_PROTO(interner_intern_pub, uint64_t, interner_intern_pub_PARAMS);
uint64_t interner_intern_pub(Interner *t, const uint64_t *w, size_t n, bool *created, InternPub pub, void *pub_ctx);
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
#define wordmap_get_PARAMS(X) X(WordMap *, m) X(const uint64_t *, k) X(size_t, n) X(uint64_t *, out)
#define wordmap_put_PARAMS(X) X(WordMap *, m) X(const uint64_t *, k) X(size_t, n) X(uint64_t, v)
KF_PROTO(wordmap_get, bool, wordmap_get_PARAMS);
KF_PROTO(wordmap_put, void, wordmap_put_PARAMS);

#endif
