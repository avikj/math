/* intern.h — structural interning of immutable word records.
 *
 * A record is a finite sequence of 64-bit words. Two records are equal
 * exactly when their word sequences are equal; hash equality alone is never
 * taken as equality (collisions are resolved by comparing the words).
 * Ids are dense, start at 1, and are never reused.
 *
 * Concurrency: insertion is serialized by one mutex per table, with a
 * critical section bounded by the key width; lookup takes no lock. Two
 * threads interning the same record obtain the same id. Record storage never moves:
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
typedef struct {
    void *dir[MAX_CHUNKS];
    size_t elem;
} Chunked;

void chunked_init(Chunked *c, size_t elem);
void chunked_free(Chunked *c);
void *chunked_at(Chunked *c, size_t i);           /* creates the chunk if needed (zeroed) */
void *chunked_get(const Chunked *c, size_t i);    /* read-only: chunk must exist */
void *chunked_peek(const Chunked *c, size_t i);   /* read-only: NULL when the chunk does not exist yet */

typedef struct { uint64_t *w; size_t n; uint64_t hash; } Rec;

/* A record's search key is the word stream (hash, n, w[0..n-1]). Records are
 * found through a 16-ary radix trie over the nibbles of that stream, with a
 * leaf at the first nibble that separates a record from every other: distinct
 * records have distinct streams, so a lookup or an insertion visits at most
 * 16·(n+2) nodes — a bound fixed by the key width, independent of the number
 * of records and of hash collisions. The trie only grows; no rehash exists.
 * Slot word: 0 empty, (id<<1)|1 a leaf, idx<<1 an inner node. */
typedef struct { uint64_t c[16]; } TrieNode;

#define WPAGE_WORDS 4096
typedef struct {
    Chunked recs;             /* Rec per id (index id-1) */
    Chunked nodes;            /* TrieNode per index-1; index 1 is the root */
    size_t n;                 /* records so far (atomic) */
    size_t nnodes;            /* under mu */
    uint64_t *page; size_t page_used;   /* current word page (under mu) */
    uint64_t *pages;          /* linked list (word 0 = previous) of every page and oversized record */
    pthread_mutex_t mu;       /* insertion only; lookup is lock-free */
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
