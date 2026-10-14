/* intern.h — structural interning of immutable word records.
 *
 * A record is a finite sequence of 64-bit words. Two records are equal
 * exactly when their word sequences are equal; hash equality alone is never
 * taken as equality (collisions are resolved by comparing the words).
 * Ids are dense, start at 1, and are never reused.
 */
#ifndef CUBICAL_INTERN_H
#define CUBICAL_INTERN_H

#include "common.h"

typedef struct {
    uint64_t *store;          /* concatenated words of all records */
    size_t store_len, store_cap;
    size_t *off, *len;        /* per id (index id-1) */
    uint64_t *hash;           /* per id */
    size_t n, cap;
    uint64_t *slots;          /* open addressing table of ids (0 = empty) */
    size_t nslots;
} Interner;

void interner_init(Interner *t);
void interner_free(Interner *t);
/* returns id; *created set to true when the record did not exist before */
uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created);
/* lookup without creating; returns 0 when absent */
uint64_t interner_find(const Interner *t, const uint64_t *w, size_t n);
const uint64_t *interner_get(const Interner *t, uint64_t id, size_t *n);
static inline size_t interner_count(const Interner *t) { return t->n; }

/* Small key→value hash map on word tuples (memo tables). */
typedef struct {
    Interner keys;
    uint64_t *vals;
    size_t cap;
} WordMap;

void wordmap_init(WordMap *m);
void wordmap_free(WordMap *m);
bool wordmap_get(WordMap *m, const uint64_t *k, size_t n, uint64_t *out);
void wordmap_put(WordMap *m, const uint64_t *k, size_t n, uint64_t v);

#endif
