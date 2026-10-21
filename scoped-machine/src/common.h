/* common.h — handle types, small vector and arena helpers.
 *
 * Handles are opaque 64-bit identities of interned immutable records.
 * 0 is never a valid handle.
 */
#ifndef CUBICAL_COMMON_H
#define CUBICAL_COMMON_H

#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>

typedef uint64_t TermVarId;
typedef uint64_t DimVarId;
typedef uint64_t RefId;
typedef uint64_t MapId;
typedef uint64_t IntervalId;
typedef uint64_t FaceId;
typedef uint64_t SymbolId;
typedef uint64_t DimSetId;   /* interned sorted set of DimVarId */
typedef uint64_t VarSetId;   /* interned sorted set of TermVarId */
typedef uint32_t BinderSlot;
typedef uint32_t FieldIndex;

#define NO_SLOT ((BinderSlot)0xFFFFFFFFu)
#define NO_FIELD ((FieldIndex)0xFFFFFFFFu)

/* ---- fatal errors (host failures, never object-language values) ---- */
#define die(...) do { fprintf(stderr, "fatal: "); fprintf(stderr, __VA_ARGS__); \
    fprintf(stderr, "\n"); abort(); } while (0)

#define require(cond, ...) do { if (!(cond)) die(__VA_ARGS__); } while (0)

/* ---- limb arithmetic: one 64-bit digit with its carry / borrow bit ---- */
static inline uint64_t add_limb(uint64_t x, uint64_t y, uint64_t *carry) { uint64_t s = x + y, t = s + *carry; *carry = (s < x) | (t < s); return t; }
static inline uint64_t sub_limb(uint64_t x, uint64_t y, uint64_t *borrow) { uint64_t d = x - y, t = d - *borrow; *borrow = (x < y) | (d < *borrow); return t; }

/* ---- growable word buffer ---- */
typedef struct {
    uint64_t *w;
    size_t n, cap;
} Words;

static inline void words_init(Words *b) { b->w = NULL; b->n = 0; b->cap = 0; }
static inline void words_free(Words *b) { free(b->w); b->w = NULL; b->n = b->cap = 0; }
static inline void words_reserve(Words *b, size_t extra) {
    if (b->n + extra > b->cap) {
        size_t nc = b->cap ? b->cap * 2 : 16;
        while (nc < b->n + extra) nc *= 2;
        b->w = (uint64_t *)realloc(b->w, nc * sizeof(uint64_t));
        require(b->w, "out of memory");
        b->cap = nc;
    }
}
static inline void words_push(Words *b, uint64_t x) { words_reserve(b, 1); b->w[b->n++] = x; }


static inline int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y ? 1 : 0;
}

/* sort and remove duplicates in place; returns new length */
static inline size_t sort_unique_u64(uint64_t *a, size_t n) {
    if (n < 2) return n;
    qsort(a, n, sizeof(uint64_t), cmp_u64);
    size_t j = 1;
    for (size_t i = 1; i < n; i++) if (a[i] != a[j - 1]) a[j++] = a[i];
    return j;
}

#endif
