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
#include <pthread.h>

/* §94 (kernel continuations, kcont.h): every mutex acquisition is counted per
 * thread so a continuation yields only where it holds no lock */
extern __thread int kc_lock_depth;
#ifdef KC_LOCK_AUDIT
/* the lock-section audit (tests/lock_audit): the fine steps taken between the
 * outermost acquisition and the matching release, per acquisition site */
void kc_audit_enter(const char *site); void kc_audit_leave(void);
static inline int kc_mutex_lock_at(pthread_mutex_t *m, const char *site) { int r = (pthread_mutex_lock)(m); if (kc_lock_depth++ == 0) kc_audit_enter(site); return r; }
static inline int kc_mutex_unlock(pthread_mutex_t *m) { if (--kc_lock_depth == 0) kc_audit_leave(); return (pthread_mutex_unlock)(m); }
static inline int kc_mutex_trylock_at(pthread_mutex_t *m, const char *site) { int r = (pthread_mutex_trylock)(m); if (r == 0 && kc_lock_depth++ == 0) kc_audit_enter(site); return r; }
#define KC_STR2(x) #x
#define KC_STR(x) KC_STR2(x)
#define pthread_mutex_lock(m) kc_mutex_lock_at((m), __FILE__ ":" KC_STR(__LINE__))
#define pthread_mutex_trylock(m) kc_mutex_trylock_at((m), __FILE__ ":" KC_STR(__LINE__))
#else
static inline int kc_mutex_lock(pthread_mutex_t *m) { int r = (pthread_mutex_lock)(m); kc_lock_depth++; return r; }
static inline int kc_mutex_unlock(pthread_mutex_t *m) { kc_lock_depth--; return (pthread_mutex_unlock)(m); }
static inline int kc_mutex_trylock(pthread_mutex_t *m) { int r = (pthread_mutex_trylock)(m); if (r == 0) kc_lock_depth++; return r; }
#define pthread_mutex_lock(m) kc_mutex_lock(m)
#define pthread_mutex_trylock(m) kc_mutex_trylock(m)
#endif
#define pthread_mutex_unlock(m) kc_mutex_unlock(m)

/* §§89/94: the kernel's and the engine's allocations are served by kalloc.c
 * over the arena (size-class free lists, clearing and copying one word per
 * fine step); a block from the host (strdup, pre-arena) is recognized and
 * returned to the host */
#ifndef KALLOC_IMPL
void *k_malloc(size_t n); void *k_calloc(size_t a, size_t b); void *k_realloc(void *p, size_t n); void k_free(void *p);
#define malloc(n) k_malloc(n)
#define calloc(a, b) k_calloc((a), (b))
#define realloc(p, n) k_realloc((p), (n))
#define free(p) k_free(p)
#endif

typedef uint64_t TermVarId;
typedef uint64_t DimVarId;
typedef uint64_t ContextId;
typedef uint64_t OriginId;
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
static inline void words_append(Words *b, const uint64_t *x, size_t n) {
    words_reserve(b, n);
    if (n) memcpy(b->w + b->n, x, n * sizeof(uint64_t));
    b->n += n;
}

/* ---- generic pointer vector ---- */
#define VEC(T) struct { T *data; size_t len, cap; }
#define vec_push(v, x) do { \
    if ((v)->len == (v)->cap) { \
        (v)->cap = (v)->cap ? (v)->cap * 2 : 8; \
        (v)->data = realloc((v)->data, (v)->cap * sizeof(*(v)->data)); \
        require((v)->data, "out of memory"); \
    } \
    (v)->data[(v)->len++] = (x); } while (0)
#define vec_free(v) do { free((v)->data); (v)->data = NULL; (v)->len = (v)->cap = 0; } while (0)

static inline int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y ? 1 : 0;
}

/* sort and remove duplicates in place; returns new length */
/* §94: an in-place heap sort whose every sift (at most 64 iterations, an
 * architecture-fixed bound) and every dedupe step is a fine step — the
 * transition points of a kernel continuation (fine.h); no sort runs inside
 * one transition */
void kernel_sort_step(void);   /* fine.c: one FC_SORT_STEPS transition */
static inline void sift_down_u64(uint64_t *h, size_t n, size_t i) {
    for (;;) { size_t l = 2 * i + 1, r = l + 1, m = i; if (l < n && h[l] > h[m]) m = l; if (r < n && h[r] > h[m]) m = r; if (m == i) return; uint64_t t = h[i]; h[i] = h[m]; h[m] = t; i = m; }
}
static inline size_t sort_unique_u64(uint64_t *a, size_t n) {
    if (n < 2) return n;
    for (size_t i = n / 2; i > 0; i--) { sift_down_u64(a, n, i - 1); kernel_sort_step(); }
    for (size_t e = n - 1; e > 0; e--) { uint64_t t = a[0]; a[0] = a[e]; a[e] = t; sift_down_u64(a, e, 0); kernel_sort_step(); }
    size_t j = 1;
    for (size_t i = 1; i < n; i++) { if (a[i] != a[j - 1]) a[j++] = a[i]; kernel_sort_step(); }
    return j;
}

#endif
