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

/* §94 (frames, kframe.h): every mutex acquisition is counted per thread so a
 * frame stack suspends only at the lock depth it was granted at */
extern __thread int kf_lock_depth;
#ifdef KF_LOCK_AUDIT
/* the lock-section audit (tests/lock_audit): the fine steps taken between the
 * outermost acquisition and the matching release, per acquisition site */
void kf_audit_enter(const char *site); void kf_audit_leave(void);
static inline int kf_mutex_lock_at(pthread_mutex_t *m, const char *site) { int r = (pthread_mutex_lock)(m); if (kf_lock_depth++ == 0) kf_audit_enter(site); return r; }
static inline int kf_mutex_unlock(pthread_mutex_t *m) { if (--kf_lock_depth == 0) kf_audit_leave(); return (pthread_mutex_unlock)(m); }
static inline int kf_mutex_trylock_at(pthread_mutex_t *m, const char *site) { int r = (pthread_mutex_trylock)(m); if (r == 0 && kf_lock_depth++ == 0) kf_audit_enter(site); return r; }
#define KF_STR2(x) #x
#define KF_STR(x) KF_STR2(x)
#define pthread_mutex_lock(m) kf_mutex_lock_at((m), __FILE__ ":" KF_STR(__LINE__))
#define pthread_mutex_trylock(m) kf_mutex_trylock_at((m), __FILE__ ":" KF_STR(__LINE__))
#else
static inline int kf_mutex_lock(pthread_mutex_t *m) { int r = (pthread_mutex_lock)(m); kf_lock_depth++; return r; }
static inline int kf_mutex_unlock(pthread_mutex_t *m) { kf_lock_depth--; return (pthread_mutex_unlock)(m); }
static inline int kf_mutex_trylock(pthread_mutex_t *m) { int r = (pthread_mutex_trylock)(m); if (r == 0) kf_lock_depth++; return r; }
#define pthread_mutex_lock(m) kf_mutex_lock(m)
#define pthread_mutex_trylock(m) kf_mutex_trylock(m)
#endif
#define pthread_mutex_unlock(m) kf_mutex_unlock(m)

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

/* a variable-length word copy: one fine transition per word (FC_COPY_WORDS) */
void k_copy_words(uint64_t *dst, const uint64_t *src, size_t n);

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
typedef size_t BinderSlot;
typedef size_t FieldIndex;

#define NO_SLOT ((BinderSlot)SIZE_MAX)
#define NO_FIELD ((FieldIndex)SIZE_MAX)

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
    k_copy_words(b->w + b->n, x, n);
    b->n += n;
}

/* ---- paged vector of words: segment k holds 4·2^k words and never moves, so
 * a push is one constant step (no copy) and an element's address is stable;
 * readers that hold an index below a published length need no lock ---- */
typedef struct { uint64_t **seg; size_t len; } PVec;
enum { PV_SEGS = 60 };
static inline unsigned pv_seg_(size_t i, size_t *off) { size_t j = i / 4 + 1; unsigned k = 63u - (unsigned)__builtin_clzll((unsigned long long)j); *off = i - 4 * (((size_t)1 << k) - 1); return k; }
static inline uint64_t *pv_at(const PVec *v, size_t i) { size_t off; unsigned k = pv_seg_(i, &off); return &v->seg[k][off]; }
static inline uint64_t pv_get(const PVec *v, size_t i) { return *pv_at(v, i); }
static inline void pv_set(PVec *v, size_t i, uint64_t x) { *pv_at(v, i) = x; }
/* segments are taken in order (segment k exactly when the length reaches its
 * first index), so the directory is never read beyond the last taken slot and
 * needs no clearing: every allocation here is one uncleared take */
static inline void pv_push(PVec *v, uint64_t x) {
    size_t off; unsigned k = pv_seg_(v->len, &off);
    if (!v->seg) { v->seg = (uint64_t **)malloc(PV_SEGS * sizeof *v->seg); require(v->seg, "out of memory"); }
    if (off == 0) { v->seg[k] = (uint64_t *)malloc(((size_t)4 << k) * sizeof(uint64_t)); require(v->seg[k], "out of memory"); }
    v->seg[k][off] = x; __atomic_store_n(&v->len, v->len + 1, __ATOMIC_RELEASE);
}
static inline size_t pv_len(const PVec *v) { return __atomic_load_n(&v->len, __ATOMIC_ACQUIRE); }
static inline void pv_free(PVec *v) {
    if (v->seg) { if (v->len) { size_t off; unsigned last = pv_seg_(v->len - 1, &off); for (unsigned k = 0; k <= last; k++) free(v->seg[k]); } free(v->seg); }
    v->seg = NULL; v->len = 0;
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
size_t sort_unique_u64(uint64_t *a, size_t n);

/* frame families of the kernel primitives (kframe.h, kprim.c): the same loops as resumable frames */
#include "kframe.h"
#define sort_unique_u64_PARAMS(X) X(uint64_t *, a) X(size_t, n)
#define k_copy_words_PARAMS(X) X(uint64_t *, dst) X(const uint64_t *, src) X(size_t, n)
#define words_append_PARAMS(X) X(Words *, b) X(const uint64_t *, x) X(size_t, n)
KF_PROTO(sort_unique_u64, size_t, sort_unique_u64_PARAMS);
KF_PROTO(k_copy_words, void, k_copy_words_PARAMS);
KF_PROTO(words_append, void, words_append_PARAMS);
#define pair_sort_PARAMS(X) X(uint64_t *, p) X(size_t, n)
KF_PROTO(pair_sort, void, pair_sort_PARAMS);   /* term.c: n (key, image) pairs, lexicographic, one sift per transition */
/* the clearing allocation and the reallocation as families (kalloc.c): one word per transition */
#define k_zalloc_PARAMS(X) X(size_t, a) X(size_t, b)
#define k_regrow_PARAMS(X) X(void *, p) X(size_t, n)
KF_PROTO(k_zalloc, void *, k_zalloc_PARAMS);
KF_PROTO(k_regrow, void *, k_regrow_PARAMS);
#define words_reserve_PARAMS(X) X(Words *, b) X(size_t, extra)
KF_PROTO(words_reserve, void, words_reserve_PARAMS);
/* growth inside a frame step: the reallocation is a child frame */
#define KF_WORDS_PUSH(b, x) do { if ((b)->n == (b)->cap) KF_CALL(words_reserve, NULL, (b), 1); (b)->w[(b)->n++] = (x); } while (0)
#define KF_VEC_PUSH(v, x) do { if ((v)->len == (v)->cap) { (v)->cap = (v)->cap ? (v)->cap * 2 : 8; KF_CALL(k_regrow, (void **)&(v)->data, (v)->data, (v)->cap * sizeof(*(v)->data)); } (v)->data[(v)->len++] = (x); } while (0)

#endif
