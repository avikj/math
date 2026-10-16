/* kalloc.c — the kernel's allocator over the arena (§§89/94).
 *
 * Every malloc / calloc / realloc / free in the kernel and the engine
 * (common.h maps the names here) is served from the arena: size classes of
 * 16 … 2048 bytes carved from arena pages with intrusive free lists (one
 * step to take or return a slot; a page refill is one arena allocation),
 * and whole arena blocks for larger requests. Clearing (calloc) and the copy
 * of a reallocation are performed one word at a time with a fine step each
 * (FC_ALLOC_WORDS): inside a kernel continuation they are transitions, so
 * an input-sized clear or copy is in units like any other loop. A pointer
 * not from here (strdup, a block from before the arena was live) is
 * recognized by its missing header and returned to the host allocator.
 *
 * Under AddressSanitizer the free slots, the headers and the slack of every
 * block are poisoned and an allocation's payload unpoisoned, so overflow and
 * use-after-free inside the arena are still reported.
 */
#define KALLOC_IMPL
#include "common.h"
#include "arena.h"
#include "fine.h"
#include <string.h>

#if defined(__SANITIZE_ADDRESS__)
void __asan_poison_memory_region(void const volatile *addr, size_t size);
void __asan_unpoison_memory_region(void const volatile *addr, size_t size);
#define POISON(p, n) __asan_poison_memory_region((p), (n))
#define UNPOISON(p, n) __asan_unpoison_memory_region((p), (n))
#else
#define POISON(p, n) ((void)0)
#define UNPOISON(p, n) ((void)0)
#endif

enum { HDR = 16, NCLASS = 8, MIN_SHIFT = 4 };            /* classes: 16, 32, …, 2048 bytes of payload */
#define MAGIC_SMALL 0x5A11000000000000ULL
#define MAGIC_LARGE 0x1A26000000000000ULL
#define MAGIC_MASK  0xFFFF000000000000ULL
#define PAYLOAD_MASK 0x0000FFFFFFFFFFFFULL
typedef struct { uint64_t magic_class; uint64_t size; } Hdr;   /* magic | class (small) or magic (large); the request size */

static struct { pthread_mutex_t mu; void *free_list[NCLASS]; uint64_t pages, large; bool init; } KA = { PTHREAD_MUTEX_INITIALIZER, {0}, 0, 0, false };

static unsigned class_of(size_t n) { unsigned c = 0; size_t s = (size_t)1 << MIN_SHIFT; while (s < n) { s <<= 1; c++; } return c; }
static void refill(unsigned c) {   /* one arena page carved into slots of class c (locked; O(page / slot) = a constant) */
    size_t slot = HDR + ((size_t)1 << (MIN_SHIFT + c));
    char *page = (char *)arena_alloc(ARENA_PAGE, NULL); KA.pages++;
    size_t bytes = ARENA_PAGE * sizeof(uint64_t), k = bytes / slot;
    UNPOISON(page, bytes);
    for (size_t i = 0; i < k; i++) { char *s = page + i * slot; *(void **)(s + HDR) = KA.free_list[c]; KA.free_list[c] = s; }
    POISON(page, bytes);
}
static void *take(size_t n) {
    if (!arena_live()) arena_init();
    fine_bump(FC_ALLOC_OPS);
    if (n > ((size_t)1 << (MIN_SHIFT + NCLASS - 1))) {   /* a whole arena block */
        size_t words = (n + HDR + 7) / 8, got; uint64_t *b;
        pthread_mutex_lock(&KA.mu); b = arena_alloc(words, &got); KA.large++; pthread_mutex_unlock(&KA.mu);
        POISON(b, got * 8);
        Hdr *h = (Hdr *)b; UNPOISON(h, HDR); h->magic_class = MAGIC_LARGE | (uint64_t)got; h->size = n; POISON(h, HDR);
        UNPOISON((char *)b + HDR, n);
        return (char *)b + HDR;
    }
    unsigned c = class_of(n ? n : 1);
    pthread_mutex_lock(&KA.mu);
    if (!KA.free_list[c]) refill(c);
    char *s = KA.free_list[c]; UNPOISON(s + HDR, sizeof(void *)); KA.free_list[c] = *(void **)(s + HDR);
    pthread_mutex_unlock(&KA.mu);
    Hdr *h = (Hdr *)s; UNPOISON(h, HDR); h->magic_class = MAGIC_SMALL | c; h->size = n; POISON(h, HDR);
    UNPOISON(s + HDR, n);
    return s + HDR;
}
static bool ours(const void *p, Hdr *out) {
    if (!p || !arena_live()) return false;
    const char *base = (const char *)arena_base(); size_t bytes = ARENA_WORDS * sizeof(uint64_t);
    if ((const char *)p < base + HDR || (const char *)p >= base + bytes) return false;
    const Hdr *h = (const Hdr *)((const char *)p - HDR);
    UNPOISON(h, HDR); *out = *h; POISON(h, HDR);
    return (out->magic_class & MAGIC_MASK) == MAGIC_SMALL || (out->magic_class & MAGIC_MASK) == MAGIC_LARGE;
}
static void give(void *p, const Hdr *h) {
    fine_bump(FC_ALLOC_OPS);
    char *s = (char *)p - HDR;
    if ((h->magic_class & MAGIC_MASK) == MAGIC_LARGE) {
        size_t got = h->magic_class & PAYLOAD_MASK; POISON(s, got * 8);
        pthread_mutex_lock(&KA.mu); arena_release((uint64_t *)s, got); pthread_mutex_unlock(&KA.mu);
        return;
    }
    unsigned c = (unsigned)(h->magic_class & PAYLOAD_MASK);
    POISON(s, HDR + ((size_t)1 << (MIN_SHIFT + c)));
    pthread_mutex_lock(&KA.mu);
    UNPOISON(s + HDR, sizeof(void *)); *(void **)(s + HDR) = KA.free_list[c]; POISON(s + HDR, sizeof(void *)); KA.free_list[c] = s;
    pthread_mutex_unlock(&KA.mu);
}

void *k_malloc(size_t n) { return take(n); }
void *k_calloc(size_t a, size_t b) {
    size_t n = a * b; require(!a || n / a == b, "calloc overflow");
    char *p = take(n);
    size_t w = n / 8; uint64_t *q = (uint64_t *)p;
    for (size_t i = 0; i < w; i++) { q[i] = 0; fine_bump(FC_ALLOC_WORDS); }          /* clearing: one transition per word */
    for (size_t i = w * 8; i < n; i++) p[i] = 0;
    return p;
}
void k_free(void *p) { Hdr h; if (!p) return; if (ours(p, &h)) give(p, &h); else (free)(p); }
void *k_realloc(void *p, size_t n) {
    Hdr h;
    if (!p) return take(n);
    if (!ours(p, &h)) return (realloc)(p, n);           /* a host block stays a host block */
    if (n <= h.size && (h.magic_class & MAGIC_MASK) == MAGIC_SMALL) {   /* shrinking within the slot: in place */
        Hdr *hp = (Hdr *)((char *)p - HDR); UNPOISON(hp, HDR); hp->size = n; POISON(hp, HDR); POISON((char *)p + n, h.size - n); return p;
    }
    char *q = take(n); size_t keep = h.size < n ? h.size : n;
    size_t w = keep / 8; const uint64_t *src = p; uint64_t *dst = (uint64_t *)q;
    for (size_t i = 0; i < w; i++) { dst[i] = src[i]; fine_bump(FC_ALLOC_WORDS); }   /* the copy of a reallocation: one transition per word */
    for (size_t i = w * 8; i < keep; i++) q[i] = ((char *)p)[i];
    give(p, &h);
    return q;
}
uint64_t kalloc_pages(void) { return KA.pages; }

void k_copy_words(uint64_t *dst, const uint64_t *src, size_t n) {
    for (size_t i = 0; i < n; i++) { dst[i] = src[i]; fine_bump(FC_COPY_WORDS); }
}
