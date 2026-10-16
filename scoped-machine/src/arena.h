/* §§89/94 — the bounded allocator under the work engine's bodies.
 *
 * One host operation at initialization reserves a fixed virtual range
 * (ARENA_WORDS words, untouched pages cost nothing); afterwards no host
 * allocation is made for a block of input-dependent size. Blocks are powers
 * of two pages (ARENA_PAGE words) kept on per-order free lists with intrusive
 * links; an allocation pops its order's list or splits the smallest larger
 * free block down (at most ARENA_ORDERS steps, an architecture-fixed bound);
 * a release pushes the block on its order's list (one step; blocks are not
 * coalesced — a released block is reused by requests of its order or smaller
 * via splitting). Clearing is never performed here: a caller that needs a
 * zeroed block clears it in CHUNK_WORDS units of its own (the slot-array
 * growth does); copying is never performed here.
 *
 * Paged buffers: a variable-size buffer is a sequence of fixed pages reached
 * through a directory of at most two fixed levels — push, read, write, pop and
 * ownership transfer are O(1) with one fixed-size page taken from the arena
 * when a page fills; nothing is ever copied on growth. Release of a buffer's
 * pages is retired to a queue drained one page per unit (`arena_reap`). */
#ifndef ARENA_H
#define ARENA_H
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define ARENA_PAGE   512u                       /* words per page (4 KiB) */
#define ARENA_ORDERS 23u                        /* orders 0..22: page × 2^k, the largest the whole range */
#define ARENA_WORDS  ((size_t)ARENA_PAGE << (ARENA_ORDERS - 1))   /* 2^31 words = 16 GiB of address space: the lower half on the free lists, the upper half the fresh (zero) region */
#define ARENA_FRESH_WORDS (ARENA_WORDS / 2)

void arena_init(void);                           /* the one reservation */
void arena_free(void);                           /* the one release */
bool arena_live(void);
const void *arena_base(void);                    /* the reservation's start (kalloc: ownership test) */
uint64_t *arena_alloc(size_t words, size_t *got);   /* a block of at least `words` words (rounded to the order); not cleared */
uint64_t *arena_alloc_zero(size_t words, size_t *got);   /* a zero block: from the cleared pool, else a never-used block of the fresh region; released ones are cleared in maintenance steps and reused */
bool arena_tend_zero(void);                              /* one clearing step (32 words) of a retired zero block; false when none is pending */
void arena_release(uint64_t *p, size_t words);      /* `words` as returned in *got */
size_t arena_order_words(size_t words);             /* the block size a request of `words` receives */

/* arena statistics (host-independent): pages taken from / returned to the free lists, splits performed */
typedef struct { uint64_t allocs, releases, splits, words_out, words_in; } ArenaStats;
ArenaStats arena_stats(void);

/* paged buffer of fixed-size elements (elem bytes, a divisor of the page) */
typedef struct {
    size_t elem, per;       /* element bytes, elements per page */
    union { size_t n, len; };   /* elements (both names: white-box probes read either) */
    size_t pages;           /* pages allocated (kept across pops; released at retirement) */
    void *pg0;              /* page 0 */
    void **dir;             /* pages 1..DIR-1 (dir[0] unused): one arena page of pointers */
    void ***dir2;           /* dir2[k] = directory of pages k·DIR .. k·DIR+DIR-1 */
} Paged;
#define PAGED_DIR (ARENA_PAGE)                   /* pointers per directory page */

void paged_init(Paged *p, size_t elem);
void *paged_at(const Paged *p, size_t i);        /* element i (i < n) */
void *paged_push(Paged *p);                      /* the new last element's slot (uninitialized) */
void paged_pop(Paged *p);                        /* drop the last element (a page emptied by it is retired) */
void paged_truncate(Paged *p, size_t n);         /* n ≤ p->n; emptied pages are retired one per call of arena_reap */
void paged_take(Paged *dst, Paged *src);         /* ownership transfer: dst's pages are retired, src becomes empty */
void paged_retire(Paged *p);                     /* retire all pages; p becomes empty (its directories too) */
size_t paged_pages(const Paged *p);
bool arena_reap(void);                           /* release one retired page; false when the queue is empty */
void arena_reap_all(void);

/* word buffer convenience over Paged */
static inline uint64_t pw_get(const Paged *p, size_t i) { return *(const uint64_t *)paged_at(p, i); }
static inline void pw_set(Paged *p, size_t i, uint64_t v) { *(uint64_t *)paged_at(p, i) = v; }
static inline void pw_push(Paged *p, uint64_t v) { *(uint64_t *)paged_push(p) = v; }

#endif
