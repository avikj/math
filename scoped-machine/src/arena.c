#include "common.h"
#include "arena.h"
#include "fine.h"
#include <sys/mman.h>
#include <string.h>

/* ---- extents and the block pools (BOUNDS-COMPLETION §5) ----
 *
 * The allocator owns a collection of extents, each a page-aligned anonymous
 * mapping requested from the host when the pools cannot satisfy a demand
 * (EXTEND: a host resource action; the initial extent size is a growth
 * policy, never a capacity). A block is (extent, offset, order): offsets are
 * extent-relative and orders go up to the native address width. Every block
 * not owned by a caller is in exactly one state:
 *   FRESH       — never used: the unconsumed tail of an extent (zero by the mapping)
 *   DIRTY_FREE  — released: per-order lists `dirty`; ordinary allocations take
 *                 these directly; zero allocations need them cleared first
 *   CLEARING    — the one block detached for clearing (`zactive`, cursor `zcursor`)
 *   ZERO_READY  — cleared: per-order lists `ready`
 * Ordinary allocation: DIRTY_FREE of the order, else ZERO_READY of the
 * order, else one split of a larger DIRTY_FREE block (the other half stays
 * dirty), else FRESH, else EXTEND. Zero allocation: ZERO_READY, else FRESH,
 * else EXTEND (never an input-sized clearing loop under the lock; a host
 * refusal is reported as a resource condition). Clearing advances 32 words
 * of the detached block per `arena_tend_zero` (driven per unit). Released
 * blocks become DIRTY_FREE whatever their origin. No merge across extents. */
#define ARENA_MIN_EXTENT_WORDS ((size_t)ARENA_PAGE << 11)   /* default growth policy: 2^20 words (8 MiB) per new extent at least */
typedef struct Extent { uint64_t *base; size_t words; size_t fresh; struct Extent *next; } Extent;
static struct {
    Extent *extents, *cur;             /* every owned extent; `cur` serves FRESH blocks */
    size_t nextents, owned_words, extent_policy;
    uint64_t *dirty[ARENA_ORDERS], *ready[ARENA_ORDERS];
    uint64_t *zactive; unsigned zorder; size_t zcursor;       /* CLEARING: the detached block, its order and cleared prefix */
    uint64_t zero_fresh, zero_reused, zero_sync_words;
    ArenaStats st;
    bool live;
    pthread_mutex_t mu;                /* the engine (under its lock) and kalloc's threads share the pools */
} A = { .mu = PTHREAD_MUTEX_INITIALIZER };

void arena_set_extent_policy(size_t words) { pthread_mutex_lock(&A.mu); A.extent_policy = words; pthread_mutex_unlock(&A.mu); }
void arena_init(void) {
    pthread_mutex_lock(&A.mu);
    if (!A.live) { A.live = true; if (!A.extent_policy) A.extent_policy = ARENA_MIN_EXTENT_WORDS; }
    pthread_mutex_unlock(&A.mu);
}
/* the extents live for the process: kernel blocks (kalloc.c) outlive the engine's lifecycle; the engine returns its own blocks to the pools */
void arena_free(void) { }
bool arena_live(void) { return A.live; }
/* the exact index of owned extents (kalloc's ownership test): extents are
 * only ever prepended and never released, so a reader traverses the list
 * without the lock (acquire loads of release-published records) */
bool arena_owns(const void *p) {
    for (Extent *e = __atomic_load_n(&A.extents, __ATOMIC_ACQUIRE); e; e = e->next)
        if ((const uint64_t *)p >= e->base && (const uint64_t *)p < e->base + e->words) return true;
    return false;
}
size_t arena_extents(void) { pthread_mutex_lock(&A.mu); size_t n = A.nextents; pthread_mutex_unlock(&A.mu); return n; }
size_t arena_owned_words(void) { pthread_mutex_lock(&A.mu); size_t n = A.owned_words; pthread_mutex_unlock(&A.mu); return n; }
ArenaStats arena_stats(void) { pthread_mutex_lock(&A.mu); ArenaStats s = A.st; pthread_mutex_unlock(&A.mu); return s; }

static unsigned order_of(size_t words) {
    unsigned k = 0; size_t b = ARENA_PAGE;
    while (b < words) { require(k + 1 < ARENA_ORDERS && b <= SIZE_MAX / 2, "arena: block larger than the address space"); b <<= 1; k++; }
    return k;
}
size_t arena_order_words(size_t words) { return (size_t)ARENA_PAGE << order_of(words); }
#if defined(__SANITIZE_ADDRESS__)
void __asan_poison_memory_region(void const volatile *addr, size_t size);
void __asan_unpoison_memory_region(void const volatile *addr, size_t size);
#define LINK_UNPOISON(b) __asan_unpoison_memory_region((b), sizeof(uint64_t *))
#define BLOCK_POISON(b, n) __asan_poison_memory_region((b), (n) * sizeof(uint64_t))
#define BLOCK_UNPOISON(b, n) __asan_unpoison_memory_region((b), (n) * sizeof(uint64_t))
#else
#define LINK_UNPOISON(b) ((void)0)
#define BLOCK_POISON(b, n) ((void)0)
#define BLOCK_UNPOISON(b, n) ((void)0)
#endif
/* a list link lives in the block's first word */
static uint64_t *pop_list(uint64_t **head) { uint64_t *b = *head; if (b) { LINK_UNPOISON(b); *head = *(uint64_t **)b; } return b; }
static void push_list(uint64_t **head, uint64_t *b) { LINK_UNPOISON(b); *(uint64_t **)b = *head; *head = b; }
/* EXTEND: one host mapping of at least `w` words (page-aligned by the host) */
static bool extend_locked(size_t w) {
    size_t words = A.extent_policy; while (words < w) { require(words <= SIZE_MAX / 2, "arena: extent size overflow"); words <<= 1; }
    require(words <= SIZE_MAX / sizeof(uint64_t), "arena: extent size overflow");
    void *p = mmap(NULL, words * sizeof(uint64_t), PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (p == MAP_FAILED) return false;   /* the host could not supply storage: a resource condition */
    Extent *e = (calloc)(1, sizeof *e); if (!e) { munmap(p, words * sizeof(uint64_t)); return false; }   /* extent records are host allocations (never inside an extent) */
    e->base = p; e->words = words; e->fresh = 0; e->next = A.extents; __atomic_store_n(&A.extents, e, __ATOMIC_RELEASE); A.cur = e; A.nextents++; A.owned_words += words;
    BLOCK_POISON(e->base, words);
    return true;
}
/* FRESH: the next `w` words of the current extent (alignment by order is not
 * required: offsets are extent-relative and no buddy merge crosses blocks) */
static uint64_t *fresh_locked(size_t w) {
    if (!A.cur || A.cur->words - A.cur->fresh < w) { if (!extend_locked(w)) return NULL; }
    uint64_t *b = A.cur->base + A.cur->fresh; A.cur->fresh += w;
    return b;
}
uint64_t *arena_alloc(size_t words, size_t *got) {
    if (!A.live) arena_init();
    unsigned k = order_of(words); size_t w = (size_t)ARENA_PAGE << k;
    pthread_mutex_lock(&A.mu);
    uint64_t *b = pop_list(&A.dirty[k]);
    if (!b) b = pop_list(&A.ready[k]);
    if (!b) {   /* one split chain of the smallest larger dirty block: each split publishes the other half as dirty */
        unsigned j = k + 1; while (j < ARENA_ORDERS && !A.dirty[j]) j++;
        if (j < ARENA_ORDERS) { b = pop_list(&A.dirty[j]); while (j > k) { j--; push_list(&A.dirty[j], b + ((size_t)ARENA_PAGE << j)); A.st.splits++; } }
    }
    if (!b) b = fresh_locked(w);
    require(b, "arena: the host could not supply storage");
    A.st.allocs++; A.st.words_out += w;
    pthread_mutex_unlock(&A.mu);
    BLOCK_UNPOISON(b, w);   /* a block is addressable while allocated and poisoned while free (ASan) */
    if (got) *got = w;
    return b;
}
static bool zero_tend_locked(void) {
    if (!A.zactive) {
        for (unsigned k = 0; k < ARENA_ORDERS; k++) {
            uint64_t *b = A.dirty[k]; if (!b) continue;
            LINK_UNPOISON(b); A.dirty[k] = *(uint64_t **)b;
            A.zactive = b; A.zorder = k; A.zcursor = 0;
            break;
        }
    }
    if (!A.zactive) return false;
    uint64_t *b = A.zactive; unsigned k = A.zorder;
    size_t w = (size_t)ARENA_PAGE << k, end = A.zcursor + 32; if (end > w) end = w;
    BLOCK_UNPOISON(b, w);
    for (size_t x = A.zcursor; x < end; x++) b[x] = 0;
    A.zcursor = end;
    if (end == w) { *(uint64_t **)b = A.ready[k]; A.ready[k] = b; A.zactive = NULL; A.zcursor = 0; }
    BLOCK_POISON(b, w);
    return true;
}
bool arena_tend_zero(void) { pthread_mutex_lock(&A.mu); bool did = zero_tend_locked(); pthread_mutex_unlock(&A.mu); return did; }
uint64_t *arena_alloc_zero(size_t words, size_t *got) {
    if (!A.live) arena_init();
    unsigned k = order_of(words); size_t w = (size_t)ARENA_PAGE << k;
    pthread_mutex_lock(&A.mu);
    uint64_t *b = A.ready[k];
    if (b) { LINK_UNPOISON(b); A.ready[k] = *(uint64_t **)b; BLOCK_UNPOISON(b, w); b[0] = 0; A.zero_reused++; }   /* ZERO_READY: the link word is zeroed again */
    else {
        /* a DIRTY_FREE block of the order (or one split off a larger one) is
         * detached for this requester and cleared after the lock is released,
         * one word per transition: no clearing under the lock, no growth while
         * reusable storage exists */
        uint64_t *d = pop_list(&A.dirty[k]);
        if (!d) { unsigned j = k + 1; while (j < ARENA_ORDERS && !A.dirty[j]) j++;
                  if (j < ARENA_ORDERS) { d = pop_list(&A.dirty[j]); while (j > k) { j--; push_list(&A.dirty[j], d + ((size_t)ARENA_PAGE << j)); A.st.splits++; } } }
        if (d) {
            A.zero_sync_words += w; A.zero_reused++; A.st.allocs++; A.st.words_out += w;
            pthread_mutex_unlock(&A.mu);
            BLOCK_UNPOISON(d, w);
            for (size_t x = 0; x < w; x++) { d[x] = 0; fine_bump(FC_ALLOC_WORDS); }
            if (got) *got = w;
            return d;
        }
        b = fresh_locked(w); require(b, "arena: the host could not supply storage"); BLOCK_UNPOISON(b, w); A.zero_fresh++;   /* FRESH (EXTEND when the extent is consumed) */
    }
    A.st.allocs++; A.st.words_out += w;
    pthread_mutex_unlock(&A.mu);
    if (got) *got = w;
    return b;
}
void arena_release(uint64_t *p, size_t words) {
    if (!p || !A.live) return;
    unsigned k = order_of(words);
    pthread_mutex_lock(&A.mu);
    LINK_UNPOISON(p); push_list(&A.dirty[k], p); A.st.releases++; A.st.words_in += (size_t)ARENA_PAGE << k;
    BLOCK_POISON(p, (size_t)ARENA_PAGE << k);   /* before the lock is released: a competing allocation may take it next */
    pthread_mutex_unlock(&A.mu);
}
ArenaZeroStats arena_zero_stats(void) { pthread_mutex_lock(&A.mu); ArenaZeroStats z = { A.zero_fresh, A.zero_reused, A.zero_sync_words }; pthread_mutex_unlock(&A.mu); return z; }

/* ---- paged buffers ---- */
static void *page_new(void) { return arena_alloc(ARENA_PAGE, NULL); }
static void page_del(void *p) { arena_release(p, ARENA_PAGE); }

void paged_init(Paged *p, size_t elem) {
    require(elem && elem <= ARENA_PAGE * sizeof(uint64_t), "paged: element size");
    memset(p, 0, sizeof *p); p->elem = elem; p->per = (ARENA_PAGE * sizeof(uint64_t)) / elem;
}
static void *page_ptr(const Paged *p, size_t k) { return k ? radix_get(&p->index, k) : p->pg0; }
static void page_set(Paged *p, size_t k, void *pg) {
    if (!k) { p->pg0 = pg; return; }
    void **slot = radix_slot(&p->index, k, true); *slot = pg;
}
void *paged_at(const Paged *p, size_t i) { require(i < p->n, "paged: index"); return (char *)page_ptr(p, i / p->per) + (i % p->per) * p->elem; }
void *paged_push(Paged *p) {
    require(p->n < SIZE_MAX, "paged: address space exhausted");
    size_t i = p->n; size_t k = i / p->per;
    if (k >= p->pages) { page_set(p, k, page_new()); p->pages = k + 1; }   /* a new page: one fixed-size block from the free list */
    p->n++;
    return (char *)page_ptr(p, k) + (i % p->per) * p->elem;
}
size_t paged_pages(const Paged *p) { return p->pages; }

/* retirement: a buffer's pages and directory pages are released one per
 * `arena_reap`. The queue is intrusive: a retiree's descriptor lives in its
 * own page 0 (every retiree has one) */
typedef struct Retiree { size_t pages; Radix index; RadixRetire cursor; bool clearing_dirs; struct Retiree *next; } Retiree;
_Static_assert(sizeof(Retiree) <= ARENA_PAGE * sizeof(uint64_t), "retirement cursor must fit a fixed page");
static Retiree *R_head, *R_tail;
static void enqueue(Retiree *r) { r->next = NULL; if (R_tail) R_tail->next = r; else R_head = r; R_tail = r; }
void paged_retire(Paged *p) {
    if (!p->pg0) { size_t elem = p->elem; paged_init(p, elem); return; }
    Retiree *r = p->pg0;
    *r = (Retiree){ .pages = p->pages, .index = p->index };
    enqueue(r); size_t elem = p->elem; paged_init(p, elem);
}
bool arena_reap(void) {
    Retiree *r = R_head; if (!r) return false;
    if (r->pages > 1) { page_del(radix_get(&r->index, --r->pages)); return true; }
    if (!r->clearing_dirs) { radix_retire_begin(&r->cursor, &r->index); r->clearing_dirs = true; }
    if (radix_retire_step(&r->cursor)) return true;
    R_head = r->next; if (!R_head) R_tail = NULL; page_del(r); return true;
}
void arena_reap_all(void) { while (arena_reap()) ; }
void paged_pop(Paged *p) { require(p->n, "paged: pop on empty"); p->n--; }   /* pages are kept for reuse; released at retirement */
void paged_truncate(Paged *p, size_t n) { require(n <= p->n, "paged: truncate"); p->n = n; }
void paged_take(Paged *dst, Paged *src) { paged_retire(dst); *dst = *src; size_t elem = src->elem; memset(src, 0, sizeof *src); src->elem = elem; src->per = dst->per; }
