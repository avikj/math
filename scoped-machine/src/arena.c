#include "common.h"
#include "arena.h"
#include <sys/mman.h>
#include <string.h>

/* ---- the reservation and the free lists ---- */
static struct {
    uint64_t *base; size_t words;
    uint64_t *heads[ARENA_ORDERS];     /* free lists: the first word of a free block links the next */
    size_t fresh;                      /* the fresh region's bump cursor (words from base + ARENA_WORDS/2) */
    uint64_t *zdirty[ARENA_ORDERS], *zready[ARENA_ORDERS];   /* §94 R4: retired zero-region blocks awaiting clearing / cleared and reusable, per order */
    uint64_t *zactive;                 /* detached dirty block owned by the clearing continuation */
    unsigned zorder;
    size_t zcursor;                    /* cleared prefix of zactive; queue insertions cannot change its owner */
    uint64_t zero_fresh, zero_reused, zero_sync_words;        /* zero blocks served from the fresh cursor / from the cleared pool; words cleared synchronously at a shortage */
    ArenaStats st;
    bool live;
    pthread_mutex_t mu;                /* the engine (under its lock) and kalloc's threads share the free lists */
} A = { .mu = PTHREAD_MUTEX_INITIALIZER };

void arena_init(void) {
    pthread_mutex_lock(&A.mu);
    if (A.live) { pthread_mutex_unlock(&A.mu); return; }
    size_t bytes = ARENA_WORDS * sizeof(uint64_t);
    void *p = mmap(NULL, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    require(p != MAP_FAILED, "arena: cannot reserve the address range");
    A.base = p; A.words = ARENA_WORDS; memset(A.heads, 0, sizeof A.heads); memset(&A.st, 0, sizeof A.st);
    A.heads[ARENA_ORDERS - 2] = A.base; *(uint64_t **)A.base = NULL;   /* the lower half: one block of the largest list order */
    A.fresh = 0;
    A.live = true;
    pthread_mutex_unlock(&A.mu);
}
/* the reservation lives for the process: kernel blocks (kalloc.c) outlive the engine's lifecycle; the engine returns its own blocks to the free lists */
void arena_free(void) { }
bool arena_live(void) { return A.live; }
const void *arena_base(void) { return A.base; }
ArenaStats arena_stats(void) { pthread_mutex_lock(&A.mu); ArenaStats s = A.st; pthread_mutex_unlock(&A.mu); return s; }

static unsigned order_of(size_t words) {
    unsigned k = 0; size_t b = ARENA_PAGE;
    while (b < words) { b <<= 1; k++; require(k < ARENA_ORDERS, "arena: block larger than the reservation"); }
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
/* the free-list link lives in the block's first word (kalloc poisons free blocks under ASan: the link word is unpoisoned for the list) */
static uint64_t *pop(unsigned k) { uint64_t *b = A.heads[k]; if (b) { LINK_UNPOISON(b); A.heads[k] = *(uint64_t **)b; } return b; }
static void push(unsigned k, uint64_t *b) { LINK_UNPOISON(b); *(uint64_t **)b = A.heads[k]; A.heads[k] = b; }
uint64_t *arena_alloc(size_t words, size_t *got) {
    if (!A.live) arena_init();
    unsigned k = order_of(words);
    pthread_mutex_lock(&A.mu);
    unsigned j = k; while (j < ARENA_ORDERS && !A.heads[j]) j++;
    require(j < ARENA_ORDERS, "arena: reservation exhausted");
    uint64_t *b = pop(j);
    while (j > k) { j--; push(j, b + ((size_t)ARENA_PAGE << j)); A.st.splits++; }   /* split: the upper half is freed at the lower order */
    A.st.allocs++; A.st.words_out += (size_t)ARENA_PAGE << k;
    pthread_mutex_unlock(&A.mu);
    BLOCK_UNPOISON(b, (size_t)ARENA_PAGE << k);   /* a block is addressable while allocated and poisoned while free (ASan) */
    if (got) *got = (size_t)ARENA_PAGE << k;
    return b;
}
/* zero blocks: a cleared block of the order from the reusable pool when
 * there is one, else a never-used block of the fresh region (zero by the
 * anonymous mapping). A retired zero-region block is dirty: it is cleared
 * CHUNK_WORDS per maintenance step (`arena_tend_zero`, driven once per unit
 * by the engine) and then published to the pool. When neither is available
 * and dirty blocks exist, the shortage clears a dirty block here, counted in
 * `zero_sync_words` (the fresh region is 2^30 words: the counted case is the
 * exhaustion of that). */
static bool zero_tend_locked(void) {
    if (!A.zactive) {
        for (unsigned k = 0; k < ARENA_ORDERS; k++) {
            uint64_t *b = A.zdirty[k]; if (!b) continue;
            LINK_UNPOISON(b); A.zdirty[k] = *(uint64_t **)b;
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
    if (end == w) {
        *(uint64_t **)b = A.zready[k]; A.zready[k] = b;
        A.zactive = NULL; A.zcursor = 0;
    }
    BLOCK_POISON(b, w);
    return true;
}
bool arena_tend_zero(void) { pthread_mutex_lock(&A.mu); bool did = zero_tend_locked(); pthread_mutex_unlock(&A.mu); return did; }
uint64_t *arena_alloc_zero(size_t words, size_t *got) {
    if (!A.live) arena_init();
    unsigned k = order_of(words); size_t w = (size_t)ARENA_PAGE << k;
    pthread_mutex_lock(&A.mu);
    uint64_t *b = A.zready[k];
    if (b) { LINK_UNPOISON(b); A.zready[k] = *(uint64_t **)b; BLOCK_UNPOISON(b, w); b[0] = 0; A.zero_reused++; }   /* the pool: the link word is zeroed again */
    else if (A.fresh + w <= ARENA_FRESH_WORDS) { b = A.base + ARENA_WORDS / 2 + A.fresh; A.fresh += w; A.zero_fresh++; BLOCK_UNPOISON(b, w); }
    else {   /* shortage: clear the dirty block of this order here, counted */
        require(A.zdirty[k] || (A.zactive && A.zorder == k), "arena: zero region exhausted and no dirty block to clear");
        while (!A.zready[k]) { uint64_t *d = A.zdirty[k]; (void)d; zero_tend_locked(); A.zero_sync_words += 32; }
        b = A.zready[k]; LINK_UNPOISON(b); A.zready[k] = *(uint64_t **)b; BLOCK_UNPOISON(b, w); b[0] = 0; A.zero_reused++;
    }
    A.st.allocs++; A.st.words_out += w;
    pthread_mutex_unlock(&A.mu);
    if (got) *got = w;
    return b;
}
void arena_release(uint64_t *p, size_t words) {
    if (!p || !A.live) return;
    if (p >= A.base + ARENA_WORDS / 2) {   /* a zero-region block: dirty until cleared in maintenance steps, then reusable */
        unsigned k = order_of(words);
        pthread_mutex_lock(&A.mu);
        LINK_UNPOISON(p); *(uint64_t **)p = A.zdirty[k]; A.zdirty[k] = p; A.st.releases++; A.st.words_in += (size_t)ARENA_PAGE << k;
        BLOCK_POISON(p, (size_t)ARENA_PAGE << k);
        pthread_mutex_unlock(&A.mu);
        return;
    }
    unsigned k = order_of(words);
    BLOCK_POISON(p, (size_t)ARENA_PAGE << k);
    pthread_mutex_lock(&A.mu);
    push(k, p); A.st.releases++; A.st.words_in += (size_t)ARENA_PAGE << k;
    pthread_mutex_unlock(&A.mu);
}

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
