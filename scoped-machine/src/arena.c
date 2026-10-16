#include "common.h"
#include "arena.h"
#include <sys/mman.h>
#include <string.h>

/* ---- the reservation and the free lists ---- */
static struct {
    uint64_t *base; size_t words;
    uint64_t *heads[ARENA_ORDERS];     /* free lists: the first word of a free block links the next */
    ArenaStats st;
    bool live;
} A;

void arena_init(void) {
    if (A.live) return;
    size_t bytes = ARENA_WORDS * sizeof(uint64_t);
    void *p = mmap(NULL, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    require(p != MAP_FAILED, "arena: cannot reserve the address range");
    A.base = p; A.words = ARENA_WORDS; memset(A.heads, 0, sizeof A.heads); memset(&A.st, 0, sizeof A.st);
    A.heads[ARENA_ORDERS - 1] = A.base; *(uint64_t **)A.base = NULL;   /* one block of the largest order */
    A.live = true;
}
void arena_free(void) { if (!A.live) return; munmap(A.base, A.words * sizeof(uint64_t)); memset(&A, 0, sizeof A); }
bool arena_live(void) { return A.live; }
ArenaStats arena_stats(void) { return A.st; }

static unsigned order_of(size_t words) {
    unsigned k = 0; size_t b = ARENA_PAGE;
    while (b < words) { b <<= 1; k++; require(k < ARENA_ORDERS, "arena: block larger than the reservation"); }
    return k;
}
size_t arena_order_words(size_t words) { return (size_t)ARENA_PAGE << order_of(words); }
static uint64_t *pop(unsigned k) { uint64_t *b = A.heads[k]; if (b) A.heads[k] = *(uint64_t **)b; return b; }
static void push(unsigned k, uint64_t *b) { *(uint64_t **)b = A.heads[k]; A.heads[k] = b; }
uint64_t *arena_alloc(size_t words, size_t *got) {
    require(A.live, "arena: not initialized");
    unsigned k = order_of(words);
    unsigned j = k; while (j < ARENA_ORDERS && !A.heads[j]) j++;
    require(j < ARENA_ORDERS, "arena: reservation exhausted");
    uint64_t *b = pop(j);
    while (j > k) { j--; push(j, b + ((size_t)ARENA_PAGE << j)); A.st.splits++; }   /* split: the upper half is freed at the lower order */
    A.st.allocs++; A.st.words_out += (size_t)ARENA_PAGE << k;
    if (got) *got = (size_t)ARENA_PAGE << k;
    return b;
}
void arena_release(uint64_t *p, size_t words) {
    if (!p || !A.live) return;
    unsigned k = order_of(words);
    push(k, p); A.st.releases++; A.st.words_in += (size_t)ARENA_PAGE << k;
}

/* ---- paged buffers ---- */
static void *page_new(void) { return arena_alloc(ARENA_PAGE, NULL); }
static void page_del(void *p) { arena_release(p, ARENA_PAGE); }

void paged_init(Paged *p, size_t elem) {
    require(elem && elem <= ARENA_PAGE * sizeof(uint64_t), "paged: element size");
    memset(p, 0, sizeof *p); p->elem = elem; p->per = (ARENA_PAGE * sizeof(uint64_t)) / elem;
}
static void *page_ptr(const Paged *p, size_t k) {   /* page k (exists) */
    if (k == 0) return p->pg0;
    if (k < PAGED_DIR) return p->dir[k];
    return p->dir2[k / PAGED_DIR][k % PAGED_DIR];
}
static void page_set(Paged *p, size_t k, void *pg) {
    if (k == 0) { p->pg0 = pg; return; }
    if (k < PAGED_DIR) { if (!p->dir) p->dir = page_new(); p->dir[k] = pg; return; }
    require(k / PAGED_DIR < PAGED_DIR, "paged: buffer exhausted");
    if (!p->dir2) p->dir2 = page_new();
    if (k % PAGED_DIR == 0) p->dir2[k / PAGED_DIR] = page_new();
    p->dir2[k / PAGED_DIR][k % PAGED_DIR] = pg;
}
void *paged_at(const Paged *p, size_t i) { require(i < p->n, "paged: index"); return (char *)page_ptr(p, i / p->per) + (i % p->per) * p->elem; }
void *paged_push(Paged *p) {
    size_t i = p->n; size_t k = i / p->per;
    if (k >= p->pages) { page_set(p, k, page_new()); p->pages = k + 1; }   /* a new page: one fixed-size block from the free list */
    p->n++;
    return (char *)page_ptr(p, k) + (i % p->per) * p->elem;
}
size_t paged_pages(const Paged *p) { return p->pages; }

/* retirement: a buffer's pages and directory pages are released one per
 * `arena_reap`. The queue is intrusive: a retiree's descriptor lives in its
 * own page 0 (every retiree has one) */
typedef struct { size_t pages, per, elem; void **dir; void ***dir2; size_t subdirs; void *next; } Retiree;
static Retiree *R_head, *R_tail;
static void enqueue(Retiree *r) { r->next = NULL; if (R_tail) R_tail->next = r; else R_head = r; R_tail = r; }
void paged_retire(Paged *p) {
    if (!p->pg0) { memset(p, 0, sizeof *p); return; }   /* never had a page */
    Retiree *r = (Retiree *)p->pg0;   /* page 0 is 4 KiB: the descriptor fits */
    Retiree d = { p->pages, p->per, p->elem, p->dir, p->dir2, 0, NULL };
    if (d.dir2) for (size_t s = 0; s < PAGED_DIR && d.dir2[s]; s++) d.subdirs = s + 1;
    *r = d; enqueue(r);
    size_t elem = p->elem; memset(p, 0, sizeof *p); p->elem = elem; p->per = (ARENA_PAGE * sizeof(uint64_t)) / elem;
}
bool arena_reap(void) {
    Retiree *r = R_head; if (!r) return false;
    if (r->pages > 1) {   /* data pages from the top down (page 0 holds the descriptor: last) */
        size_t k = r->pages - 1; void *pg = k < PAGED_DIR ? r->dir[k] : r->dir2[k / PAGED_DIR][k % PAGED_DIR];
        page_del(pg); r->pages--; return true;
    }
    if (r->subdirs) { page_del(r->dir2[--r->subdirs]); return true; }
    if (r->dir2) { page_del(r->dir2); r->dir2 = NULL; return true; }
    if (r->dir) { page_del(r->dir); r->dir = NULL; return true; }
    R_head = r->next; if (!R_head) R_tail = NULL;
    page_del(r);      /* page 0 last */
    return true;
}
void arena_reap_all(void) { while (arena_reap()) ; }
void paged_pop(Paged *p) { require(p->n, "paged: pop on empty"); p->n--; }   /* pages are kept for reuse; released at retirement */
void paged_truncate(Paged *p, size_t n) { require(n <= p->n, "paged: truncate"); p->n = n; }
void paged_take(Paged *dst, Paged *src) { paged_retire(dst); *dst = *src; size_t elem = src->elem; memset(src, 0, sizeof *src); src->elem = elem; src->per = dst->per; }
