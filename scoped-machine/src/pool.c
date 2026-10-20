#include "pool.h"

static uint64_t pool_gens;
/* a thread's cached free lists: direct-mapped by pool, a bounded count each.
 * A magazine that another pool displaces is spliced back into its own pool's
 * shared list (O(1): its tail is kept); one of a destroyed pool is dropped
 * with the pool's blocks. */
#define MAGS 32
#define MAG_CAP 64
typedef struct { Pool *p; uint64_t gen; void *free, *tail; size_t n; } Mag;
static __thread Mag tl_mag[MAGS];
static void mag_spill(Mag *m) {
    if (m->n && m->p && __atomic_load_n(&m->p->gen, __ATOMIC_RELAXED) == m->gen) {
        pthread_mutex_lock(&m->p->mu);
        *(void **)m->tail = m->p->free; m->p->free = m->free;
        pthread_mutex_unlock(&m->p->mu);
    }
    m->free = m->tail = NULL; m->n = 0;
}
static Mag *mag(Pool *p) {
    Mag *m = &tl_mag[((uintptr_t)p >> 4) % MAGS];
    if (m->p != p || m->gen != p->gen) { mag_spill(m); m->p = p; m->gen = p->gen; }
    return m;
}
void pool_thread_flush(void) { for (size_t i = 0; i < MAGS; i++) { mag_spill(&tl_mag[i]); tl_mag[i].p = NULL; } }
void pool_init(Pool *p, size_t size) {
    memset(p, 0, sizeof *p);
    p->gen = __atomic_add_fetch(&pool_gens, 1, __ATOMIC_RELAXED);
    p->size = size < sizeof(void *) ? sizeof(void *) : (size + 15) & ~(size_t)15;
    pthread_mutex_init(&p->mu, NULL);
}

void pool_destroy(Pool *p) {
    for (void *b = p->blocks; b; ) { void *next = *(void **)b; free(b); b = next; }
    pthread_mutex_destroy(&p->mu);
    memset(p, 0, sizeof *p);
}

/* one object, O(1) under the lock: a freed object, or the next object carved
 * from the current block by a bump. Otherwise one fixed-size host block is
 * allocated outside the lock — the declared resource boundary: one bounded
 * host allocation per POOL_BLOCK objects (a host action, not a counted
 * transition) — and the caller takes its first object; the block becomes the
 * bump block unless another thread installed one meanwhile, in which case
 * its remainder stays unused (kept for teardown). No retry. */
void *pool_alloc(Pool *p) {
#ifdef POOL_DEBUG
    { void *x = calloc(1, p->size); require(x, "oom"); return x; }
#endif
    void *x = NULL;
    Mag *m = mag(p);
    if (m->free) { x = m->free; m->free = *(void **)x; if (!--m->n) m->tail = NULL; memset(x, 0, p->size); return x; }
    pthread_mutex_lock(&p->mu);
    if (p->free) { x = p->free; p->free = *(void **)x; }
    else if (p->left) { x = p->bump; p->bump += p->size; p->left--; }
    pthread_mutex_unlock(&p->mu);
    if (!x) {
        char *b = malloc(16 + POOL_BLOCK * p->size);
        require(b, "out of memory");
        x = b + 16;
        pthread_mutex_lock(&p->mu);
        *(void **)b = p->blocks; p->blocks = b;
        if (!p->left) { p->bump = b + 16 + p->size; p->left = POOL_BLOCK - 1; }
        pthread_mutex_unlock(&p->mu);
    }
    memset(x, 0, p->size);
    return x;
}

void pool_free(Pool *p, void *x) {
#ifdef POOL_DEBUG
    { free(x); return; }
#endif
    Mag *m = mag(p);
    if (m->n < MAG_CAP) { *(void **)x = m->free; if (!m->n) m->tail = x; m->free = x; m->n++; return; }
    pthread_mutex_lock(&p->mu);
    *(void **)x = p->free;
    p->free = x;
    pthread_mutex_unlock(&p->mu);
}
