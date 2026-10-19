#include "pool.h"

void pool_init(Pool *p, size_t size) {
    memset(p, 0, sizeof *p);
    p->size = size < sizeof(void *) ? sizeof(void *) : (size + 15) & ~(size_t)15;
    pthread_mutex_init(&p->mu, NULL);
}

void pool_destroy(Pool *p) {
    for (void *b = p->blocks; b; ) { void *next = *(void **)b; free(b); b = next; }
    pthread_mutex_destroy(&p->mu);
    memset(p, 0, sizeof *p);
}

/* one object, O(1) under the lock: a freed object, or the next object carved
 * from the current block by a bump. A new block is one fixed-size host
 * allocation made outside the lock (the allocation model: one bounded unit
 * per POOL_BLOCK objects); a thread that loses the race to install it keeps
 * it linked for teardown and carves from the installed one. */
void *pool_alloc(Pool *p) {
#ifdef POOL_DEBUG
    { void *x = calloc(1, p->size); require(x, "oom"); return x; }
#endif
    void *x = NULL;
    for (;;) {
        pthread_mutex_lock(&p->mu);
        if (p->free) { x = p->free; p->free = *(void **)x; }
        else if (p->left) { x = p->bump; p->bump += p->size; p->left--; }
        pthread_mutex_unlock(&p->mu);
        if (x) break;
        char *b = malloc(16 + POOL_BLOCK * p->size);
        require(b, "out of memory");
        pthread_mutex_lock(&p->mu);
        *(void **)b = p->blocks; p->blocks = b;
        if (!p->left) { p->bump = b + 16; p->left = POOL_BLOCK; }
        pthread_mutex_unlock(&p->mu);
    }
    memset(x, 0, p->size);
    return x;
}

void pool_free(Pool *p, void *x) {
#ifdef POOL_DEBUG
    { free(x); return; }
#endif
    pthread_mutex_lock(&p->mu);
    *(void **)x = p->free;
    p->free = x;
    pthread_mutex_unlock(&p->mu);
}
