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

void *pool_alloc(Pool *p) {
#ifdef POOL_DEBUG
    { void *x = calloc(1, p->size); require(x, "oom"); return x; }
#endif
    pthread_mutex_lock(&p->mu);
    if (!p->free) {
        /* one fixed-size block: a header word, then POOL_BLOCK objects */
        char *b = malloc(16 + POOL_BLOCK * p->size);
        require(b, "out of memory");
        *(void **)b = p->blocks; p->blocks = b;
        char *o = b + 16;
        for (size_t i = 0; i < POOL_BLOCK; i++) { *(void **)(o + i * p->size) = p->free; p->free = o + i * p->size; }
    }
    void *x = p->free;
    p->free = *(void **)x;
    pthread_mutex_unlock(&p->mu);
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
