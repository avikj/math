/* pool.h — fixed-size object pools.
 *
 * Allocation and release are O(1): a free list and a bump cursor under a
 * mutex whose critical section is a constant number of pointer writes. A
 * block of POOL_BLOCK objects is one fixed-size host allocation, made outside
 * the lock. Objects are never returned to the host before pool_destroy.
 */
#ifndef CUBICAL_POOL_H
#define CUBICAL_POOL_H

#include "common.h"
#include <pthread.h>

#define POOL_BLOCK 256

typedef struct {
    size_t size;              /* object size, at least one pointer */
    void *free;               /* singly linked through the first word */
    void *blocks;             /* linked through the first word of each block */
    char *bump; size_t left;  /* the current block's uncarved objects */
    pthread_mutex_t mu;
} Pool;

void pool_init(Pool *p, size_t size);
void pool_destroy(Pool *p);
void *pool_alloc(Pool *p);    /* zeroed object */
void pool_free(Pool *p, void *x);

#endif
