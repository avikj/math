/* pool.h — fixed-size object pools.
 *
 * Allocation and release are O(1). Each thread keeps a bounded free list per
 * pool (qualified by the pool's generation, so a destroyed pool's objects are
 * never reused); the shared free list and bump cursor, under a mutex whose
 * critical section is a constant number of pointer writes, refill or absorb
 * it. A block of POOL_BLOCK objects is one fixed-size host allocation, made
 * outside the lock. Objects are never returned to the host before
 * pool_destroy.
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
    uint64_t gen;             /* this pool's lifetime, never reused */
} Pool;

void pool_init(Pool *p, size_t size);
void pool_destroy(Pool *p);
void *pool_alloc(Pool *p);    /* zeroed object */
void pool_free(Pool *p, void *x);
void pool_thread_flush(void);  /* an exiting thread returns its cached objects to their pools */

#endif
