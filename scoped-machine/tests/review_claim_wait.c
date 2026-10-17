/* Deterministic staging of a valid claim-protocol interleaving.
 * Include the checker to access the same private transition functions;
 * link every core object except check.o. No production source is changed. */
#define _POSIX_C_SOURCE 200809L
#include "../src/check.c"
#include <sched.h>

static size_t dependent, outer;
static void *reader(void *unused) {
    (void)unused; uint64_t v;
    ENTER();
    require(claim_acquire(outer, &v, NULL, NULL) == ACQ_OWNER, "reader owns outer");
    Acq a = claim_acquire(dependent, &v, NULL, NULL);
    printf("provisional claim resumed: %d value %llu\n", (int)a, (unsigned long long)v);
    claim_release(outer, 1, NULL, NULL);
    LEAVE();
    words_free(&tl_pending);
    return NULL;
}
int main(void) {
    machine_init(); eval_init(); check_init();
    uint64_t key = 1, v;
    pthread_mutex_lock(&K.mu);
    size_t symbol = claim_index_locked(CL_SYMBOL, &key, 1);
    dependent = claim_index_locked(CL_CTX, &key, 1);
    key = 2; outer = claim_index_locked(CL_CTX, &key, 1);
    pthread_mutex_unlock(&K.mu);
    ENTER(); require(claim_acquire(symbol, &v, NULL, NULL) == ACQ_OWNER, "main owns symbol");
    pthread_mutex_lock(&K.mu);
    (*CLAIM(dependent)).state = 2; (*CLAIM(dependent)).result = 1;
    words_add(&CLAIM(dependent)->deps, symbol);
    pthread_mutex_unlock(&K.mu);
    pthread_t t; pthread_create(&t, NULL, reader, NULL);
    for (;;) {
        pthread_mutex_lock(&K.mu);
        bool waiting = K.wait_on.len > 2 && K.wait_on.data[2] == symbol + 1;
        pthread_mutex_unlock(&K.mu);
        if (waiting) break;
        sched_yield();
    }
    pthread_mutex_lock(&K.mu);
    /* Legal unrelated claims grow the vector while reader's wait unlocks it. */
    for (uint64_t k = 100; k < 300; k++) (void)claim_index_locked(CL_CTX, &k, 1);
    /* Main now needs reader's outer claim: actual cycle detection tells the
     * symbol waiter to resume by its declaration assumption. */
    require(may_block_locked(2, 1), "cycle is broken at symbol wait");
    pthread_mutex_unlock(&K.mu);
    claim_release(symbol, 1, NULL, NULL); LEAVE(); words_free(&tl_pending);
    pthread_join(t, NULL);
    check_free(); eval_free(); machine_free();
    return 0;
}
