/* §94 store growth: when the record store has no capacity for a reservation,
 * one INTERN unit allocates the new block (no copy), the following units
 * relocate the old block at most CHUNK_WORDS words each, records stay
 * readable (and findable by a framed LOOKUP) throughout, and the reservation
 * happens only after the relocation completes. White-box over work.c. */
#include "work.c"
#include <assert.h>

static size_t fill_to_capacity(void) {
    /* synchronous interning until the store (at least 4096 words) is full modulo a few words */
    size_t k = 0;
    while (W.tab.store.cap < 4096 || W.tab.store.cap - W.tab.store.n > 8) { uint64_t w[3] = { K_LIST, 0x51e0, 2 + ++k }; intern_sync(w, 3, NULL); }
    return k;
}
int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    uint64_t probe_key[3] = { K_LIST, 0x51e0, 1 }; uint64_t first = intern_sync(probe_key, 3, NULL);
    size_t n = 64; uint64_t *key = malloc(n * sizeof *key); assert(key); key[0] = K_LIST; for (size_t i = 1; i < n; i++) key[i] = 2000000 + i;
    OpId h = op_new(OF_INTERN, PH_REWRITE, fr_intern(key, n));   /* (the job key record is interned synchronously here) */
    size_t made = fill_to_capacity();
    size_t steps = 0; while (top(JOB(HND(h)->job))->ph != 5) { assert(op_step(h, 1) == OP_RUNNING); assert(++steps < 4 * n + 1000); }
    size_t old_n = W.tab.store.n, old_cap = W.tab.store.cap; uint64_t *old_block = W.tab.store.w;
    assert(old_cap - old_n < n + 2 && !W.tab.sold);   /* no room for the reservation, no relocation pending */
    /* unit 1 at ph 5: the new block is allocated, nothing copied, nothing reserved */
    assert(op_step(h, 1) == OP_RUNNING);
    assert(W.tab.sold == old_block && W.tab.sold_n == old_n && W.tab.smoved == 0);
    assert(W.tab.store.w != old_block && W.tab.store.cap >= old_n + n + 2 && W.tab.store.n == old_n);
    printf("growth unit: new block allocated, words copied=0, store.n unchanged=%d\n", W.tab.store.n == old_n);
    /* relocation units: at most CHUNK_WORDS words each; records readable and findable meanwhile */
    size_t units = 0, max_copied = 0;
    while (W.tab.sold) {
        size_t before = W.tab.smoved;
        assert(op_step(h, 1) == OP_RUNNING); units++;
        size_t copied = W.tab.sold ? W.tab.smoved - before : old_n - before;
        if (copied > max_copied) max_copied = copied;
        size_t m; const uint64_t *w = rec_words(first, &m); assert(m == 3 && w[0] == K_LIST && w[2] == 1);   /* read during relocation */
        assert(find_sync(probe_key, 3) == first);                                                        /* fixed-key find during relocation */
        assert(W.tab.store.n == old_n);                                                                   /* no reservation before the relocation completes */
    }
    printf("relocation units=%zu max_words_per_unit=%zu (CHUNK_WORDS=%d) expected_units=%zu\n", units, max_copied, (int)CHUNK_WORDS, (old_n + CHUNK_WORDS - 1) / CHUNK_WORDS);
    assert(max_copied <= CHUNK_WORDS && units == (old_n + CHUNK_WORDS - 1) / CHUNK_WORDS);
    /* then the reservation and copy complete to the correct canonical record */
    while (op_status(h) == OP_RUNNING) op_step(h, 1);
    assert(op_status(h) == OP_COMPLETE); uint64_t id = op_result(h); size_t m; const uint64_t *got = rec_words(id, &m); assert(m == n);
    for (size_t i = 0; i < n; i++) assert(got[i] == key[i]);
    assert(intern_sync(key, n, NULL) == id);
    { size_t m2; const uint64_t *w = rec_words(first, &m2); assert(m2 == 3 && w[2] == 1); }
    printf("completed record correct and canonical=1; %zu earlier records intact\n", made);
    op_release(h); free(key);
    work_free(); compiler_free(); check_free(); eval_free(); machine_free(); return 0;
}
