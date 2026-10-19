/* count.c — exact counts (count.h). */
#include "common.h"
#include "count.h"

/* The writer changes only `low` on an ordinary increment (a reader sees the
 * old or the new value, both snapshots). An overflow is bracketed by the
 * sequence word (odd while the carry prefix and the low digit change), so a
 * reader that observes the same even sequence before and after its reads
 * holds a low digit consistent with its carry prefix. */
void count_bump(Count *c) {
    uint64_t l = __atomic_load_n(&c->low, __ATOMIC_RELAXED);
    if (l != UINT64_MAX) { __atomic_store_n(&c->low, l + 1, __ATOMIC_RELAXED); return; }
    Carry *b = malloc(sizeof *b);
    require(b, "out of memory: a carry block");
    b->next = __atomic_load_n(&c->carry, __ATOMIC_RELAXED);
    uint64_t s = __atomic_load_n(&c->seq, __ATOMIC_RELAXED);
    __atomic_store_n(&c->seq, s + 1, __ATOMIC_RELAXED);
    __atomic_thread_fence(__ATOMIC_RELEASE);
    __atomic_store_n(&c->carry, b, __ATOMIC_RELAXED);
    __atomic_store_n(&c->low, 0, __ATOMIC_RELAXED);
    __atomic_store_n(&c->seq, s + 2, __ATOMIC_RELEASE);
}
void count_free(Count *c) {
    for (Carry *b = c->carry, *n; b; b = n) { n = b->next; free(b); }
    c->carry = NULL; c->low = 0;
}

/* x += v · 2^(64·at) */
void exact_add_word(Exact *x, size_t at, uint64_t v) {
    for (size_t i = at; v; i++) {
        if (i >= x->n) {
            uint64_t *w = realloc(x->w, (i + 1) * sizeof *w);
            require(w, "out of memory: an exact reading");
            for (size_t j = x->n; j <= i; j++) w[j] = 0;
            x->w = w; x->n = i + 1;
        }
        uint64_t c = 0; x->w[i] = add_limb(x->w[i], v, &c); v = c;
    }
}
void exact_add_count(Exact *x, const Count *c) {
    uint64_t s1, s2, l; Carry *b;
    do {
        s1 = __atomic_load_n(&c->seq, __ATOMIC_ACQUIRE);
        b = __atomic_load_n(&c->carry, __ATOMIC_RELAXED);
        l = __atomic_load_n(&c->low, __ATOMIC_RELAXED);
        __atomic_thread_fence(__ATOMIC_ACQUIRE);
        s2 = __atomic_load_n(&c->seq, __ATOMIC_RELAXED);
    } while ((s1 & 1) || s1 != s2);
    exact_add_word(x, 0, l);
    for (; b; b = b->next) exact_add_word(x, 1, 1);    /* each carry block is 2^64 */
}
bool exact_to_u64(const Exact *x, uint64_t *out) {
    for (size_t i = 1; i < x->n; i++) if (x->w[i]) return false;
    *out = x->n ? x->w[0] : 0;
    return true;
}
void exact_free(Exact *x) { free(x->w); x->w = NULL; x->n = 0; }
