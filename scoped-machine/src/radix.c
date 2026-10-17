#include "common.h"
#include "radix.h"
#include "arena.h"

static size_t width(size_t x) { size_t d = 0; while ((x >>= RADIX_BITS)) d++; return d; }
void radix_init(Radix *r) { memset(r, 0, sizeof *r); }
static void **directory(void **slot, bool create) {
    void *p = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
    if (!p && create) {
        size_t words = (RADIX_FANOUT * sizeof(void *) + 7) / 8;
        /* One fixed directory page; clearing is bounded by RADIX_FANOUT. */
        void *fresh = arena_alloc(words, NULL), *expected = NULL;
        memset(fresh, 0, RADIX_FANOUT * sizeof(void *));
        if (__atomic_compare_exchange_n(slot, &expected, fresh, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) p = fresh;
        else { arena_release(fresh, words); p = expected; }
    }
    return p;
}
void **radix_slot(Radix *r, size_t index, bool create) {
    size_t d = width(index);
    void **p = directory(&r->root[d], create);
    if (!p) return NULL;
    while (d) {
        size_t k = (index >> (d * RADIX_BITS)) & (RADIX_FANOUT - 1);
        p = directory(&p[k], create);
        if (!p) return NULL;
        d--;
    }
    return &p[index & (RADIX_FANOUT - 1)];
}
void *radix_get(const Radix *r, size_t index) {
    void **slot = radix_slot((Radix *)r, index, false);
    return slot ? __atomic_load_n(slot, __ATOMIC_ACQUIRE) : NULL;
}
void radix_retire_begin(RadixRetire *s, Radix *r) { memset(s, 0, sizeof *s); s->tree = *r; radix_init(r); }
bool radix_retire_step(RadixRetire *s) {
    for (;;) {
        if (!s->depth) {
            while (s->root < RADIX_LEVELS && !s->tree.root[s->root]) s->root++;
            if (s->root == RADIX_LEVELS) return false;
            s->stack[0] = s->tree.root[s->root]; s->next[0] = 0; s->depth = 1;
        }
        size_t at = s->depth - 1;
        if (at < s->root) {
            void **p = s->stack[at];
            while (s->next[at] < RADIX_FANOUT && !p[s->next[at]]) s->next[at]++;
            if (s->next[at] < RADIX_FANOUT) {
                s->stack[s->depth] = p[s->next[at]++]; s->next[s->depth++] = 0; continue;
            }
        }
        arena_release(s->stack[at], (RADIX_FANOUT * sizeof(void *) + 7) / 8);
        s->depth--;
        if (!s->depth) s->tree.root[s->root++] = NULL;
        return true;
    }
}
static void release_tree(void **p, size_t level, RadixLeafFn fn, void *ctx) {
    for (size_t k = 0; k < RADIX_FANOUT; k++) if (p[k]) {
        if (level) release_tree(p[k], level - 1, fn, ctx);
        else if (fn) fn(p[k], ctx);
    }
    arena_release((uint64_t *)p, (RADIX_FANOUT * sizeof(void *) + 7) / 8);
}
void radix_free(Radix *r, RadixLeafFn fn, void *ctx) {
    for (size_t d = 0; d < RADIX_LEVELS; d++) if (r->root[d]) release_tree(r->root[d], d, fn, ctx);
    radix_init(r);
}
