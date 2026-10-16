/* §§89/94 allocator probe (white-box over work.c).
 *  1. Paged buffers never move: the address of every element stays fixed
 *     across 100 000 pushes; each push performs at most one arena allocation
 *     (a fixed page) and no host allocation.
 *  2. Slot-array growth is in units: driving an INTERN through a table at
 *     its load bound, each unit clears at most CHUNK_WORDS slots of the next
 *     array and relocates at most CHUNK_WORDS of the old one; the number of
 *     arena operations per unit is bounded by a constant.
 *  3. Releasing a frame whose buffer spans many pages is O(1) in its unit:
 *     the pages are retired and returned one per later unit.
 */
#include "work.c"
#include <assert.h>

static void probe_paged(void) {
    Paged p; paged_init(&p, sizeof(uint64_t));
    const size_t N = 100000; const uint64_t **addr = malloc(N * sizeof *addr); assert(addr);
    ArenaStats a0 = arena_stats(); uint64_t max_allocs = 0;
    for (size_t i = 0; i < N; i++) {
        ArenaStats b = arena_stats(); pw_push(&p, i); ArenaStats c = arena_stats();
        if (c.allocs - b.allocs > max_allocs) max_allocs = c.allocs - b.allocs;
        addr[i] = (const uint64_t *)paged_at(&p, i);
    }
    size_t moved = 0; for (size_t i = 0; i < N; i++) if ((const uint64_t *)paged_at(&p, i) != addr[i] || *addr[i] != i) moved++;
    ArenaStats a1 = arena_stats();
    printf("paged: pushes=%zu pages=%zu arena_allocs=%llu max_allocs_per_push=%llu elements_moved=%zu\n", N, paged_pages(&p), (unsigned long long)(a1.allocs - a0.allocs), (unsigned long long)max_allocs, moved);
    assert(moved == 0 && max_allocs <= 2);   /* a data page, and once a directory page */
    paged_retire(&p); free(addr);
}
static void probe_slots(void) {
    /* fill the table synchronously to just below its load bound, then drive one framed INTERN unit by unit */
    size_t k = 0;
    while ((W.tab.n + 2) * 2 <= W.tab.nslots) { uint64_t w[3] = { K_LIST, 0x5107, ++k }; intern_sync(w, 3, NULL); }
    assert(!W.tab.old && !W.tab.fresh);
    uint64_t key[4] = { K_LIST, 0x5107, 0xFFFF, 1 };
    OpId h = op_new(OF_INTERN, PH_REWRITE, fr_intern(key, 4));
    size_t nslots0 = W.tab.nslots, max_clear = 0, max_reloc = 0, units = 0, clear_units = 0; uint64_t max_ops = 0;
    while (op_status(h) == OP_RUNNING) {
        size_t c0 = W.tab.fresh ? W.tab.cleared : 0, r0 = W.tab.old ? W.tab.cursor : 0; bool had_fresh = W.tab.fresh != NULL, had_old = W.tab.old != NULL;
        ArenaStats b = arena_stats();
        op_step(h, 1); units++;
        ArenaStats c = arena_stats(); uint64_t ops = (c.allocs - b.allocs) + (c.releases - b.releases) + (c.splits - b.splits);
        if (ops > max_ops) max_ops = ops;
        if (had_fresh && W.tab.fresh) { size_t d = W.tab.cleared - c0; if (d > max_clear) max_clear = d; if (d) clear_units++; }
        if (had_old && W.tab.old) { size_t d = W.tab.cursor - r0; if (d > max_reloc) max_reloc = d; }
    }
    assert(op_status(h) == OP_COMPLETE && W.tab.nslots == 2 * nslots0 && !W.tab.fresh && !W.tab.old);
    printf("slots: %zu -> %zu; units=%zu clear_units=%zu max_slots_cleared_per_unit=%zu max_slots_relocated_per_unit=%zu max_arena_ops_per_unit=%llu\n", nslots0, W.tab.nslots, units, clear_units, max_clear, max_reloc, (unsigned long long)max_ops);
    assert(max_clear <= CHUNK_WORDS && max_reloc <= CHUNK_WORDS && max_ops <= ARENA_ORDERS + 2);
    assert(intern_sync(key, 4, NULL) == op_result(h));
    op_release(h);
}
static void probe_release(void) {
    /* a SORT frame whose buffer spans many pages: its completing unit releases at most one page */
    Frame f = fr(OF_SORT, K_SET, 0, 0, 0);
    const size_t N = 8 * ARENA_PAGE; for (size_t i = 0; i < N; i++) pw_push(&f.buf, 1000000 + (N - i));   /* descending: the sort does real work */
    size_t pages = paged_pages(&f.buf);
    OpId h = op_new(OF_SORT, PH_REWRITE, f);
    uint64_t max_rel = 0; size_t units = 0;
    while (op_status(h) == OP_RUNNING) { ArenaStats b = arena_stats(); op_step(h, 1); units++; ArenaStats c = arena_stats(); if (c.releases - b.releases > max_rel) max_rel = c.releases - b.releases; }
    assert(op_status(h) == OP_COMPLETE);
    size_t m; const uint64_t *w = rec_words(op_result(h), &m); assert(m == N + 1 && w[0] == K_SET && w[1] == 1000001 && w[N] == 1000000 + N);
    printf("release: buffer pages=%zu sort units=%zu max_page_releases_per_unit=%llu\n", pages, units, (unsigned long long)max_rel);
    assert(pages >= 8 && max_rel <= 1);
    op_release(h);
}
int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    probe_paged(); probe_slots(); probe_release();
    work_free(); compiler_free(); check_free(); eval_free(); machine_free(); return 0;
}
