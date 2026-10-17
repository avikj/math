/* V23 R3–R5 closure (CONTINUATION-AND-COUNT-CLOSURE.md §§A–C).
 * White-box over the engine (includes work.c; link without work.o).
 *
 *   finite-long   — a finite kernel call needing 2^20+17 transitions, attached
 *                   to an engine frame, is destroyed at closed teardown: zero
 *                   native workers remain, it was not run to completion
 *   cycle         — two continuations waiting on each other (a genuine wait
 *                   cycle), in both allocation orders: destroyed, zero workers
 *   nested        — a continuation suspended 12 stack segments deep with a
 *                   registered release at every level: every release runs
 *                   once (innermost first), every segment is unmapped
 *   temporaries   — a continuation suspended while owning private
 *                   allocations: they are reaped after the machine's
 *                   structures; 30 init/cancel/free cycles keep the
 *                   allocator's owned footprint and the worker count stable
 *   index         — the ownership index with four-page extents: first,
 *                   middle and last extents, one-past-end, holes, foreign
 *                   pointers; every lookup visits at most one node per address byte
 *                   while the number of extents grows
 *   counts        — exact counts across 2^64: a fine counter, a reuse
 *                   counter, a closed scope with late contributions, a
 *                   continuation's steps, eight threads updating while
 *                   snapshots are taken; checked word projections refuse
 * Run: test_v23_closure {finite-long|cycle|nested|temporaries|index|counts|all} */
#define _GNU_SOURCE
#include "work.c"
#include "kstack.h"
#include "fine.h"
#include "nat.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static int fails;
#define EXPECT(c, ...) do { if (!(c)) { fails++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static void init(void) { machine_init(); eval_init(); check_init(); compiler_init(); work_init(); }
static void done(void) { work_free(); compiler_free(); check_free(); eval_free(); machine_free(); }
/* attach a started continuation to a fresh engine kernel frame (as the engine does) */
static OpId attach(KCont *k) {
    static uint64_t distinct; RefId key = mk_universe(++distinct);   /* a distinct shared key per attached continuation */
    pthread_mutex_lock(&W.mu);
    OpId h = op_new(OF_KERNEL, PH_CHECK, kfr(KK_SHAPE_OF, key, 0, 0, 0));
    Op *o = JOB(HND(h)->job); Frame *f = top(o);
    k->job = o->id; f->ph = 1; f->acc = (uint64_t)(uintptr_t)k;
    pthread_mutex_unlock(&W.mu);
    return h;
}

/* ---- finite-long ---- */
static bool slow_done;
static void finite_slow(KCont *k) { for (size_t i = 0; i < ((size_t)1 << 20) + 17; i++) fine_bump(FC_NAT_LIMBS); slow_done = true; k->ok = true; }
static void t_finite_long(void) {
    init();
    KCont *k = kc_new(finite_slow, NULL, 0);
    OpId h = attach(k); op_step(h, 1); EXPECT(!kc_done(k), "started, not complete"); op_release(h);
    size_t c0 = kc_stats().cancelled;
    done();
    KcStats st = kc_stats();
    EXPECT(st.live_workers == 0 && !slow_done && st.cancelled == c0 + 1, "finite-long: destroyed, not completed (workers=%zu cancelled=%zu completed=%d)", st.live_workers, st.cancelled - c0, slow_done);
    printf("finite-long: completed=%d workers after teardown=%zu cancelled=%zu\n", slow_done, st.live_workers, st.cancelled - c0);
}

/* ---- cycle ---- */
static pthread_mutex_t cyc_mu = PTHREAD_MUTEX_INITIALIZER; static pthread_cond_t cyc_cv = PTHREAD_COND_INITIALIZER;
static bool flag[2]; static KCont *peer[2];
static void waiter(KCont *k) {
    int me = (int)k->arg[0];
    pthread_mutex_lock(&cyc_mu);
    while (!flag[1 - me]) kc_wait(&cyc_cv, &cyc_mu, peer[1 - me]);   /* each waits for the other: a genuine cycle */
    pthread_mutex_unlock(&cyc_mu);
    k->ok = true;
}
static void t_cycle(int order) {
    init(); flag[0] = flag[1] = false;
    uint64_t a0[1] = { 0 }, a1[1] = { 1 };
    KCont *k0 = kc_new(waiter, a0, 1), *k1 = kc_new(waiter, a1, 1); peer[0] = k0; peer[1] = k1;
    if (order == 0) { kc_grant(k0, 8); kc_grant(k1, 8); } else { kc_grant(k1, 8); kc_grant(k0, 8); }   /* each runs into its wait */
    OpId h0, h1;
    if (order == 0) { h0 = attach(k0); h1 = attach(k1); } else { h1 = attach(k1); h0 = attach(k0); }
    EXPECT(!kc_done(k0) && !kc_done(k1) && k0->blocked && k1->blocked, "cycle/%d: both suspended in their waits", order);
    op_release(h0); op_release(h1);
    done();
    KcStats st = kc_stats();
    EXPECT(st.live_workers == 0, "cycle/%d: zero workers after teardown (%zu)", order, st.live_workers);
    printf("cycle order=%d: both waiting at teardown; workers after=%zu\n", order, st.live_workers);
}

/* ---- nested ---- */
static int released[16], release_seq, depth_reached;
static void rel(void *p) { int lvl = (int)(intptr_t)p; released[lvl] = ++release_seq; }
static void nest(void *p) {
    int lvl = (int)(intptr_t)p;
    KCleanup c; kc_cleanup_push(&c, rel, (void *)(intptr_t)lvl);
    if (lvl < 11) kstack_run(nest, (void *)(intptr_t)(lvl + 1));
    else { depth_reached = lvl; for (;;) fine_bump(FC_NAT_LIMBS); }   /* suspends at a transition, never finishes */
    kc_cleanup_pop(&c);
}
static void nested_call(KCont *k) { nest((void *)(intptr_t)0); k->ok = true; }
static void t_nested(void) {
    init(); memset(released, 0, sizeof released); release_seq = 0;
    size_t segs0 = kstack_live_segments();
    KCont *k = kc_new(nested_call, NULL, 0);
    OpId h = attach(k); op_step(h, 1);
    for (int i = 0; i < 4 && !depth_reached; i++) op_step(h, 1);
    size_t segs_mid = kstack_live_segments();
    op_release(h);
    done();
    bool order = true; for (int l = 0; l < 12; l++) if (released[l] != 12 - l) order = false;
    EXPECT(depth_reached == 11 && segs_mid == segs0 + 11 && kstack_live_segments() == segs0 && order && kc_stats().live_workers == 0,
           "nested: 12 releases innermost first, 11 segments unmapped (depth=%d segments %zu->%zu->%zu)", depth_reached, segs0, segs_mid, kstack_live_segments());
    printf("nested: depth=%d live segments during=%zu after=%zu releases in order=%d unwound cleanups total=%zu\n", depth_reached, segs_mid - segs0, kstack_live_segments() - segs0, order, kc_stats().unwound_cleanups);
}

/* ---- temporaries ---- */
static void with_temporaries(KCont *k) {
    void *t[8]; for (int i = 0; i < 8; i++) { t[i] = malloc((size_t)8192 << i); memset(t[i], 1, 64); }   /* private: never published */
    for (;;) fine_bump(FC_NAT_LIMBS);
    for (int i = 0; i < 8; i++) free(t[i]);
    k->ok = true;
}
static void t_temporaries_baseline(size_t *grow) {
    size_t a = 0;
    for (int c = 0; c < 60; c++) { init(); done(); if (c == 29) a = arena_owned_words(); }
    *grow = arena_owned_words() - a;
}
static void t_temporaries(void) {
    size_t base_growth; t_temporaries_baseline(&base_growth);
    size_t owned[60]; size_t reaped0 = kc_stats().reaped_allocations;
    for (int c = 0; c < 60; c++) {
        init();
        KCont *k = kc_new(with_temporaries, NULL, 0);
        kc_grant(k, 4096);                                     /* runs past its allocations into its loop */
        OpId h = attach(k); op_release(h);
        done();
        owned[c] = arena_owned_words();
    }
    size_t reaped = kc_stats().reaped_allocations - reaped0;
    if (getenv("TMP_DEBUG")) for (int c = 0; c < 60; c += 5) printf("cycle %d owned %zu\n", c, owned[c]);
    EXPECT(reaped >= 60 * 8, "temporaries: each cancelled continuation's private allocations reaped (%zu)", reaped);
    EXPECT(owned[59] == owned[29] && kc_stats().live_workers == 0, "temporaries: stable owned footprint over cycles (%zu vs %zu words) and zero workers", owned[29], owned[59]);
    printf("temporaries: machine init/free alone grows the owned footprint by %zu words over the same cycles\n", base_growth);
    printf("temporaries: 60 cycles, reaped allocations=%zu, owned words after cycle 30=%zu after cycle 60=%zu, workers=%zu\n", reaped, owned[29], owned[59], kc_stats().live_workers);
}

/* ---- index ---- */
static void t_index(void) {
    init();
    arena_set_extent_policy(4 * ARENA_PAGE);
    size_t maxsteps = 0, checks = 0; bool all_ok = true;
    for (int round = 0; round < 6; round++) {
        size_t e0 = arena_extents(); while (arena_extents() < e0 + 5) (void)arena_alloc(3 * ARENA_PAGE, NULL);   /* grows the extent list by five four-page extents */
        size_t ne = arena_extents();
        size_t pick[3] = { 0, ne / 2, ne - 1 };
        for (int q = 0; q < 3; q++) {
            uintptr_t b, e; if (!arena_extent_bounds(pick[q], &b, &e)) continue;
            size_t s1, s2, s3, s4;
            bool in1 = arena_owns_steps((void *)b, &s1), in2 = arena_owns_steps((void *)(b + (e - b) / 2), &s2), in3 = arena_owns_steps((void *)(e - 1), &s3);
            bool past = arena_owns_steps((void *)e, &s4);
            bool past_owned = false; for (size_t j = 0; j < ne; j++) { uintptr_t b2, e2; if (arena_extent_bounds(j, &b2, &e2) && e >= b2 && e < e2) past_owned = true; }   /* adjacent extent */
            all_ok = all_ok && in1 && in2 && in3 && past == past_owned;
            size_t m = s1 > s2 ? s1 : s2; m = m > s3 ? m : s3; m = m > s4 ? m : s4; if (m > maxsteps) maxsteps = m;
            checks += 4;
        }
        int local; void *host = (malloc)(64); size_t s5, s6;
        bool f1 = arena_owns_steps(&local, &s5), f2 = arena_owns_steps(host, &s6); (free)(host);
        all_ok = all_ok && !f1 && !f2; if (s5 > maxsteps) maxsteps = s5; if (s6 > maxsteps) maxsteps = s6; checks += 2;
        /* holes: the word below the lowest extent and above the highest */
        uintptr_t lo = UINTPTR_MAX, hi = 0;
        for (size_t j = 0; j < ne; j++) { uintptr_t b2, e2; if (arena_extent_bounds(j, &b2, &e2)) { if (b2 < lo) lo = b2; if (e2 > hi) hi = e2; } }
        size_t s7, s8; bool h1 = arena_owns_steps((void *)(lo - 8), &s7), h2 = arena_owns_steps((void *)hi, &s8);
        all_ok = all_ok && !h1 && !h2; checks += 2;
        printf("index round %d: extents=%zu index nodes=%zu max nodes per lookup so far=%zu\n", round, ne, arena_index_nodes(), maxsteps);
    }
    EXPECT(all_ok, "index: membership exact for first/middle/last extents, one-past-end, holes and foreign pointers");
    EXPECT(maxsteps <= sizeof(uintptr_t), "index: lookups bounded by the address width in bytes (%zu)", maxsteps);
    printf("index: %zu queries, max nodes per lookup=%zu (bound %zu)\n", checks, maxsteps, sizeof(uintptr_t));
    arena_set_extent_policy((size_t)ARENA_PAGE << 11);   /* the default growth policy */
    done();
}

/* ---- counts ---- */
static bool is_2_64_plus(XSnap s, uint64_t k) { uint64_t l[2] = { k, 1 }; return xs_nat(s) == nat_from_limbs(2, l); }
static XCount shared;
static void *hammer(void *p) { (void)p; for (int i = 0; i < 1000; i++) xc_inc(&shared); return NULL; }
static void counting(KCont *k) { for (int i = 0; i < 5; i++) fine_bump(FC_NAT_LIMBS); k->ok = true; }
static void t_counts(void) {
    init();
    uint64_t w;
    fine_seed(FC_NAT_LIMBS, UINT64_MAX); fine_bump(FC_NAT_LIMBS);
    XSnap f = fine_snap(FC_NAT_LIMBS);
    EXPECT(is_2_64_plus(f, 0) && !xs_u64(f, &w), "fine counter reads exactly 2^64 after one real event; the word projection refuses");
    reuse_seed(REUSE_BETA, UINT64_MAX - 1);
    ReuseScope *sc = reuse_scope_new(PH_EXECUTE); ReuseScope *prev = reuse_scope_enter(sc);
    xc_seed(&sc->c[REUSE_BETA], UINT64_MAX);
    reuse_bump(REUSE_BETA); reuse_bump(REUSE_BETA);
    XSnap late0 = reuse_scope_late_snap(PH_EXECUTE, REUSE_BETA);
    reuse_scope_close(sc);
    reuse_bump(REUSE_BETA);                                   /* a late event of the closed scope */
    reuse_scope_leave(prev); reuse_scope_unref(sc);
    XSnap g = reuse_snap(REUSE_BETA), late = reuse_scope_late_snap(PH_EXECUTE, REUSE_BETA);
    uint64_t d;
    EXPECT(is_2_64_plus(g, 1), "global reuse counter: 2^64 - 2 + 3 = 2^64 + 1 exactly");
    EXPECT(xs_u64(late0, &d) && d == 0 && is_2_64_plus(late, 2), "closed scope folded once: 2^64 - 1 + 2 into the late total, then its late event: 2^64 + 2");
    /* a continuation's steps across 2^64 */
    KCont *k = kc_new(counting, NULL, 0); k->steps = UINT64_MAX - 2 - XC_HALF; k->steps_carry = xc_carry_push(NULL);   /* the valid exact state 2^64 - 3 */
    while (!kc_done(k)) kc_grant(k, 1);
    XSnap ks = kc_steps(k);
    EXPECT(is_2_64_plus(ks, 2), "continuation steps: 2^64 - 3 + 5 = 2^64 + 2 exactly");
    kc_free(k);
    /* concurrent updates and snapshots near the boundary */
    xc_seed(&shared, UINT64_MAX - 3000);
    pthread_t th[8]; for (int i = 0; i < 8; i++) pthread_create(&th[i], NULL, hammer, NULL);
    bool mono = true; Nat last = 0;
    for (int i = 0; i < 2000; i++) { Nat v = xs_nat(xc_snap(&shared)); if (nat_compare(v, last) < 0) mono = false; last = v; }
    for (int i = 0; i < 8; i++) pthread_join(th[i], NULL);
    XSnap fin = xc_snap(&shared);
    EXPECT(mono && is_2_64_plus(fin, 4999), "eight writers across the boundary: snapshots monotone, final 2^64 - 3001 + 8000 = 2^64 + 4999 exactly");
    uint64_t dd; XSnap a = { 5, NULL }, b = { 7, NULL };
    EXPECT(!xs_delta_u64(a, b, &dd), "a delta of out-of-order snapshots is refused, not wrapped");
    printf("counts: fine=2^64+0 reuse=2^64+1 late=2^64+2 kcont steps=2^64+2 concurrent=2^64+4999 monotone=%d\n", mono);
    fine_seed(FC_NAT_LIMBS, 0); reuse_seed(REUSE_BETA, 0); xc_reset(&shared);
    done();
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    const char *m = argc > 1 ? argv[1] : "all"; bool all = !strcmp(m, "all");
    if (all || !strcmp(m, "finite-long")) t_finite_long();
    if (all || !strcmp(m, "cycle")) { t_cycle(0); t_cycle(1); }
    if (all || !strcmp(m, "nested")) t_nested();
    if (all || !strcmp(m, "temporaries")) t_temporaries();
    if (all || !strcmp(m, "index")) t_index();
    if (all || !strcmp(m, "counts")) t_counts();
    printf("test_v23_closure %s: %d failures\n", m, fails);
    return fails ? 1 : 0;
}
