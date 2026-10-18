/* V23 R3–R5 closure (CONTINUATION-AND-COUNT-CLOSURE.md §§A–C).
 * White-box over the engine (includes work.c; link without work.o).
 *
 *   finite-long   — a finite kernel call needing 2^20+17 transitions, attached
 *                   to an engine frame, is destroyed at closed teardown (DROP):
 *                   no frame stack remains, it was not run to completion
 *   cycle         — two frame stacks waiting on each other (a genuine wait
 *                   cycle), in both allocation orders: dropped, none remains
 *   nested        — a stack suspended 12 frames deep, every frame owning a
 *                   release: every frame's drop runs once (innermost first)
 *   temporaries   — a stack suspended while its frame owns private
 *                   allocations: its drop frees them at teardown; 60
 *                   init/cancel/free cycles keep the allocator's owned
 *                   footprint stable
 *   index         — the ownership index with four-page extents: first,
 *                   middle and last extents, one-past-end, holes, foreign
 *                   pointers; every lookup visits at most one node per address byte
 *                   while the number of extents grows
 *   counts        — exact counts across 2^64: a fine counter, a reuse
 *                   counter, a closed scope with late contributions, a
 *                   frame stack's steps, eight threads updating while
 *                   snapshots are taken; checked word projections refuse
 * Run: test_v23_closure {finite-long|cycle|nested|temporaries|index|counts|all} */
#define _GNU_SOURCE
#include "work.c"
#include "fine.h"
#include "nat.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static int fails;
#define EXPECT(c, ...) do { if (!(c)) { fails++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static void init(void) { machine_init(); eval_init(); check_init(); compiler_init(); work_init(); }
static void done(void) { work_free(); compiler_free(); check_free(); eval_free(); machine_free(); }
/* attach a started frame stack to a fresh engine kernel frame (as the engine does) */
static OpId attach(KStack *k) {
    static uint64_t distinct; RefId key = mk_universe(++distinct);   /* a distinct shared key per attached stack */
    pthread_mutex_lock(&W.mu);
    OpId h = op_new(OF_KERNEL, PH_CHECK, kfr(KK_SHAPE_OF, key, 0, 0, 0));
    Op *o = JOB(HND(h)->job); Frame *f = top(o);
    k->job = o->id; f->ph = 1; f->acc = (uint64_t)(uintptr_t)k;
    pthread_mutex_unlock(&W.mu);
    return h;
}

/* ---- finite-long ---- */
static bool slow_done;
KF_DECL(finite_slow, void, KF_NOPARAMS, size_t i;)
KF_STEP(finite_slow) { KF_BEGIN(finite_slow); for (F->i = 0; F->i < ((size_t)1 << 20) + 17; F->i++) { fine_bump(FC_NAT_LIMBS); KF_SAFE(); } slow_done = true; ks->ok = true; KF_RETV(); KF_END; }
static void t_finite_long(void) {
    init();
    KStack *k = kf_new(); finite_slow_push(k, NULL);
    OpId h = attach(k); op_step(h, 1); EXPECT(!kf_done(k), "started, not complete"); op_release(h);
    KfStats s0 = kf_stats();
    done();
    KfStats st = kf_stats();
    EXPECT(st.live_stacks == 0 && !slow_done && st.cancelled == s0.cancelled + 1, "finite-long: dropped, not completed (stacks=%zu cancelled=%llu completed=%d)", st.live_stacks, (unsigned long long)(st.cancelled - s0.cancelled), slow_done);
    printf("finite-long: completed=%d frame stacks after teardown=%zu dropped stacks=%llu frames=%llu (no thread is involved)\n", slow_done, st.live_stacks, (unsigned long long)(st.cancelled - s0.cancelled), (unsigned long long)(st.dropped_frames - s0.dropped_frames));
}

/* ---- cycle ---- */
static pthread_mutex_t cyc_mu = PTHREAD_MUTEX_INITIALIZER; static pthread_cond_t cyc_cv = PTHREAD_COND_INITIALIZER;
static bool flag[2]; static KStack *peer[2];
KF_DECL(waiter, void, KF_NOPARAMS, int me;)
KF_STEP(waiter) {
    KF_BEGIN(waiter);
    F->me = (int)ks->arg[0];
    pthread_mutex_lock(&cyc_mu);
    while (!flag[1 - F->me]) KF_WAIT(&cyc_cv, &cyc_mu, peer[1 - F->me], peer[1 - F->me]->job);   /* each waits for the other: a genuine cycle */
    pthread_mutex_unlock(&cyc_mu);
    ks->ok = true;
    KF_RETV();
    KF_END;
}
static void t_cycle(int order) {
    init(); flag[0] = flag[1] = false;
    KStack *k0 = kf_new(), *k1 = kf_new(); k0->arg[0] = 0; k1->arg[0] = 1; waiter_push(k0, NULL); waiter_push(k1, NULL); peer[0] = k0; peer[1] = k1;
    if (order == 0) { kf_grant(k0, 8); kf_grant(k1, 8); } else { kf_grant(k1, 8); kf_grant(k0, 8); }   /* each runs into its wait */
    OpId h0, h1;
    if (order == 0) { h0 = attach(k0); h1 = attach(k1); } else { h1 = attach(k1); h0 = attach(k0); }
    EXPECT(!kf_done(k0) && !kf_done(k1) && k0->blocked && k1->blocked && k0->blocked_on == k1 && k1->blocked_on == k0, "cycle/%d: both suspended in their waits, each naming the other", order);
    op_release(h0); op_release(h1);
    done();
    KfStats st = kf_stats();
    EXPECT(st.live_stacks == 0, "cycle/%d: no frame stack after teardown (%zu)", order, st.live_stacks);
    printf("cycle order=%d: both waiting at teardown; frame stacks after=%zu\n", order, st.live_stacks);
}

/* ---- nested ---- */
static int released[16], release_seq, depth_reached;
#define nest_PARAMS(X) X(int, lvl)
KF_DECL_DROP(nest, void, nest_PARAMS, nest_drop, int owned;)
static void nest_drop(nest_F *F) { if (F->owned) { released[F->lvl] = ++release_seq; F->owned = 0; } }   /* this frame's release, at its phase */
KF_STEP(nest) {
    KF_BEGIN(nest);
    F->owned = 1;
    if (F->lvl < 11) KF_CALL(nest, NULL, F->lvl + 1);
    else { depth_reached = F->lvl; for (;;) { fine_bump(FC_NAT_LIMBS); KF_SAFE(); } }   /* suspends at a transition, never finishes */
    released[F->lvl] = ++release_seq; F->owned = 0;
    KF_RETV();
    KF_END;
}
static void t_nested(void) {
    init(); memset(released, 0, sizeof released); release_seq = 0;
    KfStats s0 = kf_stats();
    KStack *k = kf_new(); nest_push(k, NULL, 0);
    OpId h = attach(k); op_step(h, 1);
    for (int i = 0; i < 4 && !depth_reached; i++) op_step(h, 1);
    size_t depth_mid = k->depth;
    op_release(h);
    done();
    KfStats st = kf_stats();
    bool order = true; for (int l = 0; l < 12; l++) if (released[l] != 12 - l) order = false;
    EXPECT(depth_reached == 11 && depth_mid == 12 && order && st.live_stacks == 0 && st.dropped_frames - s0.dropped_frames == 12,
           "nested: 12 drops innermost first (depth=%d frames=%zu dropped=%llu)", depth_reached, depth_mid, (unsigned long long)(st.dropped_frames - s0.dropped_frames));
    printf("nested: depth=%d frames during=%zu dropped=%llu releases in order=%d\n", depth_reached, depth_mid, (unsigned long long)(st.dropped_frames - s0.dropped_frames), order);
}

/* ---- temporaries ---- */
static size_t temporaries_freed;
KF_DECL_DROP(with_temporaries, void, KF_NOPARAMS, with_temporaries_drop, void *t[8];)
static void with_temporaries_drop(with_temporaries_F *F) { for (int i = 0; i < 8; i++) if (F->t[i]) { free(F->t[i]); F->t[i] = NULL; temporaries_freed++; } }
KF_STEP(with_temporaries) {
    KF_BEGIN(with_temporaries);
    for (int i = 0; i < 8; i++) { F->t[i] = malloc((size_t)8192 << i); memset(F->t[i], 1, 64); }   /* private: never published */
    for (;;) { fine_bump(FC_NAT_LIMBS); KF_SAFE(); }
    KF_END;
}
static void t_temporaries_baseline(size_t *grow) {
    size_t a = 0;
    for (int c = 0; c < 60; c++) { init(); done(); if (c == 29) a = arena_owned_words(); }
    *grow = arena_owned_words() - a;
}
static void t_temporaries(void) {
    size_t base_growth; t_temporaries_baseline(&base_growth);
    size_t owned[60]; size_t freed0 = temporaries_freed;
    for (int c = 0; c < 60; c++) {
        init();
        KStack *k = kf_new(); with_temporaries_push(k, NULL);
        kf_grant(k, 4096);                                     /* runs past its allocations into its loop */
        OpId h = attach(k); op_release(h);
        done();
        owned[c] = arena_owned_words();
    }
    size_t freed = temporaries_freed - freed0;
    if (getenv("TMP_DEBUG")) for (int c = 0; c < 60; c += 5) printf("cycle %d owned %zu\n", c, owned[c]);
    EXPECT(freed == 60 * 8, "temporaries: each dropped frame released its private allocations (%zu)", freed);
    EXPECT(owned[59] == owned[29] && kf_stats().live_stacks == 0, "temporaries: stable owned footprint over cycles (%zu vs %zu words), no stack left", owned[29], owned[59]);
    printf("temporaries: machine init/free alone grows the owned footprint by %zu words over the same cycles\n", base_growth);
    printf("temporaries: 60 cycles, allocations released by drops=%zu, owned words after cycle 30=%zu after cycle 60=%zu\n", freed, owned[29], owned[59]);
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
KF_DECL(counting, void, KF_NOPARAMS, int i;)
KF_STEP(counting) { KF_BEGIN(counting); for (F->i = 0; F->i < 5; F->i++) { fine_bump(FC_NAT_LIMBS); KF_SAFE(); } ks->ok = true; KF_RETV(); KF_END; }
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
    /* a frame stack's steps across 2^64 */
    KStack *k = kf_new(); counting_push(k, NULL); k->steps = UINT64_MAX - 2 - XC_HALF; k->steps_carry = xc_carry_push(NULL);   /* the valid exact state 2^64 - 3 */
    while (!kf_done(k)) kf_grant(k, 1);
    XSnap kst = kf_steps(k);
    EXPECT(is_2_64_plus(kst, 2), "frame stack steps: 2^64 - 3 + 5 = 2^64 + 2 exactly");
    kf_free(k);
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
    printf("counts: fine=2^64+0 reuse=2^64+1 late=2^64+2 frame steps=2^64+2 concurrent=2^64+4999 monotone=%d\n", mono);
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
