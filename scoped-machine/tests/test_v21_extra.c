/* V21 acceptance beyond review_v21.c (REVIEW.md R2–R5 "Acceptance" lists).
 *   ledger-mixed   — serial vs interleaved shape and inference kernel jobs:
 *                    exclusive charges equal actual events for the shape,
 *                    dependency-check and receipt classes, with and without
 *                    four evaluator workers
 *   wait-shared    — two consumers of one producer both name its owner; an
 *                    unrelated continuation stays suspended throughout and the
 *                    consumers complete
 *   wait-early     — a predicate wait is discharged when the awaited producer
 *                    publishes, before the owning continuation's whole call
 *                    returns
 *   growth         — claims, root occurrences and queue positions across several
 *                    chunk boundaries (CHUNK_SIZE = 2048): results stay exact
 *   cleanup-orders — teardown with the dependency allocated after / started
 *                    before the consumer, two consumers, released handles
 * Run: test_v21_extra {ledger-mixed|wait-shared|wait-early|growth|cleanup-orders} */
#include "work.c"
#include "fine.h"
#include <assert.h>
#include <string.h>

static void init(void) { machine_init(); eval_init(); check_init(); compiler_init(); work_init(); }
static void done(void) { work_free(); compiler_free(); check_free(); eval_free(); machine_free(); }
static OpId kernel(uint64_t kind, uint64_t a, uint64_t b, uint64_t c, uint64_t d) {
    pthread_mutex_lock(&W.mu); OpId h = op_new(OF_KERNEL, PH_CHECK, kfr(kind, a, b, c, d)); pthread_mutex_unlock(&W.mu); return h;
}
static void finish(OpId h) { size_t n = 0; while (op_status(h) == OP_RUNNING && n++ < 4000000) op_step(h, 1); assert(op_status(h) == OP_COMPLETE); }

static int ledger_mixed(void) {
    int bad = 0;
    for (int workers = 0; workers <= 4; workers += 4) for (int inter = 0; inter < 2; inter++) {
        init(); if (workers) eval_set_workers((size_t)workers);
        RefId U = mk_universe(0); TermVarId va = declare_term(U, fc_true()); RefId A = ref_var(va);
        TermVarId vx = declare_term(A, fc_true()); RefId x = ref_var(vx);
        RefId f = ref_var(declare_term(mk_fun(0, 0, A, A), fc_true()));
        RefId a = x; for (size_t i = 0; i < 12; i++) a = mk_app(f, a);
        CtxDecl ds[] = { { S_TERM, va, U }, { S_TERM, vx, A } }; ContextId G = context_make(2, ds, fc_true());
        RefId t = mk_refl(0, A, x);
        static const ReuseCounter rcs[3] = { REUSE_SHAPE_NODE, REUSE_DEPENDENCY_CHECK, REUSE_RECEIPT_INSTANCE };
        static const FrameFamily frs[3] = { FR_SHAPE_NODE, FR_DEPENDENCY_CHECK, FR_RECEIPT };
        uint64_t act0[3], chg0[3]; WorkLedger l0 = work_ledger();
        for (int k = 0; k < 3; k++) { act0[k] = reuse_count(rcs[k]); chg0[k] = l0.frames[frs[k]]; }
        OpId h1 = kernel(KK_SHAPE_OF, a, 0, 0, 0), h2 = kernel(KK_INFER, G, fc_true(), t, 0), h3 = kernel(KK_SHAPE_OF, mk_app(f, a), 0, 0, 0);
        if (inter) { op_step(h1, 1); op_step(h2, 3); op_step(h3, 1); finish(h2); finish(h3); finish(h1); }
        else { finish(h1); finish(h2); finish(h3); }
        WorkLedger l1 = work_ledger();
        for (int k = 0; k < 3; k++) {
            uint64_t act = reuse_count(rcs[k]) - act0[k], chg = l1.frames[frs[k]] - chg0[k];
            printf("ledger-mixed workers=%d interleaved=%d class=%d actual=%llu charged=%llu\n", workers, inter, k, (unsigned long long)act, (unsigned long long)chg);
            if (act != chg) bad = 1;
        }
        op_release(h1); op_release(h2); op_release(h3); done();
    }
    return bad;
}

/* an observation on an engine stack: arg[0] the reference, arg[2] the face */
KF_DECL(observe, void, KF_NOPARAMS, WhnfStatus s; EvalResult *r;)
KF_STEP(observe) { KF_BEGIN(observe); KF_CALL(whnf, &F->r, ks->arg[0], ks->arg[2], &F->s); ks->ok = F->s == W_OK && F->r; ks->out[0] = F->s; KF_RETV(); KF_END; }
static KStack *observer(RefId t) { KStack *k = kf_new(); k->arg[0] = t; k->arg[2] = fc_true(); observe_push(k, NULL); return k; }
static RefId big_system(uint64_t level) {
    FaceId fs[16]; RefId ts[16];
    for (size_t i = 0; i < 16; i++) { fs[i] = i ? fc_false() : fc_true(); ts[i] = mk_universe(level); }
    return mk_system(16, fs, ts);
}
static int wait_shared(void) {
    init();
    RefId a = big_system(0), b = big_system(1);
    KStack *unrelated = observer(a), *owner = observer(b), *w1 = observer(b), *w2 = observer(b);
    for (size_t n = 0; !unrelated->in_eval && n < 100000; n++) kf_grant(unrelated, 1);
    for (size_t n = 0; !owner->in_eval && n < 100000; n++) kf_grant(owner, 1);
    for (size_t n = 0; !w1->blocked && !kf_done(w1) && n < 100000; n++) kf_grant(w1, 1);
    for (size_t n = 0; !w2->blocked && !kf_done(w2) && n < 100000; n++) kf_grant(w2, 1);
    bool ok = w1->blocked && w2->blocked && w1->blocked_on == owner && w2->blocked_on == owner && w1->blocked_job == owner->job;
    printf("wait-shared: both consumers name the owner=%d\n", ok);
    while (!kf_done(owner)) kf_grant(owner, KF_UNBOUNDED);
    while (!kf_done(w1)) kf_grant(w1, KF_UNBOUNDED);
    while (!kf_done(w2)) kf_grant(w2, KF_UNBOUNDED);
    bool unrelated_still = !kf_done(unrelated);
    printf("wait-shared: consumers completed with the unrelated stack still suspended=%d\n", unrelated_still);
    ok = ok && owner->ok && w1->ok && w2->ok && unrelated_still;
    while (!kf_done(unrelated)) kf_grant(unrelated, KF_UNBOUNDED);
    kf_free(w1); kf_free(w2); kf_free(owner); kf_free(unrelated); done();
    return ok ? 0 : 1;
}

/* the owner observes b, then performs further work (a second observation)
 * before its call returns; the consumer of b is released at b's publication */
KF_DECL(observe_then_more, void, KF_NOPARAMS, WhnfStatus s; EvalResult *r, *r2;)
KF_STEP(observe_then_more) {
    KF_BEGIN(observe_then_more);
    KF_CALL(whnf, &F->r, ks->arg[0], ks->arg[2], &F->s);
    ks->out[1] = 1;   /* b is published */
    KF_CALL(whnf, &F->r2, ks->arg[1], ks->arg[2], &F->s);
    ks->ok = F->r && F->r2;
    KF_RETV();
    KF_END;
}
static int wait_early(void) {
    init();
    RefId b = big_system(1), c = big_system(2);
    KStack *owner = kf_new(); owner->arg[0] = b; owner->arg[1] = c; owner->arg[2] = fc_true(); observe_then_more_push(owner, NULL);
    KStack *w = observer(b);
    for (size_t n = 0; !owner->in_eval && n < 100000; n++) kf_grant(owner, 1);
    for (size_t n = 0; !w->blocked && !kf_done(w) && n < 100000; n++) kf_grant(w, 1);
    assert(w->blocked && w->blocked_on == owner);
    for (size_t n = 0; !owner->out[1] && n < 1000000; n++) kf_grant(owner, 1);   /* until b is published, not the whole call */
    bool owner_running = !kf_done(owner);
    for (size_t n = 0; !kf_done(w) && n < 1000000; n++) kf_grant(w, 1);
    bool early = kf_done(w) && w->ok && owner_running;
    printf("wait-early: consumer completed while the owner's call is still running=%d\n", early);
    while (!kf_done(owner)) kf_grant(owner, KF_UNBOUNDED);
    kf_free(w); kf_free(owner); done();
    return early ? 0 : 1;
}

static void count_delivery(void *ctx, EvalResult *r) { if (r && r->cls != R_INVALID) __atomic_add_fetch((int *)ctx, 1, __ATOMIC_SEQ_CST); }
static int growth(void) {
    init();
    RefId U = mk_universe(0); TermVarId va = declare_term(U, fc_true()); RefId A = ref_var(va);
    const size_t N = 5000;   /* > 2 chunks of claims, roots and queue positions */
    CtxDecl *ds = malloc((N + 1) * sizeof *ds); ds[0] = (CtxDecl){ S_TERM, va, U };
    RefId *xs = malloc(N * sizeof *xs);
    for (size_t i = 0; i < N; i++) { TermVarId v = declare_term(A, fc_true()); xs[i] = ref_var(v); ds[i + 1] = (CtxDecl){ S_TERM, v, A }; }
    ContextId G = context_make(N + 1, ds, fc_true());
    size_t valid = 0; const char *why = NULL;
    for (size_t i = 0; i < N; i++) if (check(G, fc_true(), xs[i], A, &why) == CK_VALID) valid++;   /* one claim per judgment */
    size_t roots_ok = 0;
    for (size_t i = 0; i < N; i++) { WhnfStatus s; EvalResult *r = whnf(xs[i], fc_true(), &s); if (s == W_OK && r && r->ref == xs[i]) roots_ok++; }
    EntryId *occ; size_t nocc = eval_root_occurrences(&occ); free(occ);
    /* queue: N fresh requests issued before the scheduler runs put N launch
     * tasks in the queue at once */
    static int delivered; delivered = 0;
    RefId *ys = malloc(N * sizeof *ys);
    for (size_t i = 0; i < N; i++) ys[i] = mk_app(ref_var(declare_term(mk_fun(0, 0, A, A), fc_true())), xs[i]);
    size_t q0 = eval_task_count(); EvalEvents ev0 = eval_events();
    for (size_t i = 0; i < N; i++) eval_request(ys[i], fc_true(), cont_external(count_delivery, &delivered, NULL));
    size_t inflight = eval_task_count() - q0; bool none_ran = eval_events().eval_step == ev0.eval_step;   /* N launches queued, none executed yet */
    eval_run();
    bool sys_ok = inflight >= N && none_ran && delivered == (int)N;
    free(ys);
    printf("growth: claims valid=%zu/%zu roots=%zu/%zu occurrences=%zu queue in flight=%zu delivered=%d\n", valid, N, roots_ok, N, nocc, inflight, delivered);
    free(ds); free(xs); done();
    return valid == N && roots_ok == N && nocc >= N && sys_ok ? 0 : 1;
}

static int cleanup_case(bool owner_first_alloc, bool second_consumer, bool release_first) {
    init();
    RefId U = mk_universe(0); TermVarId va = declare_term(U, fc_true()); RefId A = ref_var(va);
    TermVarId vx = declare_term(A, fc_true()); RefId x = ref_var(vx);
    CtxDecl ds[] = { { S_TERM, va, U }, { S_TERM, vx, A } }; ContextId G = context_make(2, ds, fc_true());
    RefId t = mk_refl(0, A, x), T = mk_path_const(0, A, x, x);
    OpId owner, waiter, w2 = 0;
    if (owner_first_alloc) { owner = kernel(KK_INFER, G, fc_true(), t, 0); waiter = kernel(KK_CHECK, G, fc_true(), t, T); }
    else { waiter = kernel(KK_CHECK, G, fc_true(), t, T); owner = kernel(KK_INFER, G, fc_true(), t, 0); }
    if (second_consumer) w2 = kernel(KK_IS_TYPE, G, fc_true(), T, 0);
    uint64_t f0 = fine_count(FC_CHECK_FRAMES);
    for (size_t i = 0; i < 100000 && op_status(owner) == OP_RUNNING; i++) { op_step(owner, 1); if (fine_count(FC_CHECK_FRAMES) > f0 + 1) break; }
    for (size_t i = 0; i < 2000 && op_status(waiter) == OP_RUNNING; i++) op_step(waiter, 1);
    if (w2) for (size_t i = 0; i < 2000 && op_status(w2) == OP_RUNNING; i++) op_step(w2, 1);
    if (release_first) { op_release(owner); op_release(waiter); if (w2) op_release(w2); }
    printf("cleanup-orders owner_first=%d second=%d released=%d: teardown\n", owner_first_alloc, second_consumer, release_first);
    if (!release_first) { op_release(waiter); op_release(owner); if (w2) op_release(w2); }
    done();
    return 0;
}
static int cleanup_orders(void) {
    for (int a = 0; a < 2; a++) for (int b = 0; b < 2; b++) for (int c = 0; c < 2; c++) cleanup_case(a, b, c);
    puts("cleanup-orders: every teardown returned");
    return 0;
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0); assert(argc == 2);
    if (!strcmp(argv[1], "ledger-mixed")) return ledger_mixed();
    if (!strcmp(argv[1], "wait-shared")) return wait_shared();
    if (!strcmp(argv[1], "wait-early")) return wait_early();
    if (!strcmp(argv[1], "growth")) return growth();
    if (!strcmp(argv[1], "cleanup-orders")) return cleanup_orders();
    return 2;
}
