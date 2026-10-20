/* test_protocol.c — the one execution protocol for registered families:
 * one producer per key, frames reused across children, delivery chains of
 * one delivery per job, launched independent demands, the root-driving
 * synchronous API (refused inside a counted step), a self-request as an
 * unresolved dependency, workers and concurrent clients; independence of
 * the native stack (a producer chain past 2^20 and a deep term checked and
 * observed on a thread with a small stack); closed init/free cycles leave
 * no native workers. */
#include "reading.h"
#include "../src/eval.h"
#include "../src/lib.h"
#include "../src/check.h"
#include <dirent.h>
#include <pthread.h>
#include <sys/wait.h>
#include <unistd.h>
#include <fcntl.h>
#undef W_OK   /* <unistd.h> access mode; the evaluator status is meant */

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

static Family F_SUM;
static pthread_barrier_t gate;
/* sum(n) = n + sum(n-1), sum(0) = 0 (values stored +1): one frame, reused for its one child */
static void sum_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    FR_BEGIN(k);
    if (k->w[0] == 0) FR_FINISH(k, 1);
    FR_AWAIT(k, r, F_SUM, k->w[0] - 1, 0);
    FR_FINISH(k, r + k->w[0]);
    FR_END(k);
}

/* frame programs: a pure producer awaiting itself, a subroutine stepping
 * with yields over its locals record, a producer calling the subroutine and
 * awaiting a producer */
static Family F_TRI, F_COUNT, F_USE, F_SYNC, F_PRIV;
static void tri_step(Cont *k, uint64_t v) {             /* tri(n) = n + tri(n-1), tri(0) = 1 */
    uint64_t r = 0;
    FR_BEGIN(k);
    if (k->w[0] == 0) FR_FINISH(k, 1);
    FR_AWAIT(k, r, F_TRI, k->w[0] - 1, 0);
    FR_FINISH(k, r + k->w[0]);
    FR_END(k);
}
typedef struct { uint64_t i, n, acc; } CountLoc;
static void count_step(Cont *k, uint64_t v) {           /* 1 + Σ_{i<n} i, one i per step */
    CountLoc *L = FR_LOC(k, CountLoc);
    FR_BEGIN(k);
    L->acc = 1;
    for (L->i = 0; L->i < L->n; L->i++) { L->acc += L->i; FR_YIELD(k); }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
static void use_step(Cont *k, uint64_t v) {             /* count(n) + tri(n) */
    uint64_t x = 0;
    FR_BEGIN(k);
    { Cont *c = frame_sub(F_COUNT, k); FR_LOC(c, CountLoc)->n = k->w[0]; FR_CALL(k, x, c); }
    k->w[2] = x;
    FR_AWAIT(k, x, F_TRI, k->w[0], 0);
    FR_FINISH(k, k->w[2] + x);
    FR_END(k);
}
static void sync_step(Cont *k, uint64_t v) {            /* a synchronous request inside a counted step */
    (void)v;
    frame_finish(k, family_call(F_TRI, k->w[0], 0) + 1000000);
}
static void self_step(Cont *k, uint64_t v) {            /* awaits its own key: an unresolved dependency */
    uint64_t r = 0;
    FR_BEGIN(k);
    FR_AWAIT(k, r, F_PRIV, k->w[0], 0);
    FR_FINISH(k, r + 1);
    FR_END(k);
}
static Family F_FAN;
typedef struct { uint64_t i, n, acc, r; } FanLoc;
static void fan_step(Cont *k, uint64_t v) {             /* Σ_{i<n} tri(i): n independent demands, launched, then awaited */
    FanLoc *L = FR_LOC(k, FanLoc);
    FR_BEGIN(k);
    L->n = k->w[0];
    for (L->i = 0; L->i < L->n; L->i++) { family_launch(F_TRI, L->i, 0); FR_YIELD(k); }
    for (L->i = 0; L->i < L->n; L->i++) { FR_AWAIT(k, L->r, F_TRI, L->i, 0); L->acc += L->r; }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
static void fresh_machine(size_t workers) { eval_set_workers(0); machine_free(); machine_init(); eval_set_workers(workers); }
static uint64_t use_expected(uint64_t n) { return (1 + n * (n - 1) / 2) + (1 + n * (n + 1) / 2); }
static uint64_t inl_got[8];
static void *inl_client(void *p) {
    size_t i = *(size_t *)p;
    pthread_barrier_wait(&gate);
    inl_got[i] = family_call(F_USE, 2000, 0);
    return NULL;
}

static uint64_t got[8];
static void *client(void *p) {
    size_t i = *(size_t *)p; WhnfStatus st;
    pthread_barrier_wait(&gate);
    got[i] = family_run(F_SUM, 3000, 0, &st) - 1;
    return NULL;
}

/* run fn on a thread whose native stack is 256 KiB */
static void on_small_stack(void *(*fn)(void *), void *arg) {
    pthread_attr_t at; pthread_attr_init(&at); pthread_attr_setstacksize(&at, 256 * 1024);
    pthread_t t; pthread_create(&t, &at, fn, arg); pthread_join(t, NULL); pthread_attr_destroy(&at);
}
static uint64_t deep_v; static WhnfStatus deep_st;
static void *deep_chain(void *p) { deep_v = family_run(F_SUM, *(uint64_t *)p, 0, &deep_st) - 1; return NULL; }
typedef struct { ContextId G; RefId t, A, a; CheckStatus ck; EvalResult r; WhnfStatus st; } DeepTerm;
static void *deep_term(void *p) { DeepTerm *d = p; const char *why; d->ck = check(d->G, fc_true(), d->t, d->A, &why); d->r = whnf(d->t, fc_true(), &d->st); return NULL; }
static size_t native_threads(void) { size_t n = 0; DIR *d = opendir("/proc/self/task"); struct dirent *e; while (d && (e = readdir(d))) if (e->d_name[0] != '.') n++; if (d) closedir(d); return n; }

int main(void) {
    machine_init();
    /* exact counts (CONTINUATION-AND-COUNT-CLOSURE §C): one event past 2^64 - 1 */
    {   Count c = { UINT64_MAX, NULL, 0 }; count_bump(&c);
        Exact x = { 0, NULL }; exact_add_count(&x, &c); uint64_t w;
        CHECK(x.n == 2 && x.w[0] == 0 && x.w[1] == 1, "2^64 - 1 plus one event reads exactly 2^64");
        CHECK(!exact_to_u64(&x, &w), "its word conversion reports out of range");
        count_bump(&c); exact_free(&x); exact_add_count(&x, &c);
        CHECK(x.n == 2 && x.w[0] == 1 && x.w[1] == 1, "the next event adds one to the low digit");
        exact_free(&x); count_free(&c); }
    F_SUM = family_new("test.sum", sum_step, 0);
    WhnfStatus st;
    uint64_t v = family_run(F_SUM, 1000, 0, &st) - 1;
    CHECK(st == W_OK && v == 500500, "sum(1000) = 500500 through 1001 producers");
    CHECK(rd(RD_STEPS, F_SUM) == 2001, "each key: one evaluator step, plus one resume per frame");
    size_t before = rd(RD_STEPS, F_SUM);
    v = family_run(F_SUM, 1000, 0, &st) - 1;
    CHECK(v == 500500 && rd(RD_STEPS, F_SUM) == before, "a ready key is delivered without producer work");
    v = family_run(F_SUM, 1500, 0, &st) - 1;
    CHECK(v == 1125750 && rd(RD_STEPS, F_SUM) == before + 2 * 500, "a larger request runs only its new keys");
    for (EntryId e = 1; e <= eval_entry_count(); e++) if (eval_entry_live(e) && eval_entry_runs(e) > 1) { CHECK(0, "a key ran twice"); break; }
    /* the work reading: a producer's support is its dependency closure, each
     * producer counted once in a union */
    {   EntryId r1 = eval_entry_find(F_SUM, 1500, 0), r2 = eval_entry_find(F_SUM, 700, 0);
        Exact w1 = { 0, NULL }, w12 = { 0, NULL }; size_t n1, n12; uint64_t a1, a12;
        eval_work(1, &r1, &w1, &n1);
        EntryId both[2] = { r1, r2 }; eval_work(2, both, &w12, &n12);
        CHECK(exact_to_u64(&w1, &a1) && a1 == rd(RD_STEPS, F_SUM) && n1 == 1501, "W(sum(1500)) is the steps of its 1501 producers");
        CHECK(exact_to_u64(&w12, &a12) && a12 == a1 && n12 == n1, "a producer inside the support is counted once in the union");
        exact_free(&w1); exact_free(&w12); }

    /* eight concurrent clients of one fresh key, sequential and with workers */
    for (int w = 0; w <= 4; w += 4) {
        fresh_machine(w);
        size_t q0 = rd(RD_REQUEST, 0), d0 = rd(RD_DELIVER, 0);
        pthread_barrier_init(&gate, NULL, 8);
        pthread_t th[8]; size_t ids[8];
        for (size_t i = 0; i < 8; i++) { ids[i] = i; pthread_create(&th[i], NULL, client, &ids[i]); }
        for (size_t i = 0; i < 8; i++) pthread_join(th[i], NULL);
        pthread_barrier_destroy(&gate);
        bool same = true; for (size_t i = 0; i < 8; i++) same = same && got[i] == 4501500;
        CHECK(same, w ? "eight clients, four workers: one value" : "eight clients, no pool: one value");
        bool once = true; size_t ne = eval_entry_count(), live = 0;
        for (EntryId e = 1; e <= ne; e++) { if (!eval_entry_live(e) || eval_entry_family(e) != F_SUM) continue; live++; if (eval_entry_runs(e) != 1) once = false; }
        CHECK(once && live == 3001, "every key produced exactly once");
        eval_run();                                    /* deliveries a returning client left queued */
        CHECK(rd(RD_DELIVER, 0) - d0 == rd(RD_REQUEST, 0) - q0, "one delivery per request (chains deliver one per job)");
    }
    eval_set_workers(0);

    /* frame programs, scheduled */
    F_TRI = family_new("test.tri", tri_step, 0);
    F_COUNT = family_new("test.count", count_step, sizeof(CountLoc));
    F_USE = family_new("test.use", use_step, 0);
    F_SYNC = family_new("test.sync", sync_step, 0);
    F_PRIV = family_new("test.self", self_step, 0);
    F_FAN = family_new("test.fan", fan_step, sizeof(FanLoc));
    fresh_machine(0);
    size_t t0 = rd(RD_STEPS, F_TRI), c0 = rd(RD_STEPS, F_COUNT), u0 = rd(RD_STEPS, F_USE);
    v = family_run(F_USE, 300, 0, &st);
    CHECK(st == W_OK && v == use_expected(300), "scheduled: a producer calls a stepping subroutine and awaits a producer");
    CHECK(rd(RD_STEPS, F_COUNT) - c0 == 301, "the subroutine: one step per element, one to finish");
    CHECK(rd(RD_STEPS, F_TRI) - t0 == 301 + 300 && rd(RD_STEPS, F_USE) - u0 == 3, "producers: one step per key plus one per delivered child");
    /* the root-driving synchronous API: the same jobs as a scheduled request */
    fresh_machine(0);
    t0 = rd(RD_STEPS, F_TRI); c0 = rd(RD_STEPS, F_COUNT); u0 = rd(RD_STEPS, F_USE);
    v = family_call(F_USE, 300, 0);
    CHECK(v == use_expected(300), "root-driving: the same value");
    CHECK(rd(RD_STEPS, F_COUNT) - c0 == 301 && rd(RD_STEPS, F_TRI) - t0 == 301 + 300 && rd(RD_STEPS, F_USE) - u0 == 3, "root-driving: the same steps");
    { bool once = true; size_t n = 0;
      for (EntryId e = 1; e <= eval_entry_count(); e++) {
          if (!eval_entry_live(e) || (eval_entry_family(e) != F_USE && eval_entry_family(e) != F_TRI)) continue;
          n++; if (eval_entry_state(e) != E_READY || eval_entry_runs(e) != 1) once = false; }
      CHECK(once && n == 302, "root-driving: every key claimed, run once and published"); }
    size_t before_root = rd(RD_STEPS, F_TRI);
    CHECK(family_call(F_TRI, 300, 0) == 1 + 300 * 301 / 2 && rd(RD_STEPS, F_TRI) == before_root, "a ready key returns its value without steps");
    /* fifty independent demands: launched one per step, then awaited in order */
    fresh_machine(0);
    { size_t j0 = rd(RD_STEPS, F_FAN); t0 = rd(RD_STEPS, F_TRI);
      v = family_run(F_FAN, 50, 0, &st);
      uint64_t want = 0; for (uint64_t i = 0; i < 50; i++) want += 1 + i * (i + 1) / 2;
      CHECK(st == W_OK && v == want, "fifty independent demands, launched then awaited");
      CHECK(rd(RD_STEPS, F_FAN) - j0 == 1 + 50 + 50, "the frame: its first step, one step per launch, one resumption per await");
      CHECK(rd(RD_STEPS, F_TRI) - t0 == 50 + 49, "the demanded keys: each produced once"); }
    /* a synchronous request inside a counted step is refused (it would be a
     * private recomputation outside the protocol) */
    {   fflush(stdout);
        pid_t pid = fork();
        if (pid == 0) { int fd = open("/dev/null", 1); if (fd >= 0) { dup2(fd, 2); } family_run(F_SYNC, 350, 0, &st); _exit(0); }
        int ws = 0; waitpid(pid, &ws, 0);
        CHECK(!(WIFEXITED(ws) && WEXITSTATUS(ws) == 0), "a synchronous request inside a counted step dies"); }
    /* a self-request is an unresolved dependency: no private recomputation */
    fresh_machine(0);
    v = family_run(F_PRIV, 7, 0, &st);
    CHECK(st == W_STUCK && v == 0, "a key awaiting itself is an unresolved dependency");
    { EntryId e = 0; for (EntryId q = 1; q <= eval_entry_count(); q++) if (eval_entry_live(q) && eval_entry_family(q) == F_PRIV) e = q;
      CHECK(e && eval_entry_runs(e) == 1 && eval_entry_state(e) != E_READY, "it ran once and published nothing"); }
    /* concurrent inline clients and workers */
    for (int w = 0; w <= 4; w += 4) {
        fresh_machine(w);
        pthread_barrier_init(&gate, NULL, 8);
        pthread_t th[8]; size_t ids[8];
        for (size_t i = 0; i < 8; i++) { ids[i] = i; pthread_create(&th[i], NULL, inl_client, &ids[i]); }
        for (size_t i = 0; i < 8; i++) pthread_join(th[i], NULL);
        pthread_barrier_destroy(&gate);
        bool same = true; for (size_t i = 0; i < 8; i++) same = same && inl_got[i] == use_expected(2000);
        CHECK(same, w ? "eight root-driving clients, four workers: one value" : "eight root-driving clients: one value");
        bool once = true; size_t ne = eval_entry_count();
        for (EntryId e = 1; e <= ne; e++) if (eval_entry_live(e) && (eval_entry_runs(e) != 1 || eval_entry_state(e) != E_READY)) once = false;
        CHECK(once, "every key claimed once and published");
    }
    /* the native stack bounds no computation: a chain of 2^20 + 2 producers,
     * and a term nested 20000 deep, checked and observed, on a 256 KiB stack */
    fresh_machine(0);
    {   uint64_t n = ((uint64_t)1 << 20) + 1;
        on_small_stack(deep_chain, &n);
        CHECK(deep_st == W_OK && deep_v == n * (n + 1) / 2, "sum(2^20 + 1) through 2^20 + 2 producers on a small native stack"); }
    fresh_machine(0); check_init();
    {   RefId U0 = mk_universe(0); TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
        TermVarId vf = declare_term(mk_fun(0, 0, A, A), fc_true()), va = declare_term(A, fc_true());
        CtxDecl ds[3] = { { S_TERM, vA }, { S_TERM, vf }, { S_TERM, va } };
        DeepTerm d = { context_make(3, ds, fc_true()), ref_var(va), A, ref_var(va), 0, { 0 }, 0 };
        for (size_t i = 0; i < 20000; i++) d.t = mk_app(ref_var(vf), d.t);
        on_small_stack(deep_term, &d);
        CHECK(d.ck == CK_VALID && d.st == W_OK && d.r.cls == R_NEUTRAL && d.r.ref == d.t, "f^20000 a : A checked and observed on a small native stack"); }
    /* closed init/free cycles with a pool: no native worker survives */
    eval_set_workers(0);
    {   size_t base = native_threads(); bool clean = true;
        for (int c = 0; c < 3; c++) {
            fresh_machine(4);
            if (family_call(F_TRI, 500, 0) != 1 + 500 * 501 / 2) clean = false;
            eval_set_workers(0); machine_free(); machine_init();
            if (native_threads() != base) clean = false;
        }
        CHECK(clean, "three closed init/free cycles with four workers: the same value, no native worker left"); }
    eval_set_workers(0);
    machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}
