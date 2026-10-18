/* test_protocol.c — the one execution protocol for registered families:
 * one producer per key, frames reused across children, delivery chains of
 * one delivery per job, the synchronous driver, workers and concurrent
 * clients. */
#include "../src/eval.h"
#include "../src/lib.h"
#include <pthread.h>

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

static Family F_SUM;
static pthread_barrier_t gate;
/* sum(n) = n + sum(n-1), sum(0) = 0: one frame, reused for its one child */
static void sum_start(EntryId e, uint64_t n, uint64_t b) {
    (void)b;
    if (n == 0) { family_publish(e, 1); return; }          /* values are stored +1 (0 is reserved) */
    Cont *k = frame_new(F_SUM, e); k->w[0] = n;
    family_request(F_SUM, n - 1, 0, k);
}
static void sum_resume(Cont *k, uint64_t v) { family_publish(k->dest, v + k->w[0]); }

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
static void sync_step(Cont *k, uint64_t v) {            /* a not-yet-converted caller inside a job */
    (void)v;
    frame_finish(k, family_call(F_TRI, k->w[0], 0) + 1000000);
}
static __thread int priv_depth; static int priv_seen;
static void priv_step(Cont *k, uint64_t v) {            /* re-enters its own running key once */
    (void)v;
    if (priv_depth == 0) { priv_depth++; uint64_t x = family_call(F_PRIV, k->w[0], 0); priv_depth--; frame_finish(k, x + 1); }
    else { priv_seen++; frame_finish(k, 41); }
}
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

int main(void) {
    machine_init(); eval_init();
    F_SUM = family_register("test.sum", sum_start, sum_resume);
    WhnfStatus st;
    uint64_t v = family_run(F_SUM, 1000, 0, &st) - 1;
    CHECK(st == W_OK && v == 500500, "sum(1000) = 500500 through 1001 producers");
    CHECK(family_steps(F_SUM) == 2001, "each key: one evaluator step, plus one resume per frame");
    size_t before = family_steps(F_SUM);
    v = family_run(F_SUM, 1000, 0, &st) - 1;
    CHECK(v == 500500 && family_steps(F_SUM) == before, "a ready key is delivered without producer work");
    v = family_run(F_SUM, 1500, 0, &st) - 1;
    CHECK(v == 1125750 && family_steps(F_SUM) == before + 2 * 500, "a larger request runs only its new keys");
    for (EntryId e = 1; e <= eval_entry_count(); e++) if (eval_entry_runs(e) > 1) { CHECK(0, "a key ran twice"); break; }

    /* eight concurrent clients of one fresh key, sequential and with workers */
    for (int w = 0; w <= 4; w += 4) {
        eval_reset(); eval_set_workers(w);
        pthread_barrier_init(&gate, NULL, 8);
        pthread_t th[8]; size_t ids[8];
        for (size_t i = 0; i < 8; i++) { ids[i] = i; pthread_create(&th[i], NULL, client, &ids[i]); }
        for (size_t i = 0; i < 8; i++) pthread_join(th[i], NULL);
        pthread_barrier_destroy(&gate);
        bool same = true; for (size_t i = 0; i < 8; i++) same = same && got[i] == 4501500;
        CHECK(same, w ? "eight clients, four workers: one value" : "eight clients, no pool: one value");
        bool once = true; size_t ne = eval_entry_count();
        for (EntryId e = 1; e <= ne; e++) if (eval_entry_runs(e) != 1) once = false;
        CHECK(once && ne == 3001, "every key produced exactly once");
        EvalEvents ev = eval_events();
        CHECK(ev.deliver == ev.request, "one delivery per request (chains deliver one per job)");
    }
    eval_set_workers(0);

    /* frame programs, scheduled */
    F_TRI = family_define("test.tri", tri_step, 0, true);
    F_COUNT = family_define("test.count", count_step, sizeof(CountLoc), true);
    F_USE = family_define("test.use", use_step, 0, true);
    F_SYNC = family_define("test.sync", sync_step, 0, true);
    F_PRIV = family_define("test.priv", priv_step, 0, true);
    eval_reset();
    size_t t0 = family_steps(F_TRI), c0 = family_steps(F_COUNT), u0 = family_steps(F_USE);
    v = family_run(F_USE, 300, 0, &st);
    CHECK(st == W_OK && v == use_expected(300), "scheduled: a producer calls a stepping subroutine and awaits a producer");
    CHECK(family_steps(F_COUNT) - c0 == 301, "the subroutine: one step per element, one to finish");
    CHECK(family_steps(F_TRI) - t0 == 301 + 300 && family_steps(F_USE) - u0 == 3, "producers: one step per key plus one per delivered child");
    /* the same program inline: same value, same steps, every key published once */
    eval_reset();
    t0 = family_steps(F_TRI); c0 = family_steps(F_COUNT); u0 = family_steps(F_USE);
    v = family_call(F_USE, 300, 0);
    CHECK(v == use_expected(300), "inline: the same value from the same step functions");
    CHECK(family_steps(F_COUNT) - c0 == 301 && family_steps(F_TRI) - t0 == 301 + 300 && family_steps(F_USE) - u0 == 3, "inline: the same steps");
    { bool once = true; for (EntryId e = 1; e <= eval_entry_count(); e++) if (eval_entry_state(e) != E_READY || eval_entry_runs(e) != 1) once = false;
      CHECK(once && eval_entry_count() == 302, "inline: every key claimed, run once and published"); }
    size_t before_inline = family_steps(F_TRI);
    CHECK(family_call(F_TRI, 300, 0) == 1 + 300 * 301 / 2 && family_steps(F_TRI) == before_inline, "inline: a ready key returns its value without steps");
    v = family_run(F_TRI, 301, 0, &st);
    CHECK(v == 1 + 301 * 302 / 2 && family_steps(F_TRI) == before_inline + 2, "a scheduled request uses the keys published inline");
    /* inline inside a job */
    v = family_run(F_SYNC, 350, 0, &st);
    CHECK(st == W_OK && v == 1000000 + 1 + 350 * 351 / 2, "a synchronous call inside a job drives its keys inline");
    /* a key running elsewhere is computed without publication */
    priv_seen = 0;
    v = family_call(F_PRIV, 7, 0);
    CHECK(v == 42 && priv_seen == 1, "a re-entered running key is computed on the calling thread");
    { EntryId e = 0; for (EntryId q = 1; q <= eval_entry_count(); q++) if (eval_entry_family(q) == F_PRIV) e = q;
      size_t rq, dl, pb; eval_entry_events(e, &rq, &dl, &pb);
      CHECK(e && eval_entry_runs(e) == 1 && pb == 1 && family_call(F_PRIV, 7, 0) == 42, "it published once, from its claimer"); }
    /* concurrent inline clients and workers */
    for (int w = 0; w <= 4; w += 4) {
        eval_reset(); eval_set_workers(w);
        pthread_barrier_init(&gate, NULL, 8);
        pthread_t th[8]; size_t ids[8];
        for (size_t i = 0; i < 8; i++) { ids[i] = i; pthread_create(&th[i], NULL, inl_client, &ids[i]); }
        for (size_t i = 0; i < 8; i++) pthread_join(th[i], NULL);
        pthread_barrier_destroy(&gate);
        bool same = true; for (size_t i = 0; i < 8; i++) same = same && inl_got[i] == use_expected(2000);
        CHECK(same, w ? "eight inline clients, four workers: one value" : "eight inline clients: one value");
        bool once = true; size_t ne = eval_entry_count();
        for (EntryId e = 1; e <= ne; e++) if (eval_entry_runs(e) != 1 || eval_entry_state(e) != E_READY) once = false;
        CHECK(once, "every key claimed once and published");
    }
    eval_set_workers(0);
    eval_free(); machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}
