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
/* sum(n) = n + sum(n-1), sum(0) = 0: one frame, reused for its one child */
static void sum_start(EntryId e, uint64_t n, uint64_t b) {
    (void)b;
    if (n == 0) { family_publish(e, 1); return; }          /* values are stored +1 (0 is reserved) */
    Cont *k = frame_new(F_SUM, e); k->w[0] = n;
    family_request(F_SUM, n - 1, 0, k);
}
static void sum_resume(Cont *k, uint64_t v) { family_publish(k->dest, v + k->w[0]); }

static uint64_t got[8];
static pthread_barrier_t gate;
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
    eval_free(); machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}
