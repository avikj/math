/* HANDOFF §§6–7, §21 F: the primitive execution stream. Every counter family
 * registered with the stream is a projection of it: at a quiescent prefix the
 * fold over all records equals the independently maintained shadow, dimension
 * by dimension, with workers 0 and 4, across evaluator tasks, net pairs,
 * engine units, kernel grants, effect jobs and chain steps.
 * Run: test_event [workers] */
#include "check.h"
#include "lib.h"
#include "compiler.h"
#include "work.h"
#include "event.h"
#include "reuse.h"
#include "fine.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int fails;
#define EXPECT(c, ...) do { if (!(c)) { fails++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    size_t workers = argc > 1 ? (size_t)strtoull(argv[1], NULL, 10) : 0;
    for (int session = 0; session < 2; session++) {
        machine_init(); eval_init(); check_init(); compiler_init(); work_init();
        if (workers) eval_set_workers(workers);
        RefId U = mk_universe(0);
        TermVarId va = declare_term(U, fc_true()); RefId A = ref_var(va);
        TermVarId vx = declare_term(A, fc_true()); RefId x = ref_var(vx);
        /* evaluator work: nested betas */
        RefId t = x; for (int k = 0; k < 6; k++) { TermVarId z = declare_term(A, fc_true()); t = mk_app(mk_lam_lv(0, z, A, t), x); }
        WhnfStatus st; EvalResult *r = whnf(t, fc_true(), &st);
        EXPECT(st == W_OK && r && r->ref == x, "the evaluator answers");
        /* checker and engine work */
        ContextId G = context_make(0, NULL, fc_true());
        CtxDecl d[] = { { S_TERM, va, U }, { S_TERM, vx, A } }; ContextId G2 = context_make(2, d, fc_true());
        const char *why = NULL;
        EXPECT(check(G2, fc_true(), x, A, &why) == CK_VALID, "the checker admits x : A");
        OpId h = op_proof_audit(G2, fc_true(), x, A); while (op_step(h, 1) == OP_RUNNING) {} op_release(h);
        (void)G;
        eval_run();
        size_t bad = eval_shadow_check(true);   /* publishes this thread's ambient label, then captures shadows and prefix together */
        EvPrefix p = ev_prefix();
        EvStats es = ev_stats();
        EXPECT(bad == 0, "session %d: every registered dimension's fold equals its shadow (%zu mismatches)", session, bad);
        EvFilter fe = { 0, EK_ENGINE_UNIT, 0 }, fv = { 0, EK_EVAL_TASK, 0 }, fk = { 0, EK_KERNEL_GRANT, 0 };
        uint64_t ne = ev_count_records(&p, &fe), nv = ev_count_records(&p, &fv), nk = ev_count_records(&p, &fk);
        EXPECT(ne > 0 && nv > 0 && nk > 0, "engine units, evaluator tasks and kernel grants all emitted records (%llu/%llu/%llu)", (unsigned long long)ne, (unsigned long long)nv, (unsigned long long)nk);
        printf("session %d workers=%zu: records=%llu words=%llu streams=%llu segments=%llu ambient=%llu; engine=%llu eval=%llu kernel=%llu; mismatches=%zu\n", session, workers,
               (unsigned long long)es.records, (unsigned long long)es.words, (unsigned long long)es.streams, (unsigned long long)es.segments, (unsigned long long)es.ambient,
               (unsigned long long)ne, (unsigned long long)nv, (unsigned long long)nk, bad);
        ev_prefix_free(&p);
        work_free(); compiler_free(); check_free(); eval_free(); machine_free();
    }
    printf("test_event workers=%zu: %d failures\n", workers, fails);
    return fails ? 1 : 0;
}
