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
        /* §21 A, G: one producer, two consumers; supports share it; union counts its records once */
        { uint64_t pars[] = { va, vx };
          SymbolId loop = define_global("ev_loop", varset_make(pars, 2), dimset_make(NULL, 0), mk_path_const(0, A, x, x));
          DimVarId i = declare_dim(); uint64_t di[] = { i };
          TermVarId z = declare_term(A, fc_true());
          RefId P = mk_app(mk_lam_lv(0, z, A, mk_papp_const(0, A, x, x, global_ref(loop), iv_var(i))), x);   /* (λz. loop@i) x: one beta */
          SymbolId F = define_global("ev_source", varset_make(pars, 2), dimset_make(di, 1), A); set_global_body(F, P);
          SymbolId W1 = define_global("ev_client1", varset_make(pars, 2), dimset_make(di, 1), A); set_global_body(W1, global_ref(F));
          SymbolId W2 = define_global("ev_client2", varset_make(pars, 2), dimset_make(di, 1), A); set_global_body(W2, global_ref(F));
          FaceId f0 = fc_lit(i, 0);
          whnf(global_ref(W1), f0, &st); eval_run(); ev_quiesce();
          EntryId Fe = eval_entry_lookup(global_ref(F), f0), W1e = eval_entry_lookup(global_ref(W1), f0);
          EvPrefix q1 = ev_prefix(); EvFilter fp = { 0, -1, OCC(OCC_ENTRY, Fe), NULL, 0 };
          uint64_t prod1 = ev_count_records(&q1, &fp);
          whnf(global_ref(W2), f0, &st); eval_run(); ev_quiesce();
          EntryId W2e = eval_entry_lookup(global_ref(W2), f0);
          EvPrefix q = ev_prefix();
          uint64_t prod2 = ev_count_records(&q, &fp);
          EvFilter fw1 = { 0, -1, OCC(OCC_ENTRY, W1e), NULL, 0 }, fw2 = { 0, -1, OCC(OCC_ENTRY, W2e), NULL, 0 };
          uint64_t own1 = ev_count_records(&q, &fw1), own2 = ev_count_records(&q, &fw2);
          uint64_t *s1, *s2, *su, *si; size_t n1 = eval_entry_support(W1e, &s1), n2 = eval_entry_support(W2e, &s2);
          size_t nu = ev_occ_union(s1, n1, s2, n2, &su), ni = ev_occ_intersection(s1, n1, s2, n2, &si);
          static XCount a[ED_MAX], b[ED_MAX], u[ED_MAX], m[ED_MAX];
          for (unsigned k = 0; k < ED_MAX; k++) { xc_reset(&a[k]); xc_reset(&b[k]); xc_reset(&u[k]); xc_reset(&m[k]); }
          EvFilter F1 = { 0, -1, 0, s1, n1 }, F2 = { 0, -1, 0, s2, n2 }, FU = { 0, -1, 0, su, nu }, FI = { 0, -1, 0, si, ni };
          ev_fold_dims(&q, &F1, a); ev_fold_dims(&q, &F2, b); ev_fold_dims(&q, &FU, u); ev_fold_dims(&q, &FI, m);
          bool ie = true; for (unsigned k = 0; k < ev_dims(); k++) { uint64_t x1 = 0, x2 = 0, xu = 0, xi = 0; xs_u64(xc_snap(&a[k]), &x1); xs_u64(xc_snap(&b[k]), &x2); xs_u64(xc_snap(&u[k]), &xu); xs_u64(xc_snap(&m[k]), &xi); if (xu != x1 + x2 - xi) ie = false; }
          bool shared = false; for (size_t k = 0; k < ni; k++) if (si[k] == OCC(OCC_ENTRY, Fe)) shared = true;
          uint64_t wbeta_i = 0; xs_u64(xc_snap(&m[ED_REUSE + REUSE_BETA]), &wbeta_i);
          EXPECT(Fe && eval_entry_runs(Fe) == 1 && prod1 > 0 && prod1 == prod2, "the producer ran once; reusing it for the second consumer added none of its records (%llu, %llu)", (unsigned long long)prod1, (unsigned long long)prod2);
          EXPECT(own1 > 0 && own2 > 0 && shared, "the two consumers have their own records (%llu, %llu); both supports contain the shared producer", (unsigned long long)own1, (unsigned long long)own2);
          EXPECT(ie && wbeta_i >= 1, "W(S1 ∪ S2) = W(S1) + W(S2) − W(S1 ∩ S2) on every dimension; the shared part carries the beta (%llu)", (unsigned long long)wbeta_i);
          printf("session %d: producer records %llu (unchanged by reuse), consumer records %llu / %llu, supports %zu / %zu, union %zu, intersection %zu; inclusion-exclusion exact on %u dimensions\n",
                 session, (unsigned long long)prod2, (unsigned long long)own1, (unsigned long long)own2, n1, n2, nu, ni, ev_dims());
          (free)(s1); (free)(s2); (free)(su); (free)(si); ev_prefix_free(&q1); ev_prefix_free(&q); }
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
        /* §21 F: owner projection and one late attribution */
        { ReuseScope *sc = reuse_scope_new(0);
          ReuseScope *prev = reuse_scope_enter(sc);
          RefId t2 = x; for (int k = 0; k < 9; k++) { TermVarId z = declare_term(A, fc_true()); t2 = mk_app(mk_lam_lv(0, z, A, k & 1 ? ref_var(z) : t2), x); }
          whnf(t2, fc_true(), &st);
          reuse_scope_leave(prev); eval_run();
          reuse_scope_close(sc);
          XSnap late0 = reuse_scope_late_snap(0, REUSE_BETA);
          EvPrefix p1 = ev_prefix(); ev_quiesce(); ev_prefix_free(&p1); p1 = ev_prefix();
          prev = reuse_scope_enter(sc); reuse_bump(REUSE_BETA); reuse_scope_leave(prev);   /* an event of this owner after its scope closed */
          ev_quiesce();
          EvPrefix p2 = ev_prefix();
          static XCount f[ED_MAX]; for (unsigned i = 0; i < ED_MAX; i++) xc_reset(&f[i]);
          EvFilter fo = { reuse_scope_id(sc), -1, 0 };
          ev_fold_dims(&p2, &fo, f);
          bool all = true; for (int c = 0; c < REUSE_COUNTER_COUNT; c++) if (!xs_eq(xc_snap(&f[ED_REUSE + c]), xc_snap(&sc->total[c]))) { all = false; uint64_t a = 0, b = 0; xs_u64(xc_snap(&f[ED_REUSE + c]), &a); xs_u64(xc_snap(&sc->total[c]), &b); printf("  marker %d: fold %llu shadow %llu\n", c, (unsigned long long)a, (unsigned long long)b); }
          uint64_t late = 0; xs_delta_u64(reuse_scope_late_snap(0, REUSE_BETA), late0, &late);
          uint64_t betas = 0; xs_u64(xc_snap(&f[ED_REUSE + REUSE_BETA]), &betas);
          EXPECT(all && betas >= 2 && late == 1, "owner projection: the scope's stream fold equals its shadow on every marker (betas %llu); the event after close is attributed once, late (%llu)", (unsigned long long)betas, (unsigned long long)late);
          printf("session %d: owner %llu: %llu betas in its fold, late attributions after close: %llu\n", session, (unsigned long long)reuse_scope_id(sc), (unsigned long long)betas, (unsigned long long)late);
          ev_prefix_free(&p1); ev_prefix_free(&p2); reuse_scope_unref(sc); }
        work_free(); compiler_free(); check_free(); eval_free(); machine_free();
    }
    printf("test_event workers=%zu: %d failures\n", workers, fails);
    return fails ? 1 : 0;
}
