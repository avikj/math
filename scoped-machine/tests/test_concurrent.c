/* Concurrent clients (§10, §20, §26–§27): several client threads observe a
 * shared pool of roots at once while worker pools run the evaluator and the
 * net. Checks: one evaluator task and one publication per key; every
 * request delivered exactly once; identical result payload for one key;
 * the interaction-work vector and the exact canonical result graph equal
 * those of the same client program run sequentially on a fresh machine. */
#define _POSIX_C_SOURCE 200809L
#include "../src/eval.h"
#include "../src/lib.h"
#include "../src/net.h"
#include "../src/canon.h"

#define NROOTS 16
static RefId roots[NROOTS]; static FaceId faces[NROOTS];
static EvalResult *results[8][NROOTS]; static WhnfStatus statuses[8][NROOTS];
static int nclients;

static RefId var(RefId t) { return ref_var(declare_term(t, fc_true())); }

static void build(void) {
    RefId U0 = mk_universe(0);
    RefId A = var(U0), B = var(U0), T = var(U0);
    DimVarId i = declare_dim(), k = declare_dim(), m = declare_dim(), n = declare_dim();
    RefId a = var(A), b = var(A);
    TermVarId x = declare_term(A, fc_true()), y = declare_term(A, fc_true());
    RefId p = var(mk_path_const(0, A, a, b));
    RefId pi = mk_papp_const(0, A, a, b, p, iv_var(i));
    RefId t0 = mk_app(mk_app(mk_lam_lv(0, x, A, mk_lam_lv(0, y, A, ref_var(x))), a), b);
    FaceId fs[2] = { fc_lit(k, 0), fc_lit(k, 1) };
    RefId ts3[2] = { mk_lam_lv(0, declare_term(A, fc_true()), A, t0), mk_lam_lv(0, declare_term(A, fc_true()), A, t0) };
    RefId e = var(mk_equiv(0, 0, T, A));
    RefId Gm = mk_glue_type_lv(0, A, fc_lit(m, 1), T, e);
    RefId cg = mk_coe_at(0, i, Gm, var(Gm));
    RefId ua = mk_ua(1, U0, U0, mk_id_equiv(1, U0));
    RefId tr = mk_coe_at(1, i, mk_papp_const(2, mk_universe(1), U0, U0, ua, iv_var(i)), A);
    FaceId gs[2] = { fc_lit(n, 0), fc_lit(n, 1) };
    RefId Ys2[2] = { mk_fun(0, 0, A, B), mk_sigma_lv(0, 0, x, A, B) };
    RefId cmp5 = mk_comp_lv(0, m, mk_system(2, gs, Ys2), fc_false(), mk_system(0, NULL, NULL), var(A));
    RefId S = mk_sigma_lv(0, 0, x, A, B);
    RefId csg = mk_coe_at(0, i, S, var(S));
    size_t q = 0;
    roots[q] = pi; faces[q++] = fc_true();
    roots[q] = pi; faces[q++] = fc_lit(i, 0);
    roots[q] = pi; faces[q++] = fc_lit(i, 1);
    roots[q] = t0; faces[q++] = fc_true();
    roots[q] = mk_app(mk_system(2, fs, ts3), b); faces[q++] = fc_join(fs[0], fs[1]);
    roots[q] = cg; faces[q++] = fc_true();
    roots[q] = mk_unglue_lv(0, A, fc_lit(m, 1), T, e, cg); faces[q++] = fc_true();
    roots[q] = cg; faces[q++] = fc_lit(m, 1);
    roots[q] = tr; faces[q++] = fc_true();
    roots[q] = mk_fst(mk_unglue_lv(0, U0, fc_true(), U0, mk_id_equiv(0, U0), tr)); faces[q++] = fc_true();
    roots[q] = cmp5; faces[q++] = fc_join(gs[0], gs[1]);
    roots[q] = cmp5; faces[q++] = gs[1];
    roots[q] = csg; faces[q++] = fc_true();
    roots[q] = mk_fst(csg); faces[q++] = fc_true();
    roots[q] = mk_snd(csg); faces[q++] = fc_true();
    roots[q] = mk_coe_at(0, i, mk_fun(0, 0, A, B), var(mk_fun(0, 0, A, B))); faces[q++] = fc_true();
    require(q == NROOTS, "root count");
}

static void *client(void *arg) {
    int id = (int)(intptr_t)arg;
    for (int r = 0; r < NROOTS; r++) {
        int q = (r + id * 3) % NROOTS;
        results[id][q] = whnf(roots[q], faces[q], &statuses[id][q]);
    }
    return NULL;
}

typedef struct { EvalEvents ev; Graph *graph; size_t entries; size_t bad_runs, bad_pub, bad_deliver, mismatched; } Outcome;

static Outcome run(size_t workers, int clients) {
    Outcome o; memset(&o, 0, sizeof o);
    machine_init(); eval_init();
    if (workers) eval_set_workers(workers);
    nclients = clients;
    build();
    if (workers) {
        pthread_t th[8];
        for (int c = 0; c < clients; c++) pthread_create(&th[c], NULL, client, (void *)(intptr_t)c);
        for (int c = 0; c < clients; c++) pthread_join(th[c], NULL);
    } else {
        for (int c = 0; c < clients; c++) client((void *)(intptr_t)c);
    }
    eval_run();
    /* per-key invariants */
    size_t ne = eval_entry_count();
    Canon *cn = canon_new();
    for (int q = 0; q < NROOTS; q++) {
        char lab[32]; snprintf(lab, sizeof lab, "%d", q);
        canon_add_result(cn, lab, results[0][q]);
        for (int c = 1; c < clients; c++) if (results[c][q] != results[0][q]) o.mismatched++;
    }
    for (EntryId e = 1; e <= ne; e++) {
        if (!eval_entry_live(e)) continue;
        size_t req, del, pub; eval_entry_events(e, &req, &del, &pub);
        if (eval_entry_runs(e) > 1) o.bad_runs++;
        if (pub > 1) o.bad_pub++;
        if (eval_entry_state(e) == E_READY && req != del) o.bad_deliver++;
        if (!eval_entry_is_observation(e)) continue;
        canon_add_key(cn, eval_entry_ref(e), eval_entry_face(e), req, del, pub, (int)eval_entry_state(e));
    }
    o.graph = canon_export(cn);
    canon_free(cn);
    o.ev = eval_events(); o.entries = 0;
    for (EntryId e = 1; e <= ne; e++) if (eval_entry_live(e)) o.entries++;
    eval_free(); machine_free();
    return o;
}

/* storm: clients released by a barrier demand one fresh key at once; every
 * client must obtain the result (never a spurious W_STUCK), the key must run
 * exactly once, and a genuinely stuck key must be reported stuck by all
 * clients with nothing published and a clean teardown. */
static pthread_barrier_t bar;
static RefId storm_ref; static FaceId storm_face; static int storm_stuck[8]; static EvalResult *storm_res[8];
static void *storm_client(void *arg) {
    int id = (int)(intptr_t)arg;
    pthread_barrier_wait(&bar);
    WhnfStatus st;
    storm_res[id] = whnf(storm_ref, storm_face, &st);
    storm_stuck[id] = (st == W_STUCK);
    return NULL;
}
static int storm(size_t workers, int clients, int rounds, bool cyclic) {
    int bad = 0;
    for (int r = 0; r < rounds; r++) {
        machine_init(); eval_init(); eval_set_workers(workers);
        RefId U0 = mk_universe(0), A = var(U0), a = var(A), b = var(A);
        if (cyclic) {
            SymbolId L = define_global("loop", varset_make(NULL, 0), dimset_make(NULL, 0), U0);
            set_global_body(L, global_ref(L));
            storm_ref = global_ref(L);
        } else {
            TermVarId x = declare_term(A, fc_true()), y = declare_term(A, fc_true());
            storm_ref = mk_app(mk_app(mk_lam_lv(0, x, A, mk_lam_lv(0, y, A, ref_var(x))), a), b);   /* fresh each round */
        }
        storm_face = fc_true();
        pthread_barrier_init(&bar, NULL, (unsigned)clients);
        pthread_t th[8];
        for (int c = 0; c < clients; c++) pthread_create(&th[c], NULL, storm_client, (void *)(intptr_t)c);
        for (int c = 0; c < clients; c++) pthread_join(th[c], NULL);
        pthread_barrier_destroy(&bar);
        for (int c = 0; c < clients; c++) {
            if (cyclic) { if (!storm_stuck[c] || storm_res[c] != NULL) bad++; }
            else if (storm_stuck[c] || storm_res[c] == NULL || storm_res[c] != storm_res[0]) bad++;
        }
        EntryId e = eval_entry_lookup(storm_ref, storm_face);
        if (!e || eval_entry_runs(e) != 1) bad++;
        if (cyclic && eval_entry_state(e) != E_RUNNING) bad++;
        if (!cyclic && eval_entry_state(e) != E_READY) bad++;
        eval_free(); machine_free();
    }
    return bad;
}

/* §36/§38: teardown of a stuck branchwise join (LeakSanitizer must be clean) */
static int stuck_join_teardown(size_t workers) {
    machine_init(); eval_init(); if (workers) eval_set_workers(workers);
    RefId U0 = mk_universe(0), A = var(U0), a = var(A);
    uint64_t params[1] = { ref_var_id(A) };
    SymbolId L = define_global("loopf", varset_make(params, 1), dimset_make(NULL, 0), mk_fun(0, 0, A, A));
    set_global_body(L, global_ref(L));
    DimVarId k = declare_dim();
    FaceId fs[2] = { fc_lit(k, 0), fc_lit(k, 1) };
    RefId ts[2] = { global_ref(L), mk_lam_lv(0, declare_term(A, fc_true()), A, a) };
    WhnfStatus st;
    EvalResult *r = whnf(mk_app(mk_system(2, fs, ts), a), fc_join(fs[0], fs[1]), &st);
    int bad = (st != W_STUCK || r != NULL) ? 1 : 0;
    if (eval_running_count() == 0) bad++;
    eval_free(); machine_free();
    return bad;
}

int main(void) {
    printf("== concurrent clients against the shared cache\n");
    int fails = 0;
    { int b = stuck_join_teardown(0) + stuck_join_teardown(4);
      printf("  stuck branchwise join: W_STUCK, nothing published, join dismantled at teardown (%d anomalies)\n", b);
      if (b) fails++; }
    { int b1 = storm(1, 8, 300, false), b4 = storm(4, 8, 300, false);
      printf("  storm on one fresh key, 8 clients x 300 rounds: %d anomalies with 1 worker, %d with 4 workers\n", b1, b4);
      if (b1 || b4) fails++; }
    { int c1 = storm(1, 8, 50, true), c4 = storm(4, 8, 50, true);
      printf("  storm on a cyclic key: %d anomalies (every client W_STUCK, nothing published, one task)\n", c1 + c4);
      if (c1 || c4) fails++; }
    Outcome seq = run(0, 4);
    printf("  sequential 4 clients: W=(REQUEST %zu, EVAL_STEP %zu, PUB %zu, DELIVER %zu) keys=%zu\n", seq.ev.request, seq.ev.eval_step, seq.ev.publish, seq.ev.deliver, seq.entries);
    size_t cfg[][2] = { {2, 2}, {4, 4}, {8, 4}, {3, 8}, {8, 8} };
    for (size_t k = 0; k < sizeof cfg / sizeof cfg[0]; k++) {
        for (int rep = 0; rep < 3; rep++) {
            Outcome c = run(cfg[k][0], (int)cfg[k][1]);
            Outcome s4 = (cfg[k][1] == 4) ? seq : run(0, (int)cfg[k][1]);
            MatchReport mr; bool same_graph = graph_match(c.graph, s4.graph, &mr);
            bool ok = c.ev.request == s4.ev.request && c.ev.eval_step == s4.ev.eval_step && c.ev.publish == s4.ev.publish && c.ev.deliver == s4.ev.deliver
                      && c.bad_runs == 0 && c.bad_pub == 0 && c.bad_deliver == 0 && c.mismatched == 0 && same_graph;
            if (!ok) {
                fails++;
                printf("  FAIL workers=%zu clients=%zu rep=%d: W=(%zu,%zu,%zu,%zu) vs seq (%zu,%zu,%zu,%zu) runs>1:%zu pub>1:%zu req!=deliver:%zu mismatched:%zu dump %s\n",
                       cfg[k][0], cfg[k][1], rep, c.ev.request, c.ev.eval_step, c.ev.publish, c.ev.deliver, s4.ev.request, s4.ev.eval_step, s4.ev.publish, s4.ev.deliver,
                       c.bad_runs, c.bad_pub, c.bad_deliver, c.mismatched, same_graph ? "equal" : mr.reason);
            } else if (rep == 0) printf("  workers=%zu clients=%zu: W and canonical graph equal to the sequential run; one task and one publication per key\n", cfg[k][0], cfg[k][1]);
            graph_free(c.graph);
            if (cfg[k][1] != 4) graph_free(s4.graph);
        }
    }
    graph_free(seq.graph);
    printf(fails ? "CONCURRENT CHECK FAILED\n" : "concurrent check passed\n");
    return fails ? 1 : 0;
}
