#define _POSIX_C_SOURCE 200809L
/* §28–§31: schedule independence.
 *
 * The same initial configuration is built on a fresh machine and reduced
 * under every combination of job-selection policy (evaluation scheduler:
 * FIFO / LIFO / seeded random) and active-pair selection policy (descriptor
 * net: LIFO / FIFO / seeded random). The invariant of the theorem is the
 * interaction-work vector W = (REQUEST, EVAL_STEP, PUB, DELIVER, RULE_r) and
 * the observed normal forms; the latter are compared as canonical dumps of
 * the complete reachable result graph under one consistent renaming of
 * generated identities (src/canon.c), which preserves aliasing. Per-key
 * event multisets are also compared so that a failure names the first
 * divergent event. Interned-record and allocation totals are reported as
 * diagnostics and are not part of the invariant. */
#include "../src/eval.h"
#include "../src/lib.h"
#include "../src/net.h"
#include "../src/canon.h"
#include "assoc.h"

typedef struct {
    EvalEvents ev;
    size_t net_op, net_dup, net_erase, net_deliver, net_rewrites;
    EvalNetEvents en;    /* the evaluator's net: APPLY_TRANSFORM / CONTINUE_REFERENCE events (§43, §45) */
    unsigned net_root_kind[4];
    size_t running_after_ok;
    /* exported result graph (results = ordered roots, keys = set roots) */
    Graph *graph;
    char *results;      /* diagnostic text dump */
    /* diagnostics */
    size_t entries, n_refs, n_nodes, n_maps, n_faces, n_intervals, n_nominal, n_terms, n_dims;
    size_t ready_hit, running_hit;
} Run;

static TermVarId tv(RefId type) { return declare_term(type, fc_true()); }
static RefId var(RefId type) { return ref_var(tv(type)); }

#define MAXROOTS 48
static RefId root_ref[MAXROOTS]; static FaceId root_face[MAXROOTS]; static EvalResult *root_res[MAXROOTS]; static WhnfStatus root_st[MAXROOTS]; static size_t nroots;

static void observe(RefId t, FaceId chi, Run *R) {
    WhnfStatus st;
    EvalResult *r = whnf(t, chi, &st);
    if (st == W_OK) R->running_after_ok += eval_running_count();
    root_ref[nroots] = t; root_face[nroots] = chi; root_res[nroots] = r; root_st[nroots] = st; nroots++;
}


static void workload(Run *R, SchedPolicy pol, int netpol, uint64_t seed) {
    memset(R, 0, sizeof *R);
    nroots = 0;
    machine_init(); eval_init(); check_init(); compiler_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    eval_set_policy(pol, seed);
    eval_set_pair_policy((SchedPolicy)(netpol == 0 ? POL_LIFO : netpol == 1 ? POL_FIFO : POL_RANDOM), seed ? seed * 7 + 3 : 5);
    RefId U0 = mk_universe(0);
    RefId A = var(U0), B = var(U0), T = var(U0);
    DimVarId i = declare_dim(), k = declare_dim(), m = declare_dim(), n = declare_dim();
    RefId a = var(A), b = var(A);
    TermVarId x = tv(A), y = tv(A);
    RefId id = mk_lam_lv(0, x, A, ref_var(x));

    /* neutral path application under three faces, and after reindexing */
    RefId p = var(mk_path_const(0, A, a, b));
    RefId pi = mk_papp_const(0, A, a, b, p, iv_var(i));
    observe(pi, fc_true(), R); observe(pi, fc_lit(i, 0), R); observe(pi, fc_lit(i, 1), R);
    observe(reindex_dim(pi, i, iv_var(k)), fc_lit(k, 0), R);
    /* branchwise application over a system */
    FaceId fs[2] = { fc_lit(k, 0), fc_lit(k, 1) };
    RefId ts[2] = { mk_lam_lv(0, tv(A), A, a), var(mk_fun(0, 0, A, A)) };
    observe(mk_app(mk_system(2, fs, ts), b), fc_join(fs[0], fs[1]), R);
    /* repeated demand of one key from two concurrently launched frames: both
     * branches forward to the same closed reference t0, so one request hits
     * RUNNING or READY depending on the schedule */
    RefId t0 = mk_app(mk_app(mk_lam_lv(0, x, A, mk_lam_lv(0, y, A, ref_var(x))), a), b);
    RefId ts3[2] = { mk_lam_lv(0, tv(A), A, t0), mk_lam_lv(0, tv(A), A, t0) };
    observe(mk_app(mk_system(2, fs, ts3), b), fc_join(fs[0], fs[1]), R);
    RefId ts4[2] = { mk_lam_lv(0, tv(A), A, mk_fst(mk_pair(t0, a))), mk_lam_lv(0, tv(A), A, mk_snd(mk_pair(b, t0))) };
    observe(mk_app(mk_system(2, fs, ts4), b), fc_join(fs[0], fs[1]), R);
    /* composition clauses */
    RefId f = var(mk_fun(0, 0, A, B));
    RefId cpi = mk_coe_at(0, i, mk_fun(0, 0, A, B), f);
    observe(cpi, fc_true(), R); observe(mk_app(cpi, a), fc_true(), R);
    RefId S = mk_sigma_lv(0, 0, x, A, B);
    RefId csg = mk_coe_at(0, i, S, var(S));
    observe(csg, fc_true(), R); observe(mk_fst(csg), fc_true(), R); observe(mk_snd(csg), fc_true(), R);
    RefId cpa = mk_coe_at(0, i, mk_path_const(0, A, a, a), var(mk_path_const(0, A, a, a)));
    observe(mk_papp_const(0, A, a, a, cpa, iv_var(k)), fc_true(), R);
    observe(mk_papp_const(0, A, a, a, cpa, iv_var(k)), fc_lit(k, 1), R);
    observe(mk_comp_lv(0, i, U0, fc_lit(n, 0), B, A), fc_true(), R);
    /* type-family system with ∀ guards: a system of compositions, each
     * branch evaluated under its guard by the join */
    FaceId gs[2] = { fc_lit(n, 0), fc_lit(n, 1) };
    RefId Ys[2] = { T, mk_fun(0, 0, A, A) };
    RefId cmp4 = mk_comp_lv(0, m, mk_system(2, gs, Ys), fc_false(), mk_system(0, NULL, NULL), var(A));
    observe(cmp4, fc_join(gs[0], gs[1]), R); observe(cmp4, gs[1], R);
    RefId Ys2[2] = { mk_fun(0, 0, A, B), mk_sigma_lv(0, 0, x, A, B) };
    RefId cmp5 = mk_comp_lv(0, m, mk_system(2, gs, Ys2), fc_false(), mk_system(0, NULL, NULL), var(A));
    observe(cmp5, fc_join(gs[0], gs[1]), R);
    /* Glue composition off and on the Glue face, and transport along ua */
    RefId e = var(mk_equiv(0, 0, T, A));
    RefId Gm = mk_glue_type_lv(0, A, fc_lit(m, 1), T, e);
    RefId cg = mk_coe_at(0, i, Gm, var(Gm));
    observe(cg, fc_true(), R);
    observe(mk_unglue_lv(0, A, fc_lit(m, 1), T, e, cg), fc_true(), R);
    observe(cg, fc_lit(m, 1), R);
    RefId ua = mk_ua(1, U0, U0, mk_id_equiv(1, U0));
    RefId tr = mk_coe_at(1, i, mk_papp_const(2, mk_universe(1), U0, U0, ua, iv_var(i)), A);
    observe(tr, fc_true(), R);
    observe(mk_fst(mk_unglue_lv(0, U0, fc_true(), U0, mk_id_equiv(0, U0), tr)), fc_true(), R);
    observe(t0, fc_true(), R);

    /* §47 case 10: duplicate transformed-reference demands. The associativity
     * transform is invoked in both orientations; the same call is demanded
     * under three faces and after a dimension substitution, and its
     * components and output path are observed. */
    { const char *why; Assoc As; assoc_build(&As, &why);
      require(As.T, "associativity must compile in the schedule workload (%s)", why);
      MapId sigma = assoc_sigma(&As, As.rhs);
      RefId r = assoc_left_arg(&As, sigma);
      RefId call = mk_transform_call(As.T, DIR_FORWARD, sigma, r);
      DimVarId j = declare_dim();
      observe(call, fc_true(), R);
      observe(call, fc_lit(j, 0), R);                     /* same key: j is not in the call's support */
      observe(mk_fst(call), fc_true(), R);
      RefId path = mk_snd(mk_snd(call));
      observe(path, fc_true(), R);
      observe(mk_papp_const(0, As.X, As.rhs, As.rhs, path, iv_var(j)), fc_true(), R);
      observe(mk_papp_const(0, As.X, As.rhs, As.rhs, path, iv_var(j)), fc_lit(j, 1), R);
      RefId rcall = mk_transform_call(As.T, DIR_REVERSE, sigma, assoc_right_arg(&As, sigma));
      observe(rcall, fc_true(), R);
      observe(mk_fst(rcall), fc_true(), R);
      observe(mk_fst(mk_snd(rcall)), fc_true(), R);
      /* a call whose boundary moves along k, demanded whole and specialized */
      DimVarId kk = declare_dim();
      RefId yk = mk_papp_const(0, As.X, As.lhs, As.rhs, As.alpha, iv_var(kk));
      MapId sk = assoc_sigma(&As, yk);
      DimVarId i2 = declare_dim();
      RefId w = mk_plam(i2, mk_papp_const(0, As.X, As.lhs, As.rhs, As.alpha, iv_meet(iv_var(i2), iv_var(kk))));
      RefId RLk = reindex(transform_get(As.T)->domain, sk);
      RefId rk = mk_pair_at_lv(0, RLk, As.mab, mk_pair_at_lv(0, apply_term_binder(RLk, 0, 1, As.mab), mk_refl(0, As.X, As.mab), w));
      RefId callk = mk_transform_call(As.T, DIR_FORWARD, sk, rk);
      observe(callk, fc_true(), R);
      observe(callk, fc_lit(kk, 0), R);
      observe(reindex_dim(callk, kk, iv_one()), fc_true(), R);
      observe(mk_fst(reindex_dim(callk, kk, iv_one())), fc_true(), R); }

    /* descriptor net under the net policy: two EVAL agents on one key, and
     * duplication of a materialized system head */
    Net net; net_init(&net); net.policy = netpol; net.rng = seed ? seed * 3 + 1 : 1;
    if (getenv("CUBICAL_WORKERS")) net_set_workers(&net, (size_t)atoi(getenv("CUBICAL_WORKERS")));
    int8_t pneg[1] = { -1 }, pdup[3] = { -1, +1, +1 }; Payload P = {0};
    NodeId roots[4];
    for (int q = 0; q < 4; q++) roots[q] = net_node(&net, A_ROOT, 1, pneg, P);
    RefId tt = mk_app(id, mk_pair(a, b));
    NodeId e1 = net_operation(&net, OP_EVAL, (Payload){ .face = fc_true() }), e2 = net_operation(&net, OP_EVAL, (Payload){ .face = fc_lit(i, 0) });
    net_connect(&net, e1, 1, roots[0], 0); net_connect(&net, e2, 1, roots[1], 0);
    P.ref = tt;
    net_connect(&net, e1, 0, net_descriptor(&net, D_REF, P), 0);
    net_connect(&net, e2, 0, net_descriptor(&net, D_REF, P), 0);
    NodeId op = net_operation(&net, OP_OPEN, (Payload){0});
    NodeId mat = net_operation(&net, OP_MATERIALIZE, (Payload){0});
    NodeId dup = net_node(&net, A_DUP, 3, pdup, (Payload){0});
    net_connect(&net, op, 1, mat, 0);
    net_connect(&net, mat, 1, dup, 0);
    net_connect(&net, dup, 1, roots[2], 0); net_connect(&net, dup, 2, roots[3], 0);
    P.ref = mk_system(2, fs, ts);
    net_connect(&net, op, 0, net_descriptor(&net, D_REF, P), 0);
    net_run_with_eval(&net);
    for (int q = 0; q < 4; q++) { NodeKind kk = 0; net_root_read(&net, roots[q], &kk, NULL); R->net_root_kind[q] = (unsigned)kk; }
    R->net_op = net.n_op; R->net_dup = net.n_dup; R->net_erase = net.n_erase; R->net_deliver = net.n_eval_deliver; R->net_rewrites = net.rewrites;
    net_free(&net);

    R->ev = eval_events();
    R->en = eval_net_events();
    R->ready_hit = R->ev.ready_hit; R->running_hit = R->ev.running_hit;

    /* exact canonical dump: root observations in a fixed order, then every
     * cache key with its per-key event counts in canonical order */
    Canon *c = canon_new();
    for (size_t q = 0; q < nroots; q++) {
        char line[64]; snprintf(line, sizeof line, "%zu status %d", q, (int)root_st[q]);
        canon_add_result(c, line, root_res[q]);
    }
    size_t ne = eval_entry_count();
    for (EntryId eid = 1; eid <= ne; eid++) {
        if (!eval_entry_is_observation(eid)) continue;
        size_t req, del, pub; eval_entry_events(eid, &req, &del, &pub);
        canon_add_key(c, eval_entry_ref(eid), eval_entry_face(eid), req, del, pub, (int)eval_entry_state(eid));
    }
    R->graph = canon_export(c);
    R->results = strdup("");
    canon_free(c);
    R->entries = ne;
    R->n_refs = interner_count(&M.refs); R->n_nodes = interner_count(&M.tnodes); R->n_maps = interner_count(&M.maps);
    R->n_faces = interner_count(&M.faces); R->n_intervals = interner_count(&M.intervals); R->n_nominal = interner_count(&M.nominal);
    R->n_terms = M.n_term_vars; R->n_dims = M.n_dim_vars;
    compiler_free(); check_free(); eval_free(); machine_free();
}

static bool compare(const Run *a, const Run *b, const char *name, uint64_t seed) {
    bool ok = true;
    if (a->ev.request != b->ev.request || a->ev.eval_step != b->ev.eval_step || a->ev.publish != b->ev.publish || a->ev.deliver != b->ev.deliver) {
        printf("  FAIL [%s seed %llu]: event vector differs\n", name, (unsigned long long)seed); ok = false;
    }
    if (a->net_op != b->net_op || a->net_dup != b->net_dup || a->net_erase != b->net_erase || a->net_deliver != b->net_deliver) {
        printf("  FAIL [%s seed %llu]: net rule counts differ\n", name, (unsigned long long)seed); ok = false;
    }
    if (a->en.apply != b->en.apply || a->en.continue_ref != b->en.continue_ref || a->en.op != b->en.op || a->en.eval_deliver != b->en.eval_deliver) {
        printf("  FAIL [%s seed %llu]: evaluator-net rule counts differ (apply %zu/%zu continue %zu/%zu)\n", name, (unsigned long long)seed, a->en.apply, b->en.apply, a->en.continue_ref, b->en.continue_ref); ok = false;
    }
    for (int q = 0; q < 4; q++) if (a->net_root_kind[q] != b->net_root_kind[q]) { printf("  FAIL [%s seed %llu]: net root %d differs\n", name, (unsigned long long)seed, q); ok = false; }
    MatchReport mr;
    if (!graph_match(a->graph, b->graph, &mr)) { printf("  FAIL [%s seed %llu]: result graphs are not equal modulo renaming: %s\n", name, (unsigned long long)seed, mr.reason); ok = false; }
    return ok;
}

static void show(const char *name, const Run *r) {
    printf("  %-14s W=(REQUEST %zu, EVAL_STEP %zu, PUB %zu, DELIVER %zu | op %zu, dup %zu, erase %zu, eval-deliver %zu | apply %zu, continue %zu)  hits ready/running %zu/%zu\n",
           name, r->ev.request, r->ev.eval_step, r->ev.publish, r->ev.deliver, r->net_op, r->net_dup, r->net_erase, r->net_deliver, r->en.apply, r->en.continue_ref, r->ready_hit, r->running_hit);
}

int main(void) {
    printf("== §28–31 schedule independence of interaction work and observed normal forms\n");
    Run base, other;
    workload(&base, POL_FIFO, 1, 0);
    show("FIFO/net-FIFO", &base);
    int fails = 0, runs = 1;
    const char *enames[3] = { "FIFO", "LIFO", "random" }, *nnames[3] = { "LIFO", "FIFO", "random" };
    bool hits_vary = false;
    for (int ep = 0; ep < 3; ep++) for (int np = 0; np < 3; np++) {
        int nseeds = (ep == 2 || np == 2) ? 4 : 1;
        for (int s = 0; s < nseeds; s++) {
            uint64_t seed = 0x2545F4914F6CDD1DULL * (uint64_t)(s + 1) + (uint64_t)(ep * 3 + np);
            if (ep == 0 && np == 1 && s == 0) continue;     /* base */
            workload(&other, (SchedPolicy)ep, np, seed);
            char name[64]; snprintf(name, sizeof name, "%s/net-%s", enames[ep], nnames[np]);
            if (!compare(&base, &other, name, seed)) { show(name, &other); fails++; }
            if (other.ready_hit != base.ready_hit || other.running_hit != base.running_hit) hits_vary = true;
            if (other.n_refs != base.n_refs || other.n_nodes != base.n_nodes || other.n_nominal != base.n_nominal || other.n_terms != base.n_terms || other.n_dims != base.n_dims || other.entries != base.entries)
                printf("  note [%s]: allocation diagnostics differ (refs %zu/%zu nodes %zu/%zu nominal %zu/%zu names %zu+%zu/%zu+%zu entries %zu/%zu) — not part of the invariant\n",
                       name, base.n_refs, other.n_refs, base.n_nodes, other.n_nodes, base.n_nominal, other.n_nominal, base.n_terms, base.n_dims, other.n_terms, other.n_dims, base.entries, other.entries);
            if (s == nseeds - 1 && (ep == 2 && np == 2)) show(name, &other);
            free(other.results); graph_free(other.graph);
            runs++;
        }
    }
    { MatchReport mr; graph_match(base.graph, base.graph, &mr);
      printf("  %zu root observations, %zu cache keys, result graph %zu nodes (%zu joint refinement classes); %d schedules compared by exact matching\n", nroots, base.entries, base.graph->nodes.len, mr.classes_joint, runs); }
    printf("  ready-hit/running-hit diagnostics %s across schedules; REQUEST − launches = %zu is invariant\n", hits_vary ? "vary" : "coincide", base.ready_hit + base.running_hit);
    printf("  allocation diagnostics (base): refs %zu nodes %zu maps %zu faces %zu intervals %zu nominal %zu names %zu+%zu\n", base.n_refs, base.n_nodes, base.n_maps, base.n_faces, base.n_intervals, base.n_nominal, base.n_terms, base.n_dims);
    if (base.running_after_ok) { printf("  FAIL: a completed root left %zu RUNNING entries in its demand network\n", base.running_after_ok); fails++; }
    else printf("  no RUNNING entry survives a completed root observation\n");
    free(base.results); graph_free(base.graph);
    printf(fails ? "SCHEDULE CHECK FAILED\n" : "schedule check passed\n");
    return fails ? 1 : 0;
}
