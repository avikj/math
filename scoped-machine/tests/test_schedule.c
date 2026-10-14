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

typedef struct {
    EvalEvents ev;
    size_t net_op, net_dup, net_erase, net_deliver, net_rewrites;
    unsigned net_root_kind[4];
    size_t running_after_ok;
    /* canonical dumps */
    char *results;      /* RESULT lines + reachable record graph */
    char *events;       /* per-key event multiset, sorted lines */
    /* diagnostics */
    size_t entries, n_refs, n_origins, n_maps, n_faces, n_intervals, n_nominal, n_terms, n_dims;
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

static int cmp_lines(const void *a, const void *b) { return strcmp(*(char *const *)a, *(char *const *)b); }

static void workload(Run *R, SchedPolicy pol, int netpol, uint64_t seed) {
    memset(R, 0, sizeof *R);
    nroots = 0;
    machine_init(); eval_init();
    eval_set_policy(pol, seed);
    RefId U0 = mk_universe(0);
    RefId A = var(U0), B = var(U0), T = var(U0);
    DimVarId i = declare_dim(), k = declare_dim(), m = declare_dim(), n = declare_dim();
    RefId a = var(A), b = var(A);
    TermVarId x = tv(A), y = tv(A);
    RefId id = mk_lam(x, A, ref_var(x));

    /* neutral path application under three faces, and after reindexing */
    RefId p = var(mk_path_const(A, a, b));
    RefId pi = mk_papp_const(A, a, b, p, iv_var(i));
    observe(pi, fc_true(), R); observe(pi, fc_lit(i, 0), R); observe(pi, fc_lit(i, 1), R);
    observe(reindex_dim(pi, i, iv_var(k)), fc_lit(k, 0), R);
    /* branchwise application over a system */
    FaceId fs[2] = { fc_lit(k, 0), fc_lit(k, 1) };
    RefId ts[2] = { mk_lam(tv(A), A, a), var(mk_fun(A, A)) };
    observe(mk_app(mk_system(2, fs, ts), b), fc_join(fs[0], fs[1]), R);
    /* repeated demand of one key from two concurrently launched frames: both
     * branches forward to the same closed reference t0, so one request hits
     * RUNNING or READY depending on the schedule */
    RefId t0 = mk_app(mk_app(mk_lam(x, A, mk_lam(y, A, ref_var(x))), a), b);
    RefId ts3[2] = { mk_lam(tv(A), A, t0), mk_lam(tv(A), A, t0) };
    observe(mk_app(mk_system(2, fs, ts3), b), fc_join(fs[0], fs[1]), R);
    RefId ts4[2] = { mk_lam(tv(A), A, mk_fst(mk_pair(t0, a))), mk_lam(tv(A), A, mk_snd(mk_pair(b, t0))) };
    observe(mk_app(mk_system(2, fs, ts4), b), fc_join(fs[0], fs[1]), R);
    /* composition clauses */
    RefId f = var(mk_fun(A, B));
    RefId cpi = mk_coe(i, mk_fun(A, B), f);
    observe(cpi, fc_true(), R); observe(mk_app(cpi, a), fc_true(), R);
    RefId S = mk_sigma(x, A, B);
    RefId csg = mk_coe(i, S, var(S));
    observe(csg, fc_true(), R); observe(mk_fst(csg), fc_true(), R); observe(mk_snd(csg), fc_true(), R);
    RefId cpa = mk_coe(i, mk_path_const(A, a, a), var(mk_path_const(A, a, a)));
    observe(mk_papp_const(A, a, a, cpa, iv_var(k)), fc_true(), R);
    observe(mk_papp_const(A, a, a, cpa, iv_var(k)), fc_lit(k, 1), R);
    observe(mk_comp(i, U0, fc_lit(n, 0), B, A), fc_true(), R);
    /* type-family system with ∀ guards: a system of compositions, each
     * branch evaluated under its guard by the join */
    FaceId gs[2] = { fc_lit(n, 0), fc_lit(n, 1) };
    RefId Ys[2] = { T, mk_fun(A, A) };
    RefId cmp4 = mk_comp(m, mk_system(2, gs, Ys), fc_false(), mk_system(0, NULL, NULL), var(A));
    observe(cmp4, fc_join(gs[0], gs[1]), R); observe(cmp4, gs[1], R);
    RefId Ys2[2] = { mk_fun(A, B), mk_sigma(x, A, B) };
    RefId cmp5 = mk_comp(m, mk_system(2, gs, Ys2), fc_false(), mk_system(0, NULL, NULL), var(A));
    observe(cmp5, fc_join(gs[0], gs[1]), R);
    /* Glue composition off and on the Glue face, and transport along ua */
    RefId e = var(mk_equiv(T, A));
    RefId Gm = mk_glue_type(A, fc_lit(m, 1), T, e);
    RefId cg = mk_coe(i, Gm, var(Gm));
    observe(cg, fc_true(), R);
    observe(mk_unglue(A, fc_lit(m, 1), T, e, cg), fc_true(), R);
    observe(cg, fc_lit(m, 1), R);
    RefId ua = mk_ua(U0, U0, mk_id_equiv(U0));
    RefId tr = mk_coe(i, mk_papp_const(mk_universe(1), U0, U0, ua, iv_var(i)), A);
    observe(tr, fc_true(), R);
    observe(mk_fst(mk_unglue(U0, fc_true(), U0, mk_id_equiv(U0), tr)), fc_true(), R);
    observe(t0, fc_true(), R);

    /* descriptor net under the net policy: two EVAL agents on one key, and
     * duplication of a materialized system head */
    Net net; net_init(&net); net.policy = netpol; net.rng = seed ? seed * 3 + 1 : 1;
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
    R->ready_hit = R->ev.ready_hit; R->running_hit = R->ev.running_hit;

    /* canonical dump of all root observations (roots in a fixed order) */
    Canon *c = canon_new();
    for (size_t q = 0; q < nroots; q++) {
        char line[64]; snprintf(line, sizeof line, "ROOT %zu status %d ", q, (int)root_st[q]); canon_text(c, line);
        if (root_res[q]) canon_dump_result(c, root_res[q]); else canon_text(c, "RESULT PENDING\n");
    }
    size_t len; const char *buf = canon_buffer(c, &len);
    R->results = strdup(buf);
    /* per-key event multiset: one line per cache entry, sorted */
    Canon *ce = canon_new();
    size_t ne = eval_entry_count();
    char **lines = malloc((ne ? ne : 1) * sizeof(char *));
    for (EntryId eid = 1; eid <= ne; eid++) {
        size_t req, del, pub; eval_entry_events(eid, &req, &del, &pub);
        size_t mark; canon_buffer(ce, &mark);
        char head[128];
        snprintf(head, sizeof head, "KEY h=%016llx face=", (unsigned long long)canon_hash_ref(ce, eval_entry_ref(eid)));
        canon_text(ce, head); canon_dump_face_text(ce, eval_entry_face(eid));
        snprintf(head, sizeof head, " REQ=%zu DELIVER=%zu PUB=%zu state=%d\n", req, del, pub, (int)eval_entry_state(eid));
        canon_text(ce, head);
        size_t now; const char *b2 = canon_buffer(ce, &now);
        lines[eid - 1] = strndup(b2 + mark, now - mark);
    }
    qsort(lines, ne, sizeof(char *), cmp_lines);
    size_t tot = 1; for (size_t q = 0; q < ne; q++) tot += strlen(lines[q]);
    R->events = malloc(tot); R->events[0] = 0;
    for (size_t q = 0; q < ne; q++) { strcat(R->events, lines[q]); free(lines[q]); }
    free(lines);
    canon_free(c); canon_free(ce);

    R->entries = ne;
    R->n_refs = interner_count(&M.refs); R->n_origins = interner_count(&M.origins); R->n_maps = interner_count(&M.maps);
    R->n_faces = interner_count(&M.faces); R->n_intervals = interner_count(&M.intervals); R->n_nominal = interner_count(&M.nominal);
    R->n_terms = M.n_term_vars; R->n_dims = M.n_dim_vars;
    eval_free(); machine_free();
}

static void first_diff(const char *label, const char *a, const char *b) {
    const char *pa = a, *pb = b;
    size_t line = 1;
    while (*pa && *pb) {
        const char *ea = strchr(pa, '\n'), *eb = strchr(pb, '\n');
        size_t la = ea ? (size_t)(ea - pa) : strlen(pa), lb = eb ? (size_t)(eb - pb) : strlen(pb);
        if (la != lb || memcmp(pa, pb, la) != 0) {
            printf("    first divergent %s line %zu:\n      A: %.*s\n      B: %.*s\n", label, line, (int)la, pa, (int)lb, pb);
            return;
        }
        if (!ea || !eb) break;
        pa = ea + 1; pb = eb + 1; line++;
    }
    if (*pa || *pb) printf("    %s: one dump is a prefix of the other (line %zu)\n", label, line);
}

static bool compare(const Run *a, const Run *b, const char *name, uint64_t seed) {
    bool ok = true;
    if (a->ev.request != b->ev.request || a->ev.eval_step != b->ev.eval_step || a->ev.publish != b->ev.publish || a->ev.deliver != b->ev.deliver) {
        printf("  FAIL [%s seed %llu]: event vector differs\n", name, (unsigned long long)seed); ok = false;
    }
    if (a->net_op != b->net_op || a->net_dup != b->net_dup || a->net_erase != b->net_erase || a->net_deliver != b->net_deliver) {
        printf("  FAIL [%s seed %llu]: net rule counts differ\n", name, (unsigned long long)seed); ok = false;
    }
    for (int q = 0; q < 4; q++) if (a->net_root_kind[q] != b->net_root_kind[q]) { printf("  FAIL [%s seed %llu]: net root %d differs\n", name, (unsigned long long)seed, q); ok = false; }
    if (strcmp(a->results, b->results) != 0) { printf("  FAIL [%s seed %llu]: canonical result graphs differ\n", name, (unsigned long long)seed); first_diff("result line", a->results, b->results); ok = false; }
    if (strcmp(a->events, b->events) != 0) { printf("  FAIL [%s seed %llu]: per-key event multisets differ\n", name, (unsigned long long)seed); first_diff("event", a->events, b->events); ok = false; }
    return ok;
}

static void show(const char *name, const Run *r) {
    printf("  %-14s W=(REQUEST %zu, EVAL_STEP %zu, PUB %zu, DELIVER %zu | op %zu, dup %zu, erase %zu, eval-deliver %zu)  hits ready/running %zu/%zu\n",
           name, r->ev.request, r->ev.eval_step, r->ev.publish, r->ev.deliver, r->net_op, r->net_dup, r->net_erase, r->net_deliver, r->ready_hit, r->running_hit);
}

int main(void) {
    printf("== §28–31 schedule independence of interaction work and observed normal forms\n");
    Run base, other;
    workload(&base, SCHED_FIFO, 1, 0);
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
            if (other.n_refs != base.n_refs || other.n_origins != base.n_origins || other.n_nominal != base.n_nominal || other.n_terms != base.n_terms || other.n_dims != base.n_dims || other.entries != base.entries)
                printf("  note [%s]: allocation diagnostics differ (refs %zu/%zu origins %zu/%zu nominal %zu/%zu names %zu+%zu/%zu+%zu entries %zu/%zu) — not part of the invariant\n",
                       name, base.n_refs, other.n_refs, base.n_origins, other.n_origins, base.n_nominal, other.n_nominal, base.n_terms, base.n_dims, other.n_terms, other.n_dims, base.entries, other.entries);
            if (s == nseeds - 1 && (ep == 2 && np == 2)) show(name, &other);
            free(other.results); free(other.events);
            runs++;
        }
    }
    printf("  %zu root observations, %zu cache keys, canonical result graph %zu bytes; %d schedules compared\n", nroots, base.entries, strlen(base.results), runs);
    printf("  ready-hit/running-hit diagnostics %s across schedules; REQUEST − launches = %zu is invariant\n", hits_vary ? "vary" : "coincide", base.ready_hit + base.running_hit);
    printf("  allocation diagnostics (base): refs %zu origins %zu maps %zu faces %zu intervals %zu nominal %zu names %zu+%zu\n", base.n_refs, base.n_origins, base.n_maps, base.n_faces, base.n_intervals, base.n_nominal, base.n_terms, base.n_dims);
    if (base.running_after_ok) { printf("  FAIL: a completed root left %zu RUNNING entries in its demand network\n", base.running_after_ok); fails++; }
    else printf("  no RUNNING entry survives a completed root observation\n");
    free(base.results); free(base.events);
    printf(fails ? "SCHEDULE CHECK FAILED\n" : "schedule check passed\n");
    return fails ? 1 : 0;
}
