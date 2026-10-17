/* EFFECT-AUTHORITY §10: the ten-part acceptance witness, read from ONE
 * retained execution (one machine, one evaluator scheduler, one effect
 * registry). The cash state is a schema instance over Church numerals at
 * universe level 1; arithmetic is the ordinary lambda body of `add`; every
 * edge witness is checked by the kernel's framed proof-use audit.
 * Run: test_effect_witness [workers]   (the one-job-budget part, item 9, runs with 0 workers) */
#include "check.h"
#include "lib.h"
#include "compiler.h"
#include "runtime.h"
#include "proof.h"
#include "work.h"
#include "effect.h"
#include "reuse_stats.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fails;
#define EXPECT(c, ...) do { if (!(c)) { fails++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static RefId U0, N, ADD, NN;
static RefId kmemo[64];
static RefId numeral(int k) {
    if (kmemo[k]) return kmemo[k];
    TermVarId X = declare_term(U0, fc_true()); RefId Xr = ref_var(X);
    TermVarId f = declare_term(mk_fun(0, 0, Xr, Xr), fc_true()); TermVarId x = declare_term(Xr, fc_true());
    RefId b = ref_var(x); for (int i = 0; i < k; i++) b = mk_app(ref_var(f), b);
    return kmemo[k] = mk_lam_lv(1, X, U0, mk_lam_lv(0, f, mk_fun(0, 0, Xr, Xr), mk_lam_lv(0, x, Xr, b)));
}
/* the host exact reading of a canonical numeral state (by identity with the canonical terms) */
static int nread(RefId t) { for (int k = 0; k < 64; k++) if (kmemo[k] == t) return k; return -1; }
static RefId add(RefId a, RefId b) { return mk_app(mk_app(ADD, a), b); }
static void cash_world(void) {
    U0 = mk_universe(0);
    { TermVarId X = declare_term(U0, fc_true()); RefId Xr = ref_var(X); N = mk_pi_lv(1, 0, X, U0, mk_fun(0, 0, mk_fun(0, 0, Xr, Xr), mk_fun(0, 0, Xr, Xr))); }
    TermVarId m = declare_term(N, fc_true()), n = declare_term(N, fc_true());
    TermVarId X = declare_term(U0, fc_true()); RefId Xr = ref_var(X);
    TermVarId f = declare_term(mk_fun(0, 0, Xr, Xr), fc_true()); TermVarId x = declare_term(Xr, fc_true());
    RefId body = mk_app(mk_app(mk_app(ref_var(m), Xr), ref_var(f)), mk_app(mk_app(mk_app(ref_var(n), Xr), ref_var(f)), ref_var(x)));
    ADD = mk_lam_lv(1, m, N, mk_lam_lv(1, n, N, mk_lam_lv(1, X, U0, mk_lam_lv(0, f, mk_fun(0, 0, Xr, Xr), mk_lam_lv(0, x, Xr, body)))));
    TermVarId v = declare_term(N, fc_true()); NN = mk_sigma_lv(1, 1, v, N, N);
    for (int k = 0; k < 16; k++) numeral(k);
}

/* ---- the clients: each records its delivered outcome ---- */
typedef struct { int delivered; EffOutcome o; } Client;
static void client_cb(void *ctx, EffOutcome o) { Client *c = ctx; c->delivered++; c->o = o; }

/* ---- scheduler holds ---- */
typedef struct { bool key_on; RefId ref; FaceId face; int tags[8]; int ntags; } Hold;
static bool hold_pred(const EvalTaskInfo *in, void *ctx) {
    Hold *h = ctx;
    if (h->key_on && in->kind == ET_EVALUATE && in->producer && eval_entry_ref(in->producer) == h->ref && eval_entry_face(in->producer) == h->face) return true;
    if (in->kind == ET_EXTERNAL) for (int i = 0; i < h->ntags; i++) if (h->tags[i] == in->tag) return true;
    return false;
}

static EffAuthority *A, *B; static EffCap *capA, *capB;
typedef struct { int seen[8]; } Probe;
static bool probe_pred(const EvalTaskInfo *in, void *ctx) { Probe *p = ctx; if (in->kind == ET_EXTERNAL && in->tag >= EFF_TAG_PREPARE && in->tag <= EFF_TAG_EMIT) p->seen[in->tag - EFF_TAG_PREPARE]++; return false; }
static EffOutcomeKind eff_commit_state_of_last(Client *c) { return c->delivered ? c->o.kind : EO_PENDING; }
static EffSchema *SEND, *RECV, *REFUND;
static ContextId G0;
static uint64_t next_req = 100;
/* V(F): balances of the account heads on the current cut + quantities of the unconsumed transfer ports */
static int valuation(int *open_ports) {   /* read from one consistent cut */
    EffCut c; eff_cut_snapshot(&c);
    int v = 0;
    for (size_t i = 0; i < c.nheads; i++) v += nread(eff_head_state(c.head[i]));
    for (size_t i = 0; i < c.nopen; i++) v += nread(eff_port_payload(c.open[i]));
    if (open_ports) *open_ports = (int)c.nopen;
    eff_cut_free(&c);
    return v;
}
static int bal(EffAuthority *a) { return nread(eff_head_state(eff_head(a))); }
static RefId refl_n(int k) { return mk_refl(1, N, numeral(k)); }
/* send q from `from` (balance a) to `to`: Path N (add (a-q) q) a, witnessed by refl at a (conversion) unless w given */
static EffCommit *send(EffAuthority *from, EffCap *cap, EffAuthority *to, int q, RefId w, Client *c, uint64_t req) {
    int a = bal(from);
    EffProposal *P = eff_proposal(SEND, from == A ? 1 : 2, req);
    eff_in_head(P, from, eff_head(from)); eff_out_head(P, from, numeral(a - q)); eff_out_port(P, numeral(q), to, from);
    eff_witness(P, w ? w : refl_n(a)); eff_cap(P, cap);
    return eff_request(P, client_cb, c);
}
/* an endpoint builds its receive proposal for a port once; a duplicate or
 * retransmitted packet of the same port re-issues that identical request */
typedef struct { EffPort *m; const EffHead *h; int b; } RecvMemo;
static RecvMemo rmemo[64]; static int nrmemo;
static EffCommit *receive(EffAuthority *to, EffCap *cap, EffPort *m, Client *c, uint64_t req) {
    const EffHead *h = NULL; int b = -1;
    for (int k = 0; k < nrmemo; k++) if (rmemo[k].m == m && req == 5000 + eff_occ_id(eff_port_issuer(m))) { h = rmemo[k].h; b = rmemo[k].b; }
    if (!h) { h = eff_head(to); b = bal(to); if (nrmemo < 64) rmemo[nrmemo++] = (RecvMemo){ m, h, b }; }
    int q = nread(eff_port_payload(m));
    EffProposal *P = eff_proposal(RECV, 1000 + (to == A ? 1 : 2), req);
    eff_in_port(P, m); eff_in_head(P, to, h); eff_out_head(P, to, numeral(b + q));
    eff_witness(P, refl_n(b + q)); eff_cap(P, cap);
    return eff_request(P, client_cb, c);
}
static EffCommit *refund(EffAuthority *from, EffCap *cap, EffPort *m, RefId w, Client *c, uint64_t req) {
    int a = bal(from), q = nread(eff_port_payload(m));
    EffProposal *P = eff_proposal(REFUND, 2000 + (from == A ? 1 : 2), req);
    eff_in_port(P, m); eff_in_head(P, from, eff_head(from)); eff_out_head(P, from, numeral(a + q));
    eff_witness(P, w ? w : refl_n(a + q)); eff_cap(P, cap);
    return eff_request(P, client_cb, c);
}
static EffPort *last_port_to(EffAuthority *a) { EffPort **ps; size_t n = eff_outbox(a, &ps); EffPort *m = n ? ps[n - 1] : NULL; free(ps); return m; }

/* ---- §11 helpers ---- */
typedef struct { CellId c; int val; EffAuthority *auth; int kind; } RInfoH;
typedef struct { RInfoH *ri; size_t n; } VCtxH;
static int vval_act(void *ctx, CellId x, ModId *out) { VCtxH *v = ctx; for (size_t k = 0; k < v->n; k++) if (v->ri[k].c == x) { *out = mod_int(zx_i64(v->ri[k].val)); return 0; } *out = mod_zero(); return 0; }
typedef struct { RInfoH *ri; size_t n; EffAuthority *who; } ICtxH;
static bool iface_in(void *ctx, CellId x) {   /* the interface of a region: every port occurrence, and the region's authority's heads */
    ICtxH *ic = ctx; uint64_t ns; uint64_t tag = cell_tag(x, &ns);
    if (ns != EFF_NS_RES) return false;
    if (tag >> 63) return true;
    for (size_t k = 0; k < ic->n; k++) if (ic->ri[k].c == x) return ic->ri[k].auth == ic->who;
    return false;
}
static int vheads_act(void *ctx, CellId x, ModId *out) { ICtxH *ic = ctx; for (size_t k = 0; k < ic->n; k++) if (ic->ri[k].c == x && !ic->ri[k].kind && ic->ri[k].auth == ic->who) { *out = mod_int(zx_i64(ic->ri[k].val)); return 0; } *out = mod_zero(); return 0; }
static int vports_act(void *ctx, CellId x, ModId *out) { ICtxH *ic = ctx; for (size_t k = 0; k < ic->n; k++) if (ic->ri[k].c == x && ic->ri[k].kind) { *out = mod_int(zx_i64(ic->ri[k].val)); return 0; } *out = mod_zero(); return 0; }
static CellId to_key(void *ctx, CellId x) { (void)x; return *(CellId *)ctx; }
static bool event_occurred(void *ctx, CellId x) { (void)ctx; uint64_t ns; cell_tag(x, &ns); return ns == EFF_NS_EVENT; }

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    size_t workers = argc > 1 ? (size_t)strtoull(argv[1], NULL, 10) : 0;
    machine_init(); eval_init(); check_init(); compiler_init(); work_init(); effect_init(); chain_init();
    if (workers) eval_set_workers(workers);
    cash_world();
    G0 = context_make(0, NULL, fc_true());
    /* schemas: R_send a o = Path N (add (fst o) (snd o)) a ; R_recv i b' = Path N b' (add (snd i) (fst i)) ; R_refund likewise */
    { TermVarId a = declare_term(N, fc_true()), o = declare_term(NN, fc_true());
      RefId Rs = mk_lam_lv(1, a, N, mk_lam_lv(1, o, NN, mk_path_const(1, N, add(mk_fst(ref_var(o)), mk_snd(ref_var(o))), ref_var(a))));
      SEND = eff_schema("send", G0, fc_true(), N, NN, Rs, EFF_PORT_RECIPIENT); }
    { TermVarId i = declare_term(NN, fc_true()), b = declare_term(N, fc_true());
      RefId Rr = mk_lam_lv(1, i, NN, mk_lam_lv(1, b, N, mk_path_const(1, N, ref_var(b), add(mk_snd(ref_var(i)), mk_fst(ref_var(i))))));
      RECV = eff_schema("receive", G0, fc_true(), NN, N, Rr, EFF_PORT_RECIPIENT);
      REFUND = eff_schema("refund", G0, fc_true(), NN, N, Rr, EFF_PORT_REFUND); }
    A = eff_genesis("A", G0, fc_true(), numeral(7), N, &capA);
    B = eff_genesis("B", G0, fc_true(), numeral(2), N, &capB);
    printf("schema payloads: N = Π(X:U0).(X→X)→X→X at level 1; add = λm n X f x. m X f (n X f x);\n"
           "  send: In = N, Out = N×N, R a o = Path N (add (fst o) (snd o)) a;  receive/refund: In = N×N, Out = N, R i b' = Path N b' (add (snd i) (fst i))\n"
           "  genesis: A = 7, B = 2 (issuance is genesis); admitted assumptions: none expected (CORE audits)\n");
    int total = valuation(NULL);
    EXPECT(total == 9, "genesis valuation 9 (%d)", total);

    /* ---- 1. runtime identity evidence through the generic action ---- */
    RefId p_rt;
    { TermVarId z = declare_term(N, fc_true());
      RefId prog = mk_app(mk_lam_lv(1, z, N, mk_refl(1, N, ref_var(z))), add(numeral(4), numeral(3)));   /* computes refl at runtime */
      WhnfStatus s; EvalResult *r = whnf(prog, fc_true(), &s);
      EXPECT(s == W_OK && r && r->cls == R_INTRODUCTION, "the runtime computation produces identity evidence");
      p_rt = r ? r->ref : 0; }
    RefId C = add(numeral(4), numeral(3));
    RefId L = rt_diagram_zero(1, N, C);
    RefId w_action = rt_action(0, 1, 1, 1, N, L, L, p_rt, numeral(7), mk_refl(1, N, numeral(7)));   /* : Path N (add 4 3) 7 */
    { const char *why = ""; CheckStatus st = check(G0, fc_true(), w_action, mk_path_const(1, N, C, numeral(7)), &why);
      EXPECT(st == CK_VALID, "the generic action of the runtime identity is the send witness (%s)", why); }

    /* ---- 2. a pending generic prefix, a consumer already waiting, two later consumers ---- */
    DimVarId i = declare_dim();
    SymbolId pq = define_global("pending_q", varset_make(NULL, 0), dimset_make(NULL, 0), mk_path_const(1, N, numeral(3), numeral(3)));
    assert(pq && set_global_body(pq, global_ref(pq)));
    TermVarId zz = declare_term(N, fc_true());
    RefId Gq = mk_app(mk_lam_lv(1, zz, N, mk_papp_const(1, N, numeral(3), numeral(3), global_ref(pq), iv_var(i))), numeral(3));
    uint64_t di[1] = { i };
    SymbolId W0 = define_global("consumer0", varset_make(NULL, 0), dimset_make(di, 1), N), W1 = define_global("consumer1", varset_make(NULL, 0), dimset_make(di, 1), N), W2 = define_global("consumer2", varset_make(NULL, 0), dimset_make(di, 1), N);
    assert(W0 && W1 && W2 && set_global_body(W0, Gq) && set_global_body(W1, Gq) && set_global_body(W2, Gq));
    FaceId f0 = fc_lit(i, 0);
    Hold hk = { true, Gq, f0, {0}, 0 };
    eval_set_hold(hold_pred, &hk);
    WhnfStatus ws; whnf(global_ref(W0), f0, &ws);                         /* waiting before publication */
    EntryId W0e = eval_entry_lookup(global_ref(W0), f0);
    EXPECT(W0e && eval_entry_state(W0e) == E_RUNNING, "the first consumer waits on its held child before any fact exists");
    size_t inst0 = eval_cut_events().installs;
    uint64_t beta0 = reuse_count(REUSE_BETA);
    whnf(Gq, fc_true(), &ws);                                             /* the generic commits its beta prefix and stays pending */
    EXPECT(eval_entry_state(W0e) == E_READY && eval_cut_events().installs > inst0, "the consumer waiting before publication adopted the new fact at its cut");
    EvalResult *r1 = whnf(global_ref(W1), f0, &ws), *r2 = whnf(global_ref(W2), f0, &ws), *r0 = whnf(global_ref(W0), f0, &ws);
    EntryId Ge = eval_entry_lookup(Gq, fc_true());
    EXPECT(r0 && r1 && r2 && r0->ref == numeral(3) && r1->ref == numeral(3) && r2->ref == numeral(3), "three consumers answer 3");
    EXPECT(reuse_count(REUSE_BETA) - beta0 == 1 && eval_entry_state(Ge) == E_RUNNING && eval_entry_runs(Ge) == 1, "one historical beta, the generic still pending");
    RefId v = mk_papp_const(1, N, numeral(3), numeral(3), global_ref(pq), iv_var(i)); EntryId Ve = eval_entry_lookup(v, f0);
    size_t vreq = 0, vdel = 0, vpub = 0; if (Ve) eval_entry_events(Ve, &vreq, &vdel, &vpub);
    EXPECT(Ve && eval_entry_runs(Ve) == 1 && vreq == 3 && vdel == 3, "the adapted key's producer is shared: one run, three counted requests and deliveries (runs=%zu req=%zu del=%zu)", Ve ? eval_entry_runs(Ve) : 0, vreq, vdel);
    printf("item 2: generic pending=%d, consumers adopted (cut installs=%zu), adapted producer requests=%zu deliveries=%zu\n", eval_entry_state(Ge) == E_RUNNING, eval_cut_events().installs, vreq, vdel);
    RefId q_from_prefix = r1->ref;                                         /* the quantity the send uses */
    eval_set_hold(NULL, NULL);

    /* a recursive (pending) proof family for item 5: pend : Π(n:N). Path N n n, pend := pend (defined before the
     * first admission freezes the environment) */
    SymbolId pend; { TermVarId n = declare_term(N, fc_true());
      pend = define_global("pending_witness", varset_make(NULL, 0), dimset_make(NULL, 0), mk_pi_lv(1, 1, n, N, mk_path_const(1, N, ref_var(n), ref_var(n))));
      assert(pend && set_global_body(pend, global_ref(pend))); }
    /* ---- 3. send q = 3 from A to B; stop right after acceptance ---- */
    Hold hf = { false, 0, 0, { EFF_TAG_FINALIZE, EFF_TAG_EMIT, EFF_TAG_DELIVER }, 3 };
    eval_set_hold(hold_pred, &hf);
    Client c_send = {0};
    EffCommit *d_send = send(A, capA, B, nread(q_from_prefix), w_action, &c_send, next_req++);
    eval_run();
    EXPECT(eff_commit_state(d_send) == EO_ACCEPTED && c_send.delivered == 0, "send accepted; finalization and delivery not yet run");
    int np = 0, vv = valuation(&np);
    EXPECT(bal(A) == 4 && bal(B) == 2 && np == 1 && vv == 9, "after send acceptance: A=4 B=2, one open port of 3, V = a + b = 9 (A=%d B=%d ports=%d V=%d)", bal(A), bal(B), np, vv);
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    EXPECT(c_send.delivered == 1 && c_send.o.kind == EO_ACCEPTED, "the send's receipt delivered once");
    const EffOcc *E_send = c_send.o.receipt;
    EffPort *m1 = last_port_to(B);
    EXPECT(m1 && eff_port_issuer(m1) == E_send && eff_port_open(m1), "the transfer port is emitted to B's outbox");

    /* ---- 4. the same port to two clients plus a duplicate packet (one request identity), then two
     *         independent receives (distinct identities) racing on one port ---- */
    Client c1 = {0}, c2 = {0}, c3 = {0};
    uint64_t rid = 5000 + eff_occ_id(E_send);                              /* the receive request identity is the port's (B's endpoint) */
    EffPort *packets[3] = { m1, m1, m1 };                                  /* a duplicate and a retransmission; delivered out of order below */
    EffCommit *dr1 = receive(B, capB, packets[2], &c1, rid);
    EffCommit *dr2 = receive(B, capB, packets[0], &c2, rid);
    eval_run();
    EffCommit *dr3 = receive(B, capB, packets[1], &c3, rid);               /* late duplicate after acceptance */
    eval_run();
    EffEvents ev4 = eff_events();
    EXPECT(dr1 == dr2 && dr2 == dr3 && c1.delivered == 1 && c2.delivered == 1 && c3.delivered == 1, "three client deliveries of one descriptor");
    EXPECT(c1.o.kind == EO_ACCEPTED && c1.o.receipt == c2.o.receipt && c2.o.receipt == c3.o.receipt, "the same receipt for every duplicate");
    EXPECT(bal(B) == 5 && !eff_port_open(m1) && valuation(NULL) == 9, "one credit: B=5, port consumed, V=9 (B=%d)", bal(B));
    const EffOcc *E_recv = c1.o.receipt;
    printf("item 4: joins=%zu deliveries so far=%zu accepted receives of the port=1 B=%d\n", ev4.joins, ev4.deliveries, bal(B));
    { Client cs = {0}; send(A, capA, B, 1, 0, &cs, next_req++); eval_run();
      EffPort *m = last_port_to(B);
      Client x1 = {0}, x2 = {0};
      EffCommit *e1 = receive(B, capB, m, &x1, next_req++), *e2 = receive(B, capB, m, &x2, next_req++);   /* distinct identities: contention on the port cell */
      eval_run();
      bool w1 = eff_commit_state(e1) == EO_ACCEPTED, w2 = eff_commit_state(e2) == EO_ACCEPTED;
      EXPECT(e1 != e2 && w1 != w2 && (w1 ? x2.o.kind : x1.o.kind) == EO_CONFLICT && (w1 ? x2.o.holder : x1.o.holder) == (w1 ? x1.o.receipt : x2.o.receipt),
             "two independent receives of one port: exactly one commits, the other reports the consuming occurrence");
      EXPECT(valuation(NULL) == 9 && !eff_port_open(m), "one credit; V = 9");
      printf("item 4: independent receives of one port: winner=%s\n", w1 ? "first" : "second"); }

    /* ---- 5. delivery vs authorized refund of another pending port, both orders; a pending proof manufactures nothing ---- */
    int winners[2] = { 0, 0 };
    for (int order = 0; order < 2; order++) {
        Client cs = {0}; send(A, capA, B, 1, 0, &cs, next_req++); eval_run();
        EffPort *m = last_port_to(B);
        /* a refund whose witness is a pending recursive proof stays pending */
        Client cp = {0}; EffCommit *dp = refund(A, capA, m, mk_app(global_ref(pend), numeral(bal(A) + 1)), &cp, next_req++); eval_run();
        EXPECT(eff_commit_state(dp) == EO_PENDING && eff_commit_unresolved(dp) && cp.delivered == 0 && eff_port_open(m), "order %d: a refund whose proof is pending is not accepted and consumes nothing", order);
        Client cr = {0}, cf = {0};
        EffCommit *a1, *a2;
        if (order == 0) { a1 = receive(B, capB, m, &cr, next_req++); a2 = refund(A, capA, m, 0, &cf, next_req++); }
        else { a2 = refund(A, capA, m, 0, &cf, next_req++); a1 = receive(B, capB, m, &cr, next_req++); }
        eval_run();
        bool rw = eff_commit_state(a1) == EO_ACCEPTED, fw = eff_commit_state(a2) == EO_ACCEPTED;
        EXPECT(rw != fw, "order %d: exactly one of receive / refund commits (receive=%d refund=%d)", order, rw, fw);
        EXPECT((rw ? cf.o.kind : cr.o.kind) == EO_CONFLICT && (rw ? cf.o.holder : cr.o.holder) == (rw ? cr.o.receipt : cf.o.receipt), "order %d: the loser reports the conflict and the consuming occurrence", order);
        EXPECT(valuation(NULL) == 9, "order %d: V = 9", order);
        winners[order] = rw ? 1 : 2;
    }
    printf("item 5: external choices — order 0 winner=%s, order 1 winner=%s; A=%d B=%d\n", winners[0] == 1 ? "receive" : "refund", winners[1] == 1 ? "receive" : "refund", bal(A), bal(B));
    { size_t r = eff_retry(); eval_run();                                  /* a new attempt: the recursive proofs are still pending */
      size_t c0 = eff_events().commits; (void)c0;
      EXPECT(r == 2 && eff_events().unresolved >= 4, "the two pending refunds are retried and stay pending (%zu)", r);
      /* a proof unresolved within one attempt's checker budget keeps its client; the next attempt resumes it */
      check_set_budget(3);
      /* a fresh witness (refl at the unreduced sum, never audited before): its conversion needs more than 3 checker steps */
      int bb = bal(B);
      Client cu = {0}; EffCommit *du = send(B, capB, A, 1, mk_refl(1, N, add(numeral(bb - 1), numeral(1))), &cu, next_req++); eval_run();
      bool was_pending = eff_commit_state(du) == EO_PENDING && eff_commit_unresolved(du) && cu.delivered == 0;
      check_set_budget(0); eff_retry(); eval_run();
      EXPECT(was_pending && eff_commit_state(du) == EO_ACCEPTED && cu.delivered == 1, "an attempt-unresolved send stays pending with its client and is accepted on the next attempt");
      if (!(was_pending && cu.delivered == 1)) printf("  budget probe: pending=%d unresolved=%d delivered=%d state=%d\n", eff_commit_state(du) == EO_PENDING, eff_commit_unresolved(du), cu.delivered, eff_commit_state(du));
      Client cr2 = {0}; receive(A, capA, last_port_to(A), &cr2, next_req++); eval_run();
      EXPECT(cr2.o.kind == EO_ACCEPTED && valuation(NULL) == 9, "its port received; V = 9"); }

    /* ---- 7. receipt observations copied and reindexed ---- */
    { MapBuilder mb; mapb_init(&mb); mapb_dim(&mb, i, iv_zero()); MapId sig = mapb_finish(&mb);
      EffView vw, vw2; const char *why = "";
      bool ok = eff_receipt_view(E_send, sig, 0, numeral(3), B, &vw, &why);
      bool ok2 = ok && eff_view_reindex(&vw, sig, &vw2, &why);
      EXPECT(ok && ok2 && vw.occ == E_send && vw2.occ == E_send, "views of the send receipt keep its occurrence identity (%s)", why);
      const EffOcc *copy = E_send;   /* DUP: a copy of the handle is the same descriptor */
      EXPECT(copy == E_send && eff_receipt_observe(copy, EFF_FIELD_WITNESS) == w_action, "a copied receipt observes the same fields");
      bool bad1 = eff_receipt_view(E_send, sig, 0, numeral(3), A, &vw, &why);
      bool bad2 = eff_receipt_view(E_send, sig, 0, numeral(4), B, &vw, &why);
      EXPECT(!bad1 && !bad2, "a view changing the recipient or the resource is rejected");
      size_t acc0 = eff_events().commits;
      EffProposal *P = eff_proposal(SEND, 1, 0); eff_in_head(P, A, eff_head(A)); eff_out_head(P, A, numeral(bal(A) - 1)); eff_out_port(P, numeral(1), B, A); eff_witness(P, refl_n(bal(A))); eff_cap(P, capA);
      EffProposal *Q = eff_proposal_reindex(P, sig, 0);
      EXPECT(Q && eff_events().commits == acc0, "a compatible proposal recipe is constructed by reindexing; nothing is accepted");
      eff_proposal_free(Q); eff_proposal_free(P); }

    /* ---- 8. a second incompatible acceptance; equal payloads from distinct occurrences ---- */
    { size_t em0 = eff_events().emits; int b0 = bal(B);
      Client cx = {0}; receive(B, capB, m1, &cx, next_req++); eval_run();
      EXPECT(cx.o.kind == EO_CONFLICT && cx.o.holder == E_recv && bal(B) == b0 && eff_events().emits == em0, "a second receive of a consumed port conflicts with its consumer; no credit, no emission");
      Client s1 = {0}, s2 = {0};
      send(A, capA, B, 1, 0, &s1, next_req++); eval_run();
      send(A, capA, B, 1, 0, &s2, next_req++); eval_run();
      EXPECT(s1.o.kind == EO_ACCEPTED && s2.o.kind == EO_ACCEPTED && s1.o.receipt != s2.o.receipt
             && eff_port_payload(eff_occ_port(s1.o.receipt, 0)) == eff_port_payload(eff_occ_port(s2.o.receipt, 0))
             && eff_occ_port(s1.o.receipt, 0) != eff_occ_port(s2.o.receipt, 0), "equal payloads from distinct input occurrences: two legitimate effects, two port identities");
      Client k1 = {0}, k2 = {0};
      receive(B, capB, eff_occ_port(s1.o.receipt, 0), &k1, next_req++); eval_run();
      receive(B, capB, eff_occ_port(s2.o.receipt, 0), &k2, next_req++); eval_run();
      EXPECT(k1.o.kind == EO_ACCEPTED && k2.o.kind == EO_ACCEPTED && valuation(NULL) == 9, "both received; V = 9"); }

    /* ---- 6 + 9. send back to restore the initial balances, stepping one job at a time ---- */
    size_t hist0; { const EffOcc **h; hist0 = eff_history(&h); free(h); }
    int back = bal(B) - 2;
    bool all_ok = true; size_t steps = 0; int tags_seen = 0;
    Probe pr = {0};
    if (!workers) {
        eval_set_hold(probe_pred, &pr);
        Client sb = {0}; send(B, capB, A, back, 0, &sb, next_req++);
        while (eval_run_budget(1)) { steps++; int npp; if (valuation(&npp) != 9) all_ok = false; }
        EffPort *mb = last_port_to(A);
        Client rb = {0}; EffCommit *drb = receive(A, capA, mb, &rb, next_req++);
        while (eval_run_budget(1)) {
            steps++;
            /* both inputs of the receive are either former or both consumed/credited: no partially accepted state */
            bool port_consumed = !eff_port_open(mb); int a = bal(A);
            bool former = !port_consumed && a == 7 - back, after = port_consumed && a == 7;
            if (!(former || after) || valuation(NULL) != 9) all_ok = false;
            if (eff_commit_state(drb) == EO_ACCEPTED) tags_seen |= 1;
        }
        eval_set_hold(NULL, NULL);
        EXPECT(sb.o.kind == EO_ACCEPTED && rb.o.kind == EO_ACCEPTED, "send-back and its receive accepted");
        EXPECT(all_ok && tags_seen && pr.seen[EFF_TAG_PREPARE - EFF_TAG_PREPARE] && pr.seen[EFF_TAG_AUDIT - EFF_TAG_PREPARE] && pr.seen[EFF_TAG_RESERVE - EFF_TAG_PREPARE] >= 3
               && pr.seen[EFF_TAG_COMMIT - EFF_TAG_PREPARE] >= 2 && pr.seen[EFF_TAG_FINALIZE - EFF_TAG_PREPARE] >= 3 && pr.seen[EFF_TAG_EMIT - EFF_TAG_PREPARE] >= 1 && pr.seen[EFF_TAG_DELIVER - EFF_TAG_PREPARE] >= 2,
               "item 9: suspended before preparation, inside the audits, between the receive's two reservations, after each commit before its finalizations, and before each delivery: V = 9 and no partial receive at every one of %zu points", steps);
        printf("item 9: %zu one-job suspension points; jobs seen: prepare=%d audit=%d reserve=%d commit=%d finalize=%d deliver=%d emit=%d\n", steps,
               pr.seen[0], pr.seen[1], pr.seen[2], pr.seen[3], pr.seen[4], pr.seen[5], pr.seen[6]);
    } else {
        /* concurrent readers: cut valuations taken while worker threads run the jobs */
        Client sb = {0}; send(B, capB, A, back, 0, &sb, next_req++);
        size_t polls = 0; while (eff_commit_state_of_last(&sb) == EO_PENDING && polls < 1000000) { if (valuation(NULL) != 9) all_ok = false; polls++; }
        eval_run();
        Client rb = {0}; EffPort *mb = last_port_to(A); receive(A, capA, mb, &rb, next_req++);
        size_t polls2 = 0; while (rb.delivered == 0 && polls2 < 1000000) { if (valuation(NULL) != 9) all_ok = false; polls2++; }
        eval_run();
        EXPECT(sb.o.kind == EO_ACCEPTED && rb.o.kind == EO_ACCEPTED && all_ok, "item 9 (workers): %zu + %zu cut valuations taken while the send-back and its receive ran concurrently all read 9", polls, polls2);
        printf("item 9 (workers): %zu + %zu concurrent cut valuations, all 9\n", polls, polls2);
    }
    { const EffOcc **h; size_t nh = eff_history(&h); free(h);
      EXPECT(bal(A) == 7 && bal(B) == 2 && nh > hist0 && nh >= 10, "item 6: initial external balances A=7 B=2 restored; the accepted history grew to %zu occurrences", nh);
      EXPECT(eval_entry_state(Ge) == E_RUNNING && eval_entry_prefix(Ge) && eff_receipt_observe(E_send, EFF_FIELD_WITNESS) == w_action, "item 6: the computed identity and the pending prefix facts are retained");
      /* a compatible identity transport applied to the live boundary: the identity equivalence's map on A's state */
      EffCut before; eff_cut_snapshot(&before);
      RefId moved = mk_app(rt_maps_c(rt_maps_id(1, N)), eff_head_state(eff_head(A)));
      WhnfStatus st; EvalResult *mr = whnf(moved, fc_true(), &st);
      EffCut after; eff_cut_snapshot(&after);
      bool same = before.nheads == after.nheads && before.nopen == after.nopen; for (size_t k = 0; same && k < before.nheads; k++) same = before.head[k] == after.head[k];
      { const EffOcc **h2; size_t nh2 = eff_history(&h2); free(h2); same = same && nh2 == nh; }
      EXPECT(st == W_OK && mr && convert_term(G0, fc_true(), mr->ref, eff_head_state(eff_head(A)), N) == CV_EQUAL && same,
             "item 6: the identity transport of A's state is A's state; heads, open ports and history are unchanged by it");
      eff_cut_free(&before); eff_cut_free(&after); }

    /* ---- 10. readings of the same event DAG ---- */
    { const EffOcc **all; size_t n = eff_occurrences(&all);
      const EffOcc **hist; size_t nh = eff_history(&hist);
      bool core_ok = true, prem_ok = true; uint64_t sum_commit = 0, sum_res = 0, sum_fin = 0, sum_del = 0, sum_emit = 0, sum_prep = 0, sum_aud = 0; uint64_t w;
      for (size_t k = 0; k < nh; k++) {
          const char *why = "";
          if (check(G0, fc_true(), eff_receipt_observe(hist[k], EFF_FIELD_WITNESS), eff_receipt_observe(hist[k], EFF_FIELD_EDGE_TYPE), &why) != CK_VALID) core_ok = false;
          const uint64_t *as; if (eff_occ_assumptions(hist[k], &as) != 0 || eff_occ_env(hist[k]) > global_env_version()) prem_ok = false;
      }
      for (size_t k = 0; k < n; k++) {
          EffOccWork ow = eff_occ_work(all[k]);
          if (xs_u64(ow.commit, &w)) sum_commit += w;
          if (xs_u64(ow.reservations, &w)) sum_res += w;
          if (xs_u64(ow.finalizes, &w)) sum_fin += w;
          if (xs_u64(ow.deliveries, &w)) sum_del += w;
          if (xs_u64(ow.emits, &w)) sum_emit += w;
          if (xs_u64(ow.prepare_steps, &w)) sum_prep += w;
          if (xs_u64(ow.audit_units, &w)) sum_aud += w;
      }
      EffEvents ev = eff_events();
      int nopen; int V = valuation(&nopen);
      size_t open_by_history = 0; EffPort **ps; size_t npts = eff_ports(&ps);
      for (size_t k = 0; k < npts; k++) if (eff_occ_accepted(eff_port_issuer(ps[k])) && !eff_port_consumer(ps[k])) open_by_history++;
      free(ps);
      EXPECT(core_ok, "core result: every accepted witness re-checks at its edge type");
      EXPECT(V == 9 && (size_t)nopen == open_by_history, "interface/cut: V = 9; the open ports are exactly the issued, unconsumed ones (%d)", nopen);
      EXPECT(prem_ok, "premises: CORE audits (no assumptions), snapshots not after the current environment");
      EXPECT(sum_commit == ev.commits && nh == ev.commits && sum_res == ev.reservations && sum_fin == ev.finalizes && sum_emit == ev.emits,
             "exact work: per-occurrence readings sum to the global counts (commits %llu/%zu reservations %llu/%zu finalizes %llu/%zu emits %llu/%zu)",
             (unsigned long long)sum_commit, ev.commits, (unsigned long long)sum_res, ev.reservations, (unsigned long long)sum_fin, ev.finalizes, (unsigned long long)sum_emit, ev.emits);
      XSnap up, ua; eff_unattributed(&up, &ua); uint64_t upw = 0, uaw = 0; xs_u64(up, &upw); xs_u64(ua, &uaw);
      EXPECT(sum_prep + upw == ev.prepare_steps && sum_aud + uaw == ev.audit_units, "exact work: preparation steps and audit units sum over occurrences and the descriptors without one (%llu+%llu/%zu, %llu+%llu/%zu)",
             (unsigned long long)sum_prep, (unsigned long long)upw, ev.prepare_steps, (unsigned long long)sum_aud, (unsigned long long)uaw, ev.audit_units);
      EXPECT(sum_del + ev.deliveries_unattributed == ev.deliveries, "deliveries: accepted receipts attributed to their occurrence, every other outcome counted apart (%llu + %zu = %zu)", (unsigned long long)sum_del, ev.deliveries_unattributed, ev.deliveries);
      EXPECT(eff_pending_emissions() == 0, "no committed output is left unemitted");
      EXPECT(eval_entry_runs(Ge) == 1 && vreq == 3, "historical sharing: one run of the pending generic producer; three counted requests of the adapted producer");
      printf("item 10: occurrences=%zu accepted=%zu open ports=%d V=%d; events: requests=%zu joins=%zu prepares=%zu prepare_steps=%zu (attributed %llu) audits=%zu audit_units=%zu (attributed %llu) reservations=%zu waits=%zu helps=%zu commits=%zu aborts=%zu finalizes=%zu deliveries=%zu emits=%zu invalid=%zu unresolved=%zu\n",
             n, nh, nopen, V, ev.requests, ev.joins, ev.prepares, ev.prepare_steps, (unsigned long long)sum_prep, ev.audits, ev.audit_units, (unsigned long long)sum_aud, ev.reservations, ev.waits, ev.helps, ev.commits, ev.aborts, ev.finalizes, ev.deliveries, ev.emits, ev.invalid, ev.unresolved);
      printf("item 10: evaluator: generic producer runs=%zu (pending), adapted producer requests=%zu; beta events total=%llu\n", eval_entry_runs(Ge), vreq, (unsigned long long)reuse_count(REUSE_BETA));
      printf("history:");
      for (size_t k = 0; k < nh; k++) { const EffOcc *pr[4] = {0}; size_t ni = eff_occ_inputs(hist[k], pr, 4); printf(" #%llu %s(inputs from", (unsigned long long)eff_occ_id(hist[k]), eff_occ_schema(hist[k])); for (size_t j = 0; j < ni && j < 4; j++) printf(" %s", pr[j] ? "occ" : "genesis"); printf(")"); }
      printf("\n");
      free(all); free(hist); }

    /* ---- 11. the Stokes readings (CUBICAL-STOKES-ADDENDUM §11 checks 7, 8, 10) on this execution ---- */
    { /* a pending transfer on the open cut: an accepted send whose port is not received */
      EffCut cut0; eff_cut_snapshot(&cut0); ChainId B0_before = eff_cut_chain(&cut0); eff_cut_free(&cut0);
      Client cp = {0}; send(A, capA, B, 1, 0, &cp, next_req++); eval_run();
      EXPECT(cp.o.kind == EO_ACCEPTED && valuation(NULL) == 9, "a pending transfer: accepted, its port open; V = 9");
      EffCut cutN; eff_cut_snapshot(&cutN); ChainId B0_final = eff_cut_chain(&cutN);
      EffExecution ex; const char *why = NULL;
      bool replay = eff_execution(&ex, &why);
      EXPECT(replay && ex.n == eff_events().commits, "the accepted history replays from the records: %zu steps (%s)", ex.n, why ? why : "");
      ChainMapT *Bm = eff_resource_map();
      /* check 7: the map equation on every primitive event, then by composition */
      size_t admitted = 0; for (size_t k = 0; k < ex.n; k++) if (chainmap_admit(Bm, ex.steps[k], &why)) admitted++;
      CellId *st = ex.steps; ModId one = mod_int(zx_i64(1));
      ModId *ones = malloc((ex.n ? ex.n : 1) * sizeof *ones); for (size_t k = 0; k < ex.n; k++) ones[k] = one;
      ChainId H = chain_from(1, ex.n, st, ones);                                   /* the execution chain s_0 → … → s_n */
      ChainId BH = chain_map(Bm, H), dBH = chain_boundary(BH, NULL);
      ChainId B0_gen; { size_t ng = eff_genesis_resources(NULL, 0); EffRes g[8]; eff_genesis_resources(g, ng); B0_gen = eff_resources_chain(g, ng); }
      ChainId Bd = chain_map(Bm, chain_boundary(H, NULL));
      uint64_t lastns; uint64_t lasttag = cell_tag(ex.states[ex.n], &lastns);
      EXPECT(admitted == ex.n, "∂_res B_1(e) = B_0(target e) − B_0(source e) on every accepted event (%zu of %zu)", admitted, ex.n);
      EXPECT(lasttag == B0_final && dBH == chain_sub(B0_final, B0_gen) && dBH == Bd, "composition: ∂_res B(H) = B_0(final) − B_0(genesis) = B(∂H); the final replayed state is the current cut, pending transfer included");
      { EffPort *mp = eff_occ_port(cp.o.receipt, 0); EffRes rp = { 1, 0, 0, NULL };
        EffRes prs[4]; size_t npr = eff_occ_produced(cp.o.receipt, prs, 4); for (size_t k = 0; k < npr; k++) if (prs[k].kind == 1) rp = prs[k];
        EXPECT(mp && rp.kind == 1 && !mod_is_zero(chain_coef(B0_final, eff_res_cell(&rp))) && mod_is_zero(chain_coef(B0_before, eff_res_cell(&rp))), "the pending transfer's port occurrence is exposed in B_0 of the open cut and absent before its send"); }
      /* resource tables: authority and value of every occurrence named by the records */
      RInfoH *ri = calloc(4 * ex.n + 16, sizeof *ri); size_t nri = 0;
      #define NOTE(R) do { CellId c_ = eff_res_cell(&(R)); size_t q_ = 0; while (q_ < nri && ri[q_].c != c_) q_++; if (q_ == nri) { ri[nri].c = c_; ri[nri].val = nread((R).payload); ri[nri].auth = (R).kind ? NULL : (R).auth; ri[nri].kind = (R).kind; nri++; } } while (0)
      { EffRes g[8]; size_t ng = eff_genesis_resources(g, 8); for (size_t k = 0; k < ng; k++) NOTE(g[k]); }
      CellId *regA = malloc((ex.n ? ex.n : 1) * sizeof *regA), *regB = malloc((ex.n ? ex.n : 1) * sizeof *regB); size_t nA = 0, nB = 0;
      bool conserved = true;
      for (size_t k = 0; k < ex.n; k++) {
          EffRes in[8], out[8]; size_t ni = eff_occ_consumed(ex.occ[k], in, 8), no = eff_occ_produced(ex.occ[k], out, 8);
          int vin = 0, vout = 0; EffAuthority *owner = NULL;
          for (size_t r = 0; r < ni; r++) { NOTE(in[r]); vin += nread(in[r].payload); if (!in[r].kind) owner = in[r].auth; }
          for (size_t r = 0; r < no; r++) { NOTE(out[r]); vout += nread(out[r].payload); }
          if (vin != vout) conserved = false;
          if (owner == A) regA[nA++] = eff_event_cell(ex.occ[k]); else regB[nB++] = eff_event_cell(ex.occ[k]);
      }
      /* the valuation 0-cochain v (each occurrence's resource) and its differential on events */
      VCtxH vc = { ri, nri };
      Cochain *v = cochain_gen(0, 1, vval_act, &vc);
      ModId dvH = chain_pair(cochain_cob(v, NULL), BH), vdH = chain_pair(v, dBH);
      ModId vfinal = chain_pair(v, B0_final), vgen = chain_pair(v, B0_gen);
      Zx zf, zg; mod_scalar(vfinal, &zf); mod_scalar(vgen, &zg);
      EXPECT(conserved && mod_is_zero(dvH) && dvH == vdH && zx_eq(zf, zx_i64(9)) && zx_eq(zg, zx_i64(9)), "dv vanishes on every accepted event; ⟨v,∂B(H)⟩ = ⟨dv,B(H)⟩ = 0; ⟨v,B_0⟩ = 9 at genesis and at the open cut");
      /* check 10: the returning cycle keeps its fibre; duplicate and conflicting consumes */
      bool unit_coefs = true; for (size_t k = 0; k < chain_nterms(dBH); k++) { CellId c; ModId m; chain_term(dBH, k, &c, &m); Zx z; mod_scalar(m, &z); if (!(zx_eq(z, zx_i64(1)) || zx_eq(z, zx_i64(-1)))) unit_coefs = false; }
      EXPECT(!chain_is_zero(BH) && chain_nterms(BH) == ex.n && unit_coefs, "returning cycle: the balances return (V reading 0) while B(H) keeps its %zu events; every exposed occurrence enters ∂ with coefficient ±1 — the duplicate receive is one event, a conflicting consume none", ex.n);
      EXPECT(!mod_is_zero(chain_coef(BH, eff_event_cell(E_send))) && !mod_is_zero(chain_coef(BH, eff_event_cell(E_recv))), "the accepted send and the (duplicated) receive are events of B(H) with coefficient 1");
      /* relative cuts: A's region, its interface the port occurrences and A's boundary heads */
      ModId *oa = malloc((nA ? nA : 1) * sizeof *oa), *ob = malloc((nB ? nB : 1) * sizeof *ob); for (size_t k = 0; k < nA; k++) oa[k] = one; for (size_t k = 0; k < nB; k++) ob[k] = one;
      ChainId RA = chain_from(1, nA, regA, oa), RB = chain_from(1, nB, regB, ob);
      ICtxH ia = { ri, nri, A }, ib = { ri, nri, B };
      RelativeView rva = relative_view(RA, iface_in, &ia), rvb = relative_view(RB, iface_in, &ib);
      ModId fluxA = chain_pair(v, rva.absolute_boundary), fluxB = chain_pair(v, rvb.absolute_boundary);
      EXPECT(chain_is_zero(rva.relative_boundary) && chain_is_zero(rvb.relative_boundary) && !chain_is_zero(rva.absolute_boundary), "each authority's region is a relative cycle over its interface, its absolute boundary retained");
      EXPECT(chain_add(RA, RB) == BH && chain_add(rva.absolute_boundary, rvb.absolute_boundary) == dBH && mod_add(fluxA, fluxB) == mod_zero(), "gluing: R_A + R_B = B(H); internal ports cancel in ∂R_A + ∂R_B = ∂B(H); the fluxes read off the two regions sum to zero");
      Cochain *vA = cochain_gen(0, 1, vheads_act, &ia), *vP = cochain_gen(0, 1, vports_act, &ia);
      Zx hA, pA; mod_scalar(chain_pair(vA, rva.absolute_boundary), &hA); mod_scalar(chain_pair(vP, rva.absolute_boundary), &pA);
      EXPECT(zx_eq(hA, zx_i64(bal(A) - 7)) && zx_eq(pA, zx_neg(hA)), "the partial valuation of A's holdings reads A's change %d, and it is minus the port flux crossing A's region boundary", bal(A) - 7);
      { char fa[64], fb[64]; mod_print(mod_int(hA), fa, sizeof fa); mod_print(mod_int(pA), fb, sizeof fb);
        printf("item 11: A's holdings change %s, port flux across A's region boundary %s\n", fa, fb);
        mod_print(fluxA, fa, sizeof fa); mod_print(fluxB, fb, sizeof fb);
        printf("item 11: %zu accepted events replayed; map equation on every event; ∂B(H) = B_0(open cut) − B_0(genesis) with the pending transfer exposed; regions A (%zu events, flux %s) and B (%zu events, flux %s)\n", ex.n, nA, fa, nB, fb); }
      /* check 8: an exact common trace counted once; the shared producer once, its deliveries apart */
      size_t c1 = ex.n > 6 ? 6 : ex.n, c0 = c1 / 2;
      ChainId Hp = chain_from(1, c1, st, ones), Hq = chain_add(chain_from(1, c0, st, ones), chain_from(1, ex.n - c1, st + c1, ones)), J = chain_from(1, c0, st, ones);
      ChainId U = chain_glue(Hp, Hq, J, &why), bad = chain_glue(Hp, Hq, chain_from(1, 1, st + c1 - 1, ones), &why);
      EXPECT(U == H && !bad, "[H_1 ∪_J H_2] = H_1 + H_2 − J over the actual common prefix gives H with every step once; a non-common interface is refused");
      CellId Pc = cell_declared(0x4F4343, ((uint64_t)Ve << 8) | 0x01, 0, chain_zero(0), NULL), Dc[3], Rq[3];
      for (int k = 0; k < 3; k++) { Dc[k] = cell_declared(0x4F4343, ((uint64_t)Ve << 8) | (0x10 + (uint64_t)k), 0, chain_zero(0), NULL); Rq[k] = cell_declared(0x4F4343, ((uint64_t)Ve << 8) | (0x20 + (uint64_t)k), 0, chain_zero(0), NULL); }
      ChainId h1 = chain_add(chain_genz(Pc, 1), chain_add(chain_genz(Rq[0], 1), chain_genz(Dc[0], 1))), h2 = chain_add(chain_genz(Pc, 1), chain_add(chain_genz(Rq[1], 1), chain_genz(Dc[1], 1)));
      ChainId u12 = chain_glue(h1, h2, chain_genz(Pc, 1), &why);
      EXPECT(u12 && chain_coef(u12, Pc) == one && chain_nterms(u12) == 5 && eval_entry_runs(Ve) == 1 && vreq == 3 && vdel == 3, "two consumer histories sharing the adapted producer's one run count it once; their requests and deliveries stay distinct (5 generators)");
      ChainId dels = chain_add(chain_genz(Dc[0], 1), chain_add(chain_genz(Dc[1], 1), chain_genz(Dc[2], 1)));
      CellId key = cell_declared(0x4B4559, (uint64_t)Ve, 0, chain_zero(0), NULL);
      ChainId push = chain_pushforward(dels, to_key, &key); CellId *img; size_t nimg = chain_support_image(dels, to_key, &key, &img);
      Zx pk; mod_scalar(chain_coef(push, key), &pk);
      EXPECT(zx_eq(pk, zx_i64(3)) && nimg == 1 && img[0] == key && chain_nterms(dels) == 3, "specialized to the producer key: the additive image counts 3 deliveries, the Boolean support image is the one key, the past occurrences stay 3");
      free(img);
      /* check 10: the runtime identity leaves the cut reading unchanged */
      EffCut c1s; eff_cut_snapshot(&c1s); ChainId b1 = eff_cut_chain(&c1s); eff_cut_free(&c1s);
      { WhnfStatus ws; whnf(mk_app(rt_maps_c(rt_maps_id(1, N)), eff_head_state(eff_head(A))), fc_true(), &ws); }
      EffCut c2s; eff_cut_snapshot(&c2s); ChainId b2 = eff_cut_chain(&c2s); eff_cut_free(&c2s);
      EXPECT(b1 == b2 && b1 == B0_final, "the identity transport changes no resource occurrence: B_0 before = after");
      EXPECT(eval_entry_state(Ge) == E_RUNNING && eval_entry_runs(Ge) == 1, "the pending shared prefix stays an owned suspended producer on the open cut (not an event, not erased)");
      /* realization: a step published with its operational boundary; an invented event is refused */
      Realization rz; const char *w2 = NULL;
      bool pub = publish_realization(ex.steps[0], Bm, chain_boundary(chain_map(Bm, chain_genz(ex.steps[0], 1)), NULL), event_occurred, NULL, &rz, &w2);
      EXPECT(pub && rz.nlinks == 1, "PUBLISH_REALIZATION links the first step to its accepted event and its exact operational boundary (%s)", w2 ? w2 : "");
      printf("item 11: common trace glued once; shared producer once with %zu requests / %zu deliveries apart; specialization: additive 3, support 1; identity transport leaves B_0 unchanged\n", vreq, vdel);
      free(ones); free(oa); free(ob); free(regA); free(regB); free(ri); eff_execution_free(&ex); eff_cut_free(&cutN); }

    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    work_free(); compiler_free(); check_free(); eval_free(); effect_free(); chain_free(); machine_free();
    printf("test_effect_witness workers=%zu: %d failures\n", workers, fails);
    return fails ? 1 : 0;
}
