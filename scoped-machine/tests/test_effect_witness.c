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
static EffSchema *SEND, *RECV, *REFUND;
static ContextId G0;
static uint64_t next_req = 100;
/* V(F): balances of the account heads on the current cut + quantities of the unconsumed transfer ports */
static int valuation(int *open_ports) {
    int v = 0, np = 0;
    EffAuthority **as; size_t na = eff_authorities(&as);
    for (size_t i = 0; i < na; i++) v += nread(eff_head_state(eff_head(as[i])));
    free(as);
    EffPort **ps; size_t n = eff_ports(&ps);
    for (size_t i = 0; i < n; i++) if (eff_port_open(ps[i])) { v += nread(eff_port_payload(ps[i])); np++; }
    free(ps);
    if (open_ports) *open_ports = np;
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

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    size_t workers = argc > 1 ? (size_t)strtoull(argv[1], NULL, 10) : 0;
    machine_init(); eval_init(); check_init(); compiler_init(); work_init(); effect_init();
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
    uint64_t beta0 = reuse_count(REUSE_BETA);
    whnf(Gq, fc_true(), &ws);                                             /* the generic commits its beta prefix and stays pending */
    EvalResult *r1 = whnf(global_ref(W1), f0, &ws), *r2 = whnf(global_ref(W2), f0, &ws), *r0 = whnf(global_ref(W0), f0, &ws);
    EntryId Ge = eval_entry_lookup(Gq, fc_true());
    EXPECT(r0 && r1 && r2 && r0->ref == numeral(3) && r1->ref == numeral(3) && r2->ref == numeral(3), "three consumers answer 3");
    EXPECT(reuse_count(REUSE_BETA) - beta0 == 1 && eval_entry_state(Ge) == E_RUNNING && eval_entry_runs(Ge) == 1, "one historical beta, the generic still pending");
    RefId v = mk_papp_const(1, N, numeral(3), numeral(3), global_ref(pq), iv_var(i)); EntryId Ve = eval_entry_lookup(v, f0);
    size_t vreq = 0, vdel = 0, vpub = 0; if (Ve) eval_entry_events(Ve, &vreq, &vdel, &vpub);
    EXPECT(Ve && eval_entry_runs(Ve) == 1 && vreq >= 3 && vdel >= 3, "the adapted key's producer is shared, its requests and deliveries distinct (runs=%zu req=%zu del=%zu)", Ve ? eval_entry_runs(Ve) : 0, vreq, vdel);
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

    /* ---- 4. the same port to two clients plus a duplicate, reordered packet ---- */
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

    /* ---- 5. delivery vs authorized refund of another pending port, both orders; a pending proof manufactures nothing ---- */
    int winners[2] = { 0, 0 };
    for (int order = 0; order < 2; order++) {
        Client cs = {0}; send(A, capA, B, 1, NULL, &cs, next_req++); eval_run();
        EffPort *m = last_port_to(B);
        /* a refund whose witness is a pending recursive proof stays pending */
        Client cp = {0}; EffCommit *dp = refund(A, capA, m, mk_app(global_ref(pend), numeral(bal(A) + 1)), &cp, next_req++); eval_run();
        EXPECT(eff_commit_state(dp) == EO_PENDING && eff_commit_unresolved(dp) && cp.delivered == 0 && eff_port_open(m), "order %d: a refund whose proof is pending is not accepted and consumes nothing", order);
        Client cr = {0}, cf = {0};
        EffCommit *a1, *a2;
        if (order == 0) { a1 = receive(B, capB, m, &cr, next_req++); a2 = refund(A, capA, m, NULL, &cf, next_req++); }
        else { a2 = refund(A, capA, m, NULL, &cf, next_req++); a1 = receive(B, capB, m, &cr, next_req++); }
        eval_run();
        bool rw = eff_commit_state(a1) == EO_ACCEPTED, fw = eff_commit_state(a2) == EO_ACCEPTED;
        EXPECT(rw != fw, "order %d: exactly one of receive / refund commits (receive=%d refund=%d)", order, rw, fw);
        EXPECT((rw ? cf.o.kind : cr.o.kind) == EO_CONFLICT && (rw ? cf.o.holder : cr.o.holder) == (rw ? cr.o.receipt : cf.o.receipt), "order %d: the loser reports the conflict and the consuming occurrence", order);
        EXPECT(valuation(NULL) == 9, "order %d: V = 9", order);
        winners[order] = rw ? 1 : 2;
    }
    printf("item 5: external choices — order 0 winner=%s, order 1 winner=%s; A=%d B=%d\n", winners[0] == 1 ? "receive" : "refund", winners[1] == 1 ? "receive" : "refund", bal(A), bal(B));

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
      send(A, capA, B, 1, NULL, &s1, next_req++); eval_run();
      send(A, capA, B, 1, NULL, &s2, next_req++); eval_run();
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
    if (!workers) {
        Client sb = {0}; send(B, capB, A, back, NULL, &sb, next_req++);
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
        EXPECT(sb.o.kind == EO_ACCEPTED && rb.o.kind == EO_ACCEPTED, "send-back and its receive accepted");
    } else {
        Client sb = {0}; send(B, capB, A, back, NULL, &sb, next_req++); eval_run();
        Client rb = {0}; receive(A, capA, last_port_to(A), &rb, next_req++); eval_run();
        EXPECT(sb.o.kind == EO_ACCEPTED && rb.o.kind == EO_ACCEPTED, "send-back and its receive accepted");
    }
    EXPECT(all_ok, "item 9: at every one-job suspension point V = 9 and no partially accepted receive (%zu steps)", steps);
    { const EffOcc **h; size_t nh = eff_history(&h); free(h);
      EXPECT(bal(A) == 7 && bal(B) == 2 && nh > hist0 && nh >= 10, "item 6: initial external balances A=7 B=2 restored; the accepted history grew to %zu occurrences", nh);
      EXPECT(eval_entry_state(Ge) == E_RUNNING && eval_entry_prefix(Ge) && eff_receipt_observe(E_send, EFF_FIELD_WITNESS) == w_action, "item 6: the computed identity and the pending prefix facts are retained"); }

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
          if (xs_u64(ow.commit, &w)) sum_commit += w; if (xs_u64(ow.reservations, &w)) sum_res += w; if (xs_u64(ow.finalizes, &w)) sum_fin += w;
          if (xs_u64(ow.deliveries, &w)) sum_del += w; if (xs_u64(ow.emits, &w)) sum_emit += w; if (xs_u64(ow.prepare_steps, &w)) sum_prep += w; if (xs_u64(ow.audit_units, &w)) sum_aud += w;
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
      EXPECT(sum_del <= ev.deliveries, "deliveries: accepted-receipt deliveries are attributed to their occurrence (%llu of %zu; the rest are conflict outcomes)", (unsigned long long)sum_del, ev.deliveries);
      printf("item 10: occurrences=%zu accepted=%zu open ports=%d V=%d; events: requests=%zu joins=%zu prepares=%zu prepare_steps=%zu (attributed %llu) audits=%zu audit_units=%zu (attributed %llu) reservations=%zu waits=%zu helps=%zu commits=%zu aborts=%zu finalizes=%zu deliveries=%zu emits=%zu invalid=%zu unresolved=%zu\n",
             n, nh, nopen, V, ev.requests, ev.joins, ev.prepares, ev.prepare_steps, (unsigned long long)sum_prep, ev.audits, ev.audit_units, (unsigned long long)sum_aud, ev.reservations, ev.waits, ev.helps, ev.commits, ev.aborts, ev.finalizes, ev.deliveries, ev.emits, ev.invalid, ev.unresolved);
      printf("item 10: evaluator: generic producer runs=%zu (pending), adapted producer requests=%zu; beta events total=%llu\n", eval_entry_runs(Ge), vreq, (unsigned long long)reuse_count(REUSE_BETA));
      printf("history:");
      for (size_t k = 0; k < nh; k++) { const EffOcc *pr[4] = {0}; size_t ni = eff_occ_inputs(hist[k], pr, 4); printf(" #%llu %s(inputs from", (unsigned long long)eff_occ_id(hist[k]), eff_occ_schema(hist[k])); for (size_t j = 0; j < ni && j < 4; j++) printf(" %s", pr[j] ? "occ" : "genesis"); printf(")"); }
      printf("\n");
      free(all); free(hist); }

    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    work_free(); compiler_free(); check_free(); eval_free(); effect_free(); machine_free();
    printf("test_effect_witness workers=%zu: %d failures\n", workers, fails);
    return fails ? 1 : 0;
}
