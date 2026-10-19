/* test_effect.c — the EFFECT-AUTHORITY §10 witness: one in-process network
 * with two agents (threads) and the generic authority/port records over a
 * cash schema in core terms (Church naturals; send, receive and refund edge
 * types are Σ/Path types over add, checked by the kernel). Every assertion
 * reads the one retained execution: its cells, receipts, resource chains
 * and work readings. */
#define _POSIX_C_SOURCE 200809L
#include "../src/effect.h"
#include "../src/chain.h"
#include "../src/check.h"
#include "../src/lib.h"
#include "reading.h"
#include <pthread.h>

static int np, nf;
#define CHECK(c, ...) do { if (c) np++; else { nf++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

/* ---- the cash schema ---- */
static RefId U0, U1, N, ADD;
static RefId fun(RefId X, RefId Y, uint64_t l) { return mk_fun(l, l, X, Y); }
static RefId num(uint64_t k) {
    TermVarId vX = declare_term(U0, fc_true()); RefId X = ref_var(vX);
    TermVarId vf = declare_term(fun(X, X, 0), fc_true()); RefId f = ref_var(vf);
    TermVarId vx = declare_term(X, fc_true()); RefId t = ref_var(vx);
    for (uint64_t i = 0; i < k; i++) t = mk_app(f, t);
    return mk_lam_lv(1, vX, U0, mk_lam_lv(0, vf, fun(X, X, 0), mk_lam_lv(0, vx, X, t)));
}
static void cash_types(void) {
    U0 = mk_universe(0); U1 = mk_universe(1);
    TermVarId vX = declare_term(U0, fc_true()); RefId X = ref_var(vX);
    N = mk_pi_lv(1, 0, vX, U0, fun(fun(X, X, 0), fun(X, X, 0), 0));
    TermVarId vm = declare_term(N, fc_true()), vn = declare_term(N, fc_true());
    TermVarId vY = declare_term(U0, fc_true()); RefId Y = ref_var(vY);
    TermVarId vf = declare_term(fun(Y, Y, 0), fc_true()); RefId f = ref_var(vf);
    TermVarId vy = declare_term(Y, fc_true()); RefId y = ref_var(vy);
    RefId body = mk_app(mk_app(mk_app(ref_var(vm), Y), f), mk_app(mk_app(mk_app(ref_var(vn), Y), f), y));
    ADD = mk_lam_lv(1, vm, N, mk_lam_lv(1, vn, N, mk_lam_lv(1, vY, U0, mk_lam_lv(0, vf, fun(Y, Y, 0), mk_lam_lv(0, vy, Y, body)))));
}
static RefId add(RefId a, RefId b) { return mk_app(mk_app(ADD, a), b); }
static RefId path(RefId a, RefId b) { return mk_path_const(1, N, a, b); }
/* R_send a a' q = Σ(r:N). Path (add r q) a × Path a' r;  R_recv q b b' = Path b' (add b q);  R_refund q a a' = Path a' (add a q) */
static RefId R_send, R_recv, R_refund;
static RefId send_sigma(RefId a, RefId a2, RefId q, TermVarId *vr) {
    *vr = declare_term(N, fc_true()); RefId r = ref_var(*vr);
    TermVarId vu = declare_term(path(add(r, q), a), fc_true());
    return mk_sigma_lv(1, 1, *vr, N, mk_sigma_lv(1, 1, vu, path(add(r, q), a), path(a2, r)));
}
static void cash_edges(void) {
    TermVarId va = declare_term(N, fc_true()), va2 = declare_term(N, fc_true()), vq = declare_term(N, fc_true()), vr;
    R_send = mk_lam_lv(1, va, N, mk_lam_lv(1, va2, N, mk_lam_lv(1, vq, N, send_sigma(ref_var(va), ref_var(va2), ref_var(vq), &vr))));
    TermVarId wq = declare_term(N, fc_true()), wb = declare_term(N, fc_true()), wb2 = declare_term(N, fc_true());
    R_recv = mk_lam_lv(1, wq, N, mk_lam_lv(1, wb, N, mk_lam_lv(1, wb2, N, path(ref_var(wb2), add(ref_var(wb), ref_var(wq))))));
    TermVarId xq = declare_term(N, fc_true()), xa = declare_term(N, fc_true()), xa2 = declare_term(N, fc_true());
    R_refund = mk_lam_lv(1, xq, N, mk_lam_lv(1, xa, N, mk_lam_lv(1, xa2, N, path(ref_var(xa2), add(ref_var(xa), ref_var(xq))))));
}
/* the send witness (r, p_add, p_rest) with p_add : Path (add r q) a */
static RefId send_witness(RefId a, RefId a2, RefId q, RefId r, RefId p_add) {
    TermVarId vr; RefId S = send_sigma(a, a2, q, &vr);
    RefId inner = apply_term_binder(S, 0, 1, r);
    return mk_pair_at_lv(1, S, r, mk_pair_at_lv(1, inner, p_add, mk_refl(1, N, a2)));
}

static uint64_t SEND, RECV, REFUND;
/* values of the numerals built before a suspended run: reading them must not drive the scheduler */
static RefId NUMS[16];
static bool known(RefId n, uint64_t *v) { for (uint64_t k = 0; k < 16; k++) if (NUMS[k] == n) { *v = k; return true; } return false; }
static uint64_t cut_known(uint64_t A, uint64_t B) {
    uint64_t a = 0, b = 0, v = 0, ports[64]; known(head_state(effect_head(A)), &a); known(head_state(effect_head(B)), &b);
    size_t n = effect_open_ports(ports, 64); v = a + b;
    for (size_t i = 0; i < n; i++) { uint64_t q; if (known(port_payload(ports[i]), &q)) v += q; }
    return v;
}
static uint64_t bal(uint64_t auth) { uint64_t v = 0; if (!church_value(head_state(effect_head(auth)), &v)) return UINT64_MAX; return v; }
static uint64_t cut_value(void) {             /* V(F): balances on the cut plus pending port quantities */
    extern uint64_t A_, B_;
    uint64_t v = bal(A_) + bal(B_), ports[64]; size_t n = effect_open_ports(ports, 64);
    for (size_t i = 0; i < n; i++) { uint64_t q; if (church_value(port_payload(ports[i]), &q)) v += q; }
    return v;
}
uint64_t A_, B_;
static uint64_t capA, capB, C_, C0;

static uint64_t send(uint64_t rid, uint64_t from, uint64_t to, uint64_t cap, uint64_t a, uint64_t q, RefId p_add, WhnfStatus *st) {
    uint64_t h = effect_head(from);
    EffOut outs[2] = { { 0, from, num(a - q) }, { 1, to, num(q) } };
    RefId w = send_witness(num(a), num(a - q), num(q), num(a - q), p_add ? p_add : mk_refl(1, N, num(a)));
    uint64_t P = effect_proposal(SEND, 1, &h, 2, outs, w, 1, &cap);
    return effect_request(rid, P, st);
}
static uint64_t recv_proposal(uint64_t port, uint64_t to, uint64_t cap, uint64_t b, uint64_t q) {
    uint64_t ins[2] = { port, effect_head(to) };
    EffOut outs[1] = { { 0, to, num(b + q) } };
    return effect_proposal(RECV, 2, ins, 1, outs, mk_refl(1, N, num(b + q)), 1, &cap);
}
static uint64_t refund_proposal(uint64_t port, uint64_t from, uint64_t cap, uint64_t a, uint64_t q) {
    uint64_t ins[2] = { port, effect_head(from) };
    EffOut outs[1] = { { 0, from, num(a + q) } };
    return effect_proposal(REFUND, 2, ins, 1, outs, mk_refl(1, N, num(a + q)), 1, &cap);
}

/* agents: concurrent clients of effect requests */
typedef struct { uint64_t rid, P, out; pthread_barrier_t *gate; } Client;
static void ignore(void *ctx, EvalResult *r) { (void)ctx; (void)r; }
static void *client(void *p) { Client *c = p; WhnfStatus st; pthread_barrier_wait(c->gate); c->out = effect_request(c->rid, c->P, &st); return NULL; }

int main(void) {
    setvbuf(stdout, NULL, _IONBF, 0);
    printf("== witnessed effects: the EFFECT-AUTHORITY §10 witness\n");
    machine_init(); eval_init(); check_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    cash_types(); cash_edges();
    for (uint64_t k = 0; k < 16; k++) NUMS[k] = num(k);
    SEND = effect_schema(N, 1, R_send); RECV = effect_schema(N, 1, R_recv); REFUND = effect_schema(N, 1, R_refund);
    A_ = effect_authority(SEND, num(5), 1, &capA); B_ = effect_authority(SEND, num(3), 2, &capB);
    uint64_t A0 = effect_head(A_), B0 = effect_head(B_);
    WhnfStatus st;
    printf("  schema: S = Church N : U1; R_send a a' q = Σ(r:N). Path (add r q) a × Path a' r; R_recv q b b' = Path b' (add b q); R_refund q a a' = Path a' (add a q)\n");
    printf("  genesis: A = 5, B = 3; owner capabilities issued at genesis; admitted assumptions: none (closed core witnesses)\n");
    CHECK(cut_value() == 8, "the initial cut holds a + b = 8");

    /* 1. identity evidence computed at runtime: p = (λn. refl n)(add 3 2), evaluated */
    TermVarId vn = declare_term(N, fc_true());
    RefId lemma = mk_lam_lv(1, vn, N, mk_refl(1, N, ref_var(vn)));
    EvalResult *ev = whnf(mk_app(lemma, add(num(3), num(2))), fc_true(), &st);
    CHECK(st == W_OK && ev->cls == R_INTRODUCTION, "the runtime computation yields identity evidence");
    RefId p_add = ev->ref;

    /* 3. send 2 from A to B, stopped right after acceptance */
    uint64_t o1 = send(1001, A_, B_, capA, 5, 2, p_add, &st);
    CHECK(outcome_kind(o1) == OUT_ACCEPTED, "the send is accepted with the runtime evidence (%s)", outcome_reason(o1));
    uint64_t E1 = outcome_occurrence(o1), m = effect_port(E1, 1);
    CHECK(bal(A_) == 3 && bal(B_) == 3, "after the send: A = a − q = 3, B = b = 3");
    uint64_t ports[8]; size_t nport = effect_open_ports(ports, 8);
    CHECK(nport == 1 && ports[0] == m && port_status(m, NULL) == 1, "one open transfer port");
    { uint64_t q; CHECK(church_value(port_payload(m), &q) && q == 2, "of quantity q = 2"); }
    CHECK(cut_value() == 8, "the cut still holds a + b = 8 with the port pending");

    /* 4. the same port delivered to two concurrent clients plus a duplicate packet */
    uint64_t Pr = recv_proposal(m, B_, capB, 3, 2);
    pthread_barrier_t gate; pthread_barrier_init(&gate, NULL, 2);
    Client c1 = { 2001, Pr, 0, &gate }, c2 = { 2001, Pr, 0, &gate };
    pthread_t t1, t2; pthread_create(&t1, NULL, client, &c1); pthread_create(&t2, NULL, client, &c2);
    pthread_join(t1, NULL); pthread_join(t2, NULL); pthread_barrier_destroy(&gate);
    uint64_t dup = effect_request(2001, Pr, &st);                              /* a retransmitted packet */
    CHECK(outcome_kind(c1.out) == OUT_ACCEPTED && c1.out == c2.out && c2.out == dup, "one accepted receive, one receipt for all three requests");
    EntryId er = eval_entry_find(effect_family(), 2001, Pr);
    CHECK(er && eval_entry_runs(er) == 1, "one producer for the receive: the three deliveries are distinct, the event is one");
    CHECK(bal(B_) == 5 && port_status(m, NULL) == 2, "one credit: B = 5 and the port consumed");
    CHECK(cut_value() == 8, "the cut holds 8");

    /* 6. B sends 2 back to A, A receives: initial balances, a different history */
    uint64_t o3 = send(1002, B_, A_, capB, 5, 2, 0, &st);
    uint64_t m3 = effect_port(outcome_occurrence(o3), 1);
    uint64_t o4 = effect_request(2002, recv_proposal(m3, A_, capA, 3, 2), &st);
    CHECK(outcome_kind(o3) == OUT_ACCEPTED && outcome_kind(o4) == OUT_ACCEPTED, "the return send and receive are accepted");
    CHECK(bal(A_) == 5 && bal(B_) == 3, "the external balances are the initial ones");
    CHECK(effect_head(A_) != A0 && effect_head(B_) != B0 && head_occurrence(effect_head(A_)) == outcome_occurrence(o4), "the heads are new occurrences: the accepted history changed");
    CHECK(receipt_accepted(E1) && whnf(mk_app(lemma, add(num(3), num(2))), fc_true(), &st) == ev, "the first receipt stays accepted and the computed identity is the same retained fact");

    /* 8. a second incompatible acceptance from a consumed port, and equal payloads */
    uint64_t again = effect_request(2003, recv_proposal(m, B_, capB, 3, 2), &st);
    CHECK(outcome_kind(again) == OUT_CONFLICT, "a second receive of a consumed port is a conflict");
    nport = effect_open_ports(ports, 8);
    CHECK(nport == 0 && cut_value() == 8, "and emits nothing");
    uint64_t rc = effect_request(1001, recv_proposal(m3, A_, capA, 3, 2), &st);
    CHECK(outcome_kind(rc) == OUT_REQUEST_CONFLICT, "a request id reused for another proposal is a request conflict");

    /* 5. a receive races an authorized refund of the same pending port; then reversed */
    for (int rev = 0; rev < 2; rev++) {
        uint64_t a = bal(A_), b = bal(B_);
        uint64_t os = send(1100 + rev, A_, B_, capA, a, 1, 0, &st);
        uint64_t mp = effect_port(outcome_occurrence(os), 1);
        CHECK(outcome_kind(os) == OUT_ACCEPTED && bal(A_) == a - 1, "a pending port of quantity 1 (round %d)", rev);
        uint64_t Prv = recv_proposal(mp, B_, capB, b, 1), Prf = refund_proposal(mp, A_, capA, a - 1, 1);
        pthread_barrier_init(&gate, NULL, 2);
        Client x = { rev ? 3112 : 3101, rev ? Prf : Prv, 0, &gate }, y = { rev ? 3111 : 3102, rev ? Prv : Prf, 0, &gate };
        pthread_create(&t1, NULL, client, &x); pthread_create(&t2, NULL, client, &y);
        pthread_join(t1, NULL); pthread_join(t2, NULL); pthread_barrier_destroy(&gate);
        int acc = (outcome_kind(x.out) == OUT_ACCEPTED) + (outcome_kind(y.out) == OUT_ACCEPTED);
        int con = (outcome_kind(x.out) == OUT_CONFLICT) + (outcome_kind(y.out) == OUT_CONFLICT);
        CHECK(acc == 1 && con == 1, "precisely one of the two consumes commits (round %d)", rev);
        printf("  race round %d (%s requested first): %s committed\n", rev, rev ? "refund" : "receive",
               outcome_kind((rev ? y : x).out) == OUT_ACCEPTED ? "the receive" : "the refund");
        CHECK(port_status(mp, NULL) == 2 && cut_value() == 8 && bal(A_) + bal(B_) == 8, "the port is consumed once and the cut holds 8 (round %d)", rev);
        if (!rev) { uint64_t r2 = bal(A_), s2 = bal(B_); (void)r2; (void)s2; }
    }
    /* equal pure payloads with distinct valid inputs are distinct legitimate effects */
    {   uint64_t a = bal(A_);
        uint64_t s1 = send(1200, A_, B_, capA, a, 1, 0, &st), s2 = send(1201, A_, B_, capA, a - 1, 1, 0, &st);
        CHECK(outcome_kind(s1) == OUT_ACCEPTED && outcome_kind(s2) == OUT_ACCEPTED && outcome_occurrence(s1) != outcome_occurrence(s2), "two sends of one quantity are two occurrences");
        uint64_t p1 = effect_port(outcome_occurrence(s1), 1), p2 = effect_port(outcome_occurrence(s2), 1);
        CHECK(p1 != p2 && port_payload(p1) == port_payload(p2), "two ports with the same payload");
        uint64_t b = bal(B_);
        effect_request(1300, recv_proposal(p1, B_, capB, b, 1), &st);
        effect_request(1301, recv_proposal(p2, B_, capB, b + 1, 1), &st);
        CHECK(bal(B_) == b + 2 && cut_value() == 8, "both are received, the cut holds 8"); }

    /* authorization: a fabricated capability is no authorization */
    {   uint64_t fake = effect_capability_unissued(A_, 1), h = effect_head(A_);
        uint64_t a = bal(A_);
        EffOut outs[2] = { { 0, A_, num(a - 1) }, { 1, B_, num(1) } };
        uint64_t P = effect_proposal(SEND, 1, &h, 2, outs, send_witness(num(a), num(a - 1), num(1), num(a - 1), mk_refl(1, N, num(a))), 1, &fake);
        uint64_t o = effect_request(1400, P, &st);
        CHECK(outcome_kind(o) == OUT_INVALID && effect_head(A_) == h, "an unissued capability: invalid, the head unchanged (%s)", outcome_reason(o)); }
    /* a witness that does not check is not admitted */
    {   uint64_t h = effect_head(A_); uint64_t a = bal(A_);
        EffOut outs[2] = { { 0, A_, num(a - 1) }, { 1, B_, num(2) } };       /* takes 1, sends 2 */
        uint64_t P = effect_proposal(SEND, 1, &h, 2, outs, send_witness(num(a), num(a - 1), num(2), num(a - 1), mk_refl(1, N, num(a))), 1, &capA);
        uint64_t o = effect_request(1401, P, &st);
        CHECK(outcome_kind(o) == OUT_INVALID && effect_head(A_) == h && cut_value() == 8, "a send creating money does not check (%s)", outcome_reason(o)); }

    /* 9. suspension: a send driven one step at a time; every intermediate cut holds 8
     *    and no partially accepted multi-cell state is observed */
    {   uint64_t a = bal(A_), b0 = bal(B_), h = effect_head(A_);
        uint64_t P = effect_proposal(SEND, 1, &h, 2, (EffOut[2]){ { 0, A_, num(a - 1) }, { 1, B_, num(1) } },
                                     send_witness(num(a), num(a - 1), num(1), num(a - 1), mk_refl(1, N, num(a))), 1, &capA);
        size_t steps = 0; bool ok = true; uint64_t out = 0;
        for (;;) {
            out = family_run_budget(effect_family(), 1500, P, 1, &st);
            uint64_t ha = effect_head(A_), va = 99, vb = 99;
            known(head_state(ha), &va); known(head_state(effect_head(B_)), &vb);
            bool before = ha == h && va == a, after = ha != h && va == a - 1;
            ok = ok && (before || after) && cut_known(A_, B_) == 8 && vb == b0;
            steps++;
            EntryId ee = eval_entry_find(effect_family(), 1500, P);
            if (st == W_OK || (ee && eval_entry_state(ee) == E_READY)) break;   /* the effect published */
        }
        out = effect_request(1500, P, &st);
        printf("  suspension: a send observed after each of %zu single-job slices\n", steps);
        CHECK(ok && outcome_kind(out) == OUT_ACCEPTED, "a send driven over %zu budgeted slices: each cut holds 8, before or after, never half (outcome %d: %s)", steps, (int)outcome_kind(out), outcome_reason(out)); }

    /* 7. receipt views: copy and reindex observations; reject a view that moves the boundary */
    {   uint64_t v1 = receipt_view(E1, map_identity());
        TermVarId vz = declare_term(N, fc_true());
        uint64_t v2 = receipt_view(E1, map_single_term(vz, num(9)));
        CHECK(v1 && v2 && receipt_view_occurrence(v1) == E1 && receipt_view_occurrence(v2) == E1, "views through valid maps keep the event identity");
        /* an open payload: C sends y to B; a view substituting y moves the resource */
        uint64_t capC; TermVarId vy = declare_term(N, fc_true()); RefId yv = ref_var(vy);
        C_ = effect_authority(SEND, add(num(1), yv), 3, &capC); C0 = effect_head(C_);
        uint64_t hc = effect_head(C_);
        EffOut outs[2] = { { 0, C_, num(1) }, { 1, B_, yv } };
        uint64_t P = effect_proposal(SEND, 1, &hc, 2, outs, send_witness(add(num(1), yv), num(1), yv, num(1), mk_refl(1, N, add(num(1), yv))), 1, &capC);
        uint64_t oc = effect_request(1600, P, &st);
        CHECK(outcome_kind(oc) == OUT_ACCEPTED, "an open-quantity send is accepted (%s)", outcome_reason(oc));
        uint64_t Ec = outcome_occurrence(oc);
        CHECK(receipt_view(Ec, map_single_term(vy, num(4))) == 0, "a view changing the transferred quantity without a boundary transport is rejected");
        CHECK(receipt_view(Ec, map_single_term(vz, num(4))) != 0, "a view through a map that fixes its boundary is accepted");
        uint64_t P2 = effect_proposal(RECV, 2, (uint64_t[2]){ effect_port(Ec, 1), effect_head(B_) }, 1, (EffOut[1]){ { 0, B_, add(num(bal(B_)), num(4)) } }, mk_refl(1, N, add(num(bal(B_)), num(4))), 1, &capB);
        CHECK(P2 != 0, "a new proposal at the specialized boundary is constructed normally"); }

    /* 2. a pure producer exposing a finite prefix while its tail stays pending;
     *    a consumer waiting before publication and one after */
    {   SymbolId loop = define_global("tail", varset_make(NULL, 0), dimset_make(NULL, 0), N);
        set_global_body(loop, global_ref(loop));
        TermVarId vs = declare_term(N, fc_true()); (void)vs;
        RefId S = mk_sigma_lv(1, 1, declare_term(N, fc_true()), N, N);
        RefId prod = mk_pair_at_lv(1, S, num(2), global_ref(loop));
        RefId pre = mk_fst(prod);
        uint64_t d0 = rd(RD_DELIVER, 0);
        eval_request(pre, fc_true(), cont_external(ignore, NULL, NULL));          /* waiting before publication */
        EvalResult *r1 = whnf(pre, fc_true(), &st);                               /* drives; a second consumer */
        EvalResult *r2 = whnf(pre, fc_true(), &st);                               /* after publication */
        uint64_t q; CHECK(r1 && r1 == r2 && church_value(r1->ref, &q) && q == 2, "both consumers read the prefix 2");
        CHECK(rd(RD_DELIVER, 0) - d0 >= 3, "three counted deliveries");
        WhnfStatus ts; whnf(mk_snd(prod), fc_true(), &ts);
        CHECK(ts == W_STUCK, "the tail stays pending"); }

    /* 10. one event DAG, read four ways: the resource chain of every accepted
     *     occurrence is the cut difference; sharing and exact work */
    {   uint64_t occs[64]; EntryId ents[64]; size_t no = 0, nent = eval_entry_count();
        for (EntryId e = 1; e <= nent && no < 64; e++) {
            if (!eval_entry_live(e) || eval_entry_family(e) != effect_family()) continue;
            uint64_t o = effect_request(eval_entry_a(e), eval_entry_b(e), &st);   /* the settled outcome */
            if (outcome_kind(o) == OUT_ACCEPTED) { occs[no] = outcome_occurrence(o); ents[no] = e; no++; }
        }
        GenKind k1[64]; uint64_t z1[64];
        for (size_t i = 0; i < no; i++) { k1[i] = G_OCC; z1[i] = z_from_i64(1); }
        uint64_t dH = chain_boundary(chain_of(1, no, k1, occs, z1));
        /* B_0(final) − B_0(initial): current heads and open ports minus the genesis heads */
        GenKind kb[70]; uint64_t ib[70], zb[70], open[64]; size_t nb = 0;
        uint64_t auths[3] = { A_, B_, C_ }, gen[3] = { A0, B0, C0 };
        for (int q = 0; q < 3; q++) {
            kb[nb] = G_HEAD; ib[nb] = effect_head(auths[q]); zb[nb++] = z_from_i64(1);
            kb[nb] = G_HEAD; ib[nb] = gen[q]; zb[nb++] = z_from_i64(-1);
        }
        size_t nopen = effect_open_ports(open, 64);
        for (size_t i = 0; i < nopen; i++) { kb[nb] = G_PORT; ib[nb] = open[i]; zb[nb++] = z_from_i64(1); }
        CHECK(dH == chain_of(0, nb, kb, ib, zb), "∂_res Σ accepted events = B_0(final cut) − B_0(initial cut), the pending port included (%zu events)", no);
        Exact W = { 0, NULL }, W1 = { 0, NULL }, W2 = { 0, NULL }; size_t sup, sup1, sup2; uint64_t w, w1, w2;
        eval_work(no, ents, &W, &sup);
        CHECK(exact_to_u64(&W, &w) && w > 0 && sup >= no, "exact work of the accepted events over their shared support: %llu steps, %zu producers", (unsigned long long)w, sup);
        EntryId twice[2] = { ents[0], ents[0] };
        eval_work(1, ents, &W1, &sup1); eval_work(2, twice, &W2, &sup2);
        CHECK(exact_to_u64(&W1, &w1) && exact_to_u64(&W2, &w2) && w1 == w2 && sup1 == sup2, "a history listed twice is counted once");
        exact_free(&W); exact_free(&W1); exact_free(&W2); }

    printf("  %d passed, %d failed\n", np, nf);
    check_free(); eval_free(); machine_free();
    return nf ? 1 : 0;
}
