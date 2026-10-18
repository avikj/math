/* BOUNDS-COMPLETION §2/§3/§7 acceptance: exact naturals for levels, costs and
 * signed differences.
 *   level 2^32+1 and 2^64 stored, inferred (successor) and printed exactly;
 *   a multi-limb carry chain; canonical identity of equal values;
 *   costs beyond 2^62 and 2^64 and a negative difference beyond int64_t;
 *   one-step grants: an addition of 256-limb operands on a kernel frame
 *   stack advances a bounded number of transitions per grant. */
#include "check.h"
#include "lib.h"
#include "nat.h"
#include "work.h"
#include "compiler.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static int fails;
#define EXPECT(c, ...) do { if (!(c)) { fails++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static Nat big_add_a, big_add_b, big_add_r;
KF_DECL(add_call, void, KF_NOPARAMS, )
KF_STEP(add_call) { KF_BEGIN(add_call); KF_CALL(nat_add, &big_add_r, big_add_a, big_add_b); ks->ok = true; KF_RETV(); KF_END; }

int main(void) {
    setvbuf(stdout, NULL, _IONBF, 0);
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    char d[2048];
    /* levels */
    Nat l32 = nat_from_word((UINT64_C(1) << 32) + 1);
    RefId U32 = mk_universe(l32);
    ContextId empty = context_make(0, NULL, fc_true());
    Inference q = infer(empty, fc_true(), U32);
    Head h; open_ref(q.type, &h); Nat succ = h.payload; head_free(&h);
    nat_decimal(succ, d, sizeof d);
    EXPECT(q.st == CK_VALID && succ == nat_from_word((UINT64_C(1) << 32) + 2), "U_{2^32+1} : U_{2^32+2} (got %s)", d);
    printf("level 2^32+1: inferred type U%s\n", d);
    uint64_t l64[2] = { 0, 1 }; Nat n64 = nat_from_limbs(2, l64);
    RefId U64 = mk_universe(n64); q = infer(empty, fc_true(), U64);
    open_ref(q.type, &h); Nat s64 = h.payload; head_free(&h);
    uint64_t l64p1[2] = { 1, 1 };
    nat_decimal(s64, d, sizeof d);
    EXPECT(q.st == CK_VALID && s64 == nat_from_limbs(2, l64p1), "U_{2^64} : U_{2^64+1} (got %s)", d);
    printf("level 2^64: inferred type U%s; printed ", d); print_ref(U64, stdout); printf("\n");
    /* a pair annotation keeps both exact levels */
    TermVarId va = declare_term(U64, fc_true()); RefId A = ref_var(va);
    uint64_t lv = levels_pack(n64, l32);
    EXPECT(levels_first(lv) == n64 && levels_second(lv) == l32, "a level pair keeps both exact levels");
    (void)A;
    /* carry chain and canonical identity */
    uint64_t ones[3] = { UINT64_MAX, UINT64_MAX, UINT64_MAX }; Nat m = nat_from_limbs(3, ones);
    Nat c = nat_successor(m); size_t nl; uint64_t t; const uint64_t *cl = nat_limbs(c, &nl, &t);
    EXPECT(nl == 4 && cl[0] == 0 && cl[1] == 0 && cl[2] == 0 && cl[3] == 1, "a 3-limb carry chain gives 2^192");
    uint64_t again[5] = { 0, 0, 0, 1, 0 };
    EXPECT(nat_from_limbs(5, again) == c, "equal values are the same canonical natural");
    EXPECT(nat_sub_ge(c, 1) == m && nat_compare(m, c) < 0 && nat_max(m, c) == c, "subtraction, comparison and max are exact");
    nat_decimal(c, d, sizeof d); printf("2^192 = %s\n", d);
    EXPECT(!strcmp(d, "6277101735386680763835789423207666416102355444464034512896"), "decimal export of 2^192");
    /* costs and differences */
    Nat w62 = nat_from_word((UINT64_C(1) << 62) + 5);
    EXPECT(cost_sum(w62, w62) == nat_from_word((UINT64_C(1) << 63) + 10), "costs beyond 2^62 are exact");
    EXPECT(cost_sum(n64, n64) == nat_from_limbs(2, (uint64_t[]){ 0, 2 }) && cost_sum(COST_INF, n64) == COST_INF && cost_cmp(COST_INF, c) > 0, "costs beyond 2^64; INFINITY absorbs and orders above every finite cost");
    NatDiff nd = nat_diff(3, n64);
    EXPECT(nd.sign < 0 && nd.magnitude == nat_sub_ge(n64, 3), "a negative difference beyond int64_t is exact");
    nat_decimal(nd.magnitude, d, sizeof d); printf("3 - 2^64 = -%s\n", d);
    /* one-step grants over a long addition */
    uint64_t la[256], lb[256]; for (size_t i = 0; i < 256; i++) { la[i] = UINT64_MAX; lb[i] = i == 0 ? 1 : 0; }
    big_add_a = nat_from_limbs(256, la); big_add_b = nat_from_limbs(256, lb);
    KStack *k = kf_new(); add_call_push(k, NULL);
    size_t units = 0, maxu = 0;
    while (!kf_done(k)) { size_t u = kf_grant(k, 1); if (u > maxu) maxu = u; units++; }
    const uint64_t *rl = nat_limbs(big_add_r, &nl, &t);
    bool okc = nl == 257 && rl[256] == 1; for (size_t i = 0; i < 256 && okc; i++) okc = rl[i] == 0;
    printf("256-limb addition under one-step grants: units=%zu max transitions per grant=%zu result 2^16384 exact=%d\n", units, maxu, okc);
    EXPECT(okc && units >= 256 && maxu <= 128, "one-step grants advance a bounded number of transitions; precision adds transitions, not per-transition work");
    kf_free(k);
    /* the work engine: a SUM of boxed weights under one-unit steps — the
     * additions run as shared NAT jobs, one limb per transition */
    {
        AtomId a1 = atom_pub(atom_producer(U32, fc_true())), a2 = atom_pub(atom_producer(U64, fc_true()));
        AtomId as[2] = { a1, a2 }; SetId S = set_make(2, as);
        KindWeights kw; memset(&kw, 0, sizeof kw);
        uint64_t l128[3] = { 0, 0, 1 }; Nat w128 = nat_from_limbs(3, l128);   /* 2^128 */
        ModelId M = model_with_weight(model_with_weight(model_make(7, kw, set_make(0, NULL)), a1, w128), a2, w128);
        OpId h = op_set_weight(S, M); size_t units = 0; WorkLedger l0 = work_ledger(); uint64_t maxex = 0;
        while (op_status(h) == OP_RUNNING && units < 1000000) { op_step(h, 1); units++; }
        WorkLedger l1 = work_ledger(); (void)l0; (void)maxex;
        uint64_t l129[3] = { 0, 0, 2 };
        EXPECT(op_status(h) == OP_COMPLETE && op_result(h) == nat_from_limbs(3, l129), "SUM of two 2^128 weights is 2^129 through framed NAT jobs");
        printf("engine SUM of boxed weights: units=%zu kernel transitions=%llu result exact=%d\n", units, (unsigned long long)(l1.frames[FR_KERNEL_TRANSITION] - l0.frames[FR_KERNEL_TRANSITION]), op_result(h) == nat_from_limbs(3, l129));
        op_release(h);
    }
    work_free(); compiler_free(); check_free(); eval_free(); machine_free();
    printf("test_exact: %d failures\n", fails);
    return fails ? 1 : 0;
}
