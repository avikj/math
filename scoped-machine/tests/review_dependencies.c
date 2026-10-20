/* review_dependencies.c — the acceptance cases of the 550c018 handoff
 * (§§4–5, §10) through the public API: an ill-typed defined witness is never
 * accepted; a valid one is accepted once; an opaque check followed by an
 * invalid body never yields a CORE proof use of the unchecked body; a
 * suspended effect resumes across an unrelated declaration; head observation
 * reads no unused definition; one relevant producer for g demanded directly
 * and beside an unused sibling; a definition reached through a declared type
 * checks and observes. */
#include "../src/compiler.h"
#include "../src/proof.h"
#include "../src/effect.h"
#include "reading.h"

static int np, nf;
#define CHECK(c, ...) do { if (c) np++; else { nf++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static RefId U, U1, U2, A, x;
static TermVarId ta, tx;
static VarSetId params, none;
static ContextId G, empty;

/* the WHNF nodes of t (key [F_WHNF, t, χ, path]) and their runs */
static size_t whnf_bodies(RefId t) {
    size_t total = 0;
    for (EntryId e = 1; e <= eval_entry_count(); e++)
        if (eval_entry_live(e) && eval_entry_family(e) == F_WHNF && eval_entry_a(e) == t) total += eval_entry_runs(e);
    return total;
}
static void fresh(void) {
    machine_free(); machine_init(); check_init();
    U = mk_universe(0); U1 = mk_universe(1); U2 = mk_universe(2);
    ta = declare_term(U, fc_true()); A = ref_var(ta);
    tx = declare_term(A, fc_true()); x = ref_var(tx);
    CtxDecl ds[] = { { S_TERM, ta }, { S_TERM, tx } };
    G = context_make(2, ds, fc_true()); empty = context_make(0, NULL, fc_true());
    TermVarId ps[] = { ta, tx }; params = set_make(ps, 2); none = set_make(NULL, 0);
}
/* a one-head effect over S = U1 whose witness is a defined symbol of type U1 */
static void effect_case(bool valid, bool pause) {
    fresh();
    const char *why = "";
    TermVarId va = declare_term(U1, fc_true()), vb = declare_term(U1, fc_true());
    RefId R = mk_lam_lv(2, va, U1, mk_lam_lv(2, vb, U1, U1));
    uint64_t schema = effect_schema(U1, 2, R), cap;
    uint64_t auth = effect_authority(schema, U, 7654, &cap), h = effect_head(auth);
    SymbolId w = define_global(valid ? "valid-witness" : "ill-typed-witness", none, none, U1);
    set_global_body(w, valid ? U : mk_pair(U, U));
    RefId witness = global_ref(w);
    CheckStatus s = check(empty, fc_true(), witness, U1, &why);
    ProofUse u = proof_use(empty, fc_true(), witness, U1);
    EffOut out = { 0, auth, U };
    uint64_t P = effect_proposal(schema, 1, &h, 1, &out, witness, 1, &cap);
    WhnfStatus ws;
    if (pause) {
        family_run_budget(effect_family(), 9876, P, 1, &ws);
        CHECK(ws == W_STUCK, "the effect is suspended after one step");
        define_global("unrelated-after-pause", none, none, U1);
    }
    uint64_t o = effect_request(9876, P, &ws), occ = outcome_occurrence(o);
    if (!valid) {
        CHECK(s == CK_INVALID && u.status == PU_INVALID, "the public check and proof use reject the ill-typed witness (%s)", why);
        CHECK(outcome_kind(o) == OUT_INVALID && !occ && effect_head(auth) == h, "the ill-typed witness is not accepted: INVALID, the head unchanged (%s)", outcome_reason(o));
    } else {
        CHECK(s == CK_VALID && u.status == PU_CORE, "the valid witness checks and is a core proof");
        CHECK(outcome_kind(o) == OUT_ACCEPTED && occ && receipt_accepted(occ) && effect_head(auth) != h,
              pause ? "the suspended effect resumes across an unrelated declaration and is accepted (%s)" : "the valid witness is accepted once (%s)", outcome_reason(o));
        CHECK(effect_request(9876, P, &ws) == o, "a duplicate request returns the same receipt");
        CHECK(receipt_evidence(occ) && rword(receipt_evidence(occ), 0) == 1, "the occurrence retains its admitted proof-use judgment");
    }
    proof_use_free(&u);
}

/* the completion handoff's probe: one relative family reading s; opaque →
 * it awaits itself; a body → 42 */
static Family rel;
static void rel_step(Cont *k, uint64_t v) {
    FR_BEGIN(k);
    FR_AWAIT(k, k->w[2], F_READ, k->w[0], k->view);
    if (!revision_body(k->w[2])) {
        FR_AWAIT(k, k->w[3], rel, k->w[0], 0);
    }
    FR_FINISH(k, 42);
    FR_END(k);
}

int main(void) {
    setvbuf(stdout, NULL, _IONBF, 0);
    printf("== the 550c018 acceptance cases\n");
    machine_init();
    effect_case(false, false);
    effect_case(true, false);
    effect_case(true, true);

    /* an opaque check, then an invalid body: proof use validates the
     * revision it reads, never reports the unchecked body as CORE */
    {   fresh(); const char *why = "";
        SymbolId t = define_global("review-target", params, none, A);
        CHECK(check(G, fc_true(), global_ref(t), A, &why) == CK_VALID, "the opaque declaration checks");
        set_global_body(t, mk_pair(x, x));
        ProofUse u = proof_use(G, fc_true(), global_ref(t), A);
        CHECK(u.status == PU_INVALID, "proof use after the body is published validates it and rejects (%s)", u.reason);
        proof_use_free(&u); }

    /* head observation reads no unused definition: the steps of fst(x, g_0)
     * do not depend on the length of g's chain */
    {   uint64_t steps[3]; size_t sizes[3] = { 0, 32, 256 }; bool none_read = true;
        for (int q = 0; q < 3; q++) {
            fresh();
            RefId tail = x;
            for (size_t j = 0; j < sizes[q]; j++) { SymbolId g = define_global("unused", params, none, A); set_global_body(g, tail); tail = global_ref(g); }
            RefId parent = mk_fst(mk_pair(x, tail));
            uint64_t c0 = rd(RD_STEPS, F_CLOSURE), g0 = rd(RD_STEPS, F_GLOBALS), r0 = rd(RD_STEPS, F_READ), t0 = rd(RD_STEP, 0);
            WhnfStatus ws; EvalResult r = whnf(parent, fc_true(), &ws);
            CHECK(ws == W_OK && r.ref == x, "fst(x, g_0) observes x (chain %zu)", sizes[q]);
            if (rd(RD_STEPS, F_CLOSURE) != c0 || rd(RD_STEPS, F_GLOBALS) != g0 || rd(RD_STEPS, F_READ) != r0) none_read = false;
            steps[q] = rd(RD_STEP, 0) - t0;
        }
        CHECK(none_read, "no definition is read or audited");
        CHECK(steps[0] == steps[1] && steps[1] == steps[2], "the observation's steps do not depend on the unused chain (%llu, %llu, %llu)",
              (unsigned long long)steps[0], (unsigned long long)steps[1], (unsigned long long)steps[2]); }

    /* one relevant producer for g, directly and beside an unused sibling
     * declared in between */
    {   fresh();
        SymbolId t = define_global("g", params, none, A); set_global_body(t, x);
        WhnfStatus s0, s1; EvalResult r0 = whnf(global_ref(t), fc_true(), &s0);
        size_t b0 = whnf_bodies(global_ref(t));
        SymbolId h = define_global("discarded", params, none, A);
        EvalResult r1 = whnf(mk_fst(mk_pair(global_ref(t), global_ref(h))), fc_true(), &s1);
        size_t b1 = whnf_bodies(global_ref(t));
        CHECK(s0 == W_OK && r0.ref == x && s1 == W_OK && r1.ref == x, "both observations give x");
        CHECK(b0 >= 1 && b1 == b0, "no WHNF node of g is added across the unrelated declaration (%zu, %zu)", b0, b1); }

    /* a definition reached through a declared type */
    {   fresh(); const char *why = "";
        SymbolId alias = define_global("type-alias", none, none, U2); set_global_body(alias, U1);
        SymbolId value = define_global("value-through-type-alias", none, none, global_ref(alias)); set_global_body(value, U);
        RefId val = global_ref(value);
        CHECK(check(empty, fc_true(), val, global_ref(alias), &why) == CK_VALID, "the value checks at the alias (%s)", why);
        WhnfStatus ws; EvalResult r = observe_checked(empty, val, &ws, &why);
        CHECK(ws == W_OK && r.cls, "its checked observation succeeds (%s)", why);
        CHECK(check(empty, fc_true(), val, U1, &why) == CK_VALID, "it checks at the convertible type (%s)", why); }

    /* a relevant revision branches at the read: the old view's request stays
     * pending on itself; the new view completes without awaiting it; an
     * unrelated declaration does not split the computation */
    {   fresh();
        if (!rel) { rel = family_new("review.pending-revision", rel_step, 0); family_kind(rel, FK_RELATIVE); }
        SymbolId s = define_global("pending", none, none, U1);
        WhnfStatus st;
        family_run_in(rel, s, 0, view_current(), 0, &st);
        CHECK(st == W_STUCK, "the request in the opaque view is pending (status %d)", st);
        set_global_body(s, U);
        uint64_t out = family_run_in(rel, s, 0, view_current(), 0, &st);
        CHECK(st == W_OK && out == 42, "the request in the new view completes with 42 (status %d, value %llu)", st, (unsigned long long)out);
        size_t e0 = eval_entry_count();
        define_global("unrelated", none, none, U1);
        uint64_t again = family_run_in(rel, s, 0, view_current(), 0, &st);
        size_t grew = 0; for (EntryId e = e0 + 1; e <= eval_entry_count(); e++) if (eval_entry_live(e) && eval_entry_family(e) == rel) grew++;
        CHECK(st == W_OK && again == 42 && grew == 0, "an unrelated declaration reuses every node (%zu new)", grew); }

    printf("  %d passed, %d failed\n", np, nf);
    machine_free();
    return nf ? 1 : 0;
}
