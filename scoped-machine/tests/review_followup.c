#define _POSIX_C_SOURCE 200809L
#include "../src/check.h"
#include "../src/lib.h"
#include "../src/compiler.h"
#include <string.h>

/* each mode prints its observations and exits nonzero when an expectation of §59.6 fails */
static int failures = 0;
#define EXPECT(c, what) do { if (!(c)) { failures++; printf("  FAIL: %s\n", what); } } while (0)
int main(int argc, char **argv) {
    machine_init(); eval_init(); check_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)strtoul(getenv("CUBICAL_WORKERS"), NULL, 10));
    const char *why = "";
    RefId U = mk_universe(0);
    TermVarId va = declare_term(U, fc_true()), vb = declare_term(U, fc_true());
    RefId A = ref_var(va), B = ref_var(vb);
    TermVarId vx = declare_term(A, fc_true()), vy = declare_term(B, fc_true());
    RefId x = ref_var(vx), y = ref_var(vy);
    CtxDecl da[] = {{S_TERM, va, U}, {S_TERM, vx, A}};
    CtxDecl db[] = {{S_TERM, vb, U}, {S_TERM, vy, B}};
    ContextId GA = context_make(2, da, fc_true()), GB = context_make(2, db, fc_true());
    MapBuilder mb; mapb_init(&mb); mapb_term(&mb, va, B); mapb_term(&mb, vx, y);
    MapId s = mapb_finish(&mb);
    printf("typed substitution: %s\n", check_status_name(check_map(GB, fc_true(), s, GA, fc_true(), &why)));
    if (argc > 1 && !strcmp(argv[1], "formation")) {
        uint64_t lr; RefId d = residual_fold(0, NULL, x, 0, &lr);
        CheckStatus fs = check(GA, fc_true(), d, res_type(0, lr), &why);
        printf("empty residual with terminal x:A (A:U0): %s\n", check_status_name(fs));
        EXPECT(fs == CK_INVALID, "a term-valued residual terminal must fail formation");
        printf("terminal x has inferred type A, not a universe: %d\n", infer(GA, fc_true(), x).type == A);
    } else if (argc > 1 && !strcmp(argv[1], "admission")) {
        uint64_t vs[] = {va, vx};
        VarSetId pars = varset_make(vs, 2); DimSetId ds = dimset_make(NULL, 0);
        SymbolId good = define_global("good", pars, ds, A);
        SymbolId bad = define_global("bad", pars, ds, A);
        SymbolId dependent = define_global("dependent", pars, ds, A);
        SymbolId bad_type = define_global("bad-type", pars, ds, U);
        SymbolId bad_equiv = define_global("bad-equivalence", pars, ds, mk_equiv(0, 0, A, A));
        set_global_body(good, x); set_global_body(bad, mk_pair(x, x));
        set_global_body(dependent, global_ref(bad));
        set_global_body(bad_type, mk_pair(A, A));
        set_global_body(bad_equiv, x);
        WhnfStatus st; EvalResult *r = observe_checked(GA, global_ref(good), &st, &why);
        printf("local checked execution with unrelated invalid bodies: status=%d result=%s\n", (int)st, r ? "present" : "absent");
        EXPECT(st == W_OK && r && r->ref == x, "unrelated invalid definitions must not block a valid judgment");
        RefId id = mk_app(mk_app(mk_app(equiv_maps(0, 0), A), A), mk_id_equiv(0, A));
        EXPECT(check(GA, fc_true(), id, maps_type(0, 0, A, A), &why) == CK_VALID, "unrelated invalid definitions must not block a checked action");
        r = observe_checked(GA, maps_apply(id, DIR_FORWARD, x), &st, &why);
        EXPECT(st == W_OK && r && r->ref == x, "the action remains executable in the same environment");
        EXPECT(define_global("after-publication", varset_make(NULL, 0), dimset_make(NULL, 0), mk_universe(0)) != 0, "local judgment and transform publication leave the registry open");
        r = observe_checked(GA, global_ref(bad), &st, &why);
        EXPECT(st == W_INVALID && r == NULL, "an invalid definition must reject when actually used");
        r = observe_checked(GA, global_ref(dependent), &st, &why);
        EXPECT(st == W_INVALID && r == NULL, "an invalid transitive dependency must reject");
        TermVarId z = declare_term(global_ref(bad_type), fc_true());
        ContextId invalid_context = context_extend_term(GA, z, global_ref(bad_type));
        r = observe_checked(invalid_context, x, &st, &why);
        EXPECT(st == W_INVALID && r == NULL, "definitions used by the judgment context must also validate");
        EXPECT(check(GA, fc_true(), mk_app(mk_app(mk_app(equiv_maps(0, 0), A), A), global_ref(bad_equiv)), maps_type(0, 0, A, A), &why) == CK_INVALID,
               "an invalid definition used as transform evidence must reject");
        CheckStatus ss = check_signature(&why);
        printf("whole signature: %s\n", check_status_name(ss));
        EXPECT(ss == CK_INVALID, "an explicit check of the whole signature still reports its invalid bodies");
        r = observe_checked(GA, global_ref(good), &st, &why);
        EXPECT(st == W_OK && r && r->ref == x, "a failed whole-signature query must not invalidate an independent judgment");
    } else if (argc > 1 && !strcmp(argv[1], "call")) {
        CtxDecl d[] = {{S_TERM, va, U}};
        ContextId G = context_make(1, d, fc_true());
        (void)G;
        RefId id = mk_app(mk_app(mk_app(equiv_maps(0, 0), A), A), mk_id_equiv(0, A));
        RefId p = reindex(maps_apply(id, DIR_FORWARD, x), s);
        RefId q = maps_apply(reindex(id, s), DIR_FORWARD, y);
        printf("call reference equality: %d\n", p == q);
        EXPECT(p == q, "reindexed and direct transform calls must be one reference");
        CheckStatus c1 = check(GB, fc_true(), p, B, &why), c2 = check(GB, fc_true(), q, B, &why);
        printf("both check: %s / %s\n", check_status_name(c1), check_status_name(c2));
        EXPECT(c1 == CK_VALID && c2 == CK_VALID, "both calls check");
        WhnfStatus st; (void)whnf(p, fc_true(), &st); eval_run();
        EvalEvents n1 = eval_events();
        (void)whnf(q, fc_true(), &st); eval_run();
        printf("extra producers for the second call: %zu\n", eval_events().launch - n1.launch);
        EXPECT(eval_events().launch - n1.launch == 0, "one computation shared by both calls");
    } else {
        RefId p = reindex(mk_refl(0, A, x), s), q = mk_refl(0, B, y);
        printf("type-substituted Refl reference equality: %d\n", p == q);
        EXPECT(p == q, "type-changing Refl specialization must be one reference");
        RefId expected = mk_path_const(0, B, y, y);
        CheckStatus c1 = check(GB, fc_true(), p, expected, &why), c2 = check(GB, fc_true(), q, expected, &why);
        printf("both check: %s / %s\n", check_status_name(c1), check_status_name(c2));
        EXPECT(c1 == CK_VALID && c2 == CK_VALID, "both Refl terms check");
        WhnfStatus st; (void)whnf(p, fc_true(), &st); eval_run();
        EvalEvents n = eval_events(); (void)whnf(q, fc_true(), &st); eval_run();
        printf("extra producer on second Refl: %zu\n", eval_events().launch-n.launch);
        EXPECT(eval_events().launch - n.launch == 0, "one producer for both Refl terms");
    }
    check_free(); eval_free(); machine_free();
    return failures ? 1 : 0;
}
