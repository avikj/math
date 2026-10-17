/* Existing §84.2: a committed finite reduction prefix is reusable even
 * when its remaining computation is suspended. No theorem is inferred
 * from the recursive program used to keep that suffix pending.
 * Run: review_live_prefix {specialize|restrict} [workers]
 */
#include "check.h"
#include "lib.h"
#include "reuse_stats.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    assert(argc >= 2);
    bool restrict_face = !strcmp(argv[1], "restrict");
    assert(restrict_face || !strcmp(argv[1], "specialize"));
    machine_init(); eval_init(); check_init();
    if (argc > 2) eval_set_workers((size_t)strtoull(argv[2], NULL, 10));
    RefId U = mk_universe(0);
    TermVarId va = declare_term(U, fc_true()); RefId A = ref_var(va);
    TermVarId vx = declare_term(A, fc_true()); RefId x = ref_var(vx);
    DimVarId i = declare_dim();
    RefId P = mk_path_const(0, A, x, x);
    uint64_t pars[] = {va, vx};
    SymbolId loop = define_global("pending_path", varset_make(pars, 2),
                                  dimset_make(NULL, 0), P);
    assert(loop && set_global_body(loop, global_ref(loop)));
    RefId point = mk_papp_const(0, A, x, x, global_ref(loop), iv_var(i));
    TermVarId z = declare_term(A, fc_true());
    RefId term = mk_app(mk_lam_lv(0, z, A, point), x);
    CtxDecl ds[] = {{S_TERM, va, U}, {S_TERM, vx, A}, {S_DIM, i, 0}};
    ContextId G = context_make(3, ds, fc_true());
    const char *why = NULL;
    assert(check(G, fc_true(), term, A, &why) == CK_VALID);

    uint64_t beta0 = reuse_count(REUSE_BETA);
    WhnfStatus s0;
    EvalResult *r0 = whnf(term, fc_true(), &s0);
    assert(s0 == W_STUCK && !r0);
    assert(reuse_count(REUSE_BETA) == beta0 + 1);
    EntryId e = eval_entry_lookup(term, fc_true());
    assert(e && eval_entry_state(e) == E_RUNNING);
    /* Completed-answer accessors must not fabricate a final answer. */
    assert(!eval_entry_residual(e) && !eval_entry_receipt(e));

    RefId target = term; FaceId face = fc_lit(i, 0);
    if (!restrict_face) {
        MapBuilder m; mapb_init(&m); mapb_dim(&m, i, iv_zero());
        target = reindex(term, mapb_finish(&m)); face = fc_true();
    }
    uint64_t before = reuse_count(REUSE_BETA);
    WhnfStatus s1; EvalResult *r1 = whnf(target, face, &s1);
    bool semantic_ok = s1 == W_OK && r1 && r1->ref == x;
    uint64_t repeated_beta = reuse_count(REUSE_BETA) - before;
    bool source_pending = eval_entry_state(e) == E_RUNNING;
    printf("mode=%s workers=%zu semantic_ok=%d source_pending=%d "
           "repeated_beta=%llu expected=0\n", argv[1], eval_workers(),
           semantic_ok, source_pending, (unsigned long long)repeated_beta);
    check_free(); eval_free(); machine_free();
    return semantic_ok && source_pending && repeated_beta == 0 ? 0 : 1;
}
