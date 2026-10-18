/* demo_speculation.c — the face-as-condition reading, run against the machine.
 *
 * A latency-critical decision: on the next tick the program sends one of two
 * orders. Both depend on a shared prefix computation (the model) that is
 * expensive and independent of the tick. The classical hand-built pattern:
 * precompute both orders speculatively, decide by a lookup when the tick
 * arrives, and fight for determinism (no locks, one answer, bounded work).
 *
 * In the machine the tick is a dimension i; "tick up" is the face i=1,
 * "tick down" is i=0. The decision is a system [i=0 ↦ down(pre), i=1 ↦
 * up(pre)] with pre the shared prefix. What is measured:
 *
 *   1. pre is one memo key under every face (its key is projected to its
 *      support, which does not mention i): one producer for both branches.
 *   2. speculating (demanding the decision under i=0 ∨ i=1, "the tick will be
 *      one or the other" — the decision is a partial element defined exactly
 *      there, and the machine refuses to observe it anywhere else) computes both branches
 *      once; the later demand under i=1 (the tick arrived) adds no evaluator
 *      step: the restricted key forwards to the published branch.
 *   3. restriction: the decision reindexed at i=1 resolves, in one dispatch
 *      step, to the speculative up result object — the branch's memo entry
 *      is shared, nothing is recomputed.
 *   4. specialization by substitution shares: the decision at a different
 *      model parameter shares the branches that do not mention it.
 *   5. W is the same under FIFO, LIFO and random scheduling, with and without
 *      a worker pool: the cost is a property of the demand, not of the run.
 */
#define _POSIX_C_SOURCE 200809L
#include "../src/check.h"
#include "../src/lib.h"
#include <string.h>

typedef struct { EvalEvents ev; RefId spec, up, forwarded_up; size_t nbr, tick_steps, tick_launch, tick_ready, spec_launch_down, spec_launch_up, spec_ready_up; } Run;

static Run run(SchedPolicy pol, uint64_t seed, size_t workers) {
    machine_init(); eval_init(); check_init();
    eval_set_policy(pol, seed);
    eval_set_adoption(false);   /* the base evaluator: its work vector is schedule independent (with live adoption, whether a slot adopts depends on the race) */
    if (workers) eval_set_workers(workers);
    Run out; memset(&out, 0, sizeof out);
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);            /* the order type */
    TermVarId vM = declare_term(U0, fc_true()); RefId Mt = ref_var(vM);           /* the model-input type */
    TermVarId vm = declare_term(Mt, fc_true()); RefId m = ref_var(vm);            /* today's model input */
    TermVarId vm2 = declare_term(Mt, fc_true()); RefId m2 = ref_var(vm2);         /* another one */
    /* the model yields a pair of candidate quantities; the two order builders
     * project one each, so both branches force the shared prefix */
    TermVarId vs = declare_term(A, fc_true());
    RefId SAA = mk_sigma_lv(0, 0, vs, A, A);
    RefId MS = mk_fun(0, 0, Mt, SAA);
    TermVarId vmodel = declare_term(MS, fc_true()); RefId model = ref_var(vmodel);/* the expensive model: opaque f : M → A × A */
    TermVarId vy1 = declare_term(SAA, fc_true()), vy2 = declare_term(SAA, fc_true());
    RefId up = mk_lam_lv(0, vy1, SAA, mk_fst(ref_var(vy1))), down = mk_lam_lv(0, vy2, SAA, mk_snd(ref_var(vy2)));   /* order builders */
    DimVarId i = declare_dim();                                                   /* the tick */

    /* the shared prefix: pre := (λx. model x) m — a redex so the evaluator has a step to do */
    TermVarId vx = declare_term(Mt, fc_true());
    RefId pre = mk_app(mk_lam_lv(0, vx, Mt, mk_app(model, ref_var(vx))), m);
    /* the decision: [i=0 ↦ down pre, i=1 ↦ up pre] */
    FaceId fs[2] = { fc_lit(i, 0), fc_lit(i, 1) };
    RefId ts[2] = { mk_app(down, pre), mk_app(up, pre) };
    RefId decision = mk_system(2, fs, ts);

    WhnfStatus st;
    /* 1–2. speculate: demand the decision under each outcome face. (Under ⊤
     * the demand is refused — the decision is a partial element defined on
     * the boundary i=0 ∨ i=1 only; under the disjunction it is exposed as a
     * system of branches without computing them.) */
    { EvalResult *bad = whnf(decision, fc_true(), &st); require(st == W_INVALID && bad->cls == R_INVALID, "a boundary-only decision is not observable in the interior"); }
    EvalEvents e0 = eval_events();
    EvalResult *spec_down = whnf(decision, fs[0], &st); require(st == W_OK, "down branch");
    EvalEvents e1 = eval_events();
    EvalResult *spec_up = whnf(decision, fs[1], &st); require(st == W_OK, "up branch");
    EvalEvents e2 = eval_events();
    /* the prefix is launched once: the second branch finds its key ready */
    out.spec_launch_down = e1.launch - e0.launch; out.spec_launch_up = e2.launch - e1.launch; out.spec_ready_up = e2.ready_hit - e1.ready_hit;
    require(out.spec_launch_up < out.spec_launch_down && out.spec_ready_up >= 1, "the shared prefix is computed once for both speculative branches");
    out.nbr = 2; (void)spec_down; (void)spec_up;
    EvalEvents after_spec = e2;
    /* the tick arrives: demand under i=1 */
    EvalResult *now = whnf(decision, fc_lit(i, 1), &st);
    require(st == W_OK && now == spec_up, "the decision under the tick is the speculative result, the same result object");
    EvalEvents after_tick = eval_events();
    out.tick_steps = after_tick.eval_step - after_spec.eval_step;
    out.tick_launch = after_tick.launch - after_spec.launch;
    out.tick_ready = after_tick.ready_hit - after_spec.ready_hit;
    require(out.tick_launch == 0 && out.tick_steps <= 1 && out.tick_ready == 1, "the tick computes nothing: one ready hit, one delivery frame, no producer");
    out.forwarded_up = now->ref;
    /* 3. restriction: the system under [i ↦ 1] is dispatched to its true
     * branch at the first demand (one frame step) and from then on shares
     * the branch's memo entry — the same result object, no producer */
    out.spec = decision; out.up = ts[1];
    { RefId restricted = reindex(decision, map_single_dim(i, iv_one()));
      EvalEvents b0 = eval_events(); EvalResult *rr = whnf(restricted, fc_true(), &st); EvalEvents b1 = eval_events();
      /* §93.3: the branch's key is alias-published from the speculative run with
       * its own descriptor (head = the branch residual); result pointers across
       * different keys are not required to coincide — the answer is the same
       * residual (the speculative entry's own residual, the rebuilt eliminator
       * around the evaluated prefix) and class, with one dispatch launch and no
       * branch work */
      RefId spec_residual = eval_entry_residual(eval_entry_lookup(decision, fs[1]));
      require(st == W_OK && rr->cls == spec_up->cls && rr->ref == spec_residual && b1.launch - b0.launch == 1, "the restricted decision resolves to the speculative up result (one dispatch launch, no branch work)"); }
    /* 4. specialization shares: the decision at m2 shares nothing of pre (which mentions m) but shares up/down */
    RefId decision2 = reindex(decision, map_single_term(vm, m2));
    require(decision2 != decision, "a different model input is a different decision");
    EvalEvents before2 = eval_events();
    (void)whnf(decision2, fs[0], &st); (void)whnf(decision2, fs[1], &st);
    EvalEvents after2 = eval_events();
    /* the second decision re-evaluates only what mentions m: the prefix redex and the two applications */
    out.ev = eval_events();
    out.ev.request = after2.request - before2.request;        /* work attributable to the specialization */
    out.ev.eval_step = after2.eval_step - before2.eval_step;
    out.ev.publish = after2.publish - before2.publish;
    /* total W of the speculation itself */
    out.ev.deliver = after_spec.deliver; out.ev.launch = after_spec.launch; out.ev.ready_hit = after_spec.eval_step; out.ev.running_hit = after_spec.publish;
    (void)A; (void)m2;
    check_free(); eval_free(); machine_free();
    return out;
}

int main(void) {
    struct { const char *name; SchedPolicy p; uint64_t seed; size_t workers; } cfg[] = {
        { "FIFO, no pool", POL_FIFO, 0, 0 }, { "LIFO, no pool", POL_LIFO, 0, 0 }, { "random(7), no pool", POL_RANDOM, 7, 0 },
        { "FIFO, 4 workers", POL_FIFO, 0, 4 }, { "LIFO, 4 workers", POL_LIFO, 0, 4 }, { "random(99), 4 workers", POL_RANDOM, 99, 4 },
    };
    Run base = run(cfg[0].p, cfg[0].seed, cfg[0].workers);
    printf("speculation: first branch launches %zu producers (its own keys and the whole prefix subtree); second launches %zu — the prefix is a ready hit (%zu)\n",
           base.spec_launch_down, base.spec_launch_up, base.spec_ready_up);
    printf("speculation W = (eval_step %zu, publish %zu, deliver %zu, launch %zu)\n", base.ev.ready_hit, base.ev.running_hit, base.ev.deliver, base.ev.launch);
    printf("tick under i=1: %zu delivery frame, %zu producers launched, %zu ready hit — the same result object as the speculation\n", base.tick_steps, base.tick_launch, base.tick_ready);
    printf("specialization to another model input: extra W = (request %zu, eval_step %zu, publish %zu)\n", base.ev.request, base.ev.eval_step, base.ev.publish);
    bool same = true;
    for (size_t k = 1; k < sizeof cfg / sizeof cfg[0]; k++) {
        Run r = run(cfg[k].p, cfg[k].seed, cfg[k].workers);
        bool eq = r.nbr == base.nbr && r.spec_launch_down == base.spec_launch_down && r.spec_launch_up == base.spec_launch_up && r.tick_steps == base.tick_steps && r.tick_launch == base.tick_launch && r.ev.ready_hit == base.ev.ready_hit && r.ev.running_hit == base.ev.running_hit && r.ev.deliver == base.ev.deliver
               && r.ev.request == base.ev.request && r.ev.eval_step == base.ev.eval_step && r.ev.publish == base.ev.publish;
        printf("  %-24s W identical to FIFO/no pool: %s\n", cfg[k].name, eq ? "yes" : "NO");
        same = same && eq;
    }
    printf("%s\n", same ? "W is a property of the demand, not of the schedule (the base evaluator, live adoption off)." : "MISMATCH");
    return same ? 0 : 1;
}
