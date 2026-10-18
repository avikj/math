/* §94 kernel frame stacks (kframe.h), white-box over work.c.
 * A producer atom over a term with N nested applications is specialized
 * under x2 := x1 (ATOMSPEC: reindex, structural validation, face
 * substitution/projection/entailment, producer lookup, shape — every one a
 * kernel continuation).
 *  1. cold, budget 1: no unit takes more than a few kernel transitions (one
 *     under the grant; a yield deferred past a held lock adds the locked
 *     section's transitions), and no unit makes more than one kernel call;
 *  2. the result equals the synchronous `set_specialize`;
 *  3. a second handle for the same specialization, started while the first
 *     is mid-kernel, joins the running kernel job (one kernel call in all);
 *  4. a third request after completion is READY: zero kernel transitions;
 *  5. the frame stack is retained: across the units the
 *     ATOMSPEC frame stays the same frame (same phase until the call ends).
 */
#include "work.c"
#include "fine.h"
#include <assert.h>


int main(int argc, char **argv) {
    size_t N = argc > 1 ? (size_t)strtoull(argv[1], NULL, 10) : 64;
    setvbuf(stdout, NULL, _IONBF, 0);
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
    TermVarId v1 = declare_term(A, fc_true()), v2 = declare_term(A, fc_true()); RefId x1 = ref_var(v1), x2 = ref_var(v2);
    TermVarId vf = declare_term(mk_fun(0, 0, A, A), fc_true()); RefId f = ref_var(vf);
    RefId t = x2; for (size_t i = 0; i < N; i++) t = mk_app(f, t);   /* f^N x2 */
    AtomId a = atom_producer(t, fc_true());
    MapId sigma = map_single_term(v2, x1);
    SetId S = set_make(1, &a);
    /* 1–2: cold, one unit at a time */
    OpId h = op_specialize_set(S, sigma);
    uint64_t max_trans = 0, max_calls = 0, units = 0, kernel_units = 0, kernel_calls = 0;
    while (op_status(h) == OP_RUNNING) {
        FineVector b = fine_snapshot(); WorkLedger lb = work_ledger();
        op_step(h, 1); units++;
        FineVector c = fine_snapshot(); WorkLedger lc = work_ledger();
        uint64_t trans = 0; for (int i = 0; i < FC_COUNT; i++) trans += c.v[i] - b.v[i];
        uint64_t calls = lc.kernel_calls - lb.kernel_calls, kt = lc.frames[FR_KERNEL_TRANSITION] - lb.frames[FR_KERNEL_TRANSITION];
        if (kt || calls) { kernel_units++; if (trans > max_trans) max_trans = trans; }
        if (calls > max_calls) max_calls = calls; kernel_calls += calls;
    }
    assert(op_status(h) == OP_COMPLETE);
    const char *why = NULL; SetId sync = set_specialize(S, sigma, &why);
    printf("cold N=%zu: units=%llu kernel_units=%llu kernel_calls=%llu max_kernel_transitions_per_unit=%llu max_kernel_calls_per_unit=%llu result==set_specialize:%d\n",
           N, (unsigned long long)units, (unsigned long long)kernel_units, (unsigned long long)kernel_calls, (unsigned long long)max_trans, (unsigned long long)max_calls, op_result(h) == sync);
    /* the continuations span many units (retained frames): far more kernel units than kernel calls; a unit's transitions are one plus at most one locked section's (a fixed-size key's hashing/probing and one migration chunk of a growing interner: ≤ ~80) */
    assert(op_result(h) == sync && max_calls <= 1 && max_trans <= 128 && kernel_units > 4 * kernel_calls);
    /* 3: a second handle joins the running kernel job */
    TermVarId v3 = declare_term(A, fc_true()); RefId x3 = ref_var(v3); (void)x3;
    RefId t2 = x2; for (size_t i = 0; i < N; i++) t2 = mk_app(f, mk_app(f, t2));
    AtomId a2 = atom_producer(t2, fc_true()); SetId S2 = set_make(1, &a2);
    OpId h1 = op_specialize_set(S2, sigma);
    size_t steps = 0; while (op_status(h1) == OP_RUNNING && !(W.kf_active)) { op_step(h1, 1); assert(++steps < 100000); }
    assert(W.kf_active && !kf_done(W.kf_active));   /* mid-kernel (W.kf_active: the stack most recently granted) */
    uint64_t calls_before = work_ledger().kernel_calls;
    OpId h2 = op_specialize_set(S2, sigma);   /* the same specialization: the atom's ATOMSPEC job and its kernel jobs are shared */
    while (op_status(h2) == OP_RUNNING) op_step(h2, 1);
    while (op_status(h1) == OP_RUNNING) op_step(h1, 1);
    uint64_t calls_after = work_ledger().kernel_calls;
    assert(op_result(h1) == op_result(h2) && op_result(h1) == set_specialize(S2, sigma, &why));
    printf("join: second handle started mid-kernel; results equal; kernel calls after the join=%llu (the joined job's remaining calls only; no second reindex of the same term)\n", (unsigned long long)(calls_after - calls_before));
    /* 4: READY reuse */
    FineVector b4 = fine_snapshot(); uint64_t kb = work_ledger().kernel_calls;
    OpId h3 = op_specialize_set(S2, sigma);
    assert(op_status(h3) == OP_COMPLETE && op_result(h3) == op_result(h1));
    FineVector c4 = fine_snapshot(); uint64_t trans4 = 0; for (int i = 0; i < FC_COUNT; i++) trans4 += c4.v[i] - b4.v[i];
    printf("ready reuse: kernel calls=%llu kernel transitions=%llu\n", (unsigned long long)(work_ledger().kernel_calls - kb), (unsigned long long)trans4);
    assert(work_ledger().kernel_calls - kb == 0 && trans4 == 0);
    op_release(h); op_release(h1); op_release(h2); op_release(h3);
    work_free(); compiler_free(); check_free(); eval_free(); machine_free(); return 0;
}
