# Review of b612a07 and next implementation direction

## 92. Review baseline: uniform reuse delivered at b612a07

This amendment applies to `b612a07602bfccdcbb4ce2513ab169721cc38d56`, directory `scoped-machine/`, implementing §§74–82 on `3a0d7c4`. It supersedes the older base named in the v10/v11 implementation directions. Preserve the delivered implementation; apply the corrections below to it. Sections 83–91 remain the subsequent increment, not work the v9 delivery claimed to have implemented.

The author retrieved the exact commit and verified every reviewed source file against its Git blob SHA. The unmodified `make test` passed with ASan/UBSan and `detect_leaks=0`; `make tsan` passed. The nine supplied v9 acceptance jobs also passed under ASan/UBSan. Leak detection was attempted but failed in this host's `/proc` inspection environment, so this review makes no independent LSan claim. The worker's reported LSan result is separate evidence.

The delivery contains substantive implementation of the requested construction: persistent shared operation jobs and continuations, structural alpha/view producer identity, source-independent compiled action records, projected conversion contexts, symbol-revision validity, residual/receipt adaptation, and ordinary proof-parameterized identity actions. These are retained. The review identifies one semantic publication defect and an incomplete bounded-step refinement; it does not replace those mechanisms with another runtime or a search system.

Passing the existing gates did not expose the publication defect. The new review runner reports five failing configurations on the unmodified tree: two alias tests in sequential and four-worker modes, and one work-budget test. Twelve next-increment witness runs pass. The same pattern occurs under ASan/UBSan and TSan.

### 92.1 Exact review evidence

| Check | Result on b612a07 |
| --- | --- |
| Existing complete `make test` | Pass, ASan/UBSan; host LSan unavailable |
| Existing complete `make tsan` | Pass |
| Nine v9 acceptance jobs | Pass |
| Neutral alias stays in caller context | Fail with 0 and 4 actual workers |
| Opposite-face warmups preserve conversion inequality | Fail with 0 and 4 actual workers |
| A budget of one bounds normalization and delivery work | Fail |
| Runtime presentation, singleton inverse proofs, generic diagram actions | Pass with 0 and 4 actual workers |
| Recursive-proof boundary diagnostic and conservative audit module | Pass with 0 and 4 actual workers; confirms the integration requirement remains |
| Coarse evaluator cost counterexample | Reproduced with 0 and 4 actual workers |

The alias-publication candidate patch passes both new alias regressions, the existing 101-check reuse suite, and the existing 85-check checker suite, under both sanitizers and with zero/four workers: 16 successful runs. This is focused patch validation; the worker still runs the complete gates after applying it. No production branch was modified or pushed by this review.

## 93. R1: residual aliases must publish results at their own boundary

**Affected contract:** §§10–12, 76.3, 78.1–78.5. **Affected implementation:** `src/eval.c`, `publish_with`, the residual alias branch assigning `a->result = r`.

A source observation may intentionally retain its original neutral eliminator in `EvalResult.ref`. That reference is valid at the source observation's context and face. A residual alias can have a smaller free boundary and a weaker projected face. Copying the source result pointer into that alias transfers the original expression to a boundary at which it need not be scoped or convertible to the residual.

### 93.1 Scope reproduction

Let `A : U`, `a : A`, `f : A → A`, and introduce an additional variable `z : A`. Evaluate

`source = ((λw:A. f) z) a`.

Its neutral residual is `f a`. The source's returned neutral reference is the original `source`, which still mentions `z`. The current alias publication stores that same result pointer under the key of `f a`.

A later `observe_checked` of `f a` in the smaller context containing only `A,a,f` returns success but returns a reference mentioning undeclared `z`. Checking that returned reference in the requesting context reports `INVALID: unbound variable`.

`review_alias_scope.c` reproduces this using valid input terms. Its expected exit status after correction is zero. It currently exits one, with `escaped_z=1` and `returned_term_check=INVALID`, under both sequential execution and four workers.

### 93.2 Conversion reproduction

Let `f,g : A → A`, `a : A`, and `p : Path (A → A) f g`. Define

`source(i) = (p @ i) a`.

In a generic context, `f a` and `g a` are distinct neutrals: `convert_term` initially returns `UNEQUAL`. A propositional path between `f` and `g` does not make these terms definitionally equal.

Evaluate the same source reference under `i=0` and under `i=1`. Its respective residuals are `f a` and `g a`. The current code aliases both residual keys to neutral results retaining the same original `source(i)` reference. After these warmups, conversion of `f a` and `g a` under `true` returns `EQUAL`. Cache history has changed the answer of conversion.

`review_alias_faces.c` reproduces this. Before warmup the enum value is `CV_UNEQUAL=1`; after warmup it is `CV_EQUAL=0`. Both aliases return the same face-specific original reference. This is a semantic error, not just a difference in printing or allocation.

### 93.3 Required correction

An alias answer must describe the residual in the alias entry's own boundary. Preserve the original producer's result and its receipt. Publish a distinct immutable result descriptor for the alias:

```c
a->result = r->cls == R_SYSTEM
    ? result_system(residual, r->nbr, r->faces, r->terms)
    : result_new(r->cls, residual);
a->residual = residual;
a->receipt = rc_refl(residual);
a->is_alias = true;
```

Keep the existing dependency copying, occurrence validation, projected-face calculation, single-producer locking, and alias-without-PUB convention. The patch supplied with this review makes exactly this change. The source-specific original expression belongs in the source result/provenance, not in the alias's semantic head.

The publication invariant is: the returned head and every retained system branch must be well scoped at the receiving entry's boundary, valid under its face/branch guards, and represent the receiving residual there. Equality of result pointers across different keys is not required. Repeated demands on one key still receive its single published answer.

Do not disable residual sharing, strengthen every alias to the source's larger boundary, add global cache clearing, or change conversion to conceal the bad alias. Those would discard the requested reuse instead of repairing its result descriptor.

## 94. R2: finish the bounded-step refinement inside work.c

**Affected contract:** §§65, 71, 75.2, 81.1–81.2, 89. **Affected implementation:** `src/work.c` and the README's bounded-helper table.

The worker correctly disclosed unrefined kernel helpers. There are additional variable-size operations inside the families for which the README claims constant-factor refinement. They are not covered by excluding specialization and preparation.

### 94.1 Executed counterexamples

`review_work_budget.c` stages the production NORMALIZE frame and uses public support-operation handles to stage a shared child with multiple waiting parents. It links the actual `work.c`; it does not replace any algorithm with a mock.

| Case | Supplied budget | Charged handle frames | Actual work inside the step |
| --- | --- | --- | --- |
| NORMALIZE, 64 candidates | 1 | 1 | Initializes 64 keep flags; ledger also charges only one frame |
| NORMALIZE, 4,096 candidates | 1 | 1 | Initializes 4,096 keep flags; ledger also charges only one frame |
| Shared support result, 256 waiting parents | 1 | 1 for the servicing call | Delivers to all 256 parents before returning |

The second example is already counted as many alias-delivery ledger events, but executes all of them inside one budget unit. Retrospective accounting alone does not satisfy the suspension contract. The first example additionally hides variable work in a single ledger event. Both occur without calling the term/checker kernel.

### 94.2 Complete the existing frame representation

1. **Normalization and family buffers.** Split keep-flag initialization, survivor compaction, family-plus input copying, and the buffer copy into NORMALIZE into bounded chunks with retained cursors. `fr_sort`, `fr_intern`, and `fr_lookup` also must not synchronously copy a variable payload inside a budgeted frame. Transfer ownership in constant work where it is already exclusive; otherwise copy in chunks.
2. **Delivery.** Store a delivery cursor or queue of pending parent deliveries. Publishing the answer makes a shared immutable result available; each delivery consumes its own bounded work unit. A job whose child is complete but whose delivery is pending must remain schedulable. Preserve one delivery per registered parent and the persistence of jobs after consumer-handle release.
3. **Scheduling and cycle checks.** `enabled_job` and `waits_on` currently walk dependency chains synchronously. Charge and suspend those walks, or maintain an explicit runnable structure with bounded operations and a separately accounted cycle-check job. One unit may not traverse an arbitrary chain before entering the frame body.
4. **Table operations.** A key of eight words bounds key hashing, not the number of collision probes. Inner `job_for`, `intern_sync`, `find_sync`, and `WordMap` calls must respect the bounded interface. Preserve hash/probe/compare/insert state across frames. During incremental growth, preserve a relocation probe cursor as well as a source-slot cursor; moving 32 slots does not bound the collision chains traversed for those slots. Do not force another handle to finish the whole outstanding relocation through `ktab_settle` before it can return.
5. **Allocation and release.** Account for vector expansion, copying, initialization and stack/buffer destruction under the stated allocator model. An amortized total bound and an individual-call suspension bound are different obligations. A bulk realloc/copy or arbitrary-depth `stack_drop` is not a bounded step merely because the total number of words is recorded afterward.
6. **Kernel traversal and new reuse administration.** Retain the previously disclosed work: reindexing, face operations, structural validation, shape construction, dependency validation, lookup and checking. `FR_SHAPE_NODE`, `FR_DEPENDENCY_CHECK` and `FR_RECEIPT` currently occur only in the frame-family enum; semantic `reuse_count` counters are useful diagnostics but do not implement these resumable frame families. Finish their operational accounting where the full-machine C bound is claimed.

The mathematical operations, persistent producer keys, result interning and receipt reuse do not change. This pass refines their execution into the already required bounded machine steps. The contract remains: `op_step(h,b)` advances at most the stated budget of bounded steps and retains the continuation. Hidden unbounded work in child lookup, delivery, allocation or cleanup is included in that contract.

Keep the coarse semantic vector as a projection. Keep actual fine costs even when schedules produce different administrative counts. No search frontier, incumbent, pruning algorithm or alternative-program enumeration is introduced by these corrections.

### 94.3 Correct the test configuration claim

The original author-supplied v9 acceptance sources and v10/v11 standalone witnesses do not read `CUBICAL_WORKERS` or install a worker pool. Setting that variable in their runner did not make those particular binaries concurrent. The production `test_reuse` and other explicit concurrency suites do install workers, so this does not invalidate their concurrency evidence.

The new runner uses `review_workers.c` with link-time wrapping of `eval_init` for the older witnesses, calls `eval_set_workers`, and asserts/prints `eval_workers`. The new alias tests install their own explicit pool. Results labeled `actual_workers=0` mean the sequential caller-driven evaluator; `actual_workers=4` mean four installed evaluator workers. All twelve next-increment witness runs have now passed on b612a07 under both ASan/UBSan and TSan with those configurations. This corrects the earlier author's one/four-worker labeling; it is not a defect attributed to the worker.

## 95. Forward handoff after the b612a07 review

Work from b612a07. Apply R1 first and retain both new negative regressions. Complete R2 as a refinement of the existing engine, keeping the successful reuse cases. The immediate review bundle contains the exact candidate patch, three new C probes, the runner, source manifest, original gate logs, new sanitizer results, and the existing v10/v11 witness sources.

Then integrate §§83–84 and §88 using the delivered v9 mechanisms:

- **Runtime construction:** promote the ordinary-core presentation/diagram constructors and generic identity actions from the supplied witnesses into the implementation interface/templates. The diagrams themselves, as well as their identity proofs and realization arguments, are ordinary computed values. Host-prepared `identity_pair` remains an import/specialization convenience, not a prerequisite for runtime construction. Both forward/reverse maps and their inverse proofs are retained. No new primitive Nat/Bool handler, registry dispatch on a computed diagram, or compile/run phase boundary is required.
- **Mathematical use of evidence:** integrate the conservative proof-boundary judgment with persistent jobs and actual dependency revisions. The same interface accepts supplied and runtime-produced evidence. Preserve its context, face, expected type and opaque assumptions. A recursive proof dependency is pending, not a theorem or a proof of inequality. Preserve executable recursive programs and the existing compiler re-emission check. Audit the original evidence and its expected type when an equivalence is used mathematically; a PAIR head or a terminating forward projection is insufficient.
- **Reuse of those operations:** a suspended audit or constructor operation retains its continuation; a duplicate demand joins it; a completed result is reused wherever its dependency/face premises hold. The standalone audit's whole-environment guard is an integration scaffold, not an instruction to restore whole-environment invalidation to the v9 cache. Reading an opaque declaration's absent body is a revision dependency. A computed finite residual can receive its own audit; discarded recursive syntax does not permanently taint it.
- **Cost:** carry §89 and R2 through these additions. The old coarse-vector witness still gives `(REQUEST,EVAL,PUB,DELIVER)=(2,4,2,2)` for systems storing 2, 128 and 2,048 fields on b612a07. The new budget witness identifies additional work-engine loops. Both are implementation-level evidence; neither is a claim about wall-clock timing.

On b612a07 the recursive-equivalence diagnostic still accepts the program and compiler certificate, executes its constant forward map, and leaves its reverse call stuck. The standalone audit reports PENDING. This confirms §88 is still needed; it does not mean that v9 failed a requirement that had already been implemented. Likewise, passing the ordinary-core construction witnesses demonstrates compatibility and concrete implementability, not that their public library integration already shipped.

No part of this review claims that the complete adaptive diamond, a full fine-step-to-C simulation, or a reflected checker/evaluator has been proved by the passing tests. The author-side obligations recorded in §§85–91 are preserved; they are not discretionary choices for the worker to fill with a planner. This amendment brings the implementation instructions and evidence forward to the actual delivered revision.
