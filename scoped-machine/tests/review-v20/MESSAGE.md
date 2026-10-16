Subject: Review of c365d86 / v20 — prior corrections accepted; four specific completion findings

The v19 corrections are accepted. I independently built all 24 production C modules from the v20 archive and ran the 16-job v19 runner: 16/16 under ASan/UBSan and 16/16 under TSan. The delivered kernel-budget probe and production checker, reuse, compiler and runtime tests also pass independently. None of these findings asks for a replacement of the cubical construction.

The new continuation/allocator completion claim is not yet correct. The attached reproductions identify four classes of remaining work. Three concrete sites already have a tested patch (`v20-local-fixes.patch`). Apply it, then complete the remaining work below without waiting for another authorization. The patch is deliberately a partial correction, not a declaration that the kernel-wide bound is closed.

Read `BOUNDARY-INVARIANTS.md` alongside this review. Boundary composition and Stokes organize the existing construction. They are not a proposed extra runtime layer. The note records their exact relationship to substitution, identity actions, shared causal work, choices, loops and resource conservation, and how the present findings affect those invariants.

R1 — A continuation's progress must belong to its job, not to its original caller or one global active slot (§§75/77/94)

Expected: a handle services its actual dependency cone. Releasing or ceasing to step another handle cannot strand a completed producer or insert an unrelated kernel call as a dependency. READY publication is part of completing the shared operation.

Observed (a): start a specialization, pause its handle during a kernel call, then drive a different specialization. `step_kernel` phase 0 calls `kernel_grant(W.kc_active)` and returns. When the foreign continuation has finished, `kc_grant` returns zero forever. Only its original owning job's phase 1 clears/publishes it. The second request remains RUNNING after 30,000 steps with `foreign_done=1`. Releasing the first handle does not help.

Correction supplied: help the active owning kernel frame through completion/publication. The patched second request completes in 2,878 steps while the original request remains paused. Both retained-handle and released-handle cases pass. This closes the concrete finished-owner bug.

Observed (b): even with that patch, the single-active-continuation gate runs unrelated work. `independent-cone` pauses a REINDEX job, then steps a separate validation of U0 once. That step advances the first continuation. This is an imposed dependency, not a shared mathematical operand. An unending first computation would exclude an independent finite second computation.

Required completion: retain continuations per job and allow independent jobs to be driven while another is suspended. Serial CPU execution is compatible with this; serializing the entire lifetime of every kernel call is not. A checker wait on another running claim must yield a represented dependency/blocked continuation to the scheduler, rather than blocking the grant handshake or requiring all other kernel calls to wait. Reuse the existing claim/wait-cycle semantics. Preserve shared-key joining and one producer for a given key. Actual shared-table maintenance can remain bounded, charged maintenance; it does not authorize running an arbitrary other query's whole call.

Reproductions: `independent`, `independent-release`, `independent-cone` in `review_v20.c`. The supplied patch closes the first two. The third intentionally still fails: finish it in the kernel integration.

R2 — UNRESOLVED has become a permanent failed work job (§§34/57/59/75/77)

Expected: an exhausted checking attempt is not an invalid mathematical judgment. Increasing the checker budget/new attempt can retry, while completed dependency-valid results remain reusable.

Observed: with checker budget 1, an INFER kernel job returns UNRESOLVED and is set to OP_INVALID by `step_kernel`. After increasing the budget, direct `infer` returns CK_VALID, but requesting the same kernel job immediately returns the old failure. This also occurs through the public `op_prepare` API: after increasing the budget, direct checking of the evidence is VALID while the preparation remains permanently failed. `job_for`/`job_at` reuse the failed job, and the kernel/preparation keys have session/environment but no attempt-qualified treatment of transient outcomes.

Required correction: carry a typed outcome, not just `ok=false` plus diagnostic text. Distinguish settled INVALID from attempt-local UNRESOLVED and unresolved proof-audit outcomes. Apply the checker's existing attempt discipline to the operation layer and propagate it through dependent jobs. On a new attempt, an unresolved result is eligible for continuation/retry; a settled result remains reusable under its dependency conditions. Preserve already completed children. Do not turn all successful semantic records into budget-specific mathematical records. Old request outcomes must not silently become proofs of inequality, and changing budget must not require changing the user's term or reopening the entire environment.

Reproductions: `retry` (kernel job) and `prepare-retry` (public preparation). Both reproduce under both sanitizers; both are outside the supplied partial patch.

R3 — The fine-step boundary still contains input-sized work (§§65/81/89/94)

Expected: every granted fine transition has a proved input-independent bound on its C work. Merely charging a variable amount after a non-yielding region does not implement the budget contract. The actual execution ledger must account for the implementation work, including resumption, lookups, allocation, copying and publication.

Three independent reproductions:

1. Evaluator tasks suppress all yields by incrementing `kc_lock_depth` around `execute_task`. A kernel IS_TYPE request for a variable whose declared type is a system reaches this path. At 32 branches, one unit performs 602 fine increments and opens 64 fields; at 256 branches, one unit performs 3,087 increments and opens 512 fields. At 1,024 branches, one unit performs 12,303 increments and opens 2,048 fields. The result is semantically correct; the claimed unit bound fails. Calling this section 'transition-free' does not make its body bounded.
2. Kernel interner probing remains an unbounded locked loop. A table with 300 ordinary one-word records chosen to collide in the initial bucket produces 301 transitions in a single one-step grant. Fixed key length does not bound probe-chain length. `place` in the 32-slot migration can itself traverse arbitrarily long collision chains; 32 source slots is not a bound on the work needed to place them. The second-lock newcomer comparison and the CAND_MAX fallback also perform variable-length word comparisons under a lock.
3. `term.c:mapb_finish` still calls libc qsort on both variable-sized maps. It is reached by COMPOSE/REINDEX inside kernel continuations. A linker wrapper observes a 65-entry qsort during composition of a 64-entry map; the 512-entry case is also included. This contradicts the statement that only canon/match qsorts remain outside bounded paths.

Correction supplied for item 3: pair-key heap sorting with one bounded sift per transition, preserving duplicate-key/image checking. Both sort regressions pass after the patch.

Required completion for items 1–2 and their transitive helpers:

- Preserve an evaluator task as owned unfinished work across suspension, with its outstanding count, operands and continuation retained until completion. Quiescence/publication must not drop that ownership. Remove the blanket evaluator-task exemption by making its variable work resumable; workers executing the task must use the same accounting discipline.
- Retain interner probe and migration-placement cursors. Hold locks only around bounded inspections/publication. Compare immutable variable-length records outside those locks, with a bounded revalidation protocol if the table/producer changed. A recheck must not fall back to comparing the entire record under the lock.
- Audit all *outer* critical sections, not just the interner's own mutex. For example `origin_intern` holds `M.term_mu` around variable-length interning, `scope_intern` still hashes/interns its full telescope under that mutex, and `check.c:resolve_locked` scans the claim/dependency graph and allocates/clears a claim-sized bitmap under `K.mu`. Their size does not become constant because inner helpers are instrumented.
- Cover uninstrumented bulk helpers too: `words_append` and variable-length memcpys, dependency-list traversal, and other loops between yield sites. The criterion is the body between suspension points, not just the number of counters that happened to be inserted.
- Document a quantitative bound for each maximal non-yielding region and its callees. A maximum observed in the existing f^N(x) probe is not that bound. The test's 128 limit reproduces the delivered gate; raising it without establishing an input-independent bound does not close the finding.

Reproductions: `evaluator-32/256/1024`, `collision-64/300`, `map-sort-64/512`. The collision-64 case is a small positive control. All use actual production functions. The qsort wrapper observes calls and forwards them unchanged.

R4 — Arena ownership/reuse is incomplete (§§19/20/36/89/94)

Expected: once the owner of a buffer/table retires and no live object retains it, its space becomes available again. Repeated executions with the same bounded live state must not exhaust memory solely because dead tables cannot be reused.

Observed (a): the engine's chunked tables use `chunk_from_spare`. A supplied chunk leaves the spare but is not kept in an owning arena list. `chunked_free` skips every chunk whenever an allocation hook exists, then deletes the directory. With the process-lifetime arena, each warmed `work_init`/`work_free` cycle loses 18,432 words (147,456 bytes), even for a trivial set computation. These are dead engine chunks, not intentionally retained kernel results.

Correction supplied: `chunked_free` releases chunks from both existing arena suppliers; the allocator callback contract now explicitly transfers ownership to the table. The warmed lifecycle test reports zero unreleased words after the patch.

Observed (b): `arena_alloc_zero` only advances the upper-half fresh cursor. `arena_release` on that half poisons and discards the block without returning it to any reusable pool. `arena_free` is now a no-op. Allocating and releasing a 4,096-word zero block reports 4,096 words out and zero returned. Even zero live blocks therefore eventually exhaust the finite fresh region.

Required completion: supply reusable zeroed blocks through bounded clearing/retirement work. Keep dirty returned blocks owned until clearing completes; then publish them to an appropriate zero-ready pool. A shortage must request/suspend on that work rather than clearing an input-sized block under a lock. Fresh pages may be an initial fast path, but they cannot be the only supply. Account for every table's chunks and abandoned race allocations. Ensure lifecycle teardown and reuse return ownership correctly.

Reproductions: `lifecycle`, `fresh-retire`. The patch closes only the first. Sanitizer cleanliness does not establish logical suballocation reclamation inside a permanently mapped arena; retain explicit ownership/reuse tests.

Integration and evidence

Apply `v20-local-fixes.patch` at the scoped-machine directory. It touches work.c, term.c, intern.c and a supplier-contract comment in intern.h. It closes R1(a), R3(3), R4(a); it does NOT close R1(b), R2, the other parts of R3, or R4(b).

Run:

    python3 run_v20_review.py /path/to/scoped-machine --sanitizer asan --detect-leaks 1 --output v20-asan.json
    python3 run_v20_review.py /path/to/scoped-machine --sanitizer tsan --output v20-tsan.json

All 19 cases must pass on the completed correction. The runner builds production sources freshly by default. `--objects` is only for a matching independently built object directory. If a necessary change to private continuation fields changes a white-box inspector, retain the same public requests, paused/released-first-handle scenario, and independence assertions; report the inspector mapping. Gate the new source tests, the prior 16-case runner, and the production suites. Keep the same-key mid-kernel join and READY-reuse positives.

Report each corrected case with its actual result, bounds and ownership invariant, not only sanitizer exit status. Keep the README's earlier ~33/~80 transition statements synchronized with the final accounting table. Do not mark the constant-factor refinement complete while an input-sized evaluator task, collision chain, graph scan, sort, copy, clear or hidden host operation remains inside an allegedly bounded atom.

Reviewer evidence is in `evidence/`. ASan/UBSan ran with detect_leaks=0 here: this review host cannot enumerate /proc tasks for LSan (an attempted detect_leaks=1 run fails inside LSan). TSan used halt_on_error=1. The worker's LSan/full-gate results remain separately reported evidence. I did not rerun the entire historical make test/make tsan gates; the independent runs are enumerated in the JSON reports.

Continue on the current construction. Stack-retained continuations are a representation choice; the requirements are retained work, correct dependency-local progress, retryable control outcomes, bounded transitions, and reusable storage. Finish those invariants without introducing another evaluator or another mathematical encoding.
