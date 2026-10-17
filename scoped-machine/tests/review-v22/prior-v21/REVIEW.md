# V21 independent review

## Scope and result

Input: the uploaded `scoped-machine-v21.zip`, 920,452 bytes, SHA-256 `51eded1060cd03de71ecb17417429f12fb29bbc6fa9f78a679e5da7763fc785b`. The archive does not provide a new commit identifier in its author message; no commit is inferred here.

The worker's previous 19-case review fixes are reproducible on fresh production objects. The new tests target the interaction between those fixes: interleaved retained continuations, ownership of suspended work, accounting, and incremental reuse of storage. They identify five specific corrections. None changes the cubical reduction clauses, scope semantics, runtime identity action, or sharing keys.

| New mode | Required result | Unmodified V21, both sanitizer builds |
|---|---|---|
| `zero-head` | Every returned word zero after a new same-order release | 32 nonzero words |
| `zero-order` | Every returned word zero after a lower-order release | 32 nonzero words |
| `zero-stress` | All 4,000 returned blocks zero, four threads | Assertion failure on nonzero memory |
| `ledger` | Exclusive shape charges equal actual shape work | Actual 19; charged 29 |
| `capacity` | 257 retained continuations complete | Abort at the hardcoded 256 cap |
| `wait-owner` | B's consumer names B's active producer | Names unrelated A |
| `cleanup-wait` | Finite suspended dependency drains at teardown | Timeout after announcing teardown |
| `cleanup-drain` | Same work completes when dependency is driven first | Pass |

Evidence is captured in `evidence/v21-asan.json` and `evidence/v21-tsan.json`. The timeout is 10 seconds in these runs. The control demonstrates that the underlying judgment is finite; inspection of the teardown loop identifies the progress defect.

## R1: a clearing cursor must retain its block

Location: `src/arena.c`, `zero_tend_locked`, `arena_release`, and the shortage branch of `arena_alloc_zero`.

The old state is a set of dirty-list heads plus one `zcursor`. After clearing words 1–32 of A, releasing B installs B as a new dirty head. The next maintenance step uses cursor 33 on B. A new lower-order dirty block has the same effect because each step scans again from the lowest nonempty order. B eventually enters the ready list with its first 32 payload words unchanged. A later allocation zeroes only its link word.

This violates the allocator's contract independently of concurrency, memory capacity, or mathematical input size. Returning dirty pointers or flags as initialized side records can corrupt unrelated callers.

`arena-clear-owner.patch` changes the state to `(active_block, active_order, cursor)` plus pending queues. Selecting a block detaches it from its pending list. One maintenance step clears at most 32 words of that exact block. New releases can change only pending lists. When the cursor reaches the block length, the block enters the ready list, and active ownership is cleared. Word zero is available for clearing after detachment; it is reused as the ready-list link and reset by allocation as before.

The patch also moves the zero-region release's ASan poisoning before unlock. Publishing a released block and only later poisoning it could otherwise poison storage after a competing allocator had made it available again. This ordering repair is included; the deterministic wrong-content repro does not depend on that race.

The shortage check recognizes a matching block already being cleared. The existing synchronous shortage loop remains: its elimination and allocator extent growth are separately assigned in the bounds contract. This local patch deliberately does not claim to close them.

Correctness invariant: every retired zero block is owned by exactly one pending list, the active clearing state, or one ready list. For the active block, all words below its cursor are zero. Ready publication requires the cursor to have reached the block length. Pending insertions preserve both active identity and cursor. Mutex publication preserves exclusive ownership.

Verified: both deterministic cases, four-thread reuse stress, and all 19 previous review cases under ASan/UBSan and TSan. `evidence/allocator-patch-*.json` contains the new modes; `allocator-patch-prior-*.json` contains the previous runner. No other source object was replaced for those patched-object runs.

## R2: dependency edges must denote actual awaited work

Location: `src/eval.c:eval_wait_locked`, `execute`, `whnf`; `src/kcont.c:kc_suspended_in_eval`; the kernel-wait bridge in `src/work.c:step_kernel`.

Reproduction uses three retained continuations. A begins observing one system and pauses inside its evaluator task. B begins observing a different system and pauses inside its task. A third continuation requests B's system. It joins B's running observation, finds no runnable queue item, and waits. The implementation selects `held[0]` from all suspended evaluator continuations, so it records A. Resuming B alone satisfies the third continuation; A was not a dependency.

The scheduler must retain the awaited predicate, such as publication/delivery of this requested entry or root, together with the active task ownership that can advance it. Resolve dependencies through the actual producer/consumer edges. Do not scan for any suspended task and promote it into a causal dependency. If a predicate has several outstanding prerequisites, traversal/selection of them is retained, bounded work. If its result is already available, deliver it; do not wait for unrelated work or global quiescence.

An active task can finish before its enclosing checker/kernel call. Consequently, a wait for that task's publication is not automatically a wait for the entire enclosing job to return. Store and recheck the condition/version when service resumes. Use stable retained handles or equivalent lifetime protection; a stale `KCont *` is not a persistent dependency certificate. Clear/revalidate wait edges when predicates change. Apply the existing cycle rules to newly installed edges instead of bypassing the engine's checked JOIN path.

Acceptance: this three-continuation case must name the actual owner and complete by servicing only the required dependency cone. Extend the gate with shared-child waits, unrelated indefinitely suspended work, a real cyclic dependency, completion before whole-call return, and simultaneous publication/registration. Preserve the previous independent-cone and same-key-join positives.

## R3: exclusive event accounting under interleaving

Location: `src/work.c:KernelMark`, `kernel_mark`, `kernel_charge`, `step_kernel`; `src/reuse.c` supplies the global counters being sampled.

A's marker is captured and A is paused. B performs ten shape operations and completes. A then completes. B charges its ten; A's global before/after difference also includes those ten. The observed total is 29 for 19 actual operations.

Required invariant for each counted class `c` over a fixed observation interval is:

```
sum of exclusive owner charges[c] = number of actual events[c].
```

Joining and requesting a shared producer charge their own request/delivery work. They do not charge a second copy of that producer's already attributed body. Derived views of a ledger may aggregate dependency contributions as sets of event identities, not as repeated exclusive charges.

Record ownership at the event source or carry an exclusive accumulator with the running operation/task. If work executes on another evaluator thread, transfer/retain the appropriate task owner rather than attributing it to whichever root happens to sample global counters. Plain synchronous entry points also need an explicit owner/accounting scope. Global monotone counters remain useful as independent diagnostics. A thread-local counter alone is insufficient for tasks that migrate or are executed on behalf of another operation; ownership belongs to the work.

Acceptance: serial, nested and interleaved executions of the test have identical actual-to-exclusive totals. Include joined consumers and evaluator workers, and verify dependency/receipt classes as well as shape nodes. Interleaving may alter which reuse opportunities exist; it must not manufacture duplicate charges for a fixed set of events.

## R4: remove the newly introduced fixed capacities

Locations:

| Storage | V21 limit | Correct requirement |
|---|---|---|
| `kcont.c:live` | 256 retained active continuations | Storage grows with actual retained work; exact task ownership removes the global scan |
| `check.c:CLAIM_CAP` | `2^24` claim records | Stable, extensible claim records |
| `eval.c:ROOTS_CAP` | `2^24` recorded root occurrences | Extensible trace storage |
| `eval.c:QUEUE_CAP` | `2^24` task-array tail | Segmented queue/storage, reclaiming consumed capacity safely |

The 257-continuation abort is directly reproduced while the host can supply those threads. The other limits follow directly from reservation and append guards; this review does not allocate 16 million records merely to reach them. The queue resets its tail only on becoming empty, so its guard is not simply a bound on simultaneous live tasks.

Integrate `carried-forward/bounds.patch` with the new changes; do not overwrite the corrected V21 code. Its stable full-address-width directories and retained storage rules supply the intended storage substrate. Publish candidate chunks outside the unrelated claim/evaluator locks, revalidate and install them atomically, and retire unused candidates. Do not replace a cutoff with an unbounded copy or scan under a lock.

A fixed number of fields in a primitive rule or a fixed page fanout is legitimate. A fixed maximum number of input-dependent claims, live tasks, or roots is not. The already supplied exact-number and native-stack completion requirements remain unchanged. Enlarging `live[]`, changing `2^24` to another constant, or creating a larger fixed virtual reservation does not close this finding.

Acceptance: 257 retained continuations; multiple growth boundaries for claims, roots and queue with small test chunk sizes; preservation of old addresses/handles and no uncharged copying. Ultimately the explicit-frame driver must retain more continuations without needing one native thread per suspended mathematical call.

## R5: teardown must preserve dependency progress

Location: `src/work.c:work_free`; `src/kcont.c:kc_free`.

The test creates a checking job for `refl(A,x)` before an inference job for that same template instance. It starts inference first and pauses after it has acquired a shared checking obligation. The checking job then suspends on that obligation. Both handles are released. Teardown enumerates records in allocation order, reaches the checking continuation first, and repeatedly grants it in `kc_free`. It waits on the paused inference continuation; teardown never reaches that continuation's later record.

The positive control completes the inference job, then the checking job, then tears down successfully. This separates a teardown scheduling defect from nontermination of the term or its judgment.

Before freeing started continuations, drive their retained dependency graph with the same predicate-aware protocol used during normal execution. Keep referenced task, waiter and claim-owner records live until no consumer can access them. Record order cannot be a progress assumption. Releasing a requester must not cancel a producer used by other live requests.

Whole-machine destruction may discard unreachable pending state under its stated closed-session precondition, but must not attempt to complete a blocked consumer in isolation. Genuinely cyclic pending work also needs finite safe destruction; draining must not reinterpret a cycle as a successful judgment or blindly normalize a divergent term. The already assigned explicit-frame lowering provides an inspectable retained state for teardown; do not add a second evaluator or change the calculus.

Acceptance: `cleanup-wait` and `cleanup-drain` both finish; reverse allocation and start orders; multiple consumers and released handles; pending-cycle destruction; ASan/LSan and TSan. Cleanup must retain the established ownership invariants through final retirement.

## Cumulative next work and completion boundary

The five findings are implementation corrections atop the delivered construction. They do not supersede the previous arbitrary-finite-data and live-prefix handoffs. Those contracts are copied unchanged into `carried-forward/` so the destination is explicit.

The worker correctly leaves the constant-factor refinement open. Its admitted long sections remain: kernel operations under net redex locks, wrapped interner scans under outer locks, synchronous engine/registration/compiler sections, and shortage clearing. Also account for the retained-stack loop in `job_restart_if_stale`: it is reachable through `job_at` from a framed JOIN, so a later attempt must not silently free an input-sized stack in one unit. Use the existing one-frame retirement protocol or equivalent bounded ownership transfer. This is source-inspection guidance for the already assigned lowering, not a new mathematical subsystem.

The implementation route is cumulative:

1. Repair exclusive ownership, true wait dependencies, teardown progress and exclusive event charges, using the tests here.
2. Complete stable extensible storage, exact levels/costs, allocator resource states and kernel frame lowering under the supplied bounds contract. Keep request/retry outcomes distinct from mathematical invalidity.
3. Expose immutable completed-prefix facts independently of final READY publication. V21 still repeats one beta in every supplied live-prefix case; preserve that regression while implementing the existing contract.
4. Connect each committed interaction's witness, complete boundary and actual event contribution. Reuse refers to that same retained fact. Preserve cost differences for identities that change realizations; only appropriate commuting residual interactions form equal-work schedule diamonds.

The fourth item is the Stokes integration already described in the foundation route, not an application layer to bolt on after the runtime. The prefix defect, attribution defect and true-dependency defect are concrete places where that common retained event/boundary discipline matters.

Do not infer global optimality from finite regression coverage, or from the fact that part of the implementation uses interaction nets. The eventual claim must identify the actual machine relation and discharge its local overlap/refinement obligations. No new branch-and-bound search, theorem discovery algorithm or special domain handler is authorized by this review.

## Reproduction and evidence

From this bundle, against the worker's corrected source tree:

```sh
python3 run_v21_review.py /path/to/scoped-machine --sanitizer asan --output v21-asan.json
python3 run_v21_review.py /path/to/scoped-machine --sanitizer tsan --output v21-tsan.json
python3 prior/run_v20_review.py /path/to/scoped-machine --sanitizer asan --output prior-asan.json
python3 prior/run_v20_review.py /path/to/scoped-machine --sanitizer tsan --output prior-tsan.json
python3 carried-forward/run_live_prefix.py /path/to/scoped-machine --sanitizer asan --output prefix-asan.json
python3 carried-forward/run_live_prefix.py /path/to/scoped-machine --sanitizer tsan --output prefix-tsan.json
```

Use `--detect-leaks 0` only on a host that cannot run LSan. Each runner defaults to fresh builds; `--objects` accepts independently built matching objects. `review_v21.c` includes `work.c` for precise access to the existing kernel-job scheduler, so the runner excludes a second `work.o` from linking. It changes no production rule or ownership field to manufacture the failures.

All raw evidence included here distinguishes unmodified and allocator-patched objects. The original previous runner is 19/19 under each sanitizer; the allocator-patched previous runner is also 19/19 under each. The prefix runner has four expected failures per sanitizer. This review does not claim the worker's complete `make test`, `make tsan` or LSan execution as independently rerun evidence.
