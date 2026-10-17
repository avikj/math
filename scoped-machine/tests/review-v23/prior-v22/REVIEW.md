# V22 review and executable corrections

Reviewed local `scoped-machine-v22.zip`, SHA-256
`2caacda2e9712516f77e662be63e2468a5985141e10386038fcf0941e21f739c`.
The attachment responds to the foundation/live-prefix handoff. It does not
claim to incorporate the subsequent five-finding V21 review. Those findings
remain cumulative; this review does not count their absence as a regression
in V22's stated delivery.

## Accepted progress

The supplied original live-prefix reproduction passes in all eight
mode/worker/sanitizer combinations against freshly built V22 production
objects. A generic beta can remain pending while its endpoint instance
finishes without repeating that beta. The production `test_prefix all`
passes under ASan/UBSan and TSan. Its coverage includes pending contexts,
premises, faces, joined consumers, sequential policies, workers and proof-use
admission. These are independently reproduced results, not just the worker's
reported gate results.

The GLOBAL-shape parameter images and the interner insertion snapshot fixes
are retained. The corrections below change only `src/eval.c` and `src/eval.h`.
They preserve the reference, scope, evaluator, compiler and interaction-net
construction.

## R1 — a fact remains usable after its source finishes

Expected: an immutable prefix is available whenever its own premises hold,
independently of whether its source producer is RUNNING, READY or has an
obsolete completed observation.

Observed: `adapter_candidate` consulted a prefix only for a RUNNING source,
and only the latest fact. Let `g:A` be opaque and
`t = (λz:A. g) x`. Evaluating `t` commits a beta prefix and returns a neutral
answer. Defining `g := x` invalidates the completed observation, but not the
beta fact, which never read `g`'s body. Reobserving `t` repeats one beta in V22.

Correction: snapshot the immutable prefix list regardless of source state.
Try a valid completed answer, then applicable independently valid historical
facts. Do not stop at an unusable newest fact. Each candidate still requires
the instantiated face, required-boundary check and a different continuation
key. Fact lookup does not wait for its source to finish.

Reproduction: `ready-prefix` prints `added_beta=1` before the patch and `0`
after it, with the same correct result. `branch-prefix` additionally requests
both branch faces, exercising a non-latest historical fact.

## R2 — late subscribers must receive existing facts

Expected: publication before subscription and subscription before publication
both make a committed fact available to that consumer exactly once through
this notification protocol.

Observed: after `child = (λz. p@i) x` reaches a pending cut and its notification
jobs finish, requesting `parent = child x` registers a new waiter but never
lifts the existing child fact. The parent has no prefix.

Correction: waiter registration and prefix publication use the same entry
lock. Registration captures the old immutable fact-list head and reserves a
catch-up notification for that one waiter. Publication captures the waiter
count and notifies only that old interval. Catch-up advances one historical
fact per task; ordinary notification advances one old waiter per task.

There are two linearization orders. If publication precedes registration, the
new waiter lies outside the publication's interval and the fact is in its
catch-up snapshot. If registration precedes publication, the fact is outside
its catch-up snapshot and the waiter is in the publication interval. This
proves coverage without double notification of the same pair. If a terminal
answer consumes the waiter first, terminal delivery supersedes notification;
the immutable fact itself remains indexed.

Reproductions: `late-context` changes from `parent_fact=0` to `1`.
`subscriber-race` runs 16 fresh-machine trials per worker configuration,
simultaneously requesting child and parent. Each has exactly one fact.

## R3 — adapters retain the derivation's revision premises

Expected: using a source fact as a premise carries its dependency certificate
into every derived prefix and final answer, even when the residual does not
read the source's globals again.

Observed: with `F := λz. p@i`, the pending prefix of `F x` records the revision
of `F`. An adapter for `i↦j` forwards the specialized residual, but V22 drops
that premise. Its derived prefix has no record of `F`.

Correction: before the adapter publishes any prefix or requests its residual,
install the selected fact's immutable dependencies in the new producer.
A completed-answer adapter similarly inherits that answer's dependencies.
The copy is prepared outside the entry lock; the lock section transfers
ownership into the still-empty direct-read vector. Subsequent publication
unions the residual's actual dependencies as usual.

Reproduction: `adapter-premise` checks both a still-pending specialization and
a specialization at an endpoint that finishes. The fact and the final answer
both retain `F`. The test uses the public `eval_entry_gdeps` API's pair count;
the record's `PrefixFact.ngdeps` is instead a word count.

## R4 — pending joins expose guarded branch facts

Expected: a committed branch reduction is reusable at its branch face while
the overall system join remains pending. It cannot become a total fact.

Observed: `K_BRANCH` notifications are ignored. For
`([i=0 ↦ f, i=1 ↦ f]) x`, with `f = λz. p@j`, both branch betas commit under
`i=0 ∨ i=1`, but the pending parent has neither branch fact.

Correction: a branch continuation stores the entry receipt and its original
READY scrutinee premise. A notification composes that receipt with the child
fact under the intersection of parent, continuation and child faces. It does
not publish the join or borrow premises from unrelated sibling branches.
It also does not dereference the copied continuation's `Gather*`, which could
have been freed by a concurrent final delivery.

The added receipt tag `RR_SYSTEM_BRANCH` records a selected branch recipe
and its guard. It is the existing system-selection/distribution equation
under that guard, after the scrutinee's congruence receipt. It is not a new
object-language type, axiom, native handler or proof-use admission rule.

For `K_COMP_FAMILY`, the child's guard is universally quantified over the
opened composition dimension before intersecting the parent's guard. The
family equation must hold along that entire dimension. An endpoint-only
family fact cannot rewrite the whole composition or expose a locally bound
dimension in an outer fact.

Reproductions: `branch-prefix` changes from zero branch facts to both guarded
facts. Each endpoint instance reuses its matching branch with zero beta
repetition; the original parent stays RUNNING. `comp-guard` includes a
redundant branch guarded by the bound composition dimension: only the two
outer-face facts lift, and no published parent guard contains that bound
dimension. Both tests run with zero/four workers.

## Evidence and its limits

`run_v22_review.py` has 17 jobs per sanitizer: six reviewer modes with zero/four
workers, the four original live-prefix cases, and production `test_prefix all`.
All 17 pass with the patch under each sanitizer. `evidence/final-patch-*.json`
contains the outputs. The runner fresh-builds by default; these executions
used independently freshly built V22 objects with the patched evaluator
object substituted. No other production object was changed.

A final clean-tree verification applied the actual delivered patch to a
fresh source copy, checked the resulting evaluator files byte-for-byte,
and fresh-built every production object through the runner. Those runs also
pass 17/17 under each sanitizer. They are recorded in
`evidence/fresh-patch-asan.json` and `evidence/fresh-patch-tsan.json`.

The prior V20 reviewer runner also passes 19/19 under each sanitizer with the
four corrections. Those runs preceded the final composition-guard tightening;
the final focused suite includes and exercises that tightening. The wider
results are `evidence/wider-*.json`. The original failing observations are in
`new-prefix.json` and `branch-unmodified.json`. Earlier `patch-tests.json`
records the narrower preliminary patch tests; final-patch results govern.

Leak detection was disabled on this review host. These are ASan/UBSan and
TSan results, not independent LSan results. Retain the worker's full
`make test` with LSan and `make tsan` gates after integration. This review did
not rerun the complete Makefile suites.

## Current completion boundary

This patch closes R1–R4, including guarded branch propagation. The already
RUNNING target adoption protocol is supplied in `LIVE-CUT-ADOPTION.md`; it is
not implemented by this patch. It is an exact continuation task in the same
assignment, not permission to defer it.

The V21 allocator, actual wait ownership, exclusive accounting, arbitrary
capacities and teardown corrections remain in `prior-v21/`. The bounds,
common witnessed state, authority, effects, Stokes and whole-machine proof
obligations remain in `IMMEDIATE-SCOPE.md` and the carried contracts. Facts
retained by the live machine index have an owner; machine-lifetime retention
alone is not a new memory-correctness defect or an instruction to invent an
unrequested collection project.

The patch establishes semantic and concurrency behavior of the tested
prefix operations. It does not establish constant-factor C lowering of an
entire evaluator task: dependency walks, copying, index traversal and other
variable-size paths still need the retained, bounded frames required by the
cumulative contract. The presence of `fine_bump` inside a loop is not that
proof, particularly while an evaluator task suppresses suspension.

Nor do these tests establish optimality of every adaptive execution. New
lookups, notifications and adaptation events are actual work. Their exclusive
ownership and cost remain part of the common event ledger. They cannot be
discarded merely because the reused beta is not repeated.
