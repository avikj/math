# Committed prefixes are reusable facts

This specifies the existing §84.2 requirement on the current reference/receipt machine. It introduces no object-language constructor. The host records below implement facts already expressed by the machine's operational reduction relation.

## 1. The judgment being retained

A prefix fact is an immutable, committed judgment

\[
P=(\Gamma,\phi,t,u,\rho,\Delta):
\quad \Gamma;\phi\vdash t\Longrightarrow^* u.
\]

Here `t` and `u` are complete typed references, `ρ` is the finite operational derivation, and `Δ` records the definition revisions and other immutable premises actually used to establish this derivation and its boundary. The fact is neither a WHNF classification of `u` nor a logical proof of every proposition assigned to a partial source program. It may end at another running computation.

The source and target boundaries include levels, scope declarations, required faces and declaration-closed support. Face validity and simultaneous substitution have exactly their existing meanings. A derivation under one face is not available under a weaker face merely because its endpoint is syntactically well formed there.

For unchanged types/declarations, a beta prefix does not acquire a dependency on the future body revision of a global its suffix has not unfolded. A prefix that unfolds that global does acquire the revision. This distinction is what makes a prefix a fact about accomplished work rather than a promise about a future answer. Existing admission and formation premises remain prerequisites; their dependencies also remain where needed.

The minimal record content is:

```
PrefixFact:
    source reference and structural source key
    source occurrence boundary and face
    residual reference and residual boundary
    immutable receipt DAG root
    immutable dependency-certificate root
    committed parent fact(s), where the receipt uses them
```

Store variable-size components as existing shared records. A producer may hold a mutable handle to its latest published fact. The fact itself never changes. Interning is exact structural interning with collision comparison, not equality of digest values alone.

Project the occurrence context to the dependency-closed declarations needed by the judgment, as for existing shared checking claims. Unrelated context weakening does not create a new mathematical fact. Retain the full required face and the actual rule premises; context projection is not permission to drop them.

## 2. Fact construction rules

These are mathematical rules, not permission to traverse whole operands in one C step.

**REFL.** A well-formed reference has a trivial prefix `t⇒t`. It carries no completed reduction work and is not a useful adapter when its key is unchanged.

**STEP.** When an actual operational rule establishes `u⇒v` under boundary `Γ;φ`, commit its rule witness and the premises it used. This operation occurs after those premises are available and before the producer forgets the old cut.

**SEQ.** From committed `t⇒u` and `u⇒v` at compatible boundaries, form `t⇒v`. Retain the two derivations as a DAG. Endpoint compatibility is checked by the same trusted rule/typed construction that formed the second step; never use an arbitrary semantic equality as a definitional receipt.

**CONTEXT.** From `u⇒v`, form `C[u]⇒C[v]` for an allowed congruence context `C`. Capture `C` with its full typed scope, endpoints, guards and declarations. For example, a child reduction `f⇒g` yields `f a⇒g a`; a path scrutinee reduction yields the corresponding path application with the original family and endpoints retained. This lifts a prefix without claiming its child is in WHNF.

**RESTRICT.** If `ψ ⊢ φ`, the same derivation is available under `ψ`, after the ordinary boundary checks. The resulting residual still needs observation under `ψ` before a terminal classification is returned.

**SPEC.** A valid simultaneous map `σ` sends the retained operational equations to `t[σ]⇒*u[σ]` under the instantiated premises. Reindex the receipt DAG as a view; do not replay the original reductions. Preserve rule premises and use the existing receipt interpretation for specialized rules. The specialized target can expose additional reductions or lose a former neutral classification. Therefore do not import a generic WHNF label as the specialized answer.

**FINISH.** A READY answer consists of a committed prefix together with the actual terminal observation at its residual. FINISH adds the observation; it does not retroactively make the prefix valid. Pending work, a budget limit and demand cycles do not enable FINISH.

All applicable source/face/map checks are those of the existing machine. These rules do not weaken proof-use admission, conversion, or structural validation.

## 3. Connection to evaluator frames

The current `forward_rc(target, face, destination, receipt)` is the first mandatory publication point: the destination already knows the finite derivation leading to `target`, even if the request for `target` never returns. Publish that immutable cut before awaiting the suffix. The ordinary final forwarding continuation is retained.

The existing completion path that joins a forwarding prefix with a child's receipt becomes SEQ followed by FINISH. No second semantic evaluation is launched for the already performed prefix.

For a pending eliminator, retain its one-hole context in the continuation. Each committed child prefix can be lifted through that context by CONTEXT. This handles prefixes inside an application, projection, path application, unglue or composition-family observation. Reuse the existing typed eliminator-rebuilding recipes; do not rediscover Glue components by evaluating the whole family at an endpoint.

A composition expansion is published only after its selected head/face premises and constructed output are established. A system receipt retains its coverage and branch premises. An unfinished join cannot claim that all its branches succeeded. Separate branch prefixes can still exist as facts at their own faces.

Represent propagation as bounded producer/consumer jobs. Sharing an unchanged prefix does not allocate a new semantic producer. Notification of many subscribers is a retained cursor with one bounded delivery at a time, not a loop hidden inside a publication lock. Dependency union, receipt interning and scope instantiation use the same resumable operations as the rest of the machine.

## 4. Publication, lookup and concurrency

1. Prepare the prefix record privately through bounded shared jobs.
2. Ensure its endpoints and dependency certificate are complete.
3. Atomically publish its immutable handle in the source's prefix index. Publish no half-initialized record.
4. A reader pins/selects one immutable fact and validates its premises against the reader's snapshot. It does not dereference a later version of that fact through the producer's mutable `latest` handle.
5. If an established source relation or recorded instantiation edge connects the requested reference to this fact, specialize/restrict it, then request the resulting residual normally.
6. Reject a no-progress adapter that would immediately request the same observation key. Do not add an artificial wait on the generic source's final answer.

The destination still evaluates at its own projected face and publishes at its own boundary, as required by §93. Structural/alpha sharing does not authorize returning the source representative's unadjusted boundary metadata. Use the same checked boundary correspondence as ordinary shape sharing and alias publication.

Selection is over already available, indexed facts. It is not plan-space search. The first applicable progress fact is sufficient for correctness; a claim that choosing among several facts is optimal requires the separate exact cost argument. No such claim is needed to close the reproduced prefix bug.

The index walk, candidate premise checks and dependency checks are themselves retained bounded operations. Examining an unbounded list of source references or instantiation edges under one lock would repeat the fine-work defect already being corrected. An unavailable candidate leaves the target free to use its ordinary recipe; it does not cause waiting for an unrequested generic computation.

A source can remain RUNNING after publishing arbitrarily many finite prefixes. A completed fact remains useful while its suffix is pending. Releasing the original client does not retract a fact or make another client's progress depend on that client taking another step. Retain ownership through the fact index and its actual users; reclaim only when those owners are gone.

If the producer advances while an adapter is being prepared, the adapter continues from its selected immutable fact. A newer fact can be considered at a later safe cut. Never splice two moving prefixes together on the assumption that their targets still match.

For already running target producers, a new fact can be adopted only at a committed cut whose source matches that target's current residual, or through a checked connector between the two cuts. Already launched child requests retain their delivery obligations. This contract does not authorize cancellation, retroactive subtraction of work, or replacing one partial result by another merely because their final answers are expected to agree.

## 5. Evidence and work are different readings of the same event

The old beta event appears once in the execution history. A new SPEC/RESTRICT/CONTEXT operation reuses its fact and has its own actual lookup, validation, adaptation and delivery work. Referencing the old derivation does not execute its beta again and does not count that beta as newly performed work.

Do not union proof-reference occurrences and call that the actual event set. Two clients can refer to one fact while issuing two distinct requests and receiving two deliveries. Conversely, a receipt DAG with two references to one performed event must not charge two executions.

Publishing a prefix may add administrative work. Include it in the refined ledger. It does not entitle the implementation to claim the old coarse event vector is invariant under every adaptive reuse policy. This is an existing boundary in §§78.5, 85 and 90, resolved mathematically in `FOUNDATION-ROUTE.md`.

## 6. Acceptance

The supplied C regression fixes the first concrete contract through public APIs:

- `t(i)=(λz. p@i)x`, with recursive `p`, executes one generic beta and remains RUNNING.
- Both `t[i↦0]` under true and `t` under `i=0` return `x` with zero additional beta.
- The source stays RUNNING; its completed-answer accessors still return no final residual/receipt.
- The same assertions hold with zero/four workers. There is no sanitizer error.

The full implementation must also cover the following distinct remaining risks:

1. A beta or projection prefix inside two pending elimination contexts is lifted without waiting for their final heads. The new endpoint can finish after specialization without replaying those rules.
2. A prefix using `g@revision1` is not reused after that dependency changes. A purely structural prefix that did not use the changed body remains reusable when its actual premises still hold.
3. A prefix under `i=0` is unavailable under true. A malformed scope, invalid map image or incompatible declaration cannot enter through prefix adaptation.
4. Two clients specialize the same available prefix: one shared adapter computation where their complete keys agree, distinct consumer deliveries, no repeated source rule.
5. Suspend at every publication/instantiation/delivery phase. Resume without losing a prefix, replaying a committed rule, publishing a partial record, or holding a lock across suspension.
6. An operational receipt involving a recursive program is not promoted into unconditional logical evidence. Independently returned finite proof data uses the existing proof-use audit.
7. A READY source continues to satisfy all earlier reuse and alias-boundary tests. Adding prefix access does not change the meaning of READY or leak a stronger face into a weaker one.

This contract closes reuse of work already performed. It neither forces generic evaluation before an instance nor asks the machine to discover every possible equality before proceeding.
