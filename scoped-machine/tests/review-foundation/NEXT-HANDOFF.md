# Next handoff: preserve the construction; expose committed progress

Reviewed base: `avikj/math`, commit `c365d86`, `scoped-machine/`. This review was performed while the worker continued the earlier V20 and bounds corrections. It does not report on an unseen later commit and does not replace that work.

Finish the assigned progress, retry, bounded-transition, reclamation, arbitrary-finite-container and exact-number corrections. Preserve the cubical clauses, typed scopes/templates, runtime diagrams and identity actions, structural producer sharing, dependency certificates and existing positive tests. No plan search, alternative runtime, special cash agents or new primitive datatypes are requested.

## One additional reproduced conformance defect: §84.2 live prefixes

Let `A : U₀`, `x : A`, `i : I`, and let the operationally typed recursive symbol `p : Path A x x` have body `p`. Set

```
t(i) = (λz:A. p @ i) x.
```

The generic observation executes one beta and then suspends while observing `p`. Its completed prefix is already `t(i) ⇒ p @ i`. At `i=0`, the path endpoint rule returns `x` without evaluating `p`. The specialized demand must reuse the completed beta prefix and execute the endpoint rule; the generic source must remain pending.

On the reviewed base, both term specialization `[i↦0]` and face restriction `i=0` return the correct `x` but execute the beta again. `eval_entry_receipt`/`eval_entry_residual` expose only READY answers; `adapter_candidate` explicitly requires READY. The prefix exists only in the pending forwarding continuation. This is a missing connection in the existing receipt machinery, not an incorrect cubical rule.

`review_live_prefix.c` is the regression, with `run_live_prefix.py` as its fresh-build runner. All eight observations—two modes, zero/four workers, ASan/UBSan and TSan—show `semantic_ok=1 source_pending=1 repeated_beta=1 expected=0`. They deliberately exit nonzero until corrected. No sanitizer error occurred. ASan leak detection was disabled because this review host cannot run LSan; run your normal LSan gates on your host.

Implement the immutable prefix-fact and publication rules in `PREFIX-CONTRACT.md`. Preserve the completed-answer accessors' current meaning: a prefix is not a READY result. Prefix facts own their evidence, endpoints, face, and revision dependencies. Adapt an immutable selected fact, never a moving producer pointer. Do not wait for the generic suffix, count the old beta again, or synthesize an answer for the generic root.

The first acceptance target is the supplied regression. Then cover nested elimination/congruence, dependency revision, face direction, joined clients and resource suspension as listed in the contract. These close an existing requirement of uniform reuse; they do not authorize a new optimizer.

## Integration destination

`FOUNDATION-ROUTE.md` connects the implementation to the user's source, including Stokes, retained fibres, live commitments and cost-changing identities. Its integration requirements are cumulative:

1. A committed interaction has one retained witness, complete boundary and actual work contribution. Results, prefix receipts, dependency information and work readings refer to that same interaction.
2. Pure knowledge can be shared. Authority to perform an effect belongs to the current acceptance boundary; copying proof bytes does not duplicate that authority.
3. A returned or suspended computation retains its outstanding interfaces. Release of a requester is not cancellation of a shared producer or erasure of a committed effect.
4. Schedule diamonds compare independent residual interactions. An identity connecting different-cost realizations retains its cost difference. Do not make arbitrary identity shortcuts diamond-balanced by fiat or charge discarded work negatively.
5. Every claimed elementary machine transition must have the specified bounded implementation. A fixed helper name, a thread handoff or a counter tick around an unbounded task is not that refinement.

For the next delivery, report the new commit, the existing assigned review modes, this prefix regression, and the functions implementing prefix publication/selection, dependency validation and bounded notification. Keep the full semantic and sanitizer gates. State the native transition relation used for any theorem claim; do not infer whole-machine optimality from test results.

Do not interrupt the in-progress correction pass to rebuild the architecture. Integrate this requirement at the producer/receipt boundaries being made resumable, then return the tree for review.
