Subject: foundation review — §84.2 committed prefixes integrated at the producer/receipt boundary; review_live_prefix 4/4 under ASan+LSan and TSan

This round builds on the v20 corrections (previous delivery; README "The v20
review"). Your bundle is kept in `tests/review-foundation/`;
`PREFIX-CONTRACT.md` and `FOUNDATION-ROUTE.md` are at the repository root;
`review_live_prefix.c` and `run_live_prefix.py` are in `tests/` unchanged and
gated (`make test`: both modes × 0/4 workers; `make tsan`: the same).

Your regression, per case (fresh builds through your runner, `tests/acceptance-results/v22/`):
  specialize 0 / 4 workers, restrict 0 / 4 workers — ASan+UBSan+LSan
  (`detect_leaks=1`) and TSan: `semantic_ok=1 source_pending=1
  repeated_beta=0`, exit 0. The source stays RUNNING and its completed-answer
  accessors return nothing.

Functions

- Publication (STEP/SEQ at the forwarding cut): `forward_rc` →
  `prefix_publish(dest, target, receipt, parent, origin)` before the suffix
  is requested. The fact (`PrefixFact` in `eval.h`: source, the producer's
  key face, residual, receipt DAG, (symbol, revision) premises, origin) is
  prepared privately — premises copied one pair per lock section
  (`prefix_copy_pairs`) from the producer's direct reads and its consumed
  READY children, plus the parent fact's premises — and published by one
  release store into the producer's `prefix_head` while it is RUNNING. A
  producer answered meanwhile publishes nothing. Facts are never modified.
- Bounded notification: each fact enqueues a job that delivers it to one
  waiter and enqueues the next (`prefix_notify`, a retained cursor). FORWARD
  waiter → SEQ (`rc_seq(k->prefix, f->receipt)`); application, projection,
  path application, unglue and composition-family waiters → CONTEXT through
  the existing `rebuild_elim` / comp-rebuild recipes (`RR_CONG_*`). A lift is
  made only for a waiter that requested exactly the fact's source reference,
  never back into the fact's origin producer, and never into roots, external
  consumers or join branches. The waiter's copy is taken under the producer's
  lock (constant size); the lift is computed outside it. Notification jobs are
  administrative work counted in `eval_prefix_events`, not evaluator frame
  steps.
- Selection and dependency validation: `adapter_candidate` keeps READY first;
  for a RUNNING source it pins the latest fact with one acquire load, checks
  its own premises (`prefix_valid`, one premise per fine step), then the same
  face entailment, map, progress and required-face checks as the READY path.
  The adapter receipt is `[RC_PREFIX_RESTRICT | RC_PREFIX_SPEC, fact, face |
  map]`; `Entry.adapter_fact` / `eval_entry_adapter_fact` names the fact.
  The instance observes the adapted residual normally.

Contract §6 cases (`tests/test_prefix.c`, gated under both sanitizers)
1. nested: `(((λz. k@i) x) x) x`, pending `k : Path (A→A→A) f2 f2`. The beta
   fact is lifted through two pending applications (8 lifts, 5 published, 13
   notification steps, 1 adapter). The instance (specialized or restricted)
   performs only f2's two betas, from the pinned outer fact.
2. premises: the structural beta prefix has no premise on the pending
   global's body; a prefix through an unfolded global F records
   (F, revision); both validate. A negative revision regression is not
   included: a body revision changes only opaque → defined, and in this
   evaluator a prefix that read an opaque global ends neutral, not pending.
3. face: a fact at j=0 serves the instance at j=0 (0 betas) and is not used
   under true (the beta is performed; the j=0 answer is not used either).
4. joined: two clients of one instance key — 2 requests, 2 deliveries,
   1 publication, 1 adapter computation, 0 repeated rules.
5. suspension/interleaving: FIFO, LIFO, 16 random seeds and a 4-worker pool,
   nested and simple: same answers and beta counts. No dedicated
   kernel-continuation probe suspends at each publication phase.
6. proof use: the audit of the recursive program still answers PENDING.
7. READY sources: every earlier reuse/alias suite passes unchanged.

Two defects found and corrected along the way
- `shape.c`: a GLOBAL view's structural identity omitted the images of its
  declared parameters and dimensions, so `F[i↦0] x` shared the producer key
  of `F x` and joined its pending producer (stuck instead of `x`). The
  images are now part of the shape.
- `intern.c`: the insertion snapshot (count, migration placements) is taken
  in the section that found the chain end. Taking it at the completing
  section missed an insertion between the two (`./build/runtime` caught it).

Not implemented, exactly
- adoption of a newer fact by an already RUNNING target producer at a later
  cut (facts are consulted when a producer starts);
- separate branch facts for a pending system join;
- reclamation of facts before the machine is freed or reset (they are
  retained by the machine, `eval_free`);
- the sites from the previous round's lock audit (`net.c:740` rule
  application, the template-library registration, the synchronous engine
  drivers, `compiler.c` index lookups, wrapped interner sections).
No theorem is claimed from these tests; no native transition relation is
asserted beyond the evaluator's existing rules plus the publication and
notification jobs above.

Results (`tests/acceptance-results/v22/`): `run_live_prefix.py` 4/4 ASan+LSan,
4/4 TSan; `run_v20_review.py` 19/19 and `run_v19_review.py` 16/16 under both;
`make test` and `make tsan` clean (TEST.log, TSAN.log).
