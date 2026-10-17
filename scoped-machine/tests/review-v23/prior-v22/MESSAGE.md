Subject: V22 reviewed — four prefix corrections supplied; continue the cumulative assignment

V22's live-prefix fix works. I independently reproduced the original
specialization/restriction cases with zero/four workers under ASan/UBSan and
TSan. The production prefix suite also passes. Keep this construction.

I found and implemented four integration corrections in
`prefix-integration.patch`:

1. Committed facts remain usable after their source becomes READY, including
   when the final observation is stale but the fact's own premises still hold.
   Lookup also considers applicable older facts.
2. A late subscriber receives existing facts. Publication captures its old
   subscriber interval; registration captures the old immutable fact list.
   The two snapshots cover each fact/subscriber pair without duplicating it.
3. An adapter inherits the selected derivation's revision premises before
   publishing its prefix or requesting its residual. They survive in the
   eventual final answer as well.
4. Pending joins expose separate guarded branch facts. Their premises exclude
   unrelated siblings, their notifications never dereference an unowned
   Gather pointer, and composition-family propagation uses the universally
   quantified guard along the bound dimension.

`REVIEW.md` gives expected/observed behavior, causes, receipts and evidence.
`review_v22.c` / `run_v22_review.py` provide the regressions and positives.
The patched runner passes 17/17 jobs under each sanitizer, including the
publication/subscription race, guarded branch reuse and the bound-dimension
control. The previous V20 runner also passes 19/19 under both; the review
documents the exact patch stage and build method for those runs.
Review-host leak detection was off; retain your LSan gates.

Apply/port this patch onto your ongoing corrected tree, and gate the new
runner under both sanitizers. Do not reset your tree to V22 or undo the
already progressing V21 corrections. V22 answered the earlier foundation
handoff; the five subsequent V21 findings remain cumulative and are preserved
in `prior-v21/`, including the tested allocator patch.

`LIVE-CUT-ADOPTION.md` specifies the remaining already-running-target
integration: owned logical request slots, immutable prepared proposals,
generation-checked installation, exactly one semantic resume, and ordinary
delivery/ownership accounting for superseded tickets. It includes the exact
race outcomes and eight integration cases. Implement it in the existing
continuation path. It requires no plan-space search and does not cancel
shared work or erase executed events.

Everything in `IMMEDIATE-SCOPE.md` remains in immediate scope. Continue the
existing bounds, actual-event ownership, bounded kernel, common witnessed
state, Stokes, effects/authority and end-to-end work in dependency order.
These four fixes are a checkpoint, not a stopping point or another request
for authorization. Author-side mathematical obligations remain the author's
work; neither this patch nor the scope list is a claim that those arguments
have already been completed.

Return the corrected commit, new runner results, cumulative regression
results and full `make test`/`make tsan` gates. Report any exact unsupplied
equation or interface dependency without halting unrelated specified work.
Do not weaken an assertion or claim whole-machine optimality/C-step
refinement from the passing prefix tests.
