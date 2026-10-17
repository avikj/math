# V22 cumulative review bundle

Send `MESSAGE.md` and this entire bundle to the implementing worker.

* `prefix-integration.patch`: tested changes to V22's `src/eval.c` and
  `src/eval.h`; four prefix integration corrections.
* `REVIEW.md`: reproductions, reasoning, evidence and exact acceptance scope.
* `review_v22.c`, `run_v22_review.py`: 17 jobs per sanitizer, fresh build by
  default. Every job must return zero after the correction.
* `LIVE-CUT-ADOPTION.md`: exact remaining continuation protocol and acceptance
  cases for reusing a newly available fact in an already-running target.
* `IMMEDIATE-SCOPE.md`: cumulative whole-machine requirements. None is
  deferred by this review's focus.
* `BASE-HANDOFF-V22.md`, `WORKER-V22-MESSAGE.md`: the delivered master and
  worker report, retained verbatim as reviewed inputs.
* `prior-v21/`: the complete preceding review bundle, tested allocator patch,
  earlier master, bounds patch, prefix and foundation contracts, runners and
  evidence. Historical messages are historical; this bundle's top-level
  message governs the current handoff.
* `evidence/`: original observations and patch results. Negative original
  results are intentional reproductions, not corrected acceptance results.

From the scoped-machine directory, on V22:

```sh
git apply --check /path/to/bundle/prefix-integration.patch
git apply /path/to/bundle/prefix-integration.patch
python3 /path/to/bundle/run_v22_review.py . --sanitizer asan --output v22-asan.json
python3 /path/to/bundle/run_v22_review.py . --sanitizer tsan --output v22-tsan.json
```

If the ongoing tree has already changed these sites, preserve that work and
port the equivalent corrections. Do not roll back to apply this patch.
The runner defaults to leak detection on; the retained review-host evidence
uses `--detect-leaks 0` and does not claim LSan execution.

Read the current message, review and adoption protocol together. The copied
scope document references its original layout: its `BASE-HANDOFF.md` is in
`prior-v21/`; the carried contracts and bounds patch are in
`prior-v21/carried-forward/`. The top-level V22 master is the newer reviewed
input. Later corrections govern conflicting earlier text.

This is a cumulative implementation/review handoff, not an assertion that
every source in the repository or every historical conversation is archived
here. It retains the complete supplied prior review package and makes its
continuing requirements explicit. Requirements, executable prescriptions,
implemented changes and demonstrated properties are distinguished in the
documents rather than silently equated.
