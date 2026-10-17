# Independent review of scoped-machine V23

Reviewed input: `01-scoped-machine-v23.zip`, SHA-256
`0ed2d5b9940a37314fcfcad620c769fd1591104aaf44e5f0fb24391456855574`.
The input was read from the supplied local upload and retained unchanged. This review does not certify a different GitHub head or an unseen worker branch.

## Decision

The earlier V20 and V21 focused suites pass independently on V23: 19/19 and 8/8 respectively, under ASan/UBSan and TSan. The delivery contains useful substantive corrections: extensible claims/roots/queues, exact numeric storage and arithmetic, an extent allocator, better wait ownership and accounting, and deeper-stack support. Preserve that construction.

V23 is **not yet accepted as the complete implementation**. The new review finds a validation bypass and an omitted deep traversal path, exact-export defects, a teardown resource leak, an unbounded allocator lookup, and remaining word-sized exact-work readings. Two source patches are supplied and tested. The other corrections have concrete closure instructions below. The later V22 prefix review remains cumulative; V23 predates those corrections, so their absence is not a new regression attributed to this delivery.

`EFFECT-AUTHORITY.md` supplies the newly requested author-side operational boundary, rather than leaving the worker to invent receipt/authority/transfer semantics. It includes records, admission premises, local replacements, substitution, conservation, network refinement and the integration witness. Its presence is not a claim that its implementation or the whole-machine optimality/reflection proofs are complete.

## R1 — Small-stack structural validation can accept malformed syntax; capture still overflows

**Expected:** structural validation visits every relevant stored field independently of face satisfiability and available native-stack depth. Capture/apply handles arbitrary finite nesting up to actual resource exhaustion.

**Observed:** `scope.c` has, twice,

```c
if (!kstack_low()) val_ref_body(t, v); return;
/* the kstack_run below is unreachable */
```

and the analogous `val_scope_body` wrapper. When the stack is low, neither body runs. The `return` is unconditional. The default positive depth test can report successful validation precisely because the validation was skipped.

Separately, `trav_ref` and `trav_scope_records` are recursive entries with no segment guards. A valid 4,000-deep chain of reference-map images over `f : A → A`, captured/applied on a 256 KiB native thread, overflows the native stack. `trav_scope_records` also narrows the public `size_t` depth to `unsigned`.

**Reproductions:** `small-stack-validation` and `deep-capture` in `review_v23.c`. The former uses the existing malformed nested-scope pattern and checks both validators plus checking under a false face. The latter checks exact reference equality after `capture_scope` followed by `apply_scope`; this is not a normalization benchmark. Original validator results are `valid=1` for both malformed objects; checking the malformed wrapped term under false returns VALID. Original deep capture produces an ASan stack-overflow report and a TSan-process segmentation fault.

**Correction supplied:** `scope-depth.patch` adds braces to both validator guards, adds segment guards to the two missing recursive traversal entries, and keeps depth at `size_t`. Patched small-stack validation rejects both malformed objects; patched deep capture returns the identical original reference. Both sanitizer configurations pass. The patch uses the worker's current segmented-stack mechanism; it does not claim to complete portable explicit-frame lowering or safe destruction of native continuations.

**Acceptance:** gate both negative and positive cases. Preserve the older nested-scope regressions and the positive depth test. A successful deep positive alone is not evidence that the entire syntax was checked.

## R2 — Exact values are lost or replaced by allocation identities in graph export

**Expected:** exact comparison preserves every semantic scalar and annotation, independently of allocation order; full names and metadata are retained.

**Observed:**

| Path | Failure |
|---|---|
| Raw origin level annotations | Decimal values are truncated to 127 characters. Distinct 155-digit annotations compare equal. |
| Scope/result/local annotations | The same fixed-width decimal path is used. |
| Universe payload | The boxed Nat handle is printed as the level, so equal values allocated in different orders export differently. |
| TVIEW `PS_LEVEL` | The environment level is also exported as the boxed handle. |
| Runtime formal provenance | The level tuple is tagged `KW_CONST`, leaving numeric handles indistinguishable from opaque machine words. |
| Long global/template labels and origin metadata | Fixed-size label buffers truncate data. For a long global name the `snprintf` return value can also advance the destination beyond its array; the supplied case gives a false match under ASan and a process failure under TSan. Binder/field metadata after the label budget is omitted. |

**Reproductions:** `canon-tail`, `export-universe`, `export-template`, `export-runtime`, `long-name`. The allocation-order cases fork independent fresh children and allocate the same exact number after different unrelated Nat allocations. Their small, otherwise identical graphs differ on the original exporter. This is a targeted value-preservation test, not a claim that the diagnostic dump is a general canonical graph-labeling algorithm.

**Correction supplied:** `exact-export.patch` exports canonical limb sequences as ordered graph data; handles never stand in for numbers. It uses explicit `KW_NAT` for runtime level provenance, retains optional-level distinctions, exports all binder/field metadata and allocates complete labels. An opaque `KW_CONST` is not guessed to be a Nat by inspecting its high bit. The exact graph matcher itself is unchanged.

**Evidence:** all five new cases pass on fresh patched builds under both sanitizers. The schedule, matching, template, runtime and exact-number suites also pass with the patch. Original numeric values, runtime functions and typing rules are preserved.

## R3 — Closed teardown parks native workers permanently

**Expected:** after the closed-session ownership precondition holds, teardown destroys unfinished private continuations and releases their owned resources. It need not evaluate arbitrary programs to termination. While the machine is live, releasing one consumer must not cancel shared work still owned elsewhere.

**Observed:** `work_free` grants up to `2^20` steps to each eligible started kernel call and repeats the pass only if some call completes. A still-running call is then passed to `kc_abandon`; `kc_shutdown` detaches its thread, which remains parked forever inside `yield_now`, retaining its worker/continuation/native stack. The code explicitly says the record is kept. A finite call requiring only 17 more ticks than that allowance takes this path. The same mechanism retains genuinely pending/cyclic calls indefinitely across machine restarts.

**Reproduction:** `cleanup-long` links a transparent `pthread_create` wrapper that counts actual live native workers, including detached workers. It inserts a deterministic finite test KFn into the existing engine kernel frame and invokes normal closed teardown. Both sanitizer configurations report one native worker retained after teardown. The assertion is **zero retained workers**, not “every finite program must be evaluated during destruction.” It does not depend on `/proc`, timing or a leak detector's treatment of thread roots.

**Required correction:** see `CONTINUATION-AND-COUNT-CLOSURE.md`. Finish ownership-explicit continuation disposal; do not fix this by a larger drain allowance, a different timeout, a detached-thread list, or an unbounded semantic drain of every pending program. An interim finite-drain progress fix is not the complete reclamation fix.

## R4 — Allocator ownership lookup contains an uncounted extent scan

**Expected:** each charged elementary runtime step performs a bounded amount of C work, or retains a cursor for its remaining variable work. Increasing allocator extents must not increase an uncounted helper body.

**Observed from source:** `arena_owns` walks the entire prepended `Extent` list until it finds the address. `kalloc.c:ours` uses it for frees/reallocations. A pointer in the oldest extent requires one comparison per extent, with no retained frame and no fine transition in that loop. “Exact extent index” in the delivery is correct about membership, but does not mean constant bounded lookup. Native pointer relational comparisons should also use the backend's defined `uintptr_t` address model, rather than comparing pointers to unrelated C allocations.

**Required correction:** maintain a bounded-address-depth radix interval index, or expose each visited extent as a resumable charged step at every caller. The index route fits callers that cannot yield under an enclosing lock. A concrete radix construction is given in the closure document. Growth/index publication and any metadata allocation remain accounted; merely caching the latest pointer does not bound older/foreign lookups.

This is a source-confirmed cost-contract defect, not a claimed sanitizer failure. The earlier extent allocator correctness and reuse tests remain useful and pass; they do not bound this scan.

## R5 — Exact arithmetic has not migrated the actual-work readings

**Expected:** exact mathematical work/count readings do not wrap, saturate or turn a large count into a small one. Native diagnostic projections may expose a checked finite-width conversion but cannot be used as the exact value.

**Observed:** `FineVector`, `fine_count`, the reuse counters/scopes, `WorkLedger.frames/by_phase`, `KCont.steps` and several event/step counts remain `uint64_t`/`size_t` accumulators. `fine_bump` and `reuse_bump` wrap by unsigned addition. `counter-wrap` seeds a boundary state immediately before the wrap and takes one real fine transition: the reading becomes zero in both sanitizer configurations. The header's monotonicity contract is therefore not unrestricted. The newly exact `Cost` weights and universe levels do not correct these other readers.

**Required correction:** preserve exact count representations at authoritative readings and keep word projections explicitly separate/checked. Do not call ordinary `nat_add` recursively inside the allocator's own fine instrumentation: that would instrument the arithmetic used to instrument itself. The closure document gives a constant-size-per-event exact representation and a framed extraction boundary. The boundary-injection regression must be adapted to the new exact counter API, with a real `2^64` result and a checked out-of-range word conversion; preserving its old storage type is not required.

## Carried requirements and the new author deliverable

1. The complete V22 review is preserved at `prior-v22/`. Its four prefix fixes, `LIVE-CUT-ADOPTION.md`, and cumulative bounds/foundation materials remain in force. Port the prefix patch onto the current evaluator; do not overwrite V23's wait/accounting changes with an older file.
2. The worker's remaining lock-held sync drivers, vector-copy growth and outer-lock interner probe chains remain actual bounded-transition work. Their disclosure is accurate and is not a completion claim.
3. Segmented stacks can be a useful intermediate implementation. Accept them for the paths actually covered, after R1, without pretending they supply the frame ownership/destruction required by R3 or coverage of every recursive component. The existing explicit-frame contract is still the portable completion route.
4. `EFFECT-AUTHORITY.md` now specifies the requested generic authority/receipt boundary and integration run. Its use of existing typed core payloads and existing scheduler/descriptor operations is intentional. Do not introduce a privileged money opcode or a second effect interpreter.
5. Whole-machine overlap/optimality, general posing and complete reflection remain author obligations in immediate scope. Neither passing these regressions nor adding the effect boundary proves them. The carried foundation document gives the valid contextual/Stokes and cost-defect laws; use those exact statements, not an unproved blanket equal-cost claim over competing choices and shortcuts.

## Validation record and limits

The source patches were applied as patch files to another extraction of the original V23 ZIP, and fresh objects were compiled for both sanitizers. `evidence/fresh-patches-*.json` contains the seven corrected focused cases per configuration. `evidence/fresh-patches-production.json` contains the production schedule/match/template/runtime/exact/deep and prior nested-scope runs. Other evidence files retain the original failures and the independently rerun V20/V21 suites.

ASan uses `detect_leaks=0` on this reviewer host; LSan is unavailable here. No reviewer LSan claim is made. The worker reports LSan passing on its host. ASan emits its standard warning about partial support for `makecontext/swapcontext`; it is retained in logs, not suppressed or treated as an observed memory fault. TSan runs use `halt_on_error=1`. The full worker Makefile gates were not rerun independently in this review; the named suites and focused cases were.

Reproduction commands are in `README.md`. `MESSAGE.md` is the exact worker handoff. No source was pushed to the repository and no message was sent to the worker by this review.
