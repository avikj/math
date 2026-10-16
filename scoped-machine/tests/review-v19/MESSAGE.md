**Review of v19 / 5a8e0db, including allocator commit 41cc22e — corrections supplied.**

Preserve the allocator, Paged representation, cursor-based syntax enumeration, framed graph discovery/Tarjan, incremental tables, and all previously accepted engine work. The submitted tree has two reproducible proof-use regressions and allocator retirement defects. `v19-corrections.patch` corrects these locally; it does not replace the construction. Apply it, gate the accompanying regressions, and then continue the already-authorized kernel lowering. The scope of that work does not require another permission round.

**R1 — restore the complete proof-use judgment before dependency classification.**

Expected (§88 and the existing `proof_use` implementation): admission, context validity, expected-type formation, and evidence checking precede a CORE/ASSUMED/PENDING verdict, including false-face and memo-hit cases. A dependency graph is the next part of that check; acyclicity does not establish typing.

Observed: `audit_transform_request` extracts evidence, then the new `step_audit` immediately classifies dependencies. None of those four prerequisites runs. `audit_request` infers the evidence but likewise omits the other proof-use prerequisites.

Reproduction, `review_v19 audit-admission`: compile a transform using an opaque equivalence; open a candidate environment and give that symbol the body `U0`, which is ill-typed at its declared equivalence type; prepare a connector using the transform *before* calling the synchronous oracle. Submitted tree: preparation succeeds and reports CORE; `transform_proof_use` reports INVALID. Patched tree: preparation rejects INVALID. Calling the oracle first would mask the missing admission boundary.

The patch restores the four prerequisites as four distinct, charged phases before any audit result is reused or constructed. INVALID and UNRESOLVED reject with their respective diagnostics. These remain opaque kernel calls pending the existing continuation-lowering assignment; no unit invokes two of them. Do not restore the old whole synchronous dependency audit inside a unit.

**R2 — isolate traversal state by audit judgment and share its producer.**

Expected (§§75–79, §88): different proof-use judgments have their own discovery/Tarjan state; results retain every required assumption and dependency. Requests for the same judgment share running work.

Observed: all private AUDIT frames inside one PREPARE use the PREPARE job id for discovery and Tarjan marks. The second audit treats symbols discovered by the first as already visited, then publishes its own incomplete verdict. This is not merely redundant-work accounting: it can erase assumptions.

Reproduction, `review_v19 audit-marks`: prepare an alternative containing two distinct evidence terms, `ax` and `(λz.z) ax`, where `ax` is opaque. The combined result contains `ax`. Prepare each evidence separately using different plan atoms so that each judgment's verdict memo is reused. Submitted tree: assumption counts `1 / 0`, CORE flags `false / true`; patched tree: `1 / 1`, both ASSUMED. The submitted tree also fails the previously accepted `review_assumption_copy both` regression.

The patch makes AUDIT an ordinary shared job keyed by `(family, context, face, evidence, expected type, checker session, environment version)`, using the existing JOIN protocol. Traversal marks now belong to that audit producer. Completed dependency verdicts retain their existing judgment/revision memo, enabling reuse after the prerequisites in another session. SYMS/EDGES remain internal traversal helpers here; their completed-result memos are retained. SYMS marks now mean *active ancestor*: they are cleared on completion, including context nodes without a completed-result memo. No sequence number is added to mathematical result identity.

`review_v19_work audit-sharing` interleaves two different preparations using the same judgment: one AUDIT producer, correct assumptions in both results, at most one audit frame and one kernel call per unit. The prior two-audit test again copies 65 + 65 assumptions, one per unit, and produces the exact 66-symbol union.

**R3 — finish Paged retirement correctly and service it through both drivers.**

Expected (§§89/94): every retired data/directory page is eventually returned, at most one page per reaping unit; an initialized empty buffer remains reusable; synchronous driving performs the same maintenance as bounded driving.

Observed and reproduced:

- `review_v19 arena-directory`: 262,145 word pushes allocate 513 data pages and cross into `dir2`. After complete retirement the submitted allocator has returned 512 words fewer than it allocated: one directory page is lost. `dir2[0]` is unused, but retirement scans from it as if it were a null-terminated list. The existing 100,000-push test reaches only 196 data pages and cannot see this.
- `review_v19 arena-empty`: retiring a never-populated initialized buffer destroys `elem/per`, unlike retiring a populated buffer. Reusing it would divide by zero in `paged_push`.
- `review_v19_work sync-reap`: the synchronous set-union driver returns zero retired pages while executing the operation; `run_locked` lacks the per-unit reap performed by `op_step`.

The patch obtains the live second-directory range directly as `(pages - 1) / PAGED_DIR`, releases indices from that value down through 1, and never reads unused directory entries. It preserves the empty buffer's element configuration and adds the same one-page maintenance step to the synchronous driver. The 513-page test now returns all 264,192 allocated words; empty-buffer reuse works; synchronous union reaps pages during execution. Directory retirement remains constant work to enqueue and one page per reap.

**Two necessary changes to the existing audit probe.**

`review_audit_budget.c` changes only as required by R1: the cached-verdict bound becomes `N + 9` instead of `N + 5`, accounting for exactly the four restored prerequisite phases; the dependency scan remains N+1 revision checks with no syntax traversal. Before changing the root body, the probe now explicitly opens a new candidate environment, because preparation correctly freezes admission. Neither adjustment weakens a semantic expectation. At N=256 the corrected cache case takes exactly 265 audit units; the cyclic replacement still rejects PENDING.

**Independent evidence and scope.**

The supplied patch passes all 16 focused jobs under ASan/UBSan and TSan, including the four new public reproductions, synchronous maintenance and interleaved sharing, all three v17 assumption-copy modes, the existing allocator/audit probes, store interleaving, boundary depths 64/4096, production work (217 checks), and production proof-use (21 checks). The four core new reproductions fail on the submitted tree under both sanitizers. The additional original-tree results and complete candidate results are included as JSON.

Changed production modules (`arena.c`, `proof.c`, `work.c`) were compiled anew; unchanged modules used independently built sanitizer objects after source-byte comparison, not worker-shipped objects. Independent ASan used `detect_leaks=0`; the worker's LSan/full-gate results remain supplied evidence. Arena page balance is asserted directly because an internal arena leak need not be reported by LSan. The long full gates were not repeated here.

The portable runner defaults to a fresh build of every production source:

```sh
patch -p1 < /path/to/v19-corrections.patch
python /path/to/run_v19_review.py . --sanitizer asan --detect-leaks 1 --output v19-asan.json
python /path/to/run_v19_review.py . --sanitizer tsan --output v19-tsan.json
```

Keep the three review C files beside the runner. Integrate the new modes into both existing full gates, then run those gates. The two patched production files and the probe patch are the complete proposed source changes in this review.

**Next implementation work — proceed without another authorization request.**

1. Complete the allocator obligation for the remaining fixed-size records and Chunked storage reached from units. A constant-size `calloc` request does not establish a bound on the host allocator's internal instruction count. Route those allocations through the bounded arena/backend, with matching ownership/release and bounded initialization, or retain an explicit host-allocator assumption. The current README's unconditional allocator refinement claim is stronger than the implementation. The patch above repairs correctness but does not replace these remaining host calls.
2. Continue persistent bounded continuations through the transitive kernel work already listed: reindex/compose, face substitution, structural validation, shape construction and producer lookup, evidence extraction, inference, admission/context/formation/checking. R1's restored prerequisites belong on that same list. Preserve semantic keys, typed scopes, revision checks, all proof-use outcomes, and existing reuse behavior. A wrapper that counts one recursive call is not this lowering.
3. Give every input-dependent traversal a stored cursor/stack and one bounded transition; requests for a semantic suboperation must join its producer. Retain the same frame after budget exhaustion. Publish only after every prerequisite/result is complete. Keep synchronous APIs as drivers of the same continuation wherever they enter this work, rather than maintaining a second mathematical implementation.
4. For each lowered family, gate cold large inputs with budget 1, full completion against its existing semantic result, a second handle joining running work, a READY reuse case, and relevant invalid/revision-change cases. Instrument actual node/edge/probe/copy/allocation work; do not hide it behind a `kernel_calls` increment. Fixed architecture-bounded loops need no arbitrary one-instruction splitting.

The existing mathematical construction and the previously accepted engine lowering remain the basis. This review corrects regressions introduced by the new audit/allocator code and continues the two previously assigned implementation categories. It adds no search mechanism and makes no new claim of whole-machine completion.
