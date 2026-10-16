# v16 review: 87ce33c

## Decision

Accept the reservation correction and the delivered incremental lowering. Previously accepted correctness repairs remain closed. The remaining finding concerns the already-assigned bounded-step execution contract, and a tested local patch is supplied.

Scope: the supplied `scoped-machine-v16-delivery.zip`. The commit label is taken from its delivery message. This review used local archive bytes rather than fetching a Git tree. Comparing production C and header files with the independently built v14 baseline shows exactly one changed file: `src/work.c`. Unchanged modules were linked from the reviewer's existing sanitizer objects after verifying source equality; work.c and the white-box probes were compiled anew. Shipped worker objects were not used.

## Accepted changes and independent evidence

| Check | ASan/UBSan | TSan |
| --- | --- | --- |
| Alternating different records; alternating equal-key requests | PASS, both modes | PASS, both modes |
| Table growth between record copy and publication | PASS | PASS |
| Original R6 table-drain reproduction | PASS | PASS |
| Reservation at payload sizes 64 and 4,096 | 0 payload writes in reservation | 0 payload writes in reservation |
| Store growth probe | 0 words copied in growth setup; 128 relocation units, at most 32 words each | Same |
| New writer/lookup interleaving during store relocation | PASS | PASS |
| Normalize/fanout bounded-step probe | 32 flags and at most 1 delivery per unit | Same |
| Production work suite | 217 checks, 0 failures | 217 checks, 0 failures |
| Production reuse suite | 101 checks, 0 failures | 101 checks, 0 failures |

These are ten passing jobs per sanitizer. Two additional cold-boundary jobs reproduce the unfinished path described below. Both supplied v16 acceptance JSON files separately record fifteen successful fresh-build jobs. Makefile integration of both delivered probes is present in the ASan/UBSan and TSan gates.

Independent ASan runs used `detect_leaks=0` because of the review host's leak-checking constraints. The worker's LSan runs were not independently repeated. The entire long full gate was not repeated; this was a focused review of changed production code and its consumers.

The new interleaving stages a partially copied private candidate, starts a store relocation, advances its cursor into that candidate, and resumes the writer. It verifies that a write behind the cursor updates both blocks while writes ahead of it survive the subsequent relocation. The candidate becomes a readable, findable canonical record while the old block remains live. Its data stays correct after relocation completes. No new semantic defect was observed in these changed paths.

## Remaining PREPARE boundary traversal

Expected (§§75.2, 89, 94): one budget unit performs a bounded body; visiting an input-sized graph retains a cursor or child continuation between units.

Observed: PREPARE phase 0 calls recursive `expr_boundary(f->a)`. Per-node memoization avoids repeated visits but does not suspend the initial traversal. A cold chain of ALT nodes over a valid typed empty expression visits the whole reachable chain in one call:

| ALT depth | Budget | Handle units | Boundary nodes visited |
| --- | --- | --- | --- |
| 64 | 1 | 1 | 65 |
| 4,096 | 1 | 1 | 4,097 |

Both sanitizers reproduce these figures. The reproduction calls the public `op_prepare` and `op_step` APIs; white-box inclusion provides the existing boundary-work counter and the agreed chunk limit. Its failure is a suspension-contract failure, not an incorrect mathematical boundary result.

### Supplied correction

`prepare-boundary.patch` adds OF_BOUNDARY to the existing shared operation families, leaving existing numeric family tags unchanged. Its immutable key is the expression identity. EMPTY and PLAN finish locally; ALT and JOIN request each child through the existing scheduler and then perform their fixed-field compatibility checks. The existing expression-side memo is installed on completion, including an invalid boundary result of zero. PREPARE first awaits the root boundary; subsequent checks read already-established child boundaries without recursion or synchronous interning. The public synchronous `expr_boundary` wrapper drives this same operation.

The patch does not move a bulk traversal into handle creation or impose eager computation at expression construction. It retains the shared-job and dependency-cone scheduling protocol, result identities, expression semantics, and zero-boundary rejection.

Candidate evidence under both sanitizers:

- Both first-step boundary probes pass: zero nodes scanned in the initial scheduling unit.
- The depth-64 preparation then runs to completion one budget unit at a time: at most one boundary frame per unit; correct final boundary; identical second preparation reuses the completed result and performs no new boundary work.
- Production test_work retains all 217 passing checks, including preparation, invalid boundary rejection, interruption, schemas, and end-to-end identity work.

The depth-4,096 candidate probe checks suspension of the initial request; it does not finish the entire large preparation. No claim of that stronger test is made.

## Accurate boundary of the remaining work

1. **Memory allocation.** Bounded record copying and stable chunked offsets are accepted. Arbitrary-sized malloc/calloc/free are still host operations. In particular, `store_begin_grow`, `ktab_begin_grow`, and their release paths do not acquire a bounded C-instruction expansion merely by counting one allocation event. The README's explicit allocator-oracle model is weaker than the required §§89/94 backend. Supply the already-required bounded allocator/arena operations, count growth/initialization/retirement, and retain private-buffer/vector growth as unfinished until lowered. Existing fixed-size chunk sizes are constants; the implementation of their allocator must still satisfy its stated model.
2. **Kernel/audit traversal.** The disclosed reindexing, face/scope/shape work, checker calls, proof-use audit and retrospective reuse accounting remain unrefined. Use persistent continuations through their actual loops; a kernel_calls increment alone is not the required refinement.
3. **Assumption copying.** PU_ASSUMED appends all assumptions synchronously and needs the already-required cursor or ownership treatment.
4. **Cold boundary traversal.** The supplied patch closes the newly reproduced instance of the existing obligation when integrated; it does not claim to close 1–3.
5. **Fixed-size loops.** Architecture-fixed bounds already meet the constant-factor criterion. Do not split set membership or heap sifts merely to obtain exactly one comparison per dispatch. Document the actual sift bound: its counter charges two comparisons per level, so “64 compares” is not the correct literal ceiling; a conservative 128 charged comparisons over at most 64 iterations is appropriate within the stated 64-bit addressable-array domain.

This is a concrete continuation of the existing execution refinement. It requires no change to the calculus, identity construction, sharing semantics, or accepted repairs.

## Bundle contents and reproduction

`MESSAGE.md` is the complete worker handoff. `prepare-boundary.patch` applies at the scoped-machine root. The two new review sources and `run_v16_review.py` are self-contained alongside the target repository's existing tests. `independent-*.json` records delivered-tree results; `candidate-*.json` records the patched work suite and boundary probes. `manifest.json` identifies reviewed source bytes and artifact hashes.

Run:

```sh
python3 run_v16_review.py /path/to/scoped-machine --sanitizer asan --detect-leaks 1
python3 run_v16_review.py /path/to/scoped-machine --sanitizer tsan
```

The runner compiles all production modules from source by default. Optional `--objects` is only for independently established objects matching the exact target source and selected sanitizer. It exits nonzero on any failed test.
