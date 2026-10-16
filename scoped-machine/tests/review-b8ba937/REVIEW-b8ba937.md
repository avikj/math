# Review of the attached b8ba937 / v13 delivery

## Decision

The §96 production addition follows the specified construction. Its 85-check
production suite passes independently under ASan/UBSan and TSan. Retain it.
The six findings already reported against ba09e33 remain open and reproduce
against this delivery. This is a §96 increment, not completion of that repair
pass. No new independent defect was found in the added wrapper.

## What was reviewed

I read and extracted the user-supplied `scoped-machine-v13-delivery.zip` and
compared its production sources with the independently verified ba09e33
snapshot. Only `src/runtime.c` and `src/runtime.h` changed: the new constructor
tag, the 26-line `rt_node_fun` definition and its declaration. The original
author `review_runtime_nodes.c` is byte-for-byte unchanged. The source hashes
in both worker-supplied §96 runner JSON files match the delivered source files.

The wrapper binds B, A, t and Q in the core. Its body is the existing extension
term with Q as a bound parameter. Its type uses these exact levels:

```
s = max(a,r)
diagram input level = max(b,r+1)
tail type level = max(a,b,r+1)
diagram output level = max(b,max(a,r)+1)
```

The outer binders for B:U_b and A:U_a use domain levels b+1 and a+1; each Π
codomain annotation is the level of the remaining dependent function type.
The definition and type are built over keyed formals and the body is memoized
per exact level tuple. There is no tail-specific definition or new evaluator
dispatch. This is the requested closed ordinary constructor.

## Independent execution

All production core sources were freshly compiled separately for ASan/UBSan
and TSan. Results:

| Run | ASan/UBSan | TSan |
| --- | --- | --- |
| Updated production `test_runtime` | 85 checks, zero failures, 19.0 s | 85 checks, zero failures, 26.5 s |
| Unchanged §96 runtime witness, zero workers | PASS | PASS |
| Unchanged §96 runtime witness, four workers | PASS | PASS |
| Unchanged §96 mixed-level witness | PASS | PASS |
| Previous work interleave / same-key / growth / drain regressions | All four still fail | All four still fail |
| Previous singleton-level / residual / helper-commutation regressions | All three still fail | All three still fail |
| Previous runtime/proof cold-concurrency regressions | Complete without an ASan report | Both still report races, exit 66 |

The absence of an ASan report on the two concurrency cases does not close the
TSan findings. ASan runs use `detect_leaks=0` because this review host does
not support LSan's process inspection. Worker-supplied LSan results are retained
as their evidence; no independent full `make test` or `make tsan` run is claimed
here. The targeted tests above were actually executed.

## Existing R2 also applies through the new entry point

The supplementary `review_node_level.c` checks `rt_node_fun(2,0,0)` in an empty
context. Its declared type forms correctly at level 3, but its body currently
checks INVALID with `universe annotation differs from the formation levels`.
This is the same previously reproduced `sing_formals` error, reached through
the new wrapper. It is not a seventh independent finding.

A separate candidate changing only the old R2 line makes this exact case
VALID:

```
outer singleton Π codomain level: r+1  ->  max(a,r+1)
```

The original R2/R3 patch also passes `git apply --check` against this delivery.
The attached source snapshot was not modified. Candidate results are recorded
separately from results against the delivery.

## Next worker action

Keep `rt_node_fun` and its tests. Apply the existing R1–R6 corrections from
`REVIEW-ba09e33.md`, beginning with safe interning across suspension. Add the
higher-level wrapper regression as coverage for R2. Preserve the previous
regressions and the unchanged §96 witness. The wrapper's acceptance is an
incremental code-review decision; acceptance of its complete exact-level API
requires the already-directed underlying singleton fix.

No change to the mathematical construction or a new development track is
requested. Completion still requires the already specified interning,
universe/residual/template/lifecycle repairs and the bounded-work refinement.

Run the consolidated follow-up runner against the corrected tree:

```
python3 run_b8ba937_review.py TREE --sanitizer asan --output asan.json
python3 run_b8ba937_review.py TREE --sanitizer tsan --output tsan.json
```

It runs the previous twelve jobs, the higher-level wrapper regression, and
the tree's production runtime suite. All fourteen jobs must exit zero after
the corrections. It fresh-builds by default; `--objects` exists only to reuse
matching core objects during review. The saved independent JSON here comes
from the equivalent twelve-job runner plus separately executed production and
higher-level jobs, with the latter's candidate run explicitly distinguished.
