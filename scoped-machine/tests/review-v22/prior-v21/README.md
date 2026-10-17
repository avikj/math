# V21 reviewer bundle

Start with `IMMEDIATE-SCOPE.md`, then `MESSAGE.md` (the worker handoff) and `REVIEW.md` for exact findings and evidence. The entire intended system remains in immediate scope; the five review findings are not a completion boundary.

`BASE-HANDOFF.md` is the worker-delivered master through §96, included to make the core specification available in this bundle. Apply its later corrections and the subsequent contracts here; historical statements are not permission to restore superseded plan-search or arbitrary-limit behavior.

- `arena-clear-owner.patch`: verified localized fix for R1 only; apply from the source tree with `git apply /path/to/arena-clear-owner.patch`.
- `review_v21.c` / `run_v21_review.py`: eight regression/control modes. All must exit zero on a corrected tree.
- `prior/`: unchanged previous review runner and sources.
- `evidence/`: independent results for unmodified V21, the allocator-patched objects, and the still-pending live-prefix cases.
- `carried-forward/`: previously supplied bounds patch and remaining representation contract, prefix contract/test, and mathematical foundation route. These files are copied unchanged, not newly substituted specifications. Merge the old bounds patch with current corrections; do not overwrite newer code.

Only `arena-clear-owner.patch` is a new production change in this bundle. The remaining findings have precise worker instructions and reproductions; they are not claimed fixed. No repository was committed or pushed by this review.

During explicit-frame lowering, port setup/introspection in the continuation probes to the corresponding job interface while preserving their behavioral assertions. The objective is arbitrary finite retained work and dependency progress, not preservation of pthreads as the final representation.

Fresh-build commands and sanitizer limitations are in REVIEW.md. This review host cannot run LSan; the included ASan evidence uses `detect_leaks=0`. The worker should keep LSan enabled on its supported host.
