# V23 cumulative review package

Start with `MESSAGE.md` for the worker and `REVIEW.md` for findings/evidence.

| File | Purpose |
|---|---|
| `scope-depth.patch` | Tested validator-guard correction, missing deep traversal guards and full-width traversal depth. |
| `exact-export.patch` | Tested exact scalar/provenance export and complete labels/metadata. |
| `review_v23.c`, `run_v23_review.py` | Independent regressions; fresh builds by default. |
| `CONTINUATION-AND-COUNT-CLOSURE.md` | Exact continuation destruction, allocator-index and count-reading requirements. |
| `EFFECT-AUTHORITY.md` | Newly supplied executable authority/effect boundary, local rules and foundational end-to-end witness. |
| `evidence/` | Original failures, patched fresh-build results, independent V20/V21 results and production-suite outputs. |
| `prior-v22/` | The full preceding cumulative review, including the V22 prefix patch, live-cut adoption, earlier bounds and foundation material. |
| `WORKER-V23-MESSAGE.md` | The input delivery's exact worker report. |
| `STATUS.md` | What this review accepts, supplies, corrects and does not yet close. |

Apply patches at the `scoped-machine/` root, or port them onto a newer worker branch after examining conflicts:

```sh
patch -p1 < /path/to/review/scope-depth.patch
patch -p1 < /path/to/review/exact-export.patch
```

Run the seven cases these patches correct:

```sh
python3 /path/to/review/run_v23_review.py /path/to/scoped-machine \
  --sanitizer asan --detect-leaks 1 \
  --only canon-tail,export-universe,export-template,export-runtime,long-name,small-stack-validation,deep-capture \
  --output patched-asan.json
python3 /path/to/review/run_v23_review.py /path/to/scoped-machine \
  --sanitizer tsan \
  --only canon-tail,export-universe,export-template,export-runtime,long-name,small-stack-validation,deep-capture \
  --output patched-tsan.json
```

Run without `--only` to include `cleanup-long` and `counter-wrap`. Those still fail after only the supplied two patches; their correction is specified, not claimed implemented by the patch. `counter-wrap` intentionally injects a boundary state into V23's old counter ABI; update the injection/read helper when introducing the exact ABI. `cleanup-long` uses GNU link wrapping of `pthread_create` to count actual native workers; its requirement is complete teardown, not arbitrary semantic completion.

Use `--detect-leaks 0` only where LSan is unavailable and state that limitation. `--objects` is an optional speed-up only for matching freshly built objects. The runner excludes work.o because the review source includes work.c for its white-box continuation probe. All input-dependent-depth/quantity tests use finite instances; their accompanying source contracts state the general obligations.

Precedence: the user's cumulative immediate-scope instruction governs disposition. A newer targeted correction overrides the conflicting older implementation description. The older master text is retained as historical specification; including it does not resurrect its superseded caps, planner/frontier instructions or incomplete claims. Do not apply old entire-source snapshots over newer worker code.

This is a cumulative technical handoff, not a claim to preserve every word of all prior conversations. No new file is a substitute for an implementation or proof merely by being included. The ZIP includes no freshly built executables or user-uploaded private image.
