# Foundation review and the next concrete correction

Read `NEXT-HANDOFF.md` for the worker-ready message, `PREFIX-CONTRACT.md` for the precise next implementation, and `FOUNDATION-ROUTE.md` for the source-based mathematical route.

The new C regression is a genuine expected failure on the reviewed V20 base (`c365d86`): its specialized answer is correct, but it repeats a beta whose generic prefix has already executed. It is not a request to accept a divergent program as a mathematical proof.

Fresh builds against a supplied corrected source tree:

```sh
python3 run_live_prefix.py /path/to/scoped-machine --sanitizer asan --detect-leaks 1 --output prefix-asan.json
python3 run_live_prefix.py /path/to/scoped-machine --sanitizer tsan --output prefix-tsan.json
```

Both commands should exit zero after the correction. The runner builds production sources and runs term-specialization and face-restriction cases with zero/four evaluator workers. No production patch is included in this review: the worker is already changing the continuation boundaries, so the source test and exact contract are supplied for integration there.

Included evidence:

- `live-prefix-asan.json`: independently built matching V20 ASan/UBSan objects.
- `live-prefix-tsan.json`: independently built matching V20 TSan objects.
- `live-prefix-fresh-asan.json`: a separate fresh production rebuild through the delivered runner.

All runs report the same expected defect, with no sanitizer error. ASan runs used `detect_leaks=0` because LSan is unavailable on this review host. These focused runs do not claim a new execution of the entire historical test suite.

This handoff is cumulative with the existing V20 review and bounds implementation package. It does not supersede their corrections or report on an unseen newer worker commit.
