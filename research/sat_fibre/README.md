# SAT, coinductive fibres, and interaction costs

Start with [the research report](REPORT.md). It connects the checked theorems, runtime measurements, exact-count predictions, and their remaining proof obligations. [TSP work](../tsp_fibre/README.md) develops weighted loop reduction.

[Clause geometry](CLAUSE_GEOMETRY.md) derives the excluded-cylinder algebra, conditional information law, obligation representation at variable cuts, and the different optimality questions for sharing, factoring, and interaction counts. These are written mathematical derivations grounded in the existing modules, not additional kernel-checked proofs or runtime measurements.

[Reduction foundations](REDUCTION_FOUNDATIONS.md) connects that algebra to proof complexity, derives local HVM interaction/allocation costs from the runtime source, and explains the two new checked boundary and representative-family modules. [Their proof receipt](boundary-proof-verification.md) records commands and source hashes separately from the earlier four-module receipt.

[Directional synthesis](DIRECTIONAL_SYNTHESIS.md) preserves the project-level direction: the universal fibre is already present; SAT work instantiates its shared Boolean boundary and makes the geodesic cost receiver explicit.

Safe Cubical Agda modules:

- `SATFibre.agda`: reproduction, carried observation, retained future, residual-state exactness.
- `SATBoundary.agda`: arbitrary clause-cut equivalence, dominance, concrete witness reconstruction, and the fibre retaining discarded assignments.
- `RepresentativeContinuation.agda`: cheap XOR-span certificates preserve attained minimum costs and produce compatible representatives for every continuation.
- `ColorFrame.agda`: reversible colour-frame representation and invariant verdict.
- `InteractionGeodesic.agda`: equal complete reduction lengths under an exact one-step diamond.
- `../tsp_fibre/TropicalReduction.agda`: minimizing reduction with retained witness, common-continuation dominance, and comparison counts.

From the repository root, with Agda 2.8.0.1 and Cubical v0.9:

```sh
agda --safe --cubical --guardedness --no-import-sorts -WnoUnsupportedIndexedMatch --no-libraries -i research/sat_fibre -i formal/cubical/theorems/physics -i /path/to/cubical-v0.9 research/sat_fibre/SATFibre.agda
```

Use the same include directories for `ColorFrame` and `InteractionGeodesic`. For `TropicalReduction`, replace the local include/file by `research/tsp_fibre` and its module. No new postulates or unsolved holes are used.

The Python programs have `--help` describing runtime/compiler arguments. `experiment.py` validates small Boolean cubes; `check_bend.py` compiles the continuing SAT client; `build_profile.py` produces an instrumented copy of HVM; `np_experiment.py`, `cost_predictions.py`, and `color_experiment.py` reproduce larger measurements. Predictions, generated `.hvm4` sources, raw logs, and JSON results are retained. Profile budgets intentionally leave some cases inconclusive.

`audit.py` checks stored results, rule totals, certificates, generated TSP sources, and predicted counts without rerunning the full benchmark suite. `verification.json` records that audit and source hashes. Runtime and compiler hashes are in the individual receipts. `proof-verification.json` records fresh successful Agda exits, commands, and source hashes for all four modules; check logs accompany them. Across all suites there are 285 cases: 262 completed and 23 explicitly budget-inconclusive.
