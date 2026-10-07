# hyperactive — verified status

All modules check under Agda 2.8.0 + cubical-0.9, `--safe`, via `./check.sh`
(run from this directory). The machine is derived ground-up from
`docs/index.html` §5 (the essay's min-steps theorem) and the Laghava cost
dichotomy; nothing is inherited from the deleted net kernel or the bend2 lane.

## Verified (EXIT 0)

- **Diamond.agda** — `RandomDescent` (the essay's §5.13 equal-length /
  geodesic theorem, verbatim: any `(S, Step, diamond)` with the one-step
  diamond has strategy-independent, minimal reduction length); the slot-table
  update algebra; the consuming two-table machine's diamond; the shared-operand
  `Eql` instance (two judgments sharing an operand — the configuration linear
  interaction nets cannot host without an external checker — verdicts by refl).

- **DecTable.agda** — point-update algebra over any discrete index, plus a
  decRec-based batch layer (`find`, `writes`, `find-hit/miss`, `writes-char`,
  `writes-comm`: disjoint-domain batches commute). Built from atomic hit/miss
  so every term reduces (the idiom that beats with-abstraction non-reduction).

- **ListAddr.agda** — the concrete address model `Addr = List ℕ`,
  `child = _∷_`, `Ext = proper suffix`, `depth = length`; discharges the full
  address-axiom interface (child injective in both args, child-ext, ext-trans,
  ext-of-child, child-depth, ext-depth).

- **Spawn.agda** — the batch algebra and the spawning machine over the abstract
  address interface, with the prefix-free occupancy invariant `Inv`.

- **StatusMachine.agda** — THE AGGREGATING DATAFLOW DIAMOND, complete. Cells
  declare `deps` (addresses they read); a cell is active only when pending and
  all deps are `done`; `fire` consumes the site and writes its write-once
  verdict. The one-step diamond is proved with the novel read/write
  non-interference: an available step reads only `done` slots, and a competing
  now-available step writes `done` only at its own pending site, so the reader's
  deps are untouched (Kahn / monotone-dataflow determinacy) — aggregation never
  threatens min-steps. Instantiates `RandomDescent` on `Σ St Fresh`, so
  equal-length + geodesic hold for the aggregating (no-spawn) machine. This is
  the mechanized heart of "native checking is min-steps": `Eql` judgments that
  wait on their children resolve optimally under any schedule.

- **SpawnStatus.agda** — the full spawn+aggregate machine. Skeleton, out-side
  read-safety (`agree`, `reads-stable`), and the pending-side address-domain
  lemmas (`batch-cases`, `batch-nothing` — which also discharge the
  disjointness Spawn.agda left stubbed) all check.

## The page-proved capstone, and the one open mechanization

`MACHINE.md` gives the complete, reviewed proof of the full
spawn+aggregate one-step diamond. Mechanizing it to `--safe` green needs one
model correction surfaced while proving Fresh-preservation:

- The two-table (pending, out) encoding used by StatusMachine is sound for the
  **no-spawn** fragment (there verified). With spawning it needs an extra
  invariant to exclude a freshly-spawned child address that already carries a
  verdict. MACHINE.md's **single three-valued `Status` table**
  (`empty | pending | done`) removes this by construction: a slot has exactly
  one status, so "pending excludes done" is definitional (no `Fresh`
  invariant), spawning targets provably-`empty` children (prefix-free `Inv`),
  and read-safety is "`done ≠ pending`" with nothing to maintain.

So the completion path is: rebuild SpawnStatus on one `Status : Addr → Status`
table; then only `Inv` (prefix-free occupancy) is carried, its preservation is
the MACHINE.md case analysis (child / old-occupied, using child-inj, child-ext,
ext-trans, ext-of-child, ext-depth), and the diamond wires together the already
-verified `writes-comm` (pending), `update-comm` (out), `agree`/`reads-stable`
(read-safety), and `region-disjoint`. Every ingredient is verified or
page-proved; the remaining work is the single-table rewrite and the `Inv`
induction.

## Reproduce

    sh ../setup          # pinned Agda 2.8.0 + cubical-0.9, from source
    ./check.sh           # all modules, EXIT 0
