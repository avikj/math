# cell: the scoped cubical machine

The specification is the owner's handoff, `HANDOFF.md`. It refines the owner's documents `SCOPE.md` and `EVALUATION.md`.

## Files

- `cell.c`: the machine.
  - **Scope (§§2–9).** It provides:
    - immutable origins with required face and annotation;
    - references `VAR` / `VIEW(origin, σ)`, with σ restricted to the typed boundary and interned;
    - `reindex` and `compose`;
    - interval and face DNF with entailment, `∀` and projection;
    - universe levels;
    - binders from (owner, slot, sort);
    - `open`.
  - **Evaluation (§§10–12, 26).** The cache is keyed by (reference, face projected to its support).
    - It has one evaluator task per key.
    - Delivery is counted uniformly as REQUEST / EVALUATE / PUBLISH / DELIVER / RULE / JOIN.
    - A worker pool runs with quiescence (`-w N`, `-p lifo|fifo|random|mixed`, `-s seed`).
  - **Composition clauses (§§13–17).** Π, Σ, PathP, U, Glue, and systems of type families (`∀j` guards).
    - Each shared filler is built once as a line, and its endpoints are reindexed from it.
  - **Checking and conversion (§§33–34).**
    - Outcomes are VALID / INVALID / UNRESOLVED.
    - Conversion uses eta for Π, Σ, Path and Glue, and compares neutral spines structurally.
    - A view is typed by the substitution lemma.
  - **Ownership and teardown (§36).** A stuck workload is torn down, not published.
  - **Comparison dump (§37):** `-d FILE`.
- **The identity compiler (§§39–48).** It handles five declaration kinds:
  - `identity`: typed diagrams `left { x e : A = t ; … } o`, `right { … } o`, `by p`, with optional `under φ`;
  - `equivalence`;
  - `residual`;
  - `cutpath`;
  - `contractible`.

  Each declaration is compiled as follows.
  - **Validation:** the diagrams and evidence are checked, and the realization telescopes are folded.
  - **Emission:** the singleton collapse/expand maps (`down`, `up`) and `F_P` / `B_P` are emitted as fixed core templates, together with a proof-parameterized graph-pair template.
  - **Certificate:** the bodies are checked at their types, and a structural certificate re-emits them and requires identical references.
  - **Publication:** only then is the record published. `reject <declaration>` must fail and publish nothing.

  Calls are `apply T forward|reverse params… r` and `applyp T dir params… proof r` (the latter puts a given path in the proof slot, which gives higher coherence).
  - A call is a `TRANSFORM_CALL` instruction. The evaluator handles it with `APPLY_TRANSFORM`, then `CONTINUE_REFERENCE`, then an ordinary request.
  - These events are counted as their own classes.
- `cellcmp.c`: exact comparison of two dumps modulo renaming of generated identities, by backtracking.
- `core.cell`: the level-parametric library: `fib`, `Equiv`, `idEquiv`, `lineEquiv`, `ua`, path operations, and more.
- `examples.cell`: example evaluations.
- `checks/`: the §38 and §47 checks.
  - `checks/transform.cell` holds compiler verification cases 1–11. `checks/run.sh` runs them all.

## Running

```
cell core.cell examples.cell
cell --selftest
checks/run.sh
```

Each `eval` prints its normal form and two event vectors:
- its evaluation, from an empty cache;
- its admission (elaboration and checking).
