# cell: CCHM on instantiated cell references

- `SCOPE.md`, `EVALUATION.md`: the owner's specification, verbatim.
- `cell.c` is the machine.
  - **Scope subsystem**, as specified:
    - origins are immutable construction records;
    - a reference is `VAR(x)` or `VIEW(origin, σ|FV)`, interned;
    - `reindex` acts on references, never on bodies;
    - intervals and faces are normalized DNF, with entailment, ∀ and projection;
    - binders are instantiated from `(owner, slot)`, shared by every field the slot governs;
    - `open` exposes one constructor.
  - **Evaluation**: one entry per `(reference, ambient face projected to the reference's dimension support)`.
    - A disjunctive face is evaluated clause by clause.
    - Results never overwrite the reference.
  - **Reductions**: the CCHM rules:
    - application, projections;
    - path application, endpoints first;
    - Glue, glue and unglue at an entailed face;
    - systems by coverage;
    - comp: coverage first, otherwise the family's head at the fresh instantiated dimension;
    - the Π, Σ, PathP, Glue (six stages) and U clauses, built as cells from the component references.
- `core.cell`: `Contr`, `fib`, `Equiv`, `idEquiv`, `lineEquiv`, `ua`, path operations, singleton contraction, the identity agent's forward and backward bodies, wire elimination, handles, cut and difference.
- `examples.cell`: no numbers.

Run: `cell core.cell examples.cell`. Each `eval` prints a normal form and the number of evaluation entries it computed.
