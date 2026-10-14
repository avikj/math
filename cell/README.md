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
  - **Evaluation is interaction.** Operation agents meet data agents, and each firing is one finite payload computation.
    - `EVAL ⋈ REF` keeps one entry per `(reference, ambient face projected to its dimension support)`, either running with its waiters or ready.
    - `PUBLISH` resumes the waiters.
    - A disjunctive face goes to a `JOIN` that takes its clause results in any order.
    - Eliminators wait on their scrutinee's head through continuation agents.
    - `TYPEOF` reads the type off a neutral, so every neutral path at an entailed endpoint gives its endpoint.
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

Run: `cell core.cell examples.cell`. Each `eval` prints a normal form and its length, the number of interactions. Read-back is a fold that demands evaluation and adds no interaction of its own.
