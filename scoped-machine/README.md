# Scoped cubical machine

C11 implementation of the specification `HANDOFF.md`, scoped and ordered by
the binding plan `PLAN.md`; `INTERNING.md` specifies stepped interning.

    make test    # ASan/UBSan: every suite, then the compiler suite with a 4-worker pool
    make tsan    # ThreadSanitizer: every suite with 4 workers

## The one protocol (`eval.c`, `eval.h`, `families.h`)

Every computation over variable data is a producer keyed by (family, a, b).
Its entry moves U → R → D by compare-and-swap: the first requester installs
the one producer, later requesters push onto a lock-free waiter stack,
publication swaps the stack for READY, and each delivery is its own job. A
producer is a frame: a step function that does a bounded amount of work and
ends in request, call (a subroutine frame), yield or finish. Independent
demands are launched and then awaited in order. Host callers drive a root
key with a host frame (`family_run`, `family_call`, `family_run_budget`); a
budget bounds the work of the root's dependency support. Every family id is
named in `families.h`.

## Records

- One record table (`state.h`, `intern.c`): every record is interned in
  `M.keys` by the stepped interner; the evaluator's entry index is its own
  table.
- Intervals and faces are canonical antichain DNFs (`dnf.h`); their
  operations, and set union / removal / membership, are families (`dnfam.c`).
- One substitution record (`subst.c`): `[(key, sort, value)*]` sorted by
  key, an environment (and every total record: pin sets, context indexes,
  CLOSE contexts) followed by a trailing word. One stepped lookup, one set,
  composition of maps.
- Constructions (`construct.c`): one constructor schema per tag (field kinds,
  binder slots, binder sort, partial positions, role, scrutinee) read by
  every builder. A construction is a node whose field constants are closed by
  CLOSE over (depth, slot) atoms; its reference is TVIEW(node, environment).
- Scopes (`scope.c`, `scopefam.c`): the same binder discipline. One traversal
  engine: CLOSE (identity ↦ slot), APPLY (environment slot ↦ value, lowering
  deeper atoms), RE (a map on free identities), LOWER (∀).
- Templates (`template.c`, `lib.c`): fixed library programs interpreted by
  families; a call and a scope application build one argument environment.

## Judgments (`judge.c`, `check.c`, `pins.c`, `proof.c`)

Inference, checking, conversion, typed maps, contexts, declarations and
bodies are families keyed by their request and pin set. `judge.every` judges
a request under every clause of a face; `judge.joint` makes the face-wide
value; `judge.system` is the one system rule; `judge.glue_eq` the one Glue
comparison; `judge.open` opens a telescope (a scope's, or a node's parameter
telescope). A request pins the closure of the symbols its inputs name
(`pins.c`); `check.c` drives one root per request. `proof.c` audits proof
use (Tarjan, one edge per step).

## Effects and the additive reading (`effect.c`, `chain.c`, `count.c`)

Proposals, ordered reservations, one commit, finalization and receipts as
families; exact signed integers (one limb per step), chains, cochains,
pairing, boundaries and module values as 0-chains; exact readings of
per-producer work (`count.c`).

## Tests

`tests/test_*.c` are semantic regressions and law checks (substitution,
DNF laws, alpha identity, scopes, templates, checking, compiler, proof use,
effects, chains, the protocol); `tests/review_*.c` are the §96 integration
witnesses.
