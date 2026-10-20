# Scoped cubical machine

C11 implementation of the specification `HANDOFF.md`, scoped and ordered by
the binding plan `PLAN.md`; `INTERNING.md` specifies stepped interning.

    make test    # ASan/UBSan: every suite, then the compiler suite with a 4-worker pool
    make tsan    # ThreadSanitizer: every suite with 4 workers

## The one protocol (`eval.c`, `eval.h`, `families.h`)

Every computation over variable data is a producer keyed by (family, a, b).
Its entry moves U → R → D by a constant number of atomic operations: a
requester joins by one exchange (the one that finds U launches the producer;
a launch alone is one CAS, never retried), publication exchanges the waiter
chain for READY, and each delivery is its own job. A
producer is a frame: a step function that does a bounded amount of work and
ends in request, call (a subroutine frame), yield or finish. Independent
demands are launched and then awaited in order. Host callers drive a root
key with a host frame (`family_run`, `family_call`, `family_run_budget`); a
budget is a host control bound on the jobs executed during the call. Every family id is
named in `families.h`.

## Records

- One record table (`state.h`, `intern.c`): every record is interned in
  `M.keys` by the stepped interner; the evaluator's entry index is its own
  table. Stable stores are radix directories of fixed-size nodes over every
  `size_t` index.
- Universe levels are exact naturals (a word below 2^63, the canonical
  exact-integer record above); successor and maximum are stepped families.
- Intervals and faces are canonical antichain DNFs (`dnf.h`); their
  operations, and set union / removal / membership, are families (`dnfam.c`).
- One substitution record (`subst.c`): `[(key, sort, value)*]` sorted by
  key, an environment (and every total record: binding views, context indexes,
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

## Revisions and binding views (`term.c`, `eval.c`)

A revision is the record (symbol, body); a binding view maps symbols to
revisions, and each declaration or body makes a new view. Pure families are
keyed by their operands. A relative family (one that reads revisions) is
requested through a resolver keyed by the requester's view, which chooses the
node whose actually read revisions agree with it; node keys hold no view. A
read is the dependency `view.read(s, V)`; unfolding and body validity consume
that revision. An effect is one occurrence node.

## Judgments (`judge.c`, `check.c`, `proof.c`)

Inference, checking, conversion, typed maps, contexts, declarations and
bodies are families keyed by their request. `judge.every` judges a request
under every clause of a face; `judge.joint` makes the face-wide value;
`judge.system` is the one system rule; `judge.glue_eq` the one Glue
comparison; `judge.open` opens a telescope. `judge.admit` (`check.c`) is the
one composite judgment the public API, proof use and effect preparation
request: its derivation and the bodies of every revision it read (for proof
use also those the conservative audit reached) validated.
`proof.c` classifies the audited graph (Tarjan, one edge per step).

## Effects and the additive reading (`effect.c`, `chain.c`, `count.c`)

Proposals, ordered reservations, one commit, finalization and receipts as
families; exact signed integers (one limb per step), chains, cochains,
pairing, boundaries and module values as 0-chains; exact per-producer
counts (`count.c`) and the historical work of a published support as
families (`history.support`, `history.work`).

## Tests

`tests/test_*.c` are semantic regressions and law checks (substitution,
DNF laws, alpha identity and scopes at every arity, templates, checking with
exact levels, compiler, proof use, effects, chains, the protocol: schedule
independence, native-stack independence, exact concurrent counts);
`tests/review_*.c` are the §96 integration witnesses.
