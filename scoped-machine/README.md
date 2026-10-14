# Scoped references and face-sensitive cubical evaluation

A from-scratch C11 implementation of the handoff specification *Scoped
references and face sensitive cubical evaluation* (14 October 2026). Nothing
here is derived from earlier runtime code; the spec is the only source.

    make test        # builds with -fsanitize=address,undefined and runs the suite

## Layout — spec section → file

| Spec | File | Contents |
| --- | --- | --- |
| §2 | `src/intern.*`, `src/state.h`, `src/machine.c` | Structural interning of word records (hash collisions resolved by comparing records); one immutable record table set per machine |
| §3 | `src/dnf.*`, `src/interval.*` | Canonical antichain DNF; `i∧¬i` is retained; `join/meet/negate`; single-insertion substitution |
| §4–5 | `src/face.*` | Face DNF with contradiction removal before absorption/projection; endpoint formulas; `entails` by clause containment; `fc_forall` (deletes clauses) vs `fc_project` (deletes literals); interned dimension/variable sets |
| §6–9 | `src/term.*` | Raw simultaneous maps (identity entries removed, single lookup); origins with fields/binders and dependency-closed typed boundary; references `VAR(x)` / `VIEW(C,σ)` with instantiated support, free variables and required face frozen at interning; `make_view` restriction to the typed boundary; memoized `reindex`; `compose` including τ-only keys; binder identity `(owner, slot, sort)`; lifting; `open`; `GLOBAL` definitions unfolded as views of a fixed body |
| §10–13 | `src/eval.*` | `EvalKey = (t, π_{S(t)} χ)`; entries `UNEVALUATED/RUNNING/READY` with waiters; continuation-based scheduler (no blocking on a running key; a reentrant demand is left suspended and reported `W_STUCK`, never published); dispatch table with the stated precedences; systems; composition opening one shared dimension for family and tube; retained components specialized by `reindex` |
| §14–18 | `src/lib.*` | `fill`, `hcomp`, `coe`, lines, path operations, `Contr/fib/Equiv`, `IdEquiv`, `ExtendContr`, `LineEquiv`, `ua`, and the Π / Σ / PathP / Glue / Universe composition clauses term by term |
| §19–20 | `src/net.*` | Polarized descriptor and operation agents, the one-result rule table (all rows), `MATERIALIZE` (heads, `BRANCH_NIL/CONS/BRANCH` for systems), handle-copying duplication and erasure (also fieldwise for shells), `EVAL` agents registered as cache continuations, and `rep_commit`: every removed auxiliary port accounted for exactly once, boundary paths followed through connectors, closed wire components counted, only opposite polarities connected |
| §23 | `tests/test_main.c`, `test_net` in `src/net.c` | Every row of the acceptance table, plus the exhaustive projection/quantifier law check on all 48 canonical faces over two dimensions (2 880 + 240 comparisons) |

## The central distinction, as implemented

```
reference      = make_view(origin, map)        term.c
specialization = reindex(reference, map)       term.c   (never evaluates; traverses image records only)
observation    = whnf(reference, ambient_face) eval.c   (cached per (reference, projected face))
```

`reindex` of `VIEW(C, τ)` by `σ` builds `ρ[x] = reindex(τ(x), σ)` for `x ∈ FT(C)` and
`ρ[i] = σ(τ(i))` for `i ∈ FD(C)` and interns `VIEW(C, ρ)`; the body of `C` is not
visited. Results of evaluation live only in cache entries; no origin or reference is
ever rewritten. Composition opens its family and tube at the single dimension
`binder_dim_var(owner, 0)` and the clauses in `lib.c` specialize the retained component
references (`reindex_dim(C, j, r)`), never `component(whnf(family at r))`.

## Representation decisions (within the spec, worth knowing)

- Terms built by the constructors `mk_*` are identity views of fresh origins whose fields
  are arbitrary references; binder formals are ordinary declared variable identities.
  `VIEW(origin-with-field-i, [i ↦ 1])` and a freshly built origin with field `1` are
  different `RefId`s: identity is structural equality of records, not of denotation.
- A `VAR(x)`'s boundary is `{x} ∪ FT(type x)`, support `S(type x) ∪ dims(required x)`, so
  `make_view` restriction and cache support are closed through declaration types.
- A reference's required face folds in the required faces of its free variables and of
  its total reference fields (fields under a dimension binder contribute `∀j`); partial
  positions (tube, Glue fibre data, glue fibre term) do not propagate.
- Eliminators meeting a system result act branchwise: each `elim(t_k)` is demanded under
  `χ ∧ φ_k`, and the gathered guarded results are published as one system (nested system
  results are flattened under conjoined guards). A plain `SYSTEM` head that is covered but
  not selected is retained with its unevaluated branches.
- A neutral result retains the original eliminator reference (all operands and
  annotations), as §12 requires; a consumer that needs the evaluated scrutinee re-demands
  the field (cached).
- Fresh names inside library definitions are minted deterministically from the references
  they must be fresh for (`fresh_*_keyed`), so identical invocations intern identically and
  no image can contain the minted name.

## Interaction-work vector and schedule independence (§25–§31)

`eval_events()` returns **W = (REQUEST, EVAL_STEP, PUB, DELIVER)**; the net keeps the
local-rule classes `n_op`, `n_dup`, `n_erase`, `n_eval_deliver`. Counting boundaries:

- `REQUEST` is incremented once in `eval_request` after the key is formed, whatever the
  entry state. A false-face or invalid-occurrence request forms no key and is not a
  REQUEST event (its control status is still delivered).
- `DELIVER` is incremented in `deliver()`, the single delivery path used by the ready-hit
  case and by `publish` for every detached waiter. `deliver()` enqueues a RESUME job; the
  resumed frame step is counted separately.
- `EVAL_STEP` is incremented in `eval_run` for every executed job, i.e. each initial
  EVALUATE task and each RESUME of a continuation (including the join resumptions of a
  branchwise system). Thus `EVAL_STEP = launches + DELIVER`.
- `PUB` is incremented in `publish` on the completed RUNNING → READY transition.
- Net rule counters are incremented after `rep_commit` returns, i.e. for committed
  replacements only.
- `ready_hit`, `running_hit`, `launch` are diagnostics: their split is not
  diamond-balanced (a request can cross a publication); their sum is `REQUEST`.

The join of a branchwise system stores each branch's outcome in its original slot and
publishes exactly once when every launched branch has delivered; a failure is selected by
original branch order, never by arrival order.

`eval_set_policy(FIFO|LIFO|RANDOM, seed)` and `Net.policy` choose which ready job /
active pair runs next. `tests/test_schedule.c` builds one initial configuration on a fresh
machine for 24 combinations of the two policies and seeds and requires: the same W, the
same net rule counts, the same per-key event multiset (REQ/DELIVER/PUB per canonical key,
so a failure names the first divergent event), and the same canonical dump of the complete
reachable result graph. The dump (`src/canon.c`) compares retained fields, substitutions,
faces, binder formals and shared-reference structure under one consistent bijection:
generated names are identified by their provenance record (`(owner, slot, sort)` or the
typed key of a library-minted name), input names by declaration index, global symbols by
name; DNF clauses are compared as sets under the dimension renaming; map entries and
clauses are ordered by a renaming-invariant hash, and records are numbered by one DFS from
the roots, so aliasing is preserved (one record, one number). Interned-record and name
allocation totals are reported as diagnostics only. `W_STUCK` remains a quiescence
diagnostic: a root left pending with an empty queue, with nothing published.

## Scope

- The evaluator takes the typing premises of the cubical rules as premises (§12, §22 item
  12). `validate_occurrence` checks face entailment of the reference's required face; it
  does not type-check. Ill-typed demands that evaluation reaches are reported as `R_INVALID`
  host status, never as values.
- The machine is sequential. The entry protocol is written so that `EVALUATE` runs under
  `key.face`, one task owns a running key (asserted), waiters are registered under the same
  check as readiness, and nothing incomplete is ever published; the locking and
  acquire/release requirements of §10/§20 are therefore vacuous in this build.
- Continuations, results and gathers are rooted for the machine's lifetime and released at
  `eval_free`; there is no reclamation during a run.
