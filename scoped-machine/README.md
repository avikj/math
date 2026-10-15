# Scoped references and face-sensitive cubical evaluation

A from-scratch C11 implementation of the handoff specification *Scoped
references and face sensitive cubical evaluation* (14 October 2026). Nothing
here is derived from earlier runtime code; the spec is the only source.

    make test        # ASan/UBSan: acceptance suite, schedule suite, concurrent-client suite, and the first two again with 4-thread pools
    make tsan        # ThreadSanitizer build of the same suites

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
| §2 contexts | `src/term.*` (`context_*`, `occurrence_validate`, `term_require_push`), `whnf_in` in `src/eval.*` | Interned occurrence contexts; structural validity; declared required-face annotation on origins |
| §33–34 | `src/check.*` | `check_context`, `check_map`, `check_origin`, `infer`, `check`, `convert_type`, `convert_term`, `check_signature`, `observe_checked`; outcomes VALID/INVALID/UNRESOLVED, EQUAL/UNEQUAL/UNRESOLVED |
| §35–36 | `src/eval.c`, `src/net.c` | `outstanding` quiescence protocol, reservation under the entry lock, enqueue after unlock, ownership and teardown |
| §37 | `src/match.*`, `src/canon.*` | Exported labelled graph; exact matching with backtracking; refinement as candidate filter only |
| §25–31 | `src/eval.*` (counters, policies, worker pool), `src/net.*` (rule counters, policies, worker pool), `src/canon.*` | Interaction-work vector, deterministic joins, exact canonical comparison modulo renaming |
| §23 | `tests/test_main.c`, `test_net` in `src/net.c` | Every row of the acceptance table, plus the exhaustive projection/quantifier law check on all 48 canonical faces over two dimensions (2 880 + 240 comparisons) |
| §28–31, §38 | `tests/test_schedule.c`, `tests/test_concurrent.c`, `tests/test_match.c`, `tests/test_check.c` | 24 schedule combinations; client storms and multi-client runs; comparison acceptance/rejection incl. ambiguous refinement; checking acceptance/rejection/unresolved; `make tsan` |

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
  `χ ∧ φ_k`; the join box stores each outcome in its original slot, publishes exactly once
  when every launched branch has delivered, and selects a failure by original branch
  order. A plain `SYSTEM` head that is covered but not selected is retained with its
  unevaluated branches.
- A neutral result retains the original eliminator reference (all operands and
  annotations), as §12 requires; a consumer that needs the evaluated scrutinee re-demands
  the field (cached).
- Fresh names inside library definitions are minted deterministically from typed
  provenance keys (`fresh_*_keyed`), so identical invocations intern identically, no image
  can contain the minted name, and every generated name can be compared across runs by
  its provenance. The Π/Σ/PathP/Glue/U clauses are C definitions that build core terms
  this way rather than `GLOBAL` bodies: a family parameter with a free dimension cannot
  be passed to a `GLOBAL` through a term variable in this representation, and interning
  provides the sharing of intermediates §14 asks for (the Σ filler is one `RefId`).

## Occurrence contexts and checking (§2, §33–§34)

`context_make` interns an ordered list of `DIM(i)` / `TERM(x, type)` declarations with a
face assumption; `occurrence_validate` is the structural check (declared variables and
dimensions, declared type by identity, assumption entails the required face). The typed
check is `src/check.c`:

- `check_context(Γ)`: unique identities; the assumption over declared dimensions; each
  declaration's type and required face over its prefix; each type is a type under the
  assumption projected to the prefix dimensions.
- `check_map(Δ,ψ,σ,Γ,χ)`: dimension images over Δ; each term image against `A[σ]` under
  every consistent clause of ψ, in target declaration order; `ψ ⇒ χ[σ]` and the targets'
  required faces.
- `check_origin(C)`: an origin is validated once (memoized per `OriginId`) in its own
  parameter context (`origin_context`: free dimensions, then free variables in dependency
  order) under its required face; a view `VIEW(C,σ)` is then typed by the substitution
  lemma: `check_map` into that context and `A_C[σ]`. Views never recheck a copied body.
- `infer`/`check`: the §33 constructor table, clausewise under the consistent clauses of
  the face (the result type under a disjunctive face is the common type, or a system of
  the per-clause types); exact universe levels, no cumulativity; checking forms (λ, pair,
  path lambda, system) against the expected head; composition cap/tube agreement, path
  endpoints, Glue data and map agreement, system coverage and overlaps; scope is checked
  even under the false face, where the remaining obligations are vacuous.
- Declared symbols carry a type over their parameters; a symbol is validated on first use
  (type is a type; body, if any, checks against the type, with recursive occurrences using
  the declaration); a symbol without a body is an opaque constant and observes as a
  neutral.
- Conversion (`convert_type`, `convert_term`): per consistent clause; weak-head observation
  of both sides; reflexive fast path on identical references; type formers compared
  structurally with one fresh identity applied to both binders; term conversion by expected
  type with the Π, Σ, Path and Glue η rules (Glue: `unglue` in the base and the fibre on
  `C ∧ α`); neutral-spine comparison per the §34 table (variables, application, projections,
  path application modulo the clause, unglue, blocked composition, opaque constants); fresh
  comparison identities keyed by the request record (both sides, expected head, slot) in a
  distinct namespace. Requests are cached by (mode, declarations, projected face, inputs,
  expected type); a running request met again is a cycle and yields UNRESOLVED; UNRESOLVED
  is never cached as inequality. A step budget (`check_set_budget`) yields UNRESOLVED.
- `observe_checked(Γ, t)` validates then observes; `check_signature` validates all symbols.

Checking runs synchronously on the caller's thread as an admission phase; its weak-head
observations go through the ordinary cache and count as ordinary evaluation events.

The §2 `required_face` annotation: `term_require_push(φ)` makes constructors created in the
scope carry φ in their origin record and required face. The Glue composition clause uses it
for the constructions that are only typed on `δ = ∀i α_i` and on `α_1`. The checker's test
suite confirms that every composition clause output (Π, Σ, PathP, Glue, universe, transport
along `ua`) checks at its expected type.

## Concurrency (§10, §20)

Record tables are non-moving and interning is find-or-insert under one mutex per table,
so two threads interning the same record get one id; side data is written before an id is
published. The term layer serializes creation (origins, references, declarations, nominal
minting, definitions) under one recursive mutex; reads of published records are lock-free.

Cache: each entry has an owner lock; readiness check and waiter registration happen in the
same critical section; a launch *reserves* its job (`outstanding += 1`) while the entry lock
is held and enqueues it after unlocking (§35), so `U → R({c}) + EVAL(K)` is one transition as
far as any observer of quiescence can tell, and no continuation code or interning runs under
an entry lock; `publish` sets the result, flips to READY, detaches the waiters and delivers
after unlocking, and the publishing job stays active until those deliveries are enqueued;
one evaluator task per key is asserted. Quiescence is `outstanding = queued + executing
(+ reserved) = 0`; `finish_job` runs after a job's children are enqueued; `whnf` waits for
its root or for quiescence (then `W_STUCK`, with nothing published). The ready jobs are a
multiset served by a worker pool (`eval_set_workers`); `whnf` waits for its root or for
quiescence. Joins (`Gather`) have their own lock and are published by the last arrival.

Net: nodes are non-moving with a generation counter (pinning is trivial; stale handles are
detected). A replacement locks the two redex owners, validates the pair, collects the
surviving boundary owners, releases, locks the whole affected set in id order, revalidates
redex and boundary, installs, retires, releases, and only then enqueues the new active
pairs; publication of a result into the net locks the pending node and its consumer the
same way. `net_set_workers` runs a pool; `net_run_with_eval` drives both pools to joint
quiescence.

`make tsan` builds everything with ThreadSanitizer and runs the suites with worker pools
and with concurrent client threads. The abstract machine's elementary events are the same
in every mode: the worker runs report the same W and the same canonical result graph as
the sequential runs (`tests/test_concurrent.c`).

## Ownership and teardown (§19–§20, §36)

| Holder | Owns |
| --- | --- |
| record tables | immutable records and side data, for the machine's lifetime |
| READY entry | its result, for the machine's lifetime (no eviction during a counted workload) |
| RUNNING entry | its waiter collection |
| queue / executing worker | the job and its captured payloads |
| continuation | its destination and arguments until consumed (freed on resume, exactly once) |
| join | its slot values until it publishes (freed by the last arrival) |
| root box | shared by the client and the root continuation (refcount; the last releases) |
| descriptor / external root | its payload while live; an undelivered external context is released at teardown |

Teardown (`eval_free` before `machine_free`): stop and join the workers, dismantle the
suspended waiter/continuation graph (stuck entries' waiters, undelivered external
contexts, root boxes, unfilled joins), free results, then the cache and record tables.
The concurrent suite tears down stuck cyclic keys and a stuck branchwise join under
LeakSanitizer.

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
- A request on the false face or on an invalid occurrence forms no key: it is a DELIVER
  of a control status with no REQUEST or PUB. This is outside the four §26 transitions
  but is a deterministic function of the configuration, so W stays schedule-invariant.

The join of a branchwise system stores each branch's outcome in its original slot and
publishes exactly once when every launched branch has delivered; a failure is selected by
original branch order, never by arrival order.

`eval_set_policy(FIFO|LIFO|RANDOM, seed)` and `Net.policy` choose which ready job /
active pair runs next. `tests/test_schedule.c` builds one initial configuration on a fresh
machine for 24 combinations of the two policies and seeds and requires: the same W, the
same net rule counts, the same per-key event multiset (REQ/DELIVER/PUB per canonical key,
so a failure names the first divergent event), and the result graphs equal modulo renaming. `src/canon.c` exports the records reachable from the
results and the cache keys as a labelled graph (references with tag, payload, binder and
field shape and the required-face annotation; provenance records; faces, intervals,
clauses, literals; map entries; input names by declaration index; globals by name), with
ordered and unordered edges and sharing preserved. `src/match.c` decides equality by exact
matching (§37): joint partition refinement only filters candidates; a complete depth-first
search over bijections, with backtracking that revisits inner choices, must preserve kinds,
labels, ordered children by position, unordered children as sets and the bijection's
consistency (aliasing). `tests/test_match.c` includes graphs that refinement cannot separate
but that differ in sharing, isomorphic graphs that need backtracking, and rejected changes
of payload, endpoint, guard, aliasing and anchored input. Interned-record and name
allocation totals are reported as diagnostics only. `W_STUCK` remains a quiescence diagnostic: a root left pending with an empty queue,
with nothing published; a RUNNING entry met during evaluation is a waiter, not evidence of
a cycle.

## Status against §38

- Checking: β and the Π/Σ/Path/Glue η conversions accepted; incompatible declared types and
  unbound dependencies rejected; dependent substitution images, composition cap/tube
  agreement, path endpoints, Glue map agreement, system coverage and overlaps validated;
  cyclic computation and exhausted budgets reported UNRESOLVED (`tests/test_check.c`).
- Concurrency: duplicate requests, request/publication races, unique interning, branch joins
  and quiescence exercised with worker pools and client storms; one evaluator and one
  publication per key; `make tsan` clean (`tests/test_concurrent.c`).
- Reclamation: continuations consumed once, joins released, memo entries retained through
  the workload, successful and stuck workloads (cyclic key, stuck join) torn down under
  LeakSanitizer.
- Comparison: consistent renaming with preserved sharing accepted; changed payload,
  endpoint, guard, aliasing and anchored input rejected; ambiguous-refinement cases decided
  by exact matching (`tests/test_match.c`).
- Scheduling: job and active-pair policies varied, including mixed, from one initial
  configuration; W and the exact result graph compared; seed and first mismatch reported
  (`tests/test_schedule.c`).

Typing premises of the cubical rules are now checked by `src/check.c`; the evaluator itself
still takes them as premises and reports ill-typed demands it reaches as `R_INVALID`.
