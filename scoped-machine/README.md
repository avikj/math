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
| §2 contexts | `src/term.*` (`context_*`, `occurrence_validate`), `whnf_in` in `src/eval.*` | Interned occurrence contexts; structural validity of an occurrence |
| §25–31 | `src/eval.*` (counters, policies, worker pool), `src/net.*` (rule counters, policies, worker pool), `src/canon.*` | Interaction-work vector, deterministic joins, exact canonical comparison modulo renaming |
| §23 | `tests/test_main.c`, `test_net` in `src/net.c` | Every row of the acceptance table, plus the exhaustive projection/quantifier law check on all 48 canonical faces over two dimensions (2 880 + 240 comparisons) |
| §28–31 | `tests/test_schedule.c`, `tests/test_concurrent.c` | 24 schedule combinations on fresh machines; concurrent client threads with worker pools; `make tsan` |

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

## Occurrence contexts (§2)

`context_make` interns an ordered list of `DIM(i)` / `TERM(x, type)` declarations with a
face assumption. `occurrence_validate(t, ctx)` checks that every free dimension and free
term variable of `t` is declared, that each declared type is the variable's declaration
type, and that the assumption entails `required(t)`; `whnf_in(t, ctx)` validates and then
observes under the assumption. Weakening (`context_extend_*`) and restriction
(`context_restrict`) change the context and keep the reference. Types are compared by
reference identity: the spec supplies no conversion algorithm, and none is assumed here.

## Concurrency (§10, §20)

Record tables are non-moving and interning is find-or-insert under one mutex per table,
so two threads interning the same record get one id; side data is written before an id is
published. The term layer serializes creation (origins, references, declarations, nominal
minting, definitions) under one recursive mutex; reads of published records are lock-free.

Cache: each entry has an owner lock; readiness check, waiter registration and, for a
launch, enqueueing the EVALUATE job happen in the same critical section (so `U → R({c}) +
EVAL(K)` is one transition and no thread can observe a running key whose evaluator is not
yet runnable); `publish` sets the result, flips to READY, detaches the waiters and delivers
after unlocking; one evaluator task per key is asserted. The ready jobs are a
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

## Reclamation (§19–§20)

A continuation is freed when it is resumed (single consumer); a join box when it
publishes; net nodes are retired (live flag, generation bump) and their storage reclaimed
at `net_free`. A published result is owned by its READY entry for the life of the machine
(it is the cache); control results delivered without an entry are rooted in the machine's
result list. Nothing is reclaimed while a live root, entry, descriptor or continuation can
reach it, and no live semantic work is ever cancelled.

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
so a failure names the first divergent event), and the same canonical dump of the complete
reachable result graph and of every cache key with its event counts. The dump
(`src/canon.c`) is exact: the reachable records are exported as a labelled graph
(references, provenance records, faces, intervals, clauses, literals, map entries, input
names), node classes are computed by partition refinement with exact signatures until the
partition is stable, unordered collections are ordered by class, and records are numbered
by one DFS from the roots, so aliasing is preserved and no hash enters the comparison.
Generated names are identified by provenance, input names by declaration index, global
symbols by name. Interned-record and name allocation totals are reported as diagnostics
only. `W_STUCK` remains a quiescence diagnostic: a root left pending with an empty queue,
with nothing published; a RUNNING entry met during evaluation is a waiter, not evidence of
a cycle.

## What the spec leaves to its author

- "Compatible types" in occurrence validity (§2, §22 item 4) is checked by reference
  identity. A conversion check between type references would need a definitional-equality
  procedure the spec deliberately does not provide; it is the one open design question.
- Typing premises of the cubical rules (§12, §22 item 12) are premises: ill-typed demands
  that evaluation reaches are reported as `R_INVALID` host status, never as values.
