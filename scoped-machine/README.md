# Scoped cubical interaction machine and identity compiler

A from-scratch C11 implementation of the handoff specification *Scoped cubical
interaction machine and identity compiler* (§§1–59, 14 October 2026). Nothing
here is derived from earlier runtime code; the spec is the only source.

    make test        # ASan/UBSan/LSan: every suite, then the acceptance, schedule, checking, template and compiler suites again with 4-thread pools
    make tsan        # ThreadSanitizer build of every suite

## Layout — spec section → file

| Spec | File | Contents |
| --- | --- | --- |
| §2 | `src/intern.*`, `src/state.h`, `src/machine.c` | Structural interning of word records (hash collisions resolved by comparing records); one immutable record table set per machine |
| §3 | `src/dnf.*`, `src/interval.*` | Canonical antichain DNF; `i∧¬i` is retained; `join/meet/negate`; single-insertion substitution |
| §4–5 | `src/face.*` | Face DNF with contradiction removal before absorption/projection; endpoint formulas; `entails` by clause containment; `fc_forall` (deletes clauses) vs `fc_project` (deletes literals); interned dimension/variable sets |
| §6–9 | `src/term.*` | Raw simultaneous maps (identity entries removed, single lookup); origins with fields/binders and dependency-closed typed boundary; references `VAR(x)` / `VIEW(C,σ)` with instantiated support, free variables and required face frozen at interning; `make_view` restriction to the typed boundary; memoized `reindex`; `compose` including τ-only keys; binder identity `(owner, slot, sort)`; lifting; `open`; `GLOBAL` definitions unfolded as views of a fixed body |
| §10–13 | `src/eval.*` | `EvalKey = (t, π_{S(t)} χ)`; entries `UNEVALUATED/RUNNING/READY` with waiters; continuation-based scheduler (no blocking on a running key; a reentrant demand is left suspended and reported `W_STUCK`, never published); dispatch table with the stated precedences; systems; composition opening one shared dimension for family and tube; retained components specialized by `reindex` |
| §14–18, §52–54 | `src/lib.*` | The library as fixed template programs with explicit universe levels: `fill`, `hcomp`, `coe`, lines, path operations, `Contr/fib/Equiv`, `IdEquiv`, `ExtendContr`, `LineEquiv`, `ua`, `Down`; the Π / Σ / PathP / Glue / Universe composition clauses; `comp_clause` captures the exposed head's components into scopes and instantiates the one fixed clause |
| §49–50 | `src/scope.*`, bound atoms in `src/term.h` | Scopes: a reference / interval / face abstracted over an ordered local telescope, locals as `(depth, slot)` atoms in the id space; `capture_scope`, `apply_scope` (simultaneous substitution to a typed partial), `reindex_scope` (free identities only), `forall_scope`; one depth-aware traversal engine shared with references and template environments |
| §51 | `src/template.*` | Template definitions as acyclic expression DAGs over typed parameters (reference, interval, face, scope, level) with κ as slot 0; fixed constructor nodes; `TVIEW(node, environment)` as the third reference form, opened by interpreting the node's finite field recipes, reindexed by reindexing the environment; `tnode_signature` for checking; environments restricted to the node's free slots |
| §55 | `src/net.*` | `SCOPE`, `TEMPLATE_ENV`, `TYPED_PARTIAL` descriptors and the twelve scope/template operations as one-result rules over immutable payloads |
| §57, §59.4 | `src/check.c` | The whole-environment admission gate (`check_admission`, keyed by the global environment version; `observe_checked` and compiler publication enter it first); claim sessions and attempts |
| §19–20 | `src/net.*` | Polarized descriptor and operation agents, the one-result rule table (all rows), `MATERIALIZE` (heads, `BRANCH_NIL/CONS/BRANCH` for systems), handle-copying duplication and erasure (also fieldwise for shells), `EVAL` agents registered as cache continuations, and `rep_commit`: every removed auxiliary port accounted for exactly once, boundary paths followed through connectors, closed wire components counted, only opposite polarities connected |
| §2 contexts | `src/term.*` (`context_*`, `occurrence_validate`, `term_require_push`), `whnf_in` in `src/eval.*` | Interned occurrence contexts; structural validity; declared required-face annotation on origins |
| §33–34 | `src/check.*` | `check_context`, `check_map`, `check_origin`, `infer`, `check`, `convert_type`, `convert_term`, `check_signature`, `observe_checked`; outcomes VALID/INVALID/UNRESOLVED, EQUAL/UNEQUAL/UNRESOLVED |
| §35–36 | `src/eval.c`, `src/net.c` | `outstanding` quiescence protocol, reservation under the entry lock, enqueue after unlock, ownership and teardown |
| §37 | `src/match.*`, `src/canon.*` | Exported labelled graph; exact matching with backtracking; refinement as candidate filter only |
| §25–31 | `src/eval.*` (counters, policies, worker pool), `src/net.*` (rule counters, policies, worker pool), `src/canon.*` | Interaction-work vector, deterministic joins, exact canonical comparison modulo renaming |
| §23 | `tests/test_main.c`, `test_net` in `src/net.c` | Every row of the acceptance table, plus the exhaustive projection/quantifier law check on all 48 canonical faces over two dimensions (2 880 + 240 comparisons) |
| §39–48, §59.3 | `src/compiler.*`, `T_TCALL` in `src/term.*`, `OP_APPLY_TRANSFORM` / `A_CONTINUE_REFERENCE` in `src/net.*`, `evaluate` (T_TCALL) and the pair jobs in `src/eval.*`, the T_TCALL rule in `src/check.c` | Diagrams, realization telescopes, canonical substitution, `Down`/expand, collapse/expand templates, `compile_identity` with the graph-pair template, equivalence / residual / cut / contractible-fibre schemas, certificates, one fixed `TRANSFORM_CALL` origin per transform and orientation with invocations as its views, the application and receiver rules, one outstanding count for evaluator jobs and net pairs |
| §§60–71 under §73 | `src/work.*`, trace fields in `src/eval.*` (`deps`, `steps`, `env`, root occurrences) and `src/net.*` (identity-application trace), `tests/test_work.c` | Identity-execution accounting and cost refinement: work identities, demand closure with ready cuts, the resource algebra, Boolean direct image under specialization, cost differences, typed plan/connector/expression/cost-model records, the formula DAG with `restrict`, realization reconstruction, verification of supplied proof DAGs and geodesic certificates, Must-factoring / disjoint decomposition / the shared-choice equality, schemas, the bounded-frame engine and the fine ledger. No solver, no frontier. See the section below. |
| §§74–82 | `src/shape.*`, `src/reuse.*` + `src/reuse_stats.h`, evaluator keys/receipts/adapters in `src/eval.*`, revisions and instantiation edges in `src/term.*`, action identity and `identity_action` in `src/compiler.*`, projected judgments and dependency-validated claims in `src/check.c`, the persistent job engine in `src/work.c`; `tests/test_reuse.c`, `tests/accept_*.c` | Uniform reuse: structural computation identity, dependency-validated persistent answers, residual receipts with specialization/restriction adapters, one action per content, the runtime proof action, persistent pure-operation producers with shared continuations, and the §74.2 counter contract. See the section below. |
| §28–31, §38, §47 | `tests/test_schedule.c`, `tests/test_concurrent.c`, `tests/test_match.c`, `tests/test_check.c`, `tests/test_templates.c`, `tests/test_compiler.c`, `tests/review_regressions.c`, `tests/review_followup.c`, `tests/review_claim_wait.c`, `tests/review_checker_lifecycle.c` | 24 schedule combinations (now with the associativity transform in the workload); client storms and multi-client runs; comparison acceptance/rejection incl. ambiguous refinement; checking acceptance/rejection/unresolved; template laws and the admission transaction; the §47 compiler cases; the review's regression cases; `make tsan` |

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
- Library definitions are **fixed templates** (`src/lib.c`): each derived definition and
  each composition clause is compiled once into an origin over formal parameters, and an
  invocation is `reindex(body, σ)` with σ sending the formals to the arguments. Term-sorted
  arguments used at the template's own dimension points (values, paths, functions, caps,
  tubes used in place) are term formals (a tube is declared partial on its guard, so its
  image adds no requirement beyond the guard); interval arguments (a path application
  point, the fill parameter) are interval formals; types, families, faces, and a tube the
  body re-scopes (`u_i` at `i ↦ r∧j`) are the template's **shape**, canonicalized over
  template dimension formals and part of the key. Because reindexing composes,
  `reindex(T(a), τ) = T(a[τ])` holds as an identity of references for τ acting on formals
  (term, interval) and for order-preserving renamings of the shape's dimensions; a family
  cannot be a term formal because a variable occurrence carries no dimension substitution
  (`VAR(u)[i ↦ 1] = VAR(u)` would lose the specialization), so scoped families enter as
  references with their scope maps, as the spec's clause formulas write them. Generated
  names are keyed by (definition, role, slot, shape), so provenance compares up to
  renaming and never depends on the arguments. Pairs built by templates carry their Σ type
  (`mk_pair_at`), the §33 annotation that lets a checking-only form synthesize.
- Full parametricity in *type* arguments (`type : U_ℓ` as a formal) needs the universe level
  ℓ at invocation: the core's levels are exact and `COMP` carries no level annotation, so
  the evaluator cannot supply ℓ when it invokes a clause. Type arguments are therefore
  shape data; see REVIEW.md §5 for the question this leaves with the author.

## Occurrence contexts and checking (§2, §33–§34)

`context_make` interns an ordered list of `DIM(i)` / `TERM(x, type)` declarations with a
face assumption; `occurrence_validate` is the structural check (declared variables and
dimensions, declared type by identity, assumption entails the required face). The typed
check is `src/check.c`:

- `check_context(Γ)`: unique identities; the assumption over declared dimensions; each
  declaration's type and required face over its prefix; each type is a type under the
  assumption projected to the prefix dimensions, and is compatible with the variable's
  recorded declaration by conversion under each clause (not by identity).
- `check_map(Δ,ψ,σ,Γ,χ)`: dimension images over Δ; every term image (the identity image
  when an entry is absent) in Δ's scope whatever the source face; each term image against
  `A[σ]` under every consistent clause of `ψ ∧ φ_x[σ]`, where φ_x is the target
  declaration's required face (a declaration partial on φ_x is only used under φ_x), in
  target declaration order; `ψ ⇒ χ[σ]`.
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
- **Claims and the admission transaction.** Every memoized request (context, map, origin,
  symbol, clause conversion) is a *claim*: one producer computes it, every other client
  waits for its outcome, and the outcome is published once (`claim_acquire` /
  `claim_release`). A request met again on its own demand path is a cycle: UNRESOLVED for
  conversion, origins, contexts and maps; "typed by the declaration" for a symbol. Across
  threads a wait cycle is detected on the wait-for graph; if a symbol lies on it, the
  thread blocked on that symbol yields by taking the declaration as its assumption, exactly
  as one thread does. Verdicts reached under such an assumption are *provisional* on the
  symbol and are committed only when its body is accepted (`resolve_locked`): a rejected
  premise withdraws the dependents, which are recomputed on demand; mutually dependent
  accepted symbols (recursion validated from both ends) commit together. A top-level
  request never returns a provisional verdict: it waits for the symbols it rests on and
  recomputes (`top_settled`). `check_signature` validates every symbol; `observe_checked`
  admits only committed verdicts.
- Conversion (`convert_type`, `convert_term`): per consistent clause; weak-head observation
  of both sides; reflexive fast path on identical references; type formers compared
  structurally with one fresh identity applied to both binders; term conversion by expected
  type with the Π, Σ, Path and Glue η rules (Glue: `unglue` in the base and the fibre on
  `C ∧ α`); neutral-spine comparison per the §34 table (variables, application, projections,
  path application modulo the clause, unglue, blocked composition, opaque constants); fresh
  comparison identities keyed by the request record (both sides, expected head, slot) in a
  distinct namespace. Requests are cached by (mode, declarations, projected face, inputs,
  expected type) as claims; UNRESOLVED is never cached as inequality. A step budget
  (`check_set_budget`) yields UNRESOLVED.
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
- A request on the false face is a DELIVER of `NO_OBSERVATION`, and a request under a
  nonfalse face that fails the occurrence guard is a DELIVER of `INVALID(reason)`; neither
  forms a key, so neither contributes REQUEST or PUB (control outcomes stay in DELIVER, as
  the author confirmed). Both are fixed by the request data, so W stays schedule-invariant.

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

## Contextual templates and explicit levels (§49–§56, §59)

- **Scopes (§50).** `ScopeId` interns `(locals, body, result type, level, guard)`; local
  occurrences are `bound_id(depth, slot)` atoms (`BOUND_BIT`, below the atom shift of the
  interval/face encodings) in the variable and dimension id spaces, so every existing
  structural operation treats them as identities it never substitutes. `capture_scope`
  closes concrete identities (depth-shifting scopes already inside), `apply_scope` returns a
  `TypedPartial{body, type, level, guard}` by one simultaneous traversal, `reindex_scope`
  touches free identities only, `forall_scope` quantifies the unary dimension of a total face
  scope. The traversal engine (`Trav`) is depth-aware and memoized per traversal key.
- **Templates (§51).** Each library definition is registered once as an expression DAG with
  typed parameters (κ in slot 0, levels as parameters) and fixed constructor nodes
  (`NODE` records with field recipes, binder slots, payload/levels/required-face recipes).
  `template_call` interprets the root program; a constructor node yields
  `TVIEW(node, environment)` with the environment restricted to the node's free slots, so
  `reindex(T(a), τ) = T(a[τ])` is an identity of references for every parameter including
  type and family arguments (`test_templates.c`: refl/Fun/Equiv/IdEquiv under a type-changing
  substitution, `Down` under a reindexed scope). Opening a TVIEW interprets its field recipes;
  reindexing reindexes the environment and runs no field program.
- **Levels (§59.1).** Every origin record carries a packed levels word; the annotated
  constructors `mk_pi_lv`, `mk_sigma_lv`, `mk_lam_lv`, `mk_comp_lv`, `mk_path_lv`,
  `mk_glue_*_lv`, `mk_pair_at_lv` set it, `LEVEL_NONE` marks an unannotated user term whose
  level the checker infers. Templates always annotate; the library API takes the exact levels
  of its type arguments (`mk_fun(l, m, X, Y)`, `mk_refl(l, A, a)`, `mk_coe_at(l, i, A_i, cap)`,
  …). The checker validates every annotation against the formation level it infers
  (`level_ok1/2`), a template instance's retained reference parameters against the
  signature's instantiated declared types (`tnode_signature`), and a `TRANSFORM_CALL`'s
  annotations against the record's stored levels.
- **Composition (§53–§54).** `comp_clause(j, fam, φ, tube_j, cap, η)` captures the exposed
  head's components (`D`, `E`, `B`, `left`, `right`, `A`, `α`, `T`, `e`, the tube) into scopes
  over the evaluator's dimension with the producer entry's face as κ and instantiates the one
  fixed clause (`PiComp`, `SigmaComp`, `PathComp`, `GlueComp`, `UniverseComp`). The evaluator
  performs this inside its frame (§55: no additional administrative agents for the same
  call); a family without its level annotation is not admitted core syntax: no clause is
  instantiated and the demand is reported invalid.
- **Environments (§57 R1).** `check_admission` freezes the registered environment before
  validating it; while frozen, `define_global` returns 0 and `set_global_body` returns false.
  `check_open_environment()` opens a new candidate environment: a fresh checker session
  (claims, admission verdict, diagnostics) and a reset evaluator (all observations retired;
  workers and policies kept). It is a closed session boundary and a host precondition: the caller stops admitting
  clients and waits for whole public calls to return and evaluator work to drain (the
  in-progress counter, the attempt flag and `eval_reset`'s outstanding check are partial
  assertions of this, not its enforcement); `EvalResult` and diagnostic pointers from before
  it are dead. A new machine starts with an open environment (the version counter is never
  reused), and a thread's template source face κ is qualified by the machine generation. An admission verdict is reused for its environment version
  when settled, and an UNRESOLVED one only within the attempt that produced it
  (`check_new_attempt`, or a changed budget, begins a new attempt; a top-level request's
  budget is fixed when it enters).
- **Environment-qualified caches (§57 R1).** Every checker claim and every evaluator memo
  entry is keyed by the definition-environment version, so registering a declaration or a
  body in an open candidate environment makes all earlier verdicts, conversions and
  observations unreachable; nothing from before a mutation can establish validity after it.
  An occurrence is used only under a clause entailing its required face, on every checking
  path. Finite structural validity of references and scopes (`ref_validate`, `scope_validate`)
  is checked before any opening, independent of faces, by a walk separate from the
  substitution traversal: it covers boundary images, the stored fields of raw origins
  (inactive branches included), template environments and every nested scope with its
  actual telescope stack.
- **Levels are required (§59.1).** Every type position of admitted core syntax carries its
  level: `LEVEL_NONE` at a Π/Σ/λ/Path/PApp/Glue/comp/annotated-pair position is INVALID in
  inference and in checking, and the evaluator instantiates no composition clause for an
  unannotated family. The unannotated constructors remain for raw construction only.
- **Template boundary (§51.4).** A node's environment is closed under the declarations of
  everything it retains: parameters (declared type, level, guard, scope signature) and the
  term locals it uses freely (constructor-binder locals and scope locals, whose declaration
  recipes are recorded and closed after the definition is complete), so `Refl(0,A,x)`,
  `Refl(0,B,x)` and `Refl(1,A,x)` are three references and a child escaping its binder keeps
  the binder's declaration. A program whose root calls another program is integrated at
  registration into a caller-owned node (`LineEquiv`, `ExtendContr`, `Down`), so the caller's
  parameter signature and result type remain the retained boundary. Every library parameter
  is declared (partial ones with their guard); an instance is validated at its boundary
  before its head: reference and local images against the instantiated declared types on
  their declared guards; scope arguments first for their finite structure (`scope_validate`, before any
  opening and independent of faces: bound occurrences name existing telescopes and slots of
  the right sort, declarations use their prefix, metadata present) and their own validity
  (locals' declarations form at their required levels under their own required faces,
  result type and body under the supplied guard) and then against their contextual signatures (common fresh telescope,
  declarations by conversion, expected guard ⊢ supplied guard, result types converted under
  the expected guard); and the inferred type against the program's declared result type.
  Checking forms (λ, pair, path λ, system) enter the same boundary.
- **Claims and admission (§57, §59.4).** The claim table has a session generation (a fresh
  `check_init` re-registers thread identities, `review-checker-lifecycle`: eight identical
  conversions after a restart), per-attempt UNRESOLVED outcomes that are retried by a later
  attempt, and every wait re-reads its claim pointer after resuming (`review-claim-wait`
  forces claim-vector growth during a wait). `check_admission` validates the whole registered
  environment once per environment version; `observe_checked` and every compiler publication
  enter it first, so a rejected registered body blocks checked execution of every term
  (`review-followup admission`, `test_check.c`).

## A worked program: speculation under faces (`tests/demo_speculation.c`)

A latency-critical decision — on the next tick send one of two orders, both depending on
an expensive shared model evaluation — written as terms: the tick is a dimension `i`, the
decision is the partial element `[i=0 ↦ down(pre), i=1 ↦ up(pre)]` defined on the boundary
`i=0 ∨ i=1`. The program shows, with the event counters: the decision is not observable in
the interior (demanding it under ⊤ is refused); speculating is demanding it under each
outcome face, and the shared prefix is one memo key for both (the second branch finds it
ready); when the tick arrives the demand under `i=1` launches no producer and returns the
speculative result object; the decision reindexed at `i=1` resolves to the same object in one
dispatch step; specializing the decision to another model input by substitution re-evaluates
only what mentions it; and W is identical under FIFO, LIFO and random scheduling with and
without a worker pool. It runs in `make test`.

## Identity compiler (§39–§48)

`src/compiler.c` is additive to the runtime above and emits only annotated core syntax
through the existing constructors and the fixed library templates (§40 builders: `refl`,
`inverse` = `mk_path_rev`, `concat` = `mk_path_concat`, `Down`, `pair` with its Σ
annotation, …), every type position carrying its explicit universe level (§59.1).

- **Diagrams.** `diagram_declare(Γ, nodes, B, ℓ_B, o)` / `residual_declare(Γ, nodes, Z, ℓ_Z)`;
  a node is `(node_id, x, e, A, ℓ_A, t)` with the user's variables `x : A`, `e : Path_A(t, x)`.
  `diagram_validate` checks the typed telescope in order under the required face, that every
  type position is a type (`check_is_type`: the inferred type is observed and must be a
  universe, §59.5) and that its formation level equals the annotation. `diagram_realization` is the right fold
  `R_k = Σ(x_k:A_k).Σ(e_k:Path(t_k,x_k)).R_{k+1}`, `R_n = Path_B(o, y_d)` (residual: `Z`);
  the canonical substitution `ν` extends by `x_k ↦ t_k[ν], e_k ↦ refl` and `C = o[ν]`, so a
  shared node has one image and the DAG is not expanded.
- **Singleton maps (§41, §54).** `Down(ℓ, ℓ_A, A, t, D, x, e, z) = coe^i D⟨e@¬i, ⟨j⟩e@(¬i∧j)⟩ z`
  with `D` the captured scope `[x_k : A, e_k : Path_A(t, x_k)]. R_{k+1}[prefix]`: the fixed
  template applies the scope by contextual substitution, so the tail is specialized without
  any APP/LAM pair and the same origin serves every diagram; `emit_collapse` / `emit_expand` follow the
  stated recursions; `diagram_collapse(d)` and `diagram_expand(d)` are cached per diagram
  and role with formals `r_d : R_0` and `q_d : Path_B(C, y_d)` anchored in the diagram.
- **Identity (§42).** `graph_pair(L, R)` is the proof-parameterized template cached by the
  ordered pair: common `y`, fresh `P`, distinct input slots, `forward = d_R(concat(inverse(P),
  c_L(r_L)))`, `reverse = d_L(concat(P, c_R(r_R)))`, every subtemplate instantiated by mapping
  its formal to the argument (no APP/LAM pair). `compile_identity` validates the context,
  face and result type, both diagrams, the evidence at `Path_B(C_L, C_R)`, specializes `P` to
  the evidence, checks both bodies at their stated types in `Γ, y, r`, and publishes only
  then. `certificate_verify` re-runs the same derivation and requires an identical record.
- **Other schemas (§44).** `compile_equivalence` (`(fst e) a`, `fst(fst((snd e) b))`),
  `compile_residual_equivalence` (`d_R ∘ e.map ∘ c_L` with the terminal types as base case),
  `compile_cut` (`Cut(C,D) = Σ(z:B).Σ(u:C=z).(D=z)`, `(z,u,v) ↦ u·v⁻¹`, `h ↦ (D,h,refl D)`),
  `compile_contractible_fibre` (`(b,r) ↦ b`, `b ↦ (b, fst(k b))` from a checked `k`). All are
  fixed templates with a certificate recording their retained inputs.
- **Invocation (§43, §59.3).** Compiled records are interned by their structural key (the
  environment version, schema and every certificate input; registry numbers are not key
  fields), so identical requests, sequential or concurrent, obtain one record; diagrams are
  interned by their declaration likewise. Publication builds one fixed call origin per orientation,
  `generic_call[id,dir] = TRANSFORM_CALL(id, dir, identity images of the parameter context,
  VAR(argument_slot), domain, codomain, required)`; a record becomes visible only after both
  exist. `mk_transform_call(id, dir, σ, a) = reindex(generic_call[id,dir], σ|Γ + slot ↦ a)`,
  so a reindexed call and a call built at the reindexed data are one `RefId` and share one
  application/receiver pair (`review-followup call`). The checker validates the record, `σ`
  as a typed map whose face entails `required[σ]`, `a` at the instantiated domain, the
  annotations by conversion and their formation levels against the record's stored
  `domain_level`/`codomain_level`, and returns the output annotation. The evaluator's dispatch allocates `APPLY_TRANSFORM(id,dir,σ) -- REF(a)` with
  `CONTINUE_REFERENCE(K)` on the result in the evaluator's own net; the application rule
  produces `REF(reindex(template, σ + slot ↦ a))` without evaluating anything; the receiver
  rule issues `REQ(key(v, face K), FORWARD_RESULT(K))`; delivery publishes `K` through the
  ordinary protocol. Pending pairs are jobs of the same scheduler (`outstanding` counts
  evaluator jobs and pairs; a pair is enqueued before the creating job finishes), with their
  own selection policy (`eval_set_pair_policy`). `APPLY_TRANSFORM` and `CONTINUE_REFERENCE`
  are local rule events (`eval_net_events`), compared across schedules like the others.
- **Verification (§47).** `tests/test_compiler.c`: the empty diagram; a tail depending on
  its witness; the complete associativity declaration in both orientations (the emitted
  collapse is one transport with a false tube in a path family, the expansion the stated
  triple; the call checks, exposes the pair without evaluating the path, one application and
  one receiver event, repeated demands share the entry); a shared predecessor (one block,
  one image); dimension substitution and strengthened face (opening the reindexed call gives
  the composed data, support follows the boundary, keys are rebuilt from the call's support);
  rejections (wrong endpoints, bad node type, unmet face; a budgeted run publishes nothing
  unless checked); a higher path in the evidence parameter (`⟨i⟩F_{H@i}(r)` at its path
  type); cut followed by loop conversion (the residual is not refl); contractible-fibre
  projection/section and a rejected non-contraction; an external application pair into an
  `EVAL` consumer and into a storing consumer; recursive arguments (the pair is exposed, a
  demand through the identity equivalence at a cyclic argument stays `W_STUCK`, nothing is
  synthesized). `tests/test_schedule.c` demands the same calls under three faces and after a
  dimension substitution and compares W (including the two new rule classes) and the exact
  result graphs across 24 schedules.


## Identity-execution accounting and cost refinement (§§60–71 as disposed by §73)

`src/work.*` adds the accounting layer over the accepted machine. Nothing in it
selects a program: every operation is an explicit request over existing checked
records, and the two components §73 excludes — the §68.2 cofactor solver and the
§69.2–69.3 frontier/incumbent — are absent. A formula no direct rule reduces is
returned unreduced (`Reduction.reduced == false`); no fallback enumerates it.

**Work identities (§60.1, §62.1).** An atom is an interned record
`[kind, operands…]`: `WK_PRODUCER (ref, projected face, env version)` is the
evaluator key; `WK_REQUEST / WK_DELIVER (owner producer or 0, slot, child)` are
one consumer occurrence's two events (slot = the ordinal among the owner's
occurrences, so two requests of the same key by the same owner are two atoms);
`WK_PUB (producer)`, `WK_EVAL (producer, ordinal)` are its publication and each
of its frame steps; `WK_APPLY (transform, dir, σ, argument, receiving producer,
ordinal)` is one identity application; `WK_SLOT` is a schema parameter;
`WK_NAMED` a host control atom. A key names operation and operands, never a
value: two atoms with coincident outputs stay distinct.

**The trace (§73.3(1)–(2)).** The evaluator now records, per entry, its consumer
occurrences in request order (`Entry.deps`), its frame steps (`Entry.steps`,
EVALUATE and RESUME jobs whose destination is the entry) and its environment
version; root and external requests form a global root-occurrence list. The net
records every committed `APPLY_TRANSFORM` (with the `CONTINUE_REFERENCE(K)` it
feeds) and every `CONTINUE_REFERENCE`. `dgraph_from_trace_since(first_root)`
turns this into a producer graph; `work_ready_snapshot()` is the quiescent K of
a run (every key READY now).

**Demand (§60.2–60.4).** `demand_closure(graph, roots, K)` is the least fixpoint
with the cut: a ready root or child contributes its REQUEST/DELIVER occurrence
and nothing of its cone. `work_extract` enumerates the work: one REQUEST and one
DELIVER per occurrence, PUB and the EVAL steps per demanded producer, the APPLY
atoms a demanded producer received. On the actual run (`test_work` cases 1 and
10) the extracted counts equal the coarse event deltas: REQUEST = `request`,
DELIVER = `deliver`, PUB = `publish`, EVAL + (root/external delivery frames) =
`eval_step`, APPLY = `apply`. The §60.2 laws (closed K ⇒ subtraction; union of
roots) are checked on recipe graphs.

**Algebra (§61).** Families are interned antichains of sets; `family_plus/times`
apply N (duplicates and strict supersets removed, each subset test a merge walk);
`formula_antichain` is the counted expansion to the semantic normal form;
`family_dominates` is the subset-coverage criterion of §61.3; `family_residual`
is f_A(K). The tests check absorption, distribution, and the sharing example.

**Specialization (§62).** `set_specialize` / `formula_specialize` / `plan_specialize`
reindex the complete typed boundary of every identity, validate it
(`ref_validate`, required face), re-intern, then deduplicate: the Boolean direct
image. Cache subtraction and costs come after that identification (case 3
reproduces §62.3 both ways). `plan_specialize` checks σ with `check_map`,
re-checks the realization under the target context and keeps the first-occurrence
order of the image.

**Cost differences (§63).** `costdiff_make(A, B, K, C, model)` retains both
supports, K, C, the model and the session/environment snapshot and derives
ε = cost(A∖K) − cost(B∖K) and the overlap-masked difference. Inversion and
telescoping are checked on the associativity realizations.

**Typed records (§66–67).** `boundary_make` (context, face, inputs, type and
level — `check_is_type` at creation — continuation evidence) is interned with the
session and environment version; `plan_make` checks `r : type` and the typing of
its connecting evidence and anchors an ordered work list; `connector_make`
carries left/right/result boundaries, a transform or evidence reference, and its
work (absent work and absent evidence are distinct rejections);
`expr_empty/plan/alt/join`. `problem_prepare` validates the expression
(common boundary, connector interfaces equal to the composed boundaries,
evidence and work present), fixes the atom order by first occurrence in the
pre-order traversal of the ordered fields, builds F (PLAN = ∧ of its list, ALT =
∨, JOIN = ∧ with the connector's atoms) and F_K = F[e := 1 for e ∈ K], and
interns the problem with session, environment, boundary, model, expression, F,
F_K and order list — the key a certificate must name.

**Formulas (§68.1).** `ZERO | ONE | ATOM | AND | OR` records with exactly the six
constructor simplifications; `formula_restrict` is syntactic, memoized by
(F, e, b); `formula_subst` iterates it over a set. Support and Must are cached per
formula node.

**Realization (§68.3).** `realize(problem, S)` marks S ∪ K, evaluates the
expression (ALT: first satisfied child; JOIN: both children and the connector;
PLAN: all atoms available), rolls back witnesses of unsatisfied subtrees, and
checks W(p) ⊆ S ∪ K; its residual cost is Σ_{W(p)∖K} w. `realization_reference`
exposes the plan's own checked reference; execution is the ordinary machine.

**Certificates (§69.1, §69.4).** Proof nodes `(rule, F, aux, c1, c2, value)` for
TRIVIAL, FALSE, MANDATORY, SPLIT, FACTOR, DISJOINT_AND, OR_BOUND, WEAKEN and
EQUAL (the §70.3 displayed equality (X∨Y)∧(X∨Z) = X∨(Y∧Z), re-derived
structurally by the checker). `certificate_check` requires the certificate to
name the problem being checked, the problem to be current, the root formula to
be F_K, recomputes every premise (cofactors by `restrict`, Must, substitution,
disjointness, the equality image) and every value with checked arithmetic,
rejects a missing child and a back-reference to a node under check, reconstructs
the upper witness from its support and requires L = U finite (optimum) or L =
INFINITY with no witness (emptiness). A sum outside the checked range is
`CERT_UNRESOLVED` (resource limit), never INFINITY. `geo_check` validates a
supplied finite geodesic certificate against exactly its stated edges: terminal
V = 0, V(s) ≤ c + V(s′) on every edge, an attaining admitted step at every
finite-V nonterminal, progress by positive cost or a supplied decreasing rank.

**The direct fragment (§70).** `formula_reduce` is bottom-up: ZERO/ONE/ATOM
directly; OR by OR_BOUND; AND by DISJOINT_AND when the supports are disjoint,
else by FACTOR when Must(F) ≠ ∅ (recursing on F[M := 1], strictly fewer atoms),
else by EQUAL/shared-or when F has the shape (X∨Y)∧(X∨Z); otherwise
unreduced. `problem_reduce` turns a reduction into a certificate whose upper
witness is the realization of the attaining support. Case 7 checks the values
against the expanded antichain on six formulas and checks the factoring and
disjoint-additivity equations. `schema_make/instantiate`: a formula, proof and
attaining set over slot atoms; instantiation maps atoms (possibly identifying
slots), rebuilds the proof with recomputed values and runs the checker, which
re-establishes Must, disjointness and weights — an instance identifying two slots
of a DISJOINT_AND is refused with "supports are not disjoint".

**Frames and the ledger (§65, §71).** Every operation is an `OpId` with a frame
stack; `op_step(h, budget)` executes at most `budget` frames and returns
`OP_RUNNING` (resumable), `OP_COMPLETE`, `OP_RESOURCE_LIMIT` (checked-arithmetic
overflow; state retained) or `OP_INVALID` (diagnostic). Frame bodies are bounded:
interning hashes one word per step, probes one slot per step, compares one word
per step, copies one word per step (`FORMULA_INTERN_STEP / TABLE_PROBE /
ALLOCATE_CHUNK`); set union/intersection/difference, subset and Must/support
merges advance one element per step (`SUPPORT_CHUNK / MUST_CHUNK`); sums add one
limb per step (`COST_ADD_CHUNK`); traversals have ENTER / WAIT_LEFT / WAIT_RIGHT /
FINISH phases with memo lookups as counted probes. Families PREPARE_VISIT,
VALIDATE_PREPARED_BOUNDARY, FORMULA_VISIT, FORMULA_INTERN_STEP, COFACTOR_VISIT,
COFACTOR_REBUILD, SUPPORT_CHUNK, MUST_CHUNK, COST_ADD_CHUNK, COST_COMPARE_CHUNK,
CERTIFICATE_VISIT, REALIZATION_VISIT, ALLOCATE_CHUNK, RELEASE_CHUNK are the
required ones; SOLVE and FRONTIER are omitted as §73.2 says; TABLE_PROBE,
DEMAND_VISIT, SPECIALIZE_VISIT, FAMILY_CHUNK and GEODESIC_VISIT are the
additional families of the retained operations. The ledger (`work_ledger`)
counts frames by family and by phase (prepare / rewrite / check / commit /
execute), probes, word comparisons, limb operations, allocated and released
words, memo lookups/hits/deliveries, and the execute phase as the coarse event
vector of the run (`work_record_execution`) — the §65.1 projection. Calls into
the kernel (`reindex`, face operations, `ref_validate`, the checker) are counted
as `kernel_calls`; their internal traversal is the kernel's own, not refined
here. Case 8 suspends every operation at budget 1 and checks that the result,
and the number of frames, equal the uninterrupted run; case 9 checks the phases,
families, memo reuse and reclamation.

**What stays outside.** No `begin_selection/step_selection/commit_selection`;
`op_step` on an operation handle is the bounded interface. No incumbent, no
frontier, no cached inequality from an interrupted check. Ordinary execution
never consults a prepared family; `realization_reference` returns a reference the
checker already accepted and the evaluator runs it by its fixed recipe.


## Uniform reuse (§§74–82): identity-execution accounting on persistent computations

The increment makes mathematical work belong to persistent computations and
reusable answers, not to temporary handles, source labels, whole-environment
counters or unused context declarations. The accepted cubical formulas, scope
machinery, typed occurrence records, validation regressions and the
one-producer protocol are unchanged; §73's exclusions stay in force (no
solver, no frontier, no plan search, no learn/retire subsystem).

**Four records (§74.1).** *Occurrence*: the requested `RefId`, its context,
ambient face and validation — retained in full (every negative check is
unchanged). *Computation*: `(shape, projected face)` — the evaluator's
`Entry`, whose canonical reference is the first requester's. *Answer*: the
result, its residual and reduction receipt, and the `(symbol, revision)` pairs
it read. *Delivery*: each consumer's own REQUEST/DELIVER events (and, for
alias publications, the residual key's own entry).

**Structural identity (§76, `src/shape.*`).** `shape(t, ρ)` is the interned
descriptor `[SH_NODE, tag, payload, levels, required face, fields…]` of the
opened construction, with binder-bound identities replaced by `(depth, slot)`
tokens through the existing binder resolution (`resolve_*_binder`, so the
domain is shaped in its prefix context and fields under one slot share one
local), free identities anchored, intervals/faces in their existing normal
forms with bound atoms renamed. No evaluation, no GLOBAL unfolding; views and
template views are opened through their existing APIs so a direct
constructor, a specialized view and an equal template view have one shape
(A1–A3); levels, required faces, proofs and distinct free variables keep
their distinctions. Memoized per (reference, ρ, depth); each constructed node
is `REUSE_SHAPE_NODE`.

**Producers (§76.3, §79).** `entry_intern` keys by `(shape, π_{S(t)} χ)` and
keeps a chain of historical entries under that key. A READY entry is reusable
when every recorded `(symbol, revision)` is current
(`global_revision`, bumped by `set_global_body`; an opaque observation
records revision 1, "absent body"); a RUNNING entry is reusable while the
environment version it was created under is current. Dependencies are the
producer's direct reads (`T_GLOBAL` dispatch) ∪ the READY children's sets,
fixed at publication. An unrelated declaration therefore changes nothing (A8,
`environment`); an opaque→body transition retires exactly the answers that
read that symbol (A9). `check_open_environment` opens a new checker session
and leaves the evaluator's answers in place.

**Receipts, residuals, adapters (§78).** Every rule site emits its receipt
(`RC_REFL | RC_SEQ | RC_RULE(rule, …) | RC_RESTRICT(src, face) |
RC_SPEC(src, map)`, rules per the §78.2 table) and the entry records its
residual: the forwarded child's residual after a reduction prefix, or the
eliminator rebuilt around a neutral scrutinee's residual (`rebuild_elim`,
also for `comp` around a neutral family). A new producer first consults
(a) the same shape at a weaker face and (b) the recorded instantiation edges
`dest = reindex(src, σ)` of the requested reference and of every reference
requested with its shape; a READY, dependency-valid source whose face
premise is entailed supplies an adapter: the producer continues from
`reindex(residual, σ)` (or the residual itself under the stronger face) and
observes it normally — a formerly neutral residual may reduce further (A5),
an endpoint may be reached (A7). A candidate whose continuation key is this
key gives no progress and is skipped (A18). Adapters count as
`REUSE_RECEIPT_INSTANCE`, never as a rule or body. A residual that differs
from the producer's reference is head-normal under its face by construction
and receives the same answer under its own key (alias publication, no body
run) so later demands of it are ready hits.

**One action per content (§77.1).** The compiled record key is the semantic
content (schema, typed inputs, derived record); `IdentityDecl.id` and the
environment counter are gone from it. Source declarations are a provenance
index (`transform_sources`); a relabelled declaration returns the same
`TransformId`, the same generic call, and its second call performs no second
`APPLY_TRANSFORM` (A10); different evidence stays a different action (A11).

**Projected judgments (§77.2).** Conversion claims are keyed by the context
projected to the dependency-closed free declarations of the operands and
type, in telescope order; every claim records the symbol revisions it read
(directly, or through the evaluator entries its observations used) and a
verdict whose dependency changed is recomputed. Whole-signature admission
(`CL_SYMBOL`) stays keyed by the environment version. Weakening by an unused
declaration reuses the judgment (A15, `checker`).

**Runtime proof action (§80).** `identity_pair(L, R, B, lB, params)` exposes
the graph-pair template; `identity_action(pair, dir, σ, proof, argument)`
instantiates one orientation by a single simultaneous map (σ on the
parameters, `P ↦ proof`, `r ↦ argument`; the images are not reindexed again).
The result is an ordinary core term: a program `λP. λr. (action(P, r), P)`
applied to a projection-computed proof runs through the evaluator with no
compilation, publication or `APPLY_TRANSFORM` (A19); it agrees with the
compiled transform by conversion.

**Persistent pure operations (§75, `src/work.c`).** Every shared operation
family (formula constructors, restrict/subst, support/Must, set operations,
sums, specialization, preparation, realization, certificate and proof
checks, reduction, antichains, geodesic checks, schema maps) is a `Job`
keyed by family + immutable operands + the external versions it reads
(rule-set version for proofs/reductions; environment for specialization;
session+environment for preparation/certificate checks; builder revision for
demand graphs and geodesic builders). A job's frame stack is its shared
continuation; private helpers (interning, probes, sorts, lists, visits with
pointers) run on that stack, and a request for another shared operation
joins its job (`waiting_on`), creates it, or receives the READY answer at
once. `op_step(handle, budget)` services enabled jobs in the handle's cone,
one frame per unit of budget; two handles on one key step one job
(`handles`), releasing a handle retires only the handle, budget exhaustion
leaves the continuation resumable. Reduction answers are keyed by
`(formula, model, rule set)`, realizations by `(problem, support)`, demand
records by `(graph, revision, roots, ready)`: no sequence-qualified
mathematical results remain (`work`, A12). Work atoms for producers name
`(shape, face, snapshot)` — the shared instance — with a representative
reference for specialization kept beside, not inside, the identity.

**Counters (§74.2, `src/reuse_stats.h`).** `reuse_count` reads the
production counters: `EVAL_BODY`, the rule counters (`BETA`, `FST`, `SND`,
`PATH_BETA`, `ENDPOINT`, `GLOBAL_UNFOLD`, `GLUE_RULE`, `SYSTEM_RULE`,
`COMP_EXPAND`, `IDENTITY_APPLY`), `CONVERSION_BODY`, `REDUCE_BODY`,
`PROOF_CHECK_BODY`, and the administration `SHAPE_NODE`,
`DEPENDENCY_CHECK`, `RECEIPT_INSTANCE`, `READY_HIT`, `RUNNING_JOIN` — bumped
where the rule executes, never on delivery; monotone until `machine_free`.

**Measured before/after (the eight assessment cases, `tests/baseline-3a0d7c4/results.json` vs the gates now).**

| Case | 3a0d7c4 | now |
| --- | --- | --- |
| construction route (A1) | 1 producer, 4 frames for the direct construction | 0 producers, 1 delivery frame; one shape |
| bound names (A2) | 2 producers, 5 frames | 0 producers, 1 frame |
| generic then specialized (A4) | 1 producer, 4 frames incl. the beta | 1 adapter launch, 3 frames, 0 betas (receipt instance) |
| stronger face (A6) | 1 producer, 4 frames incl. the beta | 1 adapter launch, 3 frames, 0 betas |
| unrelated global (A8) | 3 producers, 6 frames | 0 producers, 1 frame |
| identity source name (A10) | second record, second call, 1 APPLY_TRANSFORM, 1 producer | same record and call, 0 APPLY, 0 producers |
| repeated reduction (A12) | 1 365 then 965 frames, different result records | 1 206 then 0 frames, one result record |
| conversion under weakening (A15) | 2 new claims, 2 steps | 0 conversion bodies |

**Schedule claims (§78.5, §81.3).** The fixed-recipe event-vector theorem is
retained for a fixed initial ready set and a fixed selected reuse graph
(`test_schedule`, `demo_speculation` unchanged). Opportunistic receipt
discovery can change which adapter a producer takes under another schedule;
the selected edge is recorded (`eval_entry_adapter_source`) and no equality
of the fine counts is asserted across policies.

**Bounded-helper audit (§81.2, revised by §94).** Word size 64 bits; checked
natural costs below 2^62 with overflow reported as `OP_RESOURCE_LIMIT`; chunk
bound `CHUNK_WORDS = 32`; allocator model: `malloc/free/realloc` of a block are
one step each, vector growth amortized one word per pushed word (charged as
`alloc_words`). The contract of `op_step(h, b)` is: at most `b` units, each one
of the bounded bodies below, and the continuation retained. The table lists
every variable-size operation reachable from a unit, with the state it keeps
between units:

| Operation | Status | Retained state |
| --- | --- | --- |
| hashing, probing, word comparison, record copy (`INTERN/LOOKUP`) | framed: one word / one probe / one word per unit. A suspended insertion is one transaction (R1 of the ba09e33 review): the record's whole extent is reserved in the store in one unit before any word is copied, so no other candidate's words can interleave; the record is unpublished (no id, no slot) until complete; a saved probe cursor is valid only for the slot array's generation (`KTab.gen`) and otherwise restarts from the hash; after copying, the probe is re-established in the current table — an equal key interned meanwhile is returned as the one canonical id and the reserved extent is abandoned (counted as released), otherwise the complete record is published at the slot the fresh probe found | `i`, `j`, `e` (generation), `acc2` (reserved offset), `acc3` (candidate), `acc4` (held) |
| table growth | framed: one relocation unit = at most `CHUNK_WORDS` source-slot visits + probes in total, the collision chain in progress resumed from its probe cursor (`KTab.moving/probe`); a frame that meets a relocation another job began advances it one unit per unit (`INTERN` ph 4, `LOOKUP` ph 3) and never drains it synchronously | `cursor`, `moving`, `probe` |
| request of a shared operation (`push`) | framed `JOIN`: the key interned by the framed `INTERN`, then one unit to find/create/deliver; a join of a running job commits its wait only after a cycle check of one chain hop per unit (`CYCLE_CHECK`) | JOIN frame: key words, `acc2` (job), `acc3` (hop cursor) |
| delivery to waiting parents | one delivery per unit: a finished job answers the waiter below it on the servicing root's cone path (`deliver_to`); other waiters are answered one each when their own roots are stepped; a job whose child is complete but whose delivery is pending stays schedulable; `waiters` keeps one registration per join | root `path` |
| scheduling (finding the enabled job) | the root keeps its cone path root → … → tip; a unit extends it by one hop, pops a finished tip (delivering), or steps the tip (`SCHEDULE_STEP`); no unit walks a chain | `Op.path` |
| failure cleanup | `fail` retains the stack; one retained frame is released per unit when the failed job is a cone tip (`RELEASE_CHUNK`); `work_free` releases the rest | the stack itself |
| family normalization (`NORMALIZE`) | keep-flag initialization `CHUNK_WORDS` per unit; pair tests one unit each; survivor compaction `CHUNK_WORDS` per unit; the survivors are handed to `SORT` by ownership transfer | `i`, `j`, `acc` (write cursor), `buf2` |
| variable payloads into `SORT` / `INTERN` / `LIST` from a frame's own buffer | ownership transfer (`fr_sort_own`, `fr_intern_own`, `push_intern_own`): constant work, no copy | — |
| set merge, subset, Must/support merge, sums, comparisons | framed, one element / limb per unit | `i`, `j` |
| sorting | framed heap sort: one sift (≤ 64 compares) per unit, one element per dedupe unit | `i`, `j` |
| `expr_boundary` | memoized per node; first computation charged one VALIDATE step per node | memo |
| proof / aux-list / reduction / mapped-proof / hypotheses-set records inside a frame | framed: `REDUCE` and `MAPP` end in a finishing sequence of framed `INTERN` children (aux list, proof, reduction record; `MKF` for the mapped formula), `PREPARE` interns its hypotheses set by `push_intern_own`; no `intern_sync` is reached from `service/step` (R6) | `acc`, `acc2`, `acc3`, `i`, `j`, `c`, `d`, `e`, `buf3` |
| `set_has` in demand | binary search ≤ 64 compares | — |
| demand-graph node index, atom-map index, weight override lookup from a unit (≤ 4-word keys) | framed `LOOKUP` (one hashed word / one probe / one compared word per unit; generation-checked): the demand graph's producer → node index is a record `[K_MEMO, 0xD6, graph, producer]` looked up once per popped producer (`DEMAND` ph 12, `EXTRACT` ph 24); atom images (`MAPF` ph 7, `MAPSET` ph 2, `MAPP` ph 16) and the split atom's weight (`PROOF` ph 45, `MAPP` ph 17) are delivered by the framed lookup. `find_sync` remains for the synchronous constructors only (it never drains a relocation; its collision chain is walked inside the caller, outside the bounded API) | `acc3` (node record), `acc2`/`d` (held operands) |
| record-store growth (`INTERN` ph 5) | framed: reservation is a logical extent (header words only; the payload is written one word per unit by the copy phase and never zero-filled — the v14 review's `reservation.patch`); when the store has no capacity, one unit allocates the new block (no copy) and each following unit relocates at most `CHUNK_WORDS` words of the old block (`store_grow_chunk`); during the relocation every record below the old extent is read from the old block, which stays complete (a write below it is mirrored once the copy cursor has passed), and a reservation waits for the relocation to finish; the offset table is a non-moving chunked array (no relocation on growth). The synchronous paths complete a pending store relocation before touching the store (`store_settle`) | `KTab.sold`, `sold_n`, `smoved` |
| `PREPARE` order list and hypotheses set; `FAMOP` plus | ownership transfer: the order list is accumulated as the record itself (`K_LIST` first) and handed to `LIST`; the hypotheses are handed to the framed `SORT` (one sift / one dedupe element per unit) whose `INTERN` yields the set — no sort or copy inside the unit; `FAMOP` plus pushes one member per unit and hands its buffer to `NORMALIZE` | `buf2`, `buf3` |
| growth of a frame's own buffers and of the per-operation vectors (`words_push` on `buf/buf2/buf3`, `vec_push` on demand producers/occurrences, frame stacks) | **amortized only**: a push that doubles a private buffer copies it inside the unit; the words are charged (`alloc_words`) but the call is not suspended. (The shared record store and the offset table are no longer in this row.) | — |
| kernel calls from `ATOMSPEC` / `PREPARE` / proof-use audit (`reindex`, `fc_reindex`, `ref_validate`, `shape_of`, `eval_entry_lookup`, `infer`, `check`, `check_map`, `proof_use`) | **not refined**: charged as `kernel_calls`; the reuse administration they perform is charged retrospectively into `SHAPE_NODE` / `DEPENDENCY_CHECK` / `RECEIPT` from the kernel's counters (`kernel_mark/kernel_charge`), and the audit's traversal steps into `AUDIT_STEPS` (fine vector); none of these is resumable | — |
| constructor-level synchronous APIs (`set_make`, `plan_make`, `connector_make`, `model_with_weight`, `boundary_make`, `job_sync` entries) | outside the bounded API (no bounded-step claim) | — |

`tests/review_work_budget.c` (the author's probe, white-box over the NORMALIZE
frame) measures the correction: with budget 1, NORMALIZE over 64 and 4,096
candidates writes 32 keep flags per unit (before: 64 and 4,096 in one unit);
a shared support job with 256 waiting parents performs at most one delivery
per unit (before: 256 in the completing unit).

Consequently the §65 constant-factor refinement is **not claimed** for units
that reach the kernel (specialization of producer atoms, preparation's typing
and proof-use checks, and the assumptions a `PU_ASSUMED` audit appends) or for
the amortized growth of a frame's private buffers; it is claimed for the formula, set, cost,
certificate, realization, demand, family, scheduling and delivery operations,
whose every unit is one of the bounded bodies above. `FR_SHAPE_NODE`,
`FR_DEPENDENCY_CHECK` and `FR_RECEIPT` are now charged (from the kernel's
counts) but remain accounted rather than resumable families.

## Runtime constructions, the proof-use boundary and fine cost (§§83–84, 88–89, 92–95)

Baseline `b612a07` (the v9 delivery, reviewed in §92). The two review
corrections come first; then the next increment.

### R1 — residual aliases answer at their own boundary (§93)

`publish_with` (eval.c) used to copy the source result pointer into the
residual alias entry; the source's neutral `EvalResult.ref` is the original
expression, valid only at the source's context and face. The alias now
publishes a distinct immutable descriptor whose head is the residual itself
(`result_new(r->cls, residual)`, or `result_system(residual, …)` retaining
the branches); the dependency copy, projected face, single-producer lock and
the no-PUB alias convention are unchanged, and the alias is now published
before the source entry becomes READY (a consumer woken by the source's
answer finds the residual's key already answered — the author's scope probe
read the alias entry immediately after `whnf` returned and, with workers,
could run before the alias existed). `tests/review_alias_scope.c` (a
returned reference may not mention an undeclared variable) and
`tests/review_alias_faces.c` (opposite-face warm-ups may not change
`convert_term`) are gated with 0 and 4 installed workers. One adapted
assertion: `demo_speculation` step 3 compared result pointers across two keys
(the restricted decision and the speculative branch); the branch key is
alias-published and now carries its own descriptor whose head is the
residual, so the step asserts the speculative entry's residual (the rebuilt
`up` eliminator around the evaluated prefix) and class with one dispatch
launch and no branch work, which is the mathematical content (§93.3: pointer
equality across keys is not required; the neutral at the source key keeps
its original eliminator reference per §12).

### R2 — bounded units inside work.c (§94)

The bounded-helper table above is the revised contract. The engine changes:
`push` of a shared frame is a `JOIN` frame (key interning through the framed
`INTERN`, then one unit to join/create/deliver, with a one-hop-per-unit cycle
check); the scheduler keeps a per-root cone path instead of walking the
waiting chain; delivery is one waiter per unit; `fail` retains the stack and
the scheduler releases one frame per unit; NORMALIZE's flag initialization and
compaction are chunked; frame buffers are transferred by ownership into
`SORT`/`INTERN`/`LIST`; table relocation keeps a probe cursor and is never
drained synchronously by another handle. Two new ledger families,
`SCHEDULE_STEP` and `CYCLE_CHECK`, count the scheduler's units.

### The ba09e33 review — six corrections (`REVIEW-ba09e33.md`)

| Finding | Correction | Regression |
| --- | --- | --- |
| R1 interning across suspension | `step_intern` is a transaction (table row above): reserved extent, unpublished until complete, generation-checked cursors, re-probe before publication, one canonical id; `step_lookup` cursors generation-checked; `find_sync` no longer drains | `review_work_edges interleave / same-key / growth` |
| R2 singleton Π level | `sing_formals`: outer codomain `max(a, r+1)` (author's patch) | `review_runtime_edges levels` (`a=2, r=0`) |
| R3 dependent residual export | `export_fold` carries the tail's already-specialized terminal `Z_k = Z_{k+1}[ν_k]` outward (author's patch) | `review_runtime_edges residual` (two-node loop residual) |
| R4 `rt_ap`, `rt_J`, `rt_reuse` | fixed templates over typed formals (`A,B,f,x,y,p`; `A,a,P,d,b,p` with the corrected outer Π level; `B,O,x,y,p,a`), one body per level tuple, one simultaneous instantiation — `reindex(inst σ₁, m) == inst (m∘σ₁)` as references | `review_runtime_edges commute` (three reference equalities) |
| R5 cold concurrency | `rt_init`/`proof_init` run inside `compiler_init` (serial lifecycle) and are torn down in `compiler_free`; public entries only require the module live; `rt_template_count` reads under the mutex | `review_runtime_edges runtime-cold / proof-cold` (8 clients, TSan) |
| R6 reduction unit draining growth | `REDUCE`/`MAPP` finish through framed `INTERN` children; `PREPARE`'s hypotheses set framed; `find_sync` non-draining; no `intern_sync` reachable from `service/step` | `review_work_edges drain` (cursor 0 ≤ 32, relocation retained) |

One more defined-behaviour fix found by the TSan run of `review_runtime_edges
residual`: `check` now writes an empty diagnostic on VALID (callers print the
reason after a valid check; it was left unassigned).

Still outside the unit bound after R6 (unchanged disclosure): fixed-key index
probes (`WordMap` in the demand graph, `find_sync` for weights and atom maps),
amortized buffer growth inside a unit, and the kernel/audit calls charged as
`kernel_calls`. The bounded-machine contract is not marked complete.

### The b8ba937 review — R2 through the §96 entry (`REVIEW-b8ba937.md`)

The review of the §96 delivery retains `rt_node_fun` and its tests, reports no
new defect in the wrapper, and adds one regression as coverage for R2:
`tests/review_node_level.c` checks `node_(2,0,0)` in the empty context — the
declared type forms at level 3 and the body must check VALID. On the corrected
tree it does (the body failed on the pre-R2 singleton annotation). It is gated
under both sanitizers, and the consolidated runner
`tests/run_b8ba937_review.py` (the twelve ba09e33 jobs, this regression, and
the production `test_runtime` suite) passes 14/14 under ASan+LSan and TSan
(`tests/acceptance-results/v15/`). The author's bundle is kept in
`tests/review-b8ba937/`.

### The v14 review — reservation and the §94 lowering continued (`REVIEW-v14.md`)

The v14 review accepts R1–R5 and the original R6 drain defect as corrected and
finds one more variable-size body inside R6: the reservation phase zero-filled
the payload in one unit. Its `reservation.patch` is applied as is
(`tests/review_reservation_budget.c`: n = 64 and n = 4096 payload words,
budget 1, payload words written in the reservation unit = 0, record completed
and canonical), and the lowering it asks for next is continued as the revised
rows above state: record-store growth in `CHUNK_WORDS` units with a non-moving
offset table (`tests/review_store_growth.c`: at capacity, one allocation unit
copies nothing; 128 relocation units of ≤ 32 words for a 4 096-word store;
records readable and findable throughout; the reservation waits), fixed-key
index probes from units through the framed `LOOKUP` (demand-graph node index,
atom-map images, split-atom weights), and `PREPARE`'s order-list copy and
hypotheses `qsort` replaced by ownership transfer into `LIST`/`SORT`
(`FAMOP` plus likewise). Both probes are gated under ASan/UBSan/LSan and TSan;
`run_v14_review.py` (fifteen jobs) passes under both
(`tests/acceptance-results/v16/`); the author's bundle is in `tests/review-v14/`.

Still outside the unit bound, stated exactly: (1) kernel and audit calls made
from `ATOMSPEC`, `PREPARE` and the proof-use audit (`reindex`, `fc_reindex`,
`ref_validate`, `shape_of`, `eval_entry_lookup`, `infer`, `check`,
`check_map`, `proof_use`, `transform_proof_use`) — charged as `kernel_calls`
with their reuse administration charged retrospectively, not resumable;
(2) the `words_append` of a `PU_ASSUMED` audit's assumptions into `buf3`
(kernel-sized); (3) amortized growth of a frame's private buffers and the
per-operation vectors; (4) `set_has` and the heap sift are bounded by 64
compares, not by one. The bounded-machine contract is not marked complete.

### §83 — presentations, diagram values and the generic action as core terms (`src/runtime.c`)

Every construction is one fixed template per universe-level tuple, built once
over keyed formal variables (`fresh_term_keyed`) and instantiated by
`reindex`; `rt_template_count()` reports how many exist. No registry, no
evaluator rule and no compiler call is involved in constructing or applying
them.

| §83 | Definition | Function |
| --- | --- | --- |
| 83.1 `Maps_{a,b}(X,Z) = Σc.Σd.(Πx. d(cx)=x)×(Πz. c(dz)=z)` | `rt_maps_type`; value `(c,(d,(h,k)))` | `rt_maps_id` (id, id, refl, refl), `rt_maps_compose` (`f'=u∘f`, `g'=g∘v`, `h'(x)=ap(g)(H(fx))·h(x)`, `k'(z)=ap(u)(k(vz))·K(z)`), `rt_maps_inverse` (swap) |
| 83.1 `Pres_{a,b}(Z) = Σ(X:U_a).Maps(X,Z)` | `rt_pres_type`, `rt_pres_const` | levels `max(a+1,b)`, never raised |
| 83.2 dependent singleton over `A, t, D:(x:A)→(t=x)→U_r` | `rt_singleton_type` (`S_D`), `rt_singleton_maps` (`c = Down`, `d = λz.(t,refl,z)`, `h = λw.⟨i⟩(e@i, ⟨k⟩e@(i∧k), fill(¬i))`, `k = λz.⟨i⟩fill_Z(¬i)`), `rt_singleton` (the presentation) | the author's witness terms, generalized to levels `(a, r)` with `D` a formal |
| 83.3 `Diagram_{b,r}(B) = Σ(C:B).Σ(R:B→U_r).Π(y:B).Maps(R y, Path_B(C,y))` | `rt_diagram_type`, `rt_diagram_zero` (`R y = Path(C,y)`, identity maps), `rt_diagram_extend` (`C' = C_{Q t refl}`, `R'(y) = Σx.Σe.R_{Q x e}(y)`, `maps'(y) = compose(singleton_{D_y}, maps_{Q t refl}(y))` with `D_y = λx e. R_{Q x e}(y)`) | accessors `rt_diagram_value/family/maps` |
| 83.4 action | `rt_action(dir, …)`: `F = d_R(y)(p⁻¹·c_L(y)(r))`, `G = d_L(y)(p·c_R(y)(s))`; `rt_action_fun` the closed `λL R p y r.` form with its type | `rt_action_middle`: `(λq.p⁻¹·q, λs.p·s, h, k)` with `h = assoc⁻¹ · ap(λv.v·q)(rinv p) · lunit q`, `k = assoc⁻¹ · ap(λv.v·s)(linv p) · lunit s`; `rt_action_maps = compose(compose(collapse_L, middle), inverse(maps_R))` |
| 83.4 groupoid laws | `rt_J` (`coe^i P(p@i, ⟨j⟩p@(i∧j)) d`), `rt_lunit`, `rt_rinv`, `rt_linv`, `rt_assoc` | generated by path induction left to right with later paths under Π in the motive; base cases by the finite word construction `K(w) : w = refl` (`K(refl)=refl`, `K(v⁻¹)=ap(inverse)(K v)`, `K(v·w)=⟨k⟩(K v@k)·(K w@k) · K(refl·refl)`, `K(refl·refl)@k@i = fill^j_A[(i=0)↦a,(i=1)↦a] a (¬k)`); two base words are equated by `K(u)·K(v)⁻¹` |
| 96.2 closed node function | `rt_node_fun(a,b,r,&type)`: `λB A t Q. extend(A,t,Q,B)` with its exact-level Π type `(B:U_b)→(A:U_a)→(t:A)→((x:A)→Path_A(t,x)→Diagram_{b,r}(B))→Diagram_{b,max(a,r)}(B)`, one template per `(a,b,r)` | checked closed for `(0,0,0),(1,0,0),(0,1,0),(0,0,1)`; applied to the §96.4 computed tail `id(λx e. zero(A,x))` its centre is `t`, its maps type-check, and it is β-convertible with the `extend` instance (test_runtime); the author's `review_runtime_nodes.c` is gated under ASan+LSan and TSan (runtime 0/4 and levels in both) — the full instantiated case that was resource-inconclusive under TSan on the author's host (§96.4) runs here in 5 s, the shape-memo correction below being the difference |
| 84.1 export | `rt_diagram_export(d, &type)`: right fold of `rt_diagram_extend` ending in `rt_diagram_zero(B, o)` (ordinary) or of singleton presentations composed at the centre ending in `rt_pres_const(Z)` (residual), memoized per diagram | compared with the compiler's `diagram_canonical`, `diagram_collapse`, `diagram_expand` by conversion (test case 3) |
| 84.2 reuse | `rt_reuse(O, p, a) = coe^i O(p@i) a` | — |

Checked facts (`tests/test_runtime.c`, all with `transform_count() == 0`):
the generic constructions type-check with only their parameters free (Maps,
id, compose, inverse, constant presentation, singleton maps and
presentation, Diagram type at `U_1`, zero, extend, both closed actions); the
four groupoid laws check at their stated types in a generic context; the
middle maps check with both witnesses; the full action maps are validated at
template level (compose checked once generically; each image of the
instantiating substitution checked at its formal's type) and their `c`/`d`
are convertible with `F`/`G`. `make runtime-full` (unsanitized) additionally
runs the direct checker over the fully expanded two-level composite and over
the exported one- and two-node diagrams with all four witnesses: 84 checks,
2 min 19 s on the reference host (the two-node export alone is most of it; under
ASan that one check exceeds the host's 8 GB, so the sanitized gate runs the
default mode: 76 checks in 20 s). §87 cases: (2) a core program builds a
nonempty diagram from delayed tail data, applies a computed identity (`snd`
of a pair) and evaluates both orientations and the round trip with no
transform registered; (3) the §47 examples (empty, two-node with a
witness-dependent tail, shared predecessor, a loop residual) export with
`C ≡ canonical`, `R(y) ≡ Real_0`, `c ≡ collapse`, `d ≡ expand`, and the
residual's `X_P ≡ Real_0` (the loop Σ-type is retained); (4) `zero[σ] ≡
zero(C[σ])`, `F(…)[σ] ≡ F(…[σ])` and `singleton(…)[σ] ≡ singleton(…[σ])` under a
simultaneous term/dimension substitution between contexts with required
faces; (5) a supplied and a computed proof instantiate one template, evaluate
to convertible results and the repeat runs no body and no beta; (6) wrong
level, mismatched type, unavailable guard, malformed family are rejected, and
the cyclic proof `loop := loop` types as a program, audits PENDING, its action
over a variable type is a neutral composition that still carries the pending
proof, and demanding the proof's interior is STUCK — no witness is
fabricated; (7) the administration counters are printed.

Two kernel corrections this increment needed, both in the delivered v9 code:
`shape_under` memoized by the whole binder environment ρ, so a shared
subterm under different unrelated binders was recomputed per binder path — on
the composite witnesses this was exponential (the two-node export's `R(y)`
conversion interned millions of maps and did not finish in 8 GB); ρ is now
restricted to the free boundary of the subterm (free variables, support,
required-face dimensions) before the memo lookup, which does not change any
shape (the form depends only on those entries) and also cuts `test_main`'s map
table from 16,636 to 991 records. And `net.c` counted the
`CONTINUE_REFERENCE` rule event after the forward publication, so a reader
woken by the result could read the event counter before the increment
(`test_compiler` with workers on a 2-core host); the count now precedes the
publication. A third, at the session boundary: `eval_reset` aborted when a
client left work queued or executing under a worker pool (a conversion that
returned while its sibling job was still running — `review_alias_faces 4`
under load); the reset now drains that finite work (`eval_run`) before the
quiescence requirement is enforced.

§96 (v13) adds the closed node function above. Its recipes are the production
templates already used by `rt_diagram_extend`; the runtime tail `Q` is a bound
parameter of the closed term, never a per-tail specialization, and the fields
stay lazy (observing the centre or one map demands neither the other map nor
the proofs — `whnf` of `fst` in test_runtime case 2). The §96.1 wording is the
one this implementation follows: checker, compiler and evaluator are
operations over one store of references, substitutions, scopes, templates,
persistent entries, dependencies and receipts; nothing here is a second
representation of mathematical values, and the shared storage is not offered
as the §5.26 reflection, which remains the author-side obligation it was.
Mathematical use of a proof field follows the same proof-use contract whether
the proof was supplied or computed (`test_proof_use`: `snd` of a pair
reducing to `refl` audits CORE, a pair hiding the cyclic symbol audits
PENDING). §96.5's work reading is the ledger's existing behaviour: a cache hit
is charged its lookup and delivery (`PRODUCER_LOOKUP`, `ALIAS_DELIVERY`), never
the cached computation again, and a historical receipt does not remove current
validation or delivery work (`DEPENDENCY_CHECK`, `RECEIPT` are charged per use).

### §88 — the proof-use boundary (`src/proof.c`)

`check` establishes program typing for a partial language; `certificate_verify`
establishes that a record is the compiler's own re-emission of its inputs.
Neither is a mathematical witness: a recursive declaration can carry a
circular proof. `proof_use(Γ, φ, e, E)` runs admission, context validity,
formation of `E` and `e : E`, then the dependency audit: a memoized
stored-syntax traversal with an explicit owned stack (inactive branches,
binder domains, map images, scope declarations, template environments and
compiled call bodies included; no evaluation, no scope opening, no
unfolding), Tarjan components over the reached globals' declaration/parameter/
body edges, verdict `PENDING` on a cyclic component, `ASSUMED` with the
opaque symbols listed, else `CORE`; the false face is `CORE` locally. The
verdict is cached per judgment with the `(symbol, revision)` pairs it read
and reused while they are current (§79); sub-traversals are memoized per
reference / scope / `(symbol, revision)`. `transform_proof_use(id)` audits a
record's **original** evidence at the type the compiler checked it at
(`transform_evidence`: the identity path, the equivalence, the terminal
equivalence, the contraction, a cut's own construction) — not its forward
body or WHNF. The author's `proof_boundary.h` interface is served by this
module (`tests/proof_boundary.c`); the reference implementation is kept in
`tests/reference/`. Mathematical use is at preparation (`step_prepare`,
`audit_use`): every plan continuation evidence, connector reference and
connector transform is audited; `CORE` and `ASSUMED` prepare, with the
assumptions recorded on the problem (`problem_assumptions`, `problem_core`);
`PENDING`/`INVALID`/`UNRESOLVED` reject with the audit's diagnostic, and the
diagnostic names a missing witness, never a refutation or an inequality.

Proof-use outcomes measured (`tests/test_proof_use.c`, `tests/test_runtime.c`
case 6, the author's 11-case `test_proof_boundary.c` and
`review_certificate_boundary.c`):

| Evidence | `check` | `certificate_verify` | `proof_use` | at preparation |
| --- | --- | --- | --- | --- |
| `refl`, finite definitions, lambdas, templates, compiled calls of core records | VALID | VALID | CORE | prepares, no hypotheses |
| an opaque declaration | VALID | — | ASSUMED {symbol} | prepares; symbol recorded on the problem |
| `loop := loop` (direct), a mutual pair, a lambda hiding the loop, a program through the loop | VALID | — | PENDING {component} | rejected: "proof use PENDING …" |
| the recursive equivalence certificate (§86.1) | VALID | VALID (re-emission) | PENDING | rejected at use; forward call still evaluates (constant), reverse call STUCK |
| the identity equivalence certificate | VALID | VALID | CORE | prepares |
| a judgment under the false face | VALID | — | CORE (local) | — |

Three questions, answered separately for the recursive-equivalence example:
the code is well typed (VALID); the certificate is the compiler's derivation
(VALID); the mathematical equivalence is **not established** (PENDING) and the
reverse observation does not complete (STUCK).

### §89 — fine C-work accounting (`src/fine.c`)

`tests/review_frame_cost.c` and `tests/test_fine_cost.c`: a system with 1 / 64
/ 1024 branches has the coarse vector `(REQUEST, EVAL, PUB, DELIVER) =
(2, 4, 2, 2)` in all three cases while storing 2 / 128 / 2048 fields. The fine
vector is counted where the loops run (one increment per field opened, key
word hashed, probe, compared word, copied word, relocated slot, map entry,
DNF clause step, face operation, waiter delivered, continuation registered,
queue operation, lock acquisition, cell allocated/released, net action/retry,
checker frame, audit step) and reported beside the coarse one, never added
to it. The microstep table for the three systems (ASan build):

| fine counter | n=1 | n=64 | n=1024 |
| --- | ---: | ---: | ---: |
| fields_opened | 4 | 256 | 4096 |
| head_cells | 2 | 2 | 2 |
| intern_words_hashed | 75 | 642 | 9282 |
| intern_probes | 34 | 97 | 1057 |
| intern_word_compares | 30 | 219 | 3099 |
| intern_words_copied | 35 | 413 | 6173 |
| dnf_clause_steps | 27 | 27 | 27 |
| face_ops | 12 | 201 | 3081 |
| waiters_delivered / conts_registered | 2 / 2 | 2 / 2 | 2 / 2 |
| queue_ops / lock_attempts | 9 / 8 | 9 / 8 | 9 / 8 |
| cells_allocated / released | 5 / 2 | 5 / 2 | 5 / 2 |
| TOTAL | 247 | 1885 | 26845 |

The coarse vector is a semantic projection; the fine total grows with the
stored size (the system head is opened twice per observation: once for the
head inspection, once for the system rule). This is a cost measure; it is not
a constant-factor simulation theorem (§85, §94.2(6)).

### What is not claimed

The whole-machine adaptive one-step diamond and the equal-interaction-length
theorem (§85); the fine-step-to-C simulation with a uniform bound (§85,
§94); a reflected checker/evaluator (§83.3); unconditional proof admission in
the presence of general recursion (§86.1 — PENDING is the answer); a
declaration-to-answer posing operation or any universal finite
answer-or-obstruction procedure (§86). §73's exclusions remain: no solver,
frontier, incumbent, planner or replacement runtime.
