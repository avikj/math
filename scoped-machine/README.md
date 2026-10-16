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
  is checked before any opening, independent of faces.
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
