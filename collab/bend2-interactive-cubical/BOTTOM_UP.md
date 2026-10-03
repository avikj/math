# Bottom up: the language, the checker and the runtime as one object

Working note. Everything here is either a checked term in the corpus, a
measurement on the vendored binaries, or a decision, and each paragraph says
which. The rule of the reverted design log (`WIP_FULL_RUNTIME.md` on
`claude/metacircular-pr-45-review-yt93oh`, commit 564db19e) is kept: every
change is stated first as the mathematics it applies; a change that needs
problem solving the mathematics does not dictate is a signal that something
upstream is wrong.

## 0. Where this stands relative to what exists

- PR 45 (`conductive-language-entry`): HVM4's interaction calculus unchanged,
  with `Core.WHNF`'s cubical reduction emitted as a prelude, the checker run
  first in Haskell, every definition emitted twice (`@D`, `@T`), root the typed
  point `#Pair{@Tmain, @Dmain}`. Green on head 2e8ca32.
- The reverted branch went further in the same direction this note takes:
  fresh dimension names per unfolding (P3a/P3b), the machine that asks
  (P4), a checker on the net (P5a), sharing by descent with closures and
  frames (3f), and then an audit (3g) concluding that the runtime "does not
  implement the construction" in seven specific ways. Its head reverts all of
  it to a8bbf6d4 and states the PR's design as HVM4 unchanged plus prelude.
  The audit's findings are correct and are the specification below. The
  revert was the right call for that branch: patching hvm.c toward the
  construction made the simulation cheaper, not the implementation correct.
- This note is the design for writing the cell once, from the construction,
  and keeping the vendored HVM4 and Bend2 only as oracles for the
  differential.

## 1. The object (checked)

`formal/cubical/One.agda`, sections as numbered there.

- §1 `graph≃dom`, `law : A ≃ Σ b. fiber f b`, `present a = (f a, a, refl)`,
  `transport-is-present` by `uaβ`. A map loses nothing in total; loss lives
  in the partition. `present` keeps the source as a coordinate.
- §2 `isContr (Lossless f)`, `machines-are-maps`. The completion is unique;
  a lossless machine on A is a self-map.
- §3 descent: a projection cannot carry a distinction its fibre identifies.
- §4 cost and inverse cannot coexist: an additive grade on a structure with
  inverses is zero. Cost lives on the retained walk, never on the transport.
- §5 `Geodesic`: a potential local on primitive edges (`Φ u ≤ w u v + Φ v`)
  and zero at the target bounds every walk; a walk meeting it is shortest
  against every competitor, no enumeration.
- §6 path is bisimulation; transport commutes with unfolding; `carried`.
- §7 `Interaction X = (Q, δ)`, `Run ≃ Answers`, `silence-is-determinism`: a
  closed machine is the interaction with nothing to ask, and its run is
  contractible (`fibre-of-run`), so a closed run's history carries no
  information beyond its count.
- §8 locality: depth is time; §5 read metrically.
- §14 `Step`: `decide = present`, `verify` inverts it. Finding and checking
  are the two projections of one equivalence.
- `research/sat_fibre/InteractionGeodesic.agda`: under the exact one-step
  diamond every complete reduction has the same length; any schedule is a
  geodesic. `REDUCTION_FOUNDATIONS.md`: what HVM's ITRS counts rule by rule
  (DUP-SUP equal labels 1 interaction and 0 words, different labels 1 and 4,
  DUP-LAM 5 words used and 3 erased, APP-SUP 3); `AND-ZER` and `OR-ONE` and
  an erased binder drop unevaluated subgraphs and break the diamond under
  context closure; under the demand-restricted relation the dropped subgraph
  was never demanded.
- `NaturalMachine/Visranti`: derivability is decided by two normalisations
  and a `refl`; `nf` is defined by exactly the clauses the rules perform.
  `NaturalMachine/Alopa`: the engine never touches the meaning; a rule is two
  terms carrying their certificate as a field, so soundness of the run falls
  out of the type, not out of an audit.
- `theorems/physics/BringGeodesic` (branch `claude/formal-proof-community`,
  English identifiers): `bring n` has length exactly n, a shorter word's
  light cone stops before cell n, so the minimum is n. Reversible and
  positive-distance: semantic invertibility and execution distance are
  different structures.
- `PNP_GEODESIC_REDUCTION` ledger: A completion, B coinductive answers, C
  exact descent (C1 nothing coarser is lawful, C2 nothing finer is repeated),
  D cost on retained realisations, G rope geodesic, H the costed realisation
  fibre `Fib_(Sem_b)(f)` as the uniform interface.
- `theorems/physics/Adhisthana`: the Kan floor has two primitives, not one.
  `hcomp` fills a box inside a fixed type; `transp` moves along a line of
  types; `comp` is derived from both. Free reversal (`λ i → p (~ i)`, and
  `∧`, `∨`) is a property of the De Morgan site, not of cubical type theory:
  on the cartesian site reversal is derived from the Kan operations. Choosing
  the cube category is the act that decides whether the return is free.
- Census (`DurnayaTantau`, `Avaktavyagarbha`): a fibre verdict is three-valued
  and every two-valued verdict merges two of the three.
- Abstracts 43 and 54: `NativeOperation ≃ Σ certificate. gauge`, install is a
  section of extract by `refl`, its locus is a contractible cone.

## 2. One construct: the cell

A cell is a term over dimension names, with its type, two auxiliary ports,
and its faces. Everything else is this cell in a polarity or with a
coordinate.

- Lambda and application: the same cell facing opposite ways.
- `&L{a,b}` is a 1-cell in dimension L. `<i> t` is a 1-cell in i. They are
  one thing (audit item 1: HVM4 keeps two unrelated notions of dimension, the
  SUP/DUP label and the `#IVar` interval; the construction has one, a cell's
  faces).
- `! &L{x,y} = v` is the face map i := 0 / i := 1 on dimension L. DUP-SUP at
  the same name is the face map on its own dimension (annihilate). At
  different names, faces in different dimensions commute.
- `p @ r` is substitution of a dimension. The interval's De Morgan structure
  (`~i`, `i ∧ j`, `i ∨ j`) acts on names; its normal form is the free De
  Morgan algebra's, an antichain of sorted cubes of literals, and equal
  intervals are then structurally equal.
- A dimension name is BOUND, like a lambda variable is bound by its binder.
  This is the label-capture finding of P3a, restated: HVM4 assigns auto-dup
  labels once per source binder and every unfolding reuses them, so two
  dynamic instances of one definition share names and a DUP of one instance
  annihilates with a SUP of another. Probes: `two(Nat→Nat, λg. two(Nat,g),
  suc, 0)` gives 4 in Core and `λa.#Suc{a}` on stock HVM4; the triple
  nesting is OOM-killed; `port/SchematicOperation.bend` was undercounting
  790 for 798 by an illegitimate annihilation. The corpus itself did not hit
  capture (differential 118 AGREE, 2 DISAGREE both the probe shape); the
  language admits it. P3b's representation, name = (instance, bound label)
  as a 64-bit word stored per heap location, is the same fact written as a
  patch; in the cell it is a binder, not a counter.
- Regularity (a line constant in its dimension transports as the identity)
  is today decided up to conversion: the checker applies the line to a marker
  dimension, normalises, and fires the identity rule when the marker is gone
  (`REMAINING.md` §F). That is a non-local decision made by a second copy of
  the semantics. With dimension names bound, regularity is an occurs check on
  a bound name: the line's cell does not mention its dimension. Local, and
  one rule.
- Ua is a cell whose coordinate carries an equivalence with both coherences;
  a HIT constructor is a cell with a dimension port and its parameters kept
  (the emitter refuses a bare constructor); a coinductive value is a cell
  whose tail is a free port; a quotient point is a cell whose path
  constructor is a 1-cell.

## 3. The rules

Two cells meet at principal ports; one of four things happens.

1. Same name: annihilate. Identification, the `refl` case. Zero words.
2. Different names: commute. Transport of one past the other, the square.
   This is the first chart-invariant holonomy; it is where cost is paid.
3. A face: fill, which is two rules by Adhisthana. Within a type, `hcomp`
   fills the box; across a line of types, `transp` moves the cell; `comp` is
   their composite and not a primitive. These are the only rules that
   consult the type. The Kan operations are the cells' own composition
   structure (audit item 2: in the PR they are prelude lambda-programs over
   constructor encodings, a transcription of CCHM run as ordinary code, so
   their cost is the encoding's cost, not the cell's). What `RUNTIME_FULL.md`
   already established survives as the semantics of fill: `coe` on a rigid
   type is the identity, on Π conjugates domain and codomain lines, on Σ is
   componentwise along the filled first component, on Path is the
   hcomp-conjugation square, on a universe path is `@coeU` (ua gives `f` or
   `g`, a composite is sequential); `hcomp` with a true face is that tube's
   top, with all faces false is the base, otherwise it is stuck data carrying
   its faces, decided by whoever later supplies the interval; Glue keeps its
   faces and a glue value with no live faces is its base; the set-quotient
   recursor computes on `qcl` and on `qeq @ i`. A superposed line needs no
   rule of its own: fill is a match, a match commutes over a superposition,
   and the same-name dup of the transported value annihilates. `ua` is
   notation for the Glue line, not a constructor of its own: the PR carries
   both (`Ua` and `Glue`) and `uaagree.bend` shows they are not definitionally
   equal, their agreement needing the η direction the layer lacks. One cell.
4. Erase. The one address of loss. The feed-forward of SHA-256 is this rule.

Every rule appends its receipt (rule, names) to a trace that is itself a
net. The census is a pattern on receipts. Definitional unfolding (δ) is not
counted: transport is free (§4), and the differential confirms that δ is what
HVM4 leaves uncounted.

## 4. Sharing is descent, values are points

From §1 `graph≃dom`, §3, ledger C (the reverted branch's 3f, kept):

- A datum determined by `a` is retained at `a` for free and it is ONE point;
  every use of it is that point. A computation factoring through `q` is
  performed once per point of the coarsest base it factors through (C2) and
  nothing coarser is lawful (C1).
- Syntactically: every subterm is presented over exactly its free variables;
  its coordinate lives in the frame of its innermost dependency and is shared
  by every application that agrees on that frame. Work independent of `x` is
  a coordinate of the closure, computed at most once; under `λx.λy`, work
  depending on `x` but not `y` is shared across all `y`.
- So: no duplication nodes for variables, no auto labels, no capture.
  Superposition names remain only for genuine fibres and are bound by
  position. A book lambda instantiates to a closure (code, frame, depth,
  dimension); β extends a frame; forcing writes the weak head back to the
  coordinate, counted once. A closure taken on a side of a dimension projects
  its frame entries and carries the face.
- Conversion is identity of canonical points, reached by the reduction that
  produced them, so its cost is the reduction's (audit item 3: HVM4's `===`
  walks two separately built encodings and allocates chains per field;
  nothing made a determined datum one point, so the net checker compared its
  whole book repeatedly). No unit-cost primitive hides the decision
  (`REDUCTION_FOUNDATIONS`).
- Scheduling bookkeeping is not in the values (audit item 4: `↑`/INC, the
  collapse priority queue, credit and stride are HVM4's enumeration policy and
  `===` put them into every compared value). Enumeration of a fibre is the §7
  run.
- A generic element (the fresh variable of a binder) is a coordinate of its
  binder, not a counter name (audit item 5); otherwise the descent pass, which
  assumes every subterm is a function of its free variables, shares what it
  must not.
- A call is one δι-step and the walk is the step: a call fires iff its case
  tree reaches a leaf; a stuck call is its own normal form, a spine headed by
  its name, compared by identity. This is what makes the normal form of an
  open term finite and canonical (Visranti's `nf` on the same footing). It
  must be one rule, not a side machine of case-tree walkers, partial-call
  hash tables and per-side frame projection (audit item 7).

Measured on the reverted branch: cap4 (`use(p) = p(Nat→Nat, p(Nat), suc, 0)`)
4 where stock HVM4 crashed; shared `@f(N)` used three times 35 interactions
for 64; conductive runtime 137 to 111; every other corpus value identical.

## 5. Compile time and run time

Same machine, different wiring. A net is closed when every port is
connected. Compile time is reduction of every closed redex: normalisation,
which is also partial evaluation. Run time is the same reduction with ports
left free. A free port is input not yet available, or an effect: an input is
a typed point whose type is known and whose term is a free wire, an output is
the dual, and the world supplies a section at that port. There is no
interpreter mode and no compiled mode. §7's machine that asks is the entry:
`hvm --interact` keeps the heap and the point, each question is a term
entered like a definition (its own bound names), applied to the point and
normalised; the step is `present` lowered through the one emitter, and
iterating it is §6 `carried`. Under the one-step diamond, restricted to
demand, every schedule of a closed net is a geodesic and its interaction
count is the cost. Stating the demand-restricted relation precisely and
checking an instance of `RandomDescent` for the reachable rules is the one
open theorem here (P3c in the log; never done).

## 6. Checking is `verify`, not a second program

- §14: `decide = present`, `verify` its inverse. Checking `t : A` is the
  other projection of the same presentation (audit item 6: a checker that
  reads the emitted book through peek/inst and re-evaluates types with its
  own context is an interpreter beside the net).
- Terms are never evaluated by the checker; they are viewed (`loop(x) =
  loop(x)` has no normal form and checks). Types are evaluated: conversion
  is equality of normal type cells, decided by the runtime's own reduction.
- The checker dispatches on the syntax of types, and a type-case cannot live
  inside a univalent theory (it would separate ua-equal types), so it is
  runtime semantics written as interactions, costed like every other
  inference.
- Nothing the checker needs may be erased by lowering: annotations, HIT
  parameters, enum symbols, numeric kind, both ua coherences, equality
  endpoints. The PR's emitter already keeps these; the `not` miscompile (an
  identity lowering, a wrong SAT verdict right by coincidence) is the
  standing example of what erasure costs.
- Generic elements are reflected η-long by type: Π to a lambda of the
  reflected application, Σ to a pair of reflected projections, Path to a
  line whose faces are the endpoints. A path-typed definition carries its
  faces in the cell, since a stuck lemma call has lost its type otherwise.
- Ill-typed is a non-fillable boundary: the residual after annihilation IS
  the error, and the census reads it as the empty position.
- Conformance: per-definition differential against Bend2's checker over the
  whole corpus, every ✓/✗ agreeing including every `*_mustfail`. The reverted
  branch's P5a reached AGREE 1820, 10 mismatches, 213 cannot-infer (cubical
  cases) before the audit stopped it. Core deviations to record, not
  reproduce: syntactic `rewrite` on a non-variable scrutinee, lets
  substituted, `coe` regularity decided by full normalisation.

## 7. Install and self-extension

A theorem of the object becomes a structure map of the object:
`install : Derivation lhs rhs → NativeOperation`. Extracting the certificate
of an installed derivation returns the derivation by `refl`; an operation is
exactly a certificate with a control gauge; its applicability locus
`Σ t. t ≡ lhs` is a contractible cone (the analyzer inferred the mapping-cone
target itself). In the cell: a cell whose term is a derivation, whose
interaction adds a row to the rule table, with Alopa's form: the rule carries
its certificate as a field, so the run's soundness is the type. This is the
one rule no other runtime has, and it is one rule.

## 8. Parallelism

Interactions are local (§8: depth is time, a word's length is its light
cone), so every redex not behind a free port fires at once and the redex bag
is the only scheduler. HVM4 running sequentially was an evaluator strategy, a
gauge. The equal-weight scheduler question (`SamaBhara`) is where fairness
across a fibre is decided, at pair grain, and it is a census question, not a
runtime one.

## 9. What the existing pieces got right and wrong

HVM4 (`vendor/HVM4/src/hvm.c`, 6,643 lines at 6defdfc), right: linear cells,
a redex bag, atomic linking, the memory layout, DUP/SUP as the two halves of
the fibre law, structural `===` that commutes with superposition, `-C`
collapse reading the diagonal of a superposed dependent point. Wrong, each a
missing coordinate: labels as 24-bit global integers (capture; exhaustion at
8.4M names; no fresh-name primitive; `term_clone` makes every lazy copy of an
unevaluated reference share one evaluation, so a fresh name drawn at the
reference site is shared); two notions of dimension; Kan operations simulated
in the prelude; scheduling bookkeeping in values; generics from a counter;
calls as a side machine; a normaliser that diverges under a binder on any
type mentioning a recursive call on a bound variable.

Every Kan rule in the PR is written twice, once in `whnfHCm`/`whnfCoe` and
once in `Target/HVM4Full.hs` (`REMAINING.md` §E); the prelude is
`Core.WHNF` transcribed. The kernel writes each once. The interval's normal
form already exists in the checker (flattened, deduplicated, sorted meets
and joins, no complement law since `i ∧ ¬i ≠ i0`) and not on the runtime,
where faces are evaluated and never compared; on the kernel it is the one
normal form, since names are compared.

Bend2 Core, right: the surface syntax, HITs, quotients, `Glue`/`ua`, the
elaboration of bare HIT constructors, totality. Wrong: `whnf` is a second
copy of the semantics and decides some things non-locally; the checker is a
Haskell program beside the net; `not(` always parses as unary; several
lowerings erased cells the checker needed.

## 10. The kernel, concretely

- Cell: one word tag + name + two ports, name a binder reference (frame,
  index) not an integer; a dimension is a name whose binder is a line.
  Faces are stored on the closure/frame that took the side.
- Rules: annihilate, commute, fill (coe, hcomp, Glue, quotient, HIT),
  erase, and the δι-step of a call; numeric primitives as rigid cells with
  GMP-backed ℕ where the corpus needs it; `===` as identity of points.
  About twenty rule cases. A few thousand lines of C. Not C++: nothing here
  needs classes, and atomics are C.
- Receipts: a rule appends to a trace net; ITRS is the length; the census
  is a fold over the trace. `-C` collapse and `↑` go; enumeration of a fibre
  is the §7 run.
- Host: parse the surface, lower to cells, nothing else. The Haskell
  evaluator leaves the compile path (P6 in the log).
- Entry: the typed point; `--interact` as the §7 loop; free ports for
  effects.

## 11. Conformance, the only measurement that is allowed to decide

A measurement detects an implementation flaw and never justifies a design
choice (the log's rule). The differentials that exist and are kept:

- Value and ITRS differential over all emitted corpus programs (237 at the
  last count; classes AGREE / DISAGREE / NOT-COMPARABLE / REFUSED / NO-MAIN /
  CORE-TIMEOUT / HVM-CRASH; `tools/diff/diff.py`, `tools/regress/`).
  Identical ITRS on the geodesic is the conformance criterion: equal counts
  under the diamond mean the same object.
- `verify_conductive_entry.sh` stages: TYPED-POINT, FIBRE-LAW-AND-CONTINUATION,
  CELLS, CHECK-GATE, REFUSE-NOT-MISCOMPILE, FRESH-DIMENSIONS, ASK,
  NEUTRAL-TYPE. `suite.sh`. `test_list_transport.py` 26/26.
- Label-capture probes (`probes/label_capture/`): two∘two = 4 at 27
  interactions, the triple = 16 at 50, cap4 = 4.
- Mining gate: prepare, typecheck (116 ✓), emit, link, gate; six SHA-256 and
  Bitcoin checks; 35,372,404 interactions; genesis header 26,553,327 in
  0.385 s.
- Checker differential per definition, every mustfail included.
- `RUNTIME_FULL.md`'s Kan matrix (chain, fibre law, contraction, superposed
  line, Glue, 2-dimensional universe composition, twist, quotient recursor).
- `SYNTHESIS.md` §3–4, kept as the sharing conformance points: a transport
  consumed k times is paid once (marginal 14 interactions shared against 150
  separate); one shared line over N values wins and improves with N
  (marginal 38 against 139); N different lines lose by a constant factor
  (about 1.4, and 1.8 for a bare `neg`), which is the cost of commuting the
  superposition through the body. Superposition pays exactly when the
  branches share a prefix; that is the fibre law read as a benchmark, and
  the kernel must reproduce both regimes.

## 12. Order (decided)

1. The cell in C, from §§1–8 and §14: bound names, descent sharing with
   frames, the four rules plus the call step, receipts. No checker yet.
   Vendored HVM4 stays as the oracle binary for the value differential and
   ITRS comparison only; nothing is patched into it.
2. Fill: coe/hcomp/Glue/HIT/quotient as the cells' composition, conformed
   against `RUNTIME_FULL.md`'s matrix and the corpus differential.
3. The typed-point entry and the §7 interaction loop on the new kernel.
4. Checking as `verify` on the kernel, staged MLTT core, then paths and coe,
   then hcomp/Glue/ua/Sub/Partial, then HITs, each stage differential
   against Bend2's checker; Bend2 retired from the compile path when the
   corpus agrees.
5. Install.
6. The demand-restricted diamond stated and an instance checked; the
   scheduler made parallel by removing the sequential gauge, with ITRS
   invariant across schedules as the test.

Receipts and bound names come first because the census reads receipts, the
checker reads the census, and every later stage would otherwise be built on
the capture defect.

## 13. Settled by construction (formerly listed as open)

Nothing in this list is open. Each item was inherited as a question from the
reverted branch and is a theorem of the construction or a measurement.

- The one-step diamond. Take `and(x, y)` with `x` reducing to `0`. HVM4's
  AND-ZER returns `0` and forgets `y`; nothing about `y` is counted. Under a
  relation where any redex may fire, that breaks the diamond: reduce `y`
  first and the count is `k + 1`, fire AND-ZER first and it is `1`, so the
  count is a fact about the strategy (`REDUCTION_FOUNDATIONS`). Making
  erasure an agent that reduces and then erases `y` on every route would
  restore the diamond but contradicts §7: nothing asked for `y`. The
  construction's answer is retention. The completion of `and(0, y)` is
  `(0, y, refl)`; `y` is the fibre, retained at no cost (§1, a singleton
  contraction), not evaluated (§7, nothing demands it), and erased only when
  a consumer projects the visible result and forgets the fibre, where that
  erasure is the one counted loss (§4). HVM4 is right about what to evaluate
  and wrong about what to keep: it reports `1` and has destroyed `y`. The
  kernel's step relation is demand-restricted, as §7 states it: a redex
  fires only when asked. Two demanded redexes are disjoint active pairs, and
  since nothing is ever dropped mid-run no step removes a demand already
  made, so the diamond holds for this relation and every schedule reaches
  the demanded normal form in the same number of interactions. That number
  is the program's cost. Erase remains the one address of loss, charged at
  the projection, never inside the run.
- A face on a frame meeting a superposed tube: a match commutes over a
  superposition and the same-name dup annihilates. The rule already exists
  and needs no case.
- The receipt of a fill, and a HIT constructor with a dimension port: a fill
  is a rule, its receipt is its row, and a path constructor is a 1-cell like
  any other.
- Sub and Partial: a partial element is a cell whose domain is a face; the
  checker already has them (`REMAINING.md` §C) and the kernel has them as
  cells with a face constraint.
- Coinduction: a productive free port is §7's answer stream, guardedness is
  §8's unit lookahead, and bisimulation is path equality by §6.
- Numeric primitives: their cost is a row in the rule table, a measurement,
  and the table is the metric.
- Glue is the primitive and ua its notation. The one composition law
  `REMAINING.md` §B could not state without face-restricted contexts is
  stated once names are bound.
- The cube category: De Morgan, because the corpus is checked on that site,
  so reversal is free and the label algebra is `~`, `∧`, `∨`. A recorded
  choice, not a question.

## 14. Where things are

- Design log and audit: `git show 564db19e:WIP_FULL_RUNTIME.md` on
  `claude/metacircular-pr-45-review-yt93oh` (reverted at its head 96f4e43a).
  Its runtime patches, checker (`vendor/Bend2/checker/Check.bend`), probes,
  differential tools and build script are in that branch's history.
- The English-identifier geodesic module:
  `claude/formal-proof-community-icf32v`.
- The PR's runtime description: `RUNTIME_FULL.md`, `TYPED_POINT.md`,
  `STATE_OF_THE_WORK.md`, `SETTLED_BY_THE_CORPUS.md`, `CORPUS_DIGEST.md`.
- The construction: `formal/cubical/One.agda`,
  `research/sat_fibre/{InteractionGeodesic.agda,REDUCTION_FOUNDATIONS.md,
  DIRECTIONAL_SYNTHESIS.md}`, `research/PNP_GEODESIC_REDUCTION_20260916.md`,
  `NaturalMachine/{Visranti,Alopa}`.
