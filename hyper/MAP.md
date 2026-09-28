# Hyperactive

**Read this section before anything else in this directory. It is the task. Every
regression this project has suffered came from someone building a smaller thing
than this and calling it progress.**

## 0. What this is

Hyperactive is a programming language whose runtime is the mathematics done
right, so that a declaration is the program. You write the type of a function
from lists to their sorted permutations:

    sort : Π (A : List Nat). Σ (B : List Nat). (multiset A ≡ multiset B) × Sorted B

and nothing else. The runtime produces B for any A, and the cost of producing it
is the minimum for that object. You never wrote an algorithm and never chose
one. On the next line you write

    sortCost : Π (n : Nat). Nat        -- the greatest cost of sorting any list of length n

and the same operation resolves it: over an unbounded domain, and over the
machine's own cost. If those two declarations resolve from the core, with no
organ written for lists, numbers, sorting or cost, everything else the language
is meant to be falls out. If either needs a special case, the core is wrong.

Why this is possible and not a wish, in the corpus's own checked terms:

1. **The fibre law.** For any f : A → B, A ≃ Σ_b fib_f(b), and for any lossless
   factorisation of a computation the retained trace is forced to be the fibre
   of its visible map (`fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda:129`
   `fibre-of-run`). A specification `Σ B. P A B` is a fibre. When it is
   contractible its centre is determined by A, so B is inferrable, not guessed.
   When it is empty there is no B; when it is crowded the specification
   underdetermines. The census says which, pointwise, three-valued, never a
   Boolean (`fibre/src/Fibre/WholePartialDesa_TheFibreCensusIsATermAndItRefutesTheSequentialDiagnostic.agda:87`
   `देश`).
2. **The geodesic.** Under the one-step diamond every complete reduction of an
   object to its normal form has the same length and no first move can lengthen
   it (`research/sat_fibre/InteractionGeodesic.agda:45` `same-normalization-length`,
   `:53` `normalization-is-geodesic`). Interaction nets have the diamond because
   active pairs are disjoint. So the number of interactions from a declaration
   to its resolution is an invariant of the object, and it is the minimum,
   because every path is the minimum. Cost is not a performance figure and the
   programmer never thinks about it.
3. **Univalence computes.** A proved equivalence between two presentations is a
   path in the universe and transport along it reduces (`fibre/src/Fibre/Carrier.agda:129`
   `carry-transport-descend`). Meaning descends along it; cost does not. So the
   minimal count for an object is the minimum over its charts, and the only
   lever that changes cost is a proof.
4. **Cost and inverse cannot coexist.** Only forgetting costs. Nothing is erased
   inside a run; a demanded node fires once and every holder sees its value; a
   forgotten port is charged at the projection. The run's charge is interactions
   and heap words (`research/sat_fibre/InteractionLedger.agda:20` `Charge`,
   `:74` `interactionTotal-is-length`).
5. **Interaction is the operation.** A state faces a typed map and returns the
   successor, the observation, the event and the continuation
   (`fibre/src/Fibre/Interaction_TheOrbitIsTheOneQueryCaseOfTheInteractiveCoalgebraAndTheDemandIsWhatDiffers.agda:81`
   `react`). Two parts are projections of one joint
   (`formal/cubical/theorems/logic/Jiva_EntanglementIsTheFibreOfTheProductComparisonAndTheLivingStepRefusesToDescendToTheMarginals.agda:134`
   `तुलना`); two peers with an overlap compose one trace
   (`formal/cubical/kernel-flat/TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection.agda:164`
   `interact`). What the runtime cannot infer is exactly the concrete, non-universal
   information, and it enters through a free port.

The universal part of mathematics is finite and already in the construction.
What the language accepts from outside is the specific: data, boundary
conditions, the choice at a crowded fibre. A deterministic physical law over its
boundary data is a contractible fibre and resolves like `sort`.

## 0.1 The mechanism, from the core, with no organs

How `sort` resolves. For concrete A, B is a list of **coordinates**: generic
elements of its type with no value yet. `sort`'s specification runs on them. A
path at a data type between a term with coordinates and a concrete term is
**unification**: constructor against constructor from the type's declaration,
coordinate against term as a binding, superposed at the faces the path lives
under. A case on a coordinate is not stuck: it becomes a
**superposition over the constructors of its type**, each side restricting the
coordinate, with fresh coordinates for the fields; this is exactly what the
checker already does when a match on a coordinate restricts its frame. Sides on
which a predicate reduces to False are annihilated by the face map. The
survivors are the fibre. It has one point because the fibre is contractible, and
that point is B. No enumeration of Nat happens: a coordinate is split only when
something asks about it and only as far as it is asked. This is narrowing, and
it is the fibre law run forward.

How `sortCost n` resolves. Present `sort` along a list of n coordinates. Each
undetermined comparison splits into a superposition with the residual constraint
carried. Only finitely many comparisons can be asked of n coordinates before the
order is determined, so the run over the infinite domain is a finite tree: the
symmetry of the domain is carried by the coordinates without a quotient being
written. Each leaf has a ledger. **The trace of a run is a term of the language**
and **a superposition collapses to the list of its leaves as a term**, so `cost`
is a fold, `max` over the leaves is a fold, and `sortCost n` is the decision-tree
bound, computed, minimal on every branch by the geodesic. For all n at once the
declaration is a Π over an inductive type, whose canonical inhabitant is by that
type's eliminator, so the inference is by induction and the checker confirms it
on the same loop.

The core therefore owes the language exactly these, each derived from type
structure and none written per type:

- coordinates at run time; a declaration with no body, or a Σ with no witness,
  is a coordinate of its type;
- a case on a coordinate is a superposition over its constructors with
  restriction;
- a path at a data type with coordinates decides by unification;
- the trace of a run and the leaves of a superposition are terms;
- every rule fires at an active pair and bodies are shared as nets, so the
  count is the proved geodesic and shared prefixes across branches are paid once;
- a proved equivalence between charts lets the collapse run in the cheaper chart
  under its certificate;
- the checker on the same loop verifies every inferred body against its type.

Nothing in this list names lists, numbers, sorting or cost.

## 0.2 What regressing looks like, so you can recognise it

Today's session lost most of a day to each of these, in order. Do not repeat
them.

- **Building an interface instead of the language.** Subcommands that compute
  what a corpus module proves (a census mode, a joint mode, a meet mode) are
  organs. The constructions belong in the language as terms over the two
  primitives above, and the runtime has one entry: reduce, with check on the
  same loop. The modes this branch once had are gone; their probes are
  programs (step 3).
- **Building the runtime someone else already has.** An efficient interaction
  net exists (HVM). A cubical fork of Bend on it exists
  (`collab/bend2-interactive-cubical`). This directory is not a faster one of
  those. It is the language in §0, and the fork is its first dialect and its
  value oracle.
- **Importing the toy's frame.** `formal/cubical/Kernel/` is a first-order
  term-rewriting kernel whose own theorems show its `install` fires at exactly
  one term (`formal/cubical/Kernel/Vyapti_TheInstalledOperationHasNoneSoTheKernelMemorisesAndTheSchemaIsWhatMakesItGeneralise.agda:113`
  `fires-only-at-source`) and cannot grow its reach
  (`formal/cubical/Kernel/Siddhasadhana_InstallingWhatYouCanAlreadyReachIsAPlateauSoTheKernelsOwnLibraryCannotGrowItsReach.agda:96`
  `install-chain-plateau`). Its vocabulary is not this language's design.
- **Deleting the cost.** The interaction count is a corpus quantity (item 4).
  Removing it because a toy also counted was wrong and was reverted.
- **Narrating from prior.** Every identifier in this file is cited to a file and
  line, and `cite.sh` fails the test suite when one does not resolve. A sentence
  that could have been written without reading the checked term it is about is
  not allowed here. Nineteen of twenty-one rules once cited theorems that did
  not exist; the table that exposed it is the reason this gate exists.
- **Inventing the cost model.** This file once said the proved count needed a
  face that "acts only at a superposition of its own name", never copying a
  constructor. The ledger's alphabet says the opposite: a duplicator meeting a
  node is the event `dupNode`, charged one interaction and the node's words
  (`research/sat_fibre/InteractionLedger.agda:16` `dupNode`, `:35`
  `localCharge`). A day was spent building a runtime around the invented
  sentence before it was checked against the cited line. The count's status is
  decided by the diamond and the schedule check, not by removing events.
- **Reading instead of building.** The object is fixed by items 1 to 5 and the
  modules they cite. A further module is read when its probe is being written,
  and the probe reproduces it by running.

## 0.3 Order of work

1. Coordinates at run time and the case on a coordinate as a superposition with
   restriction. Everything else is expressed through this. **Written**: a
   declaration `(def x : T)` with no body is one coordinate of `T`, created on
   first demand and shared by every reference; a match that asks a coordinate
   writes into the coordinate's own slot the superposition of the match's
   constructors, each with fresh coordinates for its fields, one line at a fresh
   bound name per choice, so every holder sees the same correlated superposition
   and the match then commutes over it by the ordinary rule (`R_SPLIT`;
   `t/coord.hyper`).
2. Unification at data types as the reduction of a path with coordinates.
   **Written** (`t/sort.hyper`: `sort`'s specification, its only text, prints
   `[1,2,3]` for A = [3,1,2]; the fibre of `isort` over `[1,2]` prints as the
   superposition of its two points; an empty fibre prints `*`). What the core
   does, and nothing per type:
   - A coordinate of an identity type is the identity cell (`T_UNIFY`) between
     its two sides; a coordinate of a Σ is a pair of coordinates. The identity
     reduces lazily: `REFL` when the sides agree, `*` when constructors or
     numerals differ, constructor against constructor as a conjunction of the
     fields' identities (`T_BOTH`), coordinate against term as a **binding**
     written into the coordinate's slot, superposed at every face the identity
     lives under (the other side of each face a fresh coordinate), so every
     holder sees the binding exactly where it holds; a superposed side
     distributes, and a name the identity's faces already fix is projected, not
     distributed.
   - **Forcing.** A cell is forced when demanded at the top; the scrutinee of a
     match and the sides of an identity are inspected, not forced. Splitting
     happens only under force, so the outermost eliminator facing a stuck term
     is the one that decomposes: a coordinate is split only as far as it is
     asked. The top resolves in **rounds** of one split each (`resolve`), so a
     split anywhere is followed by inspection everywhere and a side that dies
     cheaply is reached before another split is made.
   - A match whose scrutinee is **stuck on a coordinate** (`leq h h'` with `h`
     free) does not split `h`. The stuck term itself becomes the superposition,
     over the constructors the match lists, of each constructor under the
     identity of the computation with it (`under` in the prelude: the
     language's own J), its fields fresh **derived** coordinates. The stuck cell
     is marked with the superposition, so every holder meets the same split and
     the same worlds, and the computation moves to one fresh cell shared by every
     residual. A match on `under(p, v)` commutes to `under(p, match v)`; an
     identity with `under(p, v)` on a side is `p ∧ (v ≡ y)`.
   - A **derived** coordinate is never split: asking it forces the identity that
     defines it. Only a free port (a declared unknown, a field of a coordinate's
     split) is split.
   - Residuals have a **kind**: the specification is kind 0, the identity a
     stuck match leaves behind while a cell of kind k is forced is kind k+1. A
     round forces kind ≤ k, and k rises only when a round moved nothing, so the
     residual of a comparison is explored only when what it constrains is
     otherwise undetermined, and a comparison between free naturals is never
     enumerated while the data can still decide.
   - Coordinates carry the **world** (faces) they live in; a binding under a face
     of that world is written plainly, under the opposite side it is `*`. A face
     on a coordinate with no value, or on a match blocked on one, **waits** on
     the one shared cell rather than copying it. A match, an identity and a
     conjunction each project a superposition at a name their frame or faces
     already fix.
   - The printer prunes: a superposition with a dead side is its other side,
     with both dead it is `*`.
   The cost of `sort` for three elements is 37,159 interactions and 544
   rounds (`HYPER_CENSUS=1`, step 5 names the events).
3. The trace of a run and the leaves of a superposition as terms; the four modes
   removed and their probes rewritten as programs. **Written**: `(trace e)` and
   `(leaves e)` (§3); `main.c` has `run`, `bend`, `check`, `interact`;
   `t/census.hyper`, `t/jiva.hyper`, `t/meet.hyper` are programs over declared
   fibres, `trace` and `leaves`, and reproduce every check the modes made. Not
   yet a term: the cost of one leaf of a superposed run. The ledger is the
   run's; a leaf's own charge needs the receipts attributed to the world they
   fired in, which the trace does not record. That is what `sortCost` needs
   (step 4).
4. A declaration with no body is inferred: `sort` as the first test, its type its
   only text; `sortCost n` for small n against the decision-tree bound as the
   second. **Written, first half**: `sort : Π (L : List Nat). Σ B. …` is declared
   with no body (`t/sort.hyper`, `sort-A`); an unknown function applied is the
   coordinate of its codomain at the argument, one per (function, argument), so
   the same argument asks the same question. Along free coordinates the run is
   the decision tree: `isort` of three unknowns is six leaves (`n-isort3`), and
   `(trace e)` over a superposed run gives each leaf the events that fired in
   its world or above it (`trace_over`; `HYPER_SPLITS=1` shows each split). A
   stuck question is identified by its code and the identities of what its code
   reads, so one comparison asked at two sites is one split (`n-two-asks`).
   Inside `trace` and `leaves` a residual does not ask a port (`KIND_CAP`): the
   leaves stay the classes of inputs, printed as a value under its identities.
   The innermost eliminator not facing a bare port is the one that decomposes: a
   match on a match on a comparison asks the comparison. A residual whose
   question was split (under another cell, or before its ports were bound) is
   marked with that split, its identity read under its own faces and the frame's
   restrictions, so a comparison split as `leq b1 a` and the same comparison
   after `b1 := h2, a := h3` are one question (`n-run2`: the two arrangements,
   no leaf with contradictory residuals). A bare residual on a question no match
   has split splits it itself, along the constructors of the answer it requires
   (`decide_question`). A match's scrutinee word is never rewritten with a
   reduct that is still an identity: it may be a child of the match's own body,
   and writing it closes a cycle. A residual whose question, as now understood,
   has no registered split registers its own split under that key, so the second
   residual on the question meets the first (`HYPER_SPLITS=1` checks every leaf's
   residuals for contradiction). **Written, second half**: the declaration `sort`
   along three free inputs resolves to exactly the six arrangements, no leaf with
   contradictory residuals (`count3`); the decision tree of `isort` along three
   free coordinates is exact, six leaves with 2, 3, 2, 2, 3, 3 comparisons and 3
   at most (`c-isort3`), each comparison one split whatever the world that first
   asked it; `sortCost` is `cost3`, the greatest event count over the leaves of
   `trace` (503 for three inputs), the machine's own charge for the world with
   the longest path, comparisons and the splits, unifications and face maps
   that carry the worlds alike. A leaf's charge is the declaration's: its comparisons and the splits,
   unifications and face maps that carry its world are all events of the
   ledger's alphabet, so a concrete run of `isort` on a representative, which
   makes none of them, is a different object with a smaller charge.
5. Every rule at an active pair, bodies as nets: the count is the ledger's and
   invariant under the schedules. **Written.** The ledger asks a runtime for one
   thing: a correspondence from its transitions to the event alphabet
   (`research/sat_fibre/InteractionLedger.agda:13` `Event`; the comment above
   `heap-monotone-prefix` says the theorem does not invent that mapping). The
   receipts of the superposition algebra now carry the alphabet's own names:
   a face meeting a superposition of its name is `dupSupEqual`, of another name
   `dupSupDifferent`, a closure `dupLamUsed` or `dupLamErased` (the binder never
   read), a constructor or any other node `dupNode`; an application over a
   superposition is `appSup`, a match over one `appMatSup` (`:31` to `:36`,
   `localCharge`). The census prints each event's count and the heap words it
   allocated, the two receivers of `Charge` (`:20`), so the run's ledger is the
   fold `interactionTotal-is-length` (`:74`) over these events. For `sort A`,
   A = [3,1,2]: 37,159 interactions; `dupNode` 11,666, `dupSupEqual` 4,979,
   `dupSupDifferent` 3,391, `dupLamUsed` 2,396, `appMatSup` 1,369, `beta` 2,090,
   `case` 1,310, `unify` 2,891, `split` 156, the rest atoms shared. Every rule
   of the run fires at an active pair: the one rule that fired on a non-value
   (the face pushed into a stuck spine before the definition unfolded) is gone
   from the run and kept for the checker alone, as its substitution through a
   neutral spine. The diamond is measured as §3 says: `sort-A`, `sort-dup`,
   `n-run2` and `c-isort3` give the same value in the same count when the
   right of two independent demands is served first or a coin decides
   (`test.sh`). What the check covers is independent demands. The two sides of
   an identity are not two independent demands: a side that dies ends the
   other, so their order is the term's (`x ≡ y` forces `x` first), and a run
   that forced them in the other order is a different question with a different
   count (`n-run2`: 10,241 against 10,250). The hypothesis of `RandomDescent`
   for this loop's step relation is an Agda obligation and is not discharged
   here; nothing in this file claims it is.
6. The chart move under a checked path. **Written** (`t/sort.hyper`, `chart-move`). The two charts of `sort` at
   A: `cheap-chart`, `Σ B. B ≡ isort A`, with centre `(isort A, refl)`; and `spec-chart`, the specification.
   The equivalence's forward map is the proof. It sends `(B, p)` to `(B, proofs B)`, where `proofs` is declared
   with no body, so its point at B is the Σ of the two identities at B, decided by unification once B is known.
   The cheap centre transported along `ua` of it (`trp` over the Glue line) is `[1,2,3]` in 363 interactions,
   against 37,159 for resolving the type (`sort-A`); the forward map alone (`direct`) is 255. The count is the
   same under the three schedules. What the core needed: an interval face meeting an unknown function passes
   through it, as through a definition. A Π coordinate is never bound whole; its points at arguments carry
   their own worlds, so waiting on the function blocked every application of it under a transport.
7. The Bend dialect's grammar as a book with its certificate; parallel demand
   over the one arena.

The sections below describe the substrate as it stands.


## Read order

Read these before writing anything here, in this order: `fibre/src/Everything.agda`,
`fibre/src/Fibre/CorpusInteraction.agda`, `fibre/src/Fibre/Carrier.agda`,
`fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda`,
`fibre/src/Fibre/Interaction_TheOrbitIsTheOneQueryCaseOfTheInteractiveCoalgebraAndTheDemandIsWhatDiffers.agda`,
and §0 of `formal/cubical/Kernel/DescentNote_WhatThisIsAndHowToDescendIntoTheMetacircularKernel.agda`.
Its test applies to every sentence of this file: a sentence that could have been
written without reading the checked term it is about is narration from prior.
Every identifier named below is cited as `file:line`, and `cite.sh` fails when
the identifier is not on that line of that file.

## The name

In an interaction net the only event is an active pair: two cells whose principal
ports face each other. Everything this program does happens at an active pair, and
a question from the world is one too (§2). The files are `.hyper`, the binary is
`hyper`, this directory is `hyper/`.

## 1. The substrate

A cubical type theory in which ua's β-rule reduces, with demanded (weak head)
reduction. `formal/cubical/Kernel/DescentNote_WhatThisIsAndHowToDescendIntoTheMetacircularKernel.agda:304`
`univalence-acts` is that fact as one term, and the descent note names it as the
whole reason the rest is possible.

The substrate is `cell.c`, `cell.h`, `read.c`, `verify.c` and the two rule files.
It reduces Bend2's dialect: every `.bend` under `collab/bend2-interactive-cubical`
is checked and emitted by Bend2 (`bend F --to-hyper`, `src/Target/Hyper.hs` in
`cubical-paths.patch`), run by `hyper bend`, and its value compared with Bend2's
own normaliser (`bendtest.sh`: 124 programs agree, 12 skipped because the oracle
itself does not run them). `verify.c` checks the same books and agrees with
Bend2's checker verdict by verdict (`checktest.sh`: 3862 definitions over 150
files, the must-fail probes included). `test.sh` holds the checks of the
substrate's own probes, its ledger, its schedules and its census.

What the substrate provides: cells over bound dimension names, frames with
descent, the face map (a dimension's endpoint, a choice name's side, a
coordinate's substitution), the interval as the free De Morgan algebra in
canonical form, transp and hcomp with regularity as an occurs check, Glue and
ua, higher inductive types by a schema (constructor boundaries read from their
types), fixed points, four numeric kinds, superpositions at bound names, and a
reader for its own text. Nothing is erased inside a run: a demanded node is
marked with its result once reduced (`T_IND`) and every holder sees the value.
The checker is bidirectional over static code with coordinates and rewrites via
the face map. The corpus's machine runs on cubical Agda; this evaluator exists
so that the machine can run without Agda or HVM, and it is the part of this
directory that is not itself the corpus.

Deviations from the mathematics, recorded: a non-variable scrutinee rewrites the
goal but not the context; a definition unfolds under conversion by its head
first; the branch-wise comparison of two stuck eliminators is bounded; a face
map passes through an application of a closed name into its arguments before
the name unfolds, the one rule that fires on a node that is not a value.

## 2. The primitive: interaction

Everything in this corpus is interaction, two-place at the least, and the
runtime's one operation is the coalgebra's `react`:
`fibre/src/Fibre/Interaction_TheOrbitIsTheOneQueryCaseOfTheInteractiveCoalgebraAndTheDemandIsWhatDiffers.agda:75`
`ISC` (coinductive), `:81` `react : (q : Q w) → Σ[ w' ∈ W ] Σ[ o ∈ O w q w' ] (E w q w' o × ISC Q O E w')`:
one encounter returns the successor, the observation, the proof-relevant event,
and the continuation, which is again an interaction. Nothing is globally
normalised; a finite demand of length n asks n questions and forces nothing else
(`:99` `observe`). `:132` `det-observe`, `:139` `det-strategy-independent`: with
the trivial question every strategy sees the same prefix of the orbit; `:172`
`counter-demand-matters`: with a real question two strategies disagree at the
first step. `LIFECYCLE.rst`: do not begin by assuming two independent machines
exchanging messages; start from the joint interaction and establish which
projections, dependencies and transports it admits.

Its instances, each a checked module, each computed by one mode of `hyper`:

**A typed point and a typed map** (`fibre/src/Fibre/CorpusInteraction.agda`,
whole: `:16` `Point`, `:22` `Question`, `:25` `target`, `:28` `Receipt`, `:38`
`run`, `:41` `step`). A state is `(A, a) : Σ A. A`; a question is `(B, f)` with
`f : A → B`; the answer is `(B, f a)`; the receipt is the path `target s q ≡ s'`,
`refl` at the canonical step. The event is the residual:
`formal/cubical/theorems/residue/CorpusLosslessPresentation.agda:19` `Residual`
(`fiber (query s q) (query s q (source s))`), `:27` `current-residual`
(`source s , refl`), and `formal/cubical/theorems/residue/CorpusSelfPresentation.agda:12`
`present` returns the four together. The state carries its reading losslessly
(`fibre/src/Fibre/CorpusInteraction.agda:47` `State`, `:82` `state≡carried`,
by `fibre/src/Fibre/Carrier.agda:92` `fibre-isContr`, `:96` `descend`, `:115`
`Carrier≃`, `:119` `Carrier≡`, `:129` `carry-transport-descend`). As written:
`hyper run FILE [DEF]` is the trivial query; `hyper interact FILE [DEF]` is
`present`: the point, then each line of the world a question, the point
presented along it, the new state `(q a, (a, refl))`; an `ASK` cell is a
question the point asks the world. The residual's census is a program (§3).

**Two parts of one joint**
(`formal/cubical/theorems/logic/Jiva_EntanglementIsTheFibreOfTheProductComparisonAndTheLivingStepRefusesToDescendToTheMarginals.agda`).
A joint state is `J` with two projections, and everything is an officer of the
comparison `:134` `तुलना`, `j ↦ (p j , q j)`: `:139` `स्वातन्त्र्यम्` (independence
is the comparison being an equivalence), `:142` `संश्लेष-तन्तुः` (entanglement is
its fibre family), `:149` `संकलनम्` (the joint is the sum of its entanglement
fibres). `:164` `घटः-स्वतन्त्रः`: the product joint is independent. `:178`
`रिक्तम्`: the diagonal joint has an empty fibre over `(true, false)`, a pair of
marginal readings the whole never realises. `:207` `गूढौ-भिन्नौ`: the joint over
`Unit × Unit` has two distinct residents over the one reading. A step on `J`
descends along a projection when some endomap of the part closes the square
(`:256` `युगलम्-उभयतः`); `:266` `जीवति`: the controlled-not refuses to descend
along the visible side, interrogated at `(true, false)` and `(true, true)`;
`:276` `दक्षिण-विलयः`: it descends along the hidden side by `refl`; `:286`
`विलयः`: the step `(not a, b)` descends on both sides; `:302` `जीवन-द्विः`: the
living step is an involution, globally lossless, locally refusing. As written
(`t/jiva.hyper`, programs): the joint is a type, the fibre of the comparison
over a pair of readings is declared, `Σ j : J. (p j, q j) ≡ (a, b)`, and
resolved: one point for the product joint, `*` for the diagonal joint at
`(True, False)`, two points for the joint with a hidden bit. A step's refusal
to descend along `p` is the declared fibre
`Σ j k. (p j ≡ p k) × (eq (p (step j)) (p (step k)) ≡ False)`: a point of it is
the interrogating pair (the controlled-not along the visible side), `*` is
descent (the controlled-not along the hidden side, the dead step on both).

**Two sessions and an overlap**: the encounter, §4b.

**The fixed alphabet.** A Chu evaluation `e : A × X → K` retains `k`; the
lossless interaction retains `fib_e(k)`, forced by
`fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda:129`
`fibre-of-run`; the general interaction is a family `R : A × X → 𝒰` classified
by the universal family, and a tower of such families flattens to one
(`fibre/src/Fibre/Universal_EveryFamilyIsAPullbackOfTheUniverseAndTheTowerFlattensToOne.agda:312`
`flatten`). `CHU_LOSSLESS_INTERACTION.md` is the reading; the census of a map out of a
product domain, resolved pointwise, is the Chu matrix with its fibres.

`hyper check FILE` is `verify.c` on every definition; `hyper bend FILE` runs
`b/main` in Bend2's presentation, for the oracle.

## 3. The trace, and what a computation costs

Two measures, both corpus quantities, and they measure different things.

**The ledger: what a run costs.** `research/sat_fibre/InteractionLedger.agda:13`
`Event`, `:20` `Charge` (`interactions`, `heapWords`), `:57` `Trace` (a run is a
sequence of events), `:65` `interactionTotal`, `:74` `interactionTotal-is-length`.
`research/sat_fibre/InteractionGeodesic.agda:14` `RandomDescent`, parametrised by
a one-step `diamond`; `:45` `same-normalization-length`: every complete reduction
of one object to its normal form has the same length; `:53`
`normalization-is-geodesic`. As written: every rule appends its receipt to
`TRACE`, with the node it fired on and the heap length at that moment; a run
prints `- Itrs:` (the interactions) and `- Words:` (the heap words allocated),
the two components of `Charge`; `HYPER_CENSUS=1` prints each event's count and
the heap words it allocated, the events of the superposition algebra under the
ledger's own names (`dupNode`, `dupSupEqual`, `appSup`, …; step 5).
**The trace is a term**: `(trace e)` runs `e` to its normal form and is the
pair of the value and the list of its events, each event the rule's name as a
constructor carrying the words it allocated (`#beta{4}`), so the trace lives
over the result as in `fibre-of-run`, `interactionTotal` is `length` and
`ledger` is a fold, both written in the language (`t/meet.hyper`).
`(leaves e)` is the list of the leaves of `e`'s superposition, dead sides
dropped (`t/census.hyper`); `HYPER_SCHEDULE` serves the right of two independent demands
first, or a coin per choice, and `test.sh` and `bendtest.sh` require the same
value and the same count under the schedules (the diamond, measured, since the
hypothesis of `RandomDescent` is not discharged for this loop's step relation).
Definitional unfolding is not an event. The sharing regimes (`bendtest.sh`,
`bench_*_sup` against `bench_*_sep`; `t/ua.hyper`, a transport used k times)
are the reason a runtime exists at all: the superposition is one line over N
values and its cost is what the ledger shows.

**The census: what a question loses.**
`fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda:90`
`Conservative` (`Trace : B → Type`, `whole : A ≃ Σ[ b ∈ B ] Trace b`); `:129`
`fibre-of-run`: for any conservative factorisation the trace family is the
homotopy fibre of the visible map it induces. `:159` `exact-when-contractible`,
`:164` `contractible-when-exact`: the trace measures exactly the failure of the
visible result to be the whole event. `:181` `canonical`, `:194`
`canonical-recovers`, by `refl`: the source was never left behind.
`fibre/src/Fibre/WholePartialDesa_TheFibreCensusIsATermAndItRefutesTheSequentialDiagnostic.agda:87`
`देश`, `:93` `गणना`: the census of a question, pointwise over the codomain,
three-valued. As written (`t/census.hyper`, programs): the fibre of `f` over
`b` is declared, `Σ a : A. f a ≡ b`, with no witness; its proof is asked and
its points are asked along their type; the resolution is the census, `:88`
`नास्ति` when it is `*`, `:89` `सकलादेश` when it is one point, `:90` `विकलादेश`
when it is the superposition of two or more, both shown as the constructor
requires. `t/census.hyper` is the module's own §3: `Unit → Bool` is one point at
`True` and `*` at `False`, `Bool → Unit` is two points at `Tt`, and their
composite is one point, where the sequential diagnostic would add the losses.
No organ computes this: the fibre law, run forward (§0.1).

Erase: nothing is erased inside a run; a forgotten port is one receipt where it
is forgotten (`t/erase.hyper`: the fibre's size never enters). Commutation is
the certificate that an order was removable:
`fibre/src/Fibre/Order_CommutationIsTheProofThatTheOrderWasNeverThereAndItsFailureIsRetained.agda:102`
`serialisation`.

## 4. What is not here, and why

Removed: `install` as this directory had it (a path between two definitions at
a type, then native dispatch), the parser producing Code, and the reifier. The
first was an invented shape. The corpus's `install` is
`formal/cubical/Kernel/ControlledGrammar.agda:27` `install`, from a
`Derivation`, a trace of steps between two terms, to a `NativeOperation`, and
its own theorems bound it:
`formal/cubical/Kernel/Vyapti_TheInstalledOperationHasNoneSoTheKernelMemorisesAndTheSchemaIsWhatMakesItGeneralise.agda:113`
`fires-only-at-source`, `:176` `kernel-cannot-reach-a-tower`,
`formal/cubical/Kernel/Siddhasadhana_InstallingWhatYouCanAlreadyReachIsAPlateauSoTheKernelsOwnLibraryCannotGrowItsReach.agda:96`
`install-chain-plateau`. In this runtime the derivation of a run is `TRACE`, and
a node once fired is marked with its result (`T_IND`), which is what installing
a run's derivation as a move amounts to here. A grammar's substitution is a
Carrier instance with a base and a carried datum
(`fibre/src/Fibre/Sthanivadbhava_TheAdesasFormIsTheFreeSlotAndItsDesignationsAreCarried.agda`),
not a parser.

## 4b. The encounter of two peers

`formal/cubical/kernel-flat/TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection.agda:123`
`Peer` (a `Session`:
`formal/cubical/kernel-flat/TheKernelIsAnInteractiveSystemAndTheSessionRetiresIntoOneOperation.agda:170`
`Session`, with `origin`, `here`, `trace : Derivation origin here`, `library`;
`:155` `_⊕_`),
`formal/cubical/kernel-flat/TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection.agda:126`
`Encounter` (`A B`, `meeting`, `mine : Derivation (here A) meeting`, `theirs :
Derivation meeting (here B)`), `:138` `τ` (`mine ⊕ theirs`),
`:148` `gain` (the three moves installed), `:153` `A′`, `:158` `B′`, `:164`
`interact` (`A′ E , B′ E , τ E`), `:172` `receive`. Reversal is
`formal/cubical/kernel-flat/TheKernelIsAReversibleGroupoidWhoseJoinIsConflictFreeSoConsensusOnMeaningIsVacuous.agda:119`
`rev`, the length
`formal/cubical/kernel-flat/TheDerivationCarriesNoMeaningAtAllSoAllOfItIsRemainder.agda:126`
`len`.

As written (`t/meet.hyper`, a program over `trace`): a derivation is the trace
of a run as a term, `(trace a)` the value with its events over it; the two peers
meet when the values are equal (`eq-nat`), else there is no meeting; `mine` is
A's events, `theirs` the reversal of B's (each step under `Rev`), `τ` their
concatenation (`cat`), and the round trip `τ ⊕ rev τ`. Lengths are `length`, a
fold in the language. `t/meet.hyper` computes the module's sections:
`formal/cubical/kernel-flat/TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection.agda:256`
`the-two-results-need-not-agree` (the meeting is one value reached from two
terms), `:341` `undo` (`rev τ`), `:380` `round-trip` with `:392`
`the-round-trip-is-not-done` (2·len τ steps from `a` to `a`; the meaning is refl,
the object is not done), `:409` `the-fabric-composes-strictly` (`cat`), `:444`
`the-two-orders-differ` and `:448` `both-orders-cost-the-same` (the crossing:
`cross` under the two schedules reaches the same value with the same events;
the traces differ by the nodes they fire on, `HYPER_TRACE=1`), `:474`
`the-scalar-is-additive` (`len (d ⊕ e) = len d + len e`). Not written: `:284`
`what-crossed-is-what-B-had`, `:320` `the-pair-holds-it-after`, `:334`
`the-prior-trace-is-a-prefix` (the session's library of moves: a construction
to be written as a program when a probe needs it), `:483`
`no-section-for-any-order-blind-projection` beyond the crossing, and `:542`
`the-receipt-does-not-cross`, which needs a demanded evidence (`demand R d`)
this runtime does not model.

## 5. Files

    hyper/cell.h             the word layout, tags, frames, constructors, the receipts
    hyper/cell.c             the substrate: heap, frames, instantiation, the interval, the face map,
                             case trees, the HIT schema, numbers, transp, hcomp, Glue, the loop, the ledger, printers
    hyper/read.c             the reader for the kernel's own text
    hyper/verify.c           the checker on the same loop
    hyper/main.c             run | bend | check | interact
    hyper/prelude.hyper 158  the Kan rows, Glue, transpEquiv, the HIT rows, as data
    hyper/bend.hyper     45  the Bend2 dialect's rows
    hyper/test.sh            the substrate's checks
    hyper/bendtest.sh        values against Bend2's normaliser
    hyper/checktest.sh       verdicts against Bend2's checker
    hyper/cite.sh            every identifier this file names is on the line it cites
