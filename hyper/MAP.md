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

## 0.1 The mechanism, from the construction

The construction's whole machine is small:

- **A state** is a typed point (`fibre/src/Fibre/CorpusInteraction.agda:17` `Point ℓ = Σ[ A ∈ Type ℓ ] A`).
- **A question** is a typed map out of the state's type (`:23` `Question`).
- **A step** answers with the image of the point (`:26` `target s (B , f) = B , f (snd s)`). Its receipt and event are `refl`, and the run continues from the image (`:39` `S.react (run s) q`).
- **Presenting a point along a map** carries the image and its witness, and adds nothing: `descend a = (a , f a , refl)` (`fibre/src/Fibre/Carrier.agda:97` `descend a = carry a (f a) refl`), `ascend c = base c` (`:100` `ascend c = base c`).
  - The carried pair ranges over a contractible type (`:93` `fibre-isContr a = isContrSingl (f a)`), so presenting is an equivalence (`:116` `Carrier≃ = isoToEquiv Carrier-Iso`).
  - Transport along its `ua` computes to `descend` (`:130` `carry-transport-descend a = uaβ Carrier≃ a`).
- **The residual** a question leaves is inhabited by the point itself (`formal/cubical/theorems/residue/CorpusLosslessPresentation.agda:28` `current-residual s q = source s , refl`). It is never computed.

The core owes the language exactly the reduction of these:
- application;
- projection and match on constructors;
- superposition;
- faces;
- transport, hcomp, Glue and `ua`;
- trace and leaves as terms;
- the receipt of each rule at an active pair.

It does not solve for an unknown. An earlier core did: it made a bodyless declaration a coordinate, split coordinates at matches, unified at data types, and split the output of stuck computations. That machinery is not in the construction and has been deleted, along with the scheduler it needed.

**Open:** how a declaration with no body is resolved inside this machine. The chart move (step 4 below) is the construction's mechanism for reaching a specification's point, but there the map (`isort`) is written in the book.

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

1. **The substrate. Written.**
   - Application, match, superposition and faces, each at an active pair.
   - Transport, hcomp, Glue, `ua`, and higher inductive types.
   - Tested by `t/basic.hyper`, `t/lazy.hyper`, `t/sup.hyper`, `t/kan.hyper`, `t/ua.hyper`, `t/setcomp.hyper`, `t/hit.hyper` and `t/erase.hyper`.
2. **The trace of a run and the leaves of a superposition as terms. Written** (`trace`, `leaves`; `t/meet.hyper`).
3. **Every rule fires at an active pair and is receipted. Written.** The value and the count are the same when the right demand is served first or a coin decides (`test.sh`, the schedule loop).
4. The chart move under a checked path. **Written, run; the path is not yet checked** (`t/sort.hyper`, `chart-move`).
   The cheap chart is `Carrier isort` (`fibre/src/Fibre/Carrier.agda`): a list, its image under `isort`, and the
   witness. `descend a = (a, isort a, refl)` and `ascend c = base c`, and the two round trips are an iso. The
   prelude's `iso-to-equiv` is agda/cubical's `isoToIsEquiv`, term for term (`fill0`, `fill2`, `sq`, `sq1`,
   `lemIso`), and it makes the iso an equivalence. Transport of A along its `ua` is `descend A` (uaβ), and the
   carried image is `[1,2,3]` in 173 interactions, where the deleted narrowing core took 37,159 to resolve the
   type; no coordinate, split or unification. It is the same under the three schedules.
   **Open:** `b/sort_at_A` states the specification at that B, `(B, (refl, refl))`, but `hyper check` rejects it
   because `isort`, `sorted`, the carrier and the prelude's Kan operations are untyped definitions. The checked
   path needs them typed.
5. **A declaration with no body. Open.** See §0.1: the construction reaches a specification's point by presenting along a map and transporting along the equivalence. How a declaration with no body supplies that map is not yet stated.
6. **The Bend dialect's grammar** as a book with its certificate, and parallel demand over the one arena.

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
living step is an involution, globally lossless, locally refusing.

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
dropped; `HYPER_SCHEDULE` serves the right of two independent demands
first, or a coin per choice, and `test.sh` and `bendtest.sh` require the same
value and the same count under the schedules (the diamond: distinct active pairs
are disjoint, so the order of two independent demands cannot change the count).
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
three-valued.

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
    hyper/main.c             run | bend | check | interact | net
    hyper/net.c              the interaction net the SAT fibre results were computed on: HVM4 6defdfc src/hvm.c
                             taken literally, with build_profile.py's receipt by rule (DUP-SUP-SAME/-DIFF)
    hyper/prelude.hyper 158  the Kan rows, Glue, transpEquiv, the HIT rows, as data
    hyper/bend.hyper     45  the Bend2 dialect's rows
    hyper/test.sh            the substrate's checks
    hyper/satcheck.py        research/sat_fibre reproduced exactly on `hyper net`: outputs, interactions, heap, rules
    hyper/bendtest.sh        values against Bend2's normaliser
    hyper/checktest.sh       verdicts against Bend2's checker
    hyper/cite.sh            every identifier this file names is on the line it cites
