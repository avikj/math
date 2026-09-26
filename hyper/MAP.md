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
coordinate, with fresh coordinates for the fields, the constructors read from
the type's declaration and nowhere else. Sides on
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
type's eliminator: the value at each constructor is a point of the codomain
there, and the recursive field is the function itself at that field.

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
  under its certificate.

Nothing in this list names lists, numbers, sorting or cost.

## 0.2 What regressing looks like, so you can recognise it

Today's session lost most of a day to each of these, in order. Do not repeat
them.

- **Building an interface instead of the language.** Subcommands that compute
  what a corpus module proves (a census mode, a joint mode, a meet mode) are
  organs. The constructions belong in the language as terms over the two
  primitives above, and the runtime has one entry: reduce. The modes this
  branch once had are gone; their probes are programs.
- **Building the runtime someone else already has.** An efficient interaction
  net exists (HVM). A cubical fork of Bend on it exists
  (`collab/bend2-interactive-cubical`). This directory is not a faster one of
  those and owes them nothing. It is the language in §0; a Bend front end is a
  syntax layer if it is ever wanted.
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
  sentence before it was checked against the cited line.
- **Scheduling the mathematics.** The runtime once had kinds and rounds deciding
  when a residual identity may ask a port, a cap, a derived-coordinate special
  case, tables of the constructors of four types, a hash identifying two stuck
  matches, a knob perturbing the order of demands, and a checker with the
  Bend dialect's built-ins. Every one filled a hole left by another. §5 of
  `NOTES.md`: order is a certificate or data, never a policy; the constructors
  of a type are its declaration; one point is one point. All of it is deleted;
  what remains is the rule in §0.3.
- **Running instead of reading.** A change made to see what it does is a
  change made without knowing what the code is. Every line here is derived from
  the mathematics first and compiled second; the suite is not the standard, and
  a green suite around a wrong construction is itself the error.

## 0.3 What is written

One rule at a match, and everything else is the cubical type theory it runs in.

**The rule.** A match demands the head of its scrutinee. The scrutinee is
inspected, not forced: evaluation runs through β and constructor selection and
stops at a match facing a point whose head is not yet a constructor, because
binding that point's output is the act of the match that faces it. A
coordinate's head is the superposition of its type's declared constructors,
written into the coordinate's own slot, one line at a fresh bound name per
choice, each side's fields fresh coordinates of that side's world
(`constructor_superposition`). A computation's head is bound at its output: the
same superposition, each constructor under the identity of the computation with
it (`split_stuck`; `under` in the prelude is J), the computation moved to one
cell shared by every residual, the identity decided when demanded. A point of
an identity type is the identity cell between its sides; a point of a Σ is a
pair of points; a point of a one-constructor type is that constructor. An
identity's sides are inspected; when the identity is itself demanded a side
whose head is not a constructor is forced, the first side first, a dead side
ending the other. A conjunction inspects both sides before forcing either, so a
binding one side makes is met before a port is asked on the other.

**The identity of a point.** A function has one value per argument
(`formal/cubical/theorems/residue/Sambandha_TheRelationalProgramWithUniqueAnswersIsTheMapSoAllThreePresentationsCollapseOntoOneFunction.agda:92`
`relational-programs-are-maps`). A free function applied to a superposed
argument distributes; applied to anything else it is the point of its codomain
there, one per argument (`pi_apply`, `point_at`), the argument compared by its
canonical form over coordinates as it stands now (`same_point`): a coordinate by
its cell, a constructor by its id and fields, a closure or a match by its code
and the slots the code reads. Nothing is hashed and no depth cut identifies;
where the comparison gives out it says different, which under-shares and never
mis-shares. The point carries what it is a function of, and asking it re-reads
the argument as it stands: a superposed argument distributes the point, a bound
one meets the point registered first. Two stuck computations that are the same
point split once, by the same comparison.

**Unification** at data types: `REFL` when the sides agree, `*` when
constructors or numerals differ, constructor against constructor as a
conjunction of the fields' identities, coordinate against term as a binding
written into the coordinate's slot, superposed at every face the identity lives
under so every holder sees the binding exactly where it holds; a superposed side
distributes; a name the identity's faces already fix is projected. Coordinates
carry the world they live in; a binding under the opposite side of one of its
faces is `*`.

**The presentation.** `(trace e)` is the value with the ledger's events over
it, each leaf of a superposed run with the events that fired in its world or
above it; `(leaves e)` is the list of a superposition's leaves, dead sides
dropped; the printer prunes a superposition with a dead side to its other side
and both dead to `*`, and cuts at depth. The receipts carry the ledger's names
(`research/sat_fibre/InteractionLedger.agda:13` `data Event`).

**Not exercised.** `sort L` with `L` free, `sortCost n` with `n` free, and the
equivalence between the two charts of `sort` declared with no body, resolve, if
they resolve, by the rule above and nothing added: the free function's point at
the free argument, its Σ split into typed coordinates, the identity forcing
`isort L`, and `L` splitting along its constructors. No number in this file is
a measurement of the present runtime.

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

The substrate is `cell.c`, `cell.h`, `read.c`, `main.c` and `prelude.hyper`.
What it provides: cells over bound dimension names, frames with descent, the
face map (a dimension's endpoint, a choice name's side, a coordinate's
substitution), the interval as the free De Morgan algebra in canonical form,
transp and hcomp with regularity as an occurs check, Glue and ua, inductive and
higher inductive types by one schema (a constructor's boundary is its declared
type; Unit, Bool, Nat and List are declared in the prelude like any other),
fixed points, numerals, superpositions at bound names, free points, and a
reader for its own text. Nothing is erased inside a run: a demanded node is
marked with its result once reduced (`T_IND`) and every holder sees the value.
The corpus's machine runs on cubical Agda; this evaluator exists so that the
machine can run without Agda, and it is the part of this directory that is not
itself the corpus.

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

Its instances, each a checked module, each a program here:

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
dropped (`t/census.hyper`). The diamond of `RandomDescent` is a theorem of nets;
a runtime whose count depends on which of two independent demands fires first
is not a net, and that is a defect to remove, never a proof left to write.
Definitional unfolding is not an event. Sharing is the reason a runtime exists
at all: the superposition is one line over N values and its cost is what the
ledger shows (`t/ua.hyper`, a transport used k times).

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
                             case trees, the schema, numbers, transp, hcomp, Glue, the loop, the rule
                             at a match, unification, the identity of a point, the ledger, the printer
    hyper/read.c             the reader for the kernel's own text
    hyper/main.c             run | interact
    hyper/prelude.hyper      the data types, the Kan rows, Glue, transpEquiv, the schema's rows, as data
    hyper/test.sh            probes; not the standard
    hyper/cite.sh            every identifier this file and NOTES.md name is on the line it cites
    hyper/NOTES.md           what the system is, read from the formal sources
