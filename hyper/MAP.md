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

The runtime is an interaction net (`net.c`). A term is a graph of nodes, each with one principal port. A rule fires only where two principal ports meet (an active pair), and rewrites only that pair. So two active pairs never share a node, firing them in either order meets in one step on each side, and every complete reduction of a net to its normal form has the same length (`research/sat_fibre/InteractionGeodesic.agda:45` `same-normalization-length`). The count of a fixed net and demand is its geodesic.

The one paid decision is a duplicator meeting a superposition:
- **Same label: routes.** The two sides are the two copies. Nothing is allocated; the fibre is contractible.
- **Different label: crosses.** Each distributes over the other, and the allocation is the non-invertible part.

Witnessing a proposition is this operation. The domain is one labelled superposition shared by every occurrence, the proposition reduces once over it, a failing branch is erased, and the collapse is the fibre. Constructing a specified map is the same operation over a superposition of candidate maps (`collab/bend2-interactive-cubical/SUPGEN_DEMO.md`).

The cubical operations (transport, hcomp, Glue, `ua`) are programs on this net, as Bend2's `--to-hvm4-full` emits them, not primitives of the runtime.

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

## 0.3 What exists

The cubical language on the net is `collab/bend2-interactive-cubical/`: `cubical-paths.patch` to Bend2, whose `--to-hvm4-full` keeps the interval, paths, types, `coe`, `hcomp`, Glue and HIT cells as runtime data on HVM4, verified by `suite.sh` and `verify_conductive_entry.sh`; its state is `STATE_OF_THE_WORK.md` and the runtime the theorems dictate is `SETTLED_BY_THE_CORPUS.md` §4. Nothing in `hyper/` adds to it.

## Files

    hyper/MAP.md         this file: the task
    hyper/NOTES.md       readings of the corpus
    hyper/cite.sh        every identifier this file and NOTES.md name is on the line it cites
