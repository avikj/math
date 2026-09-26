# Reading notes: what the system is

Notes from reading, each sentence at a cited line; `cite.sh` checks this file
as it checks `MAP.md`. The test of
`formal/cubical/Kernel/DescentNote_WhatThisIsAndHowToDescendIntoTheMetacircularKernel.agda`
(§0, frame 4) applies to every line: a sentence that could have been written without reading
the term it is about is narration from prior. Where a section says what this
means for `hyper/`, that is a reading, marked as such.

The system is one construction, not parts. Everything below is the same Σ read
from different ends, and the runtime's one job is to be that Σ computing.

## 1. The one object: which side of `f a ≡ b` is bound

`fibre/src/Fibre/Carrier.agda:65` `record Carrier`: for `f : A → B`, a point is
`base : A`, `carried : B`, `witness : f base ≡ carried`. `:90` `fibre a = singl (f a)`,
`:92` `fibre-isContr`. Binding the **output**, the fibre is contractible for
every `f`, so `:115` `Carrier≃ : A ≃ Carrier`, `:120` `Carrier≡ = ua Carrier≃`,
and `:129` `carry-transport-descend`: transport along that path computes
`descend` (`:96` `descend : A → Carrier`), by `uaβ` (`:130` `uaβ`). The implementation facts in the header are about
reduction: Σ not Prod (η closes the square by `refl` on an opaque variable) and
`descend` must not pattern match.

`fibre/src/Fibre/Residue_TheResidualIsTheOtherProjectionOfTheSameGraph.agda:122`
`शेष b = Σ[ a ∈ A ] (f a ≡ b)`: binding the **input**. `:134` `स्वप्`: the graph
`Σ a. Σ b. f a ≡ b` read from either end, both round trips `refl`. `:155`
`मूल-प्रक्षेप-समता`: the source projection is always an equivalence. `:182`
`समता→निःशेषः`: the target projection is one exactly when every residual is
contractible, because `isEquiv` is defined fibrewise. `:208` `शेष-सर्वैकम्≃Bool`:
the smallest collapse, `Bool → Unit`, forgets exactly one bit, as a theorem.

The descent note says the same in two lines
(`formal/cubical/Kernel/DescentNote_WhatThisIsAndHowToDescendIntoTheMetacircularKernel.agda`, §1):
bind the output and the fibre is `singl (f a)`, always contractible; bind the
input and it is `fiber f b`, contractible exactly when `f` is an equivalence,
"that is the exact loss".

`punaragamana/src/Punaragamana/Samagra_TheSourceIsDirectlyEquivalentToTheTotalResidualWithNoCarrierInTheMiddle.agda`
composes the two into one statement, `A ≃ Σ b. शेष f b`, with forward map
`a ↦ (f a , (a , refl))` by `refl`.

## 2. The trace is forced to be the fibre

`fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda:90`
`Conservative`: a trace family `Trace : B → Type` and `whole : A ≃ Σ b. Trace b`;
`run` is read off the equivalence (`:99`), `trace a : Trace (run a)` (`:104`),
the trace lives over the result. `:129` `fibre-of-run : (b : B) → fiber (run C) b ≃ T b`,
five library equivalences, the last (`:150` `s5`) contracting the path
component. `:159` `exact-when-contractible`, `:164` `contractible-when-exact`:
the trace measures exactly the failure of the visible result to be the whole
event. `:181` `canonical`, `:194` `canonical-recovers` by `refl`. `:240`
`unitTrace` refutes the proviso: an equivalence not over `B` factorises a
different computation.

`formal/cubical/theorems/residue/Uniqueness_LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleTypeAndTheMachinesIsUnique.agda`:
the type of lossless completions of a fixed map is contractible; a lossless
machine cannot be built two ways.

**Reading for `hyper`.** `(trace e)` is the value with its events over it;
`(leaves e)` over free inputs is the fibre family over values: each leaf is the
class of inputs giving that value. Neither is a choice; both are forced.

## 3. The census, not a verdict

`fibre/src/Fibre/WholePartialDesa_TheFibreCensusIsATermAndItRefutesTheSequentialDiagnostic.agda:87`
`data देश`: `नास्ति` (empty, with `¬ शेष f b`), `सकलादेश` (contractible),
`विकलादेश` (two points and their distinctness). `:93` `गणना`: pointwise over
the codomain. `:179` `संहति-गणना`: the composite of a step with an empty fibre
and a step with a crowded one is contractible, so a sequential diagnostic is
wrong in both directions. `:194` `सर्व-सकल→समता`: the verdict is the summary of
the census; the census is not recoverable from the verdict.

`formal/cubical/theorems/residue/Anveshana_TheMiddleGradeIsWhereAnAlgorithmHasContentBecauseUniquenessIsFreeAndExistenceIsTheWork.agda:87`
`सकल   = isContr (fiber f b)`, `:88` `एकाधिक = isProp  (fiber f b)`: three grades of a fibre. Contractible: exists and determined,
nothing to search. Propositional: determined if it exists, "uniqueness is free
and existence is the whole of the work", so a search may stop at the first hit
and owes no comparison. Crowded: nothing an algorithm could return.

**Reading for `hyper`.** The printer's `*` is `नास्ति`, one point is `सकलादेश`,
a superposition of two is `विकलादेश`; `t/census.hyper` reproduces `संहति-गणना`. The
middle grade names exactly where `sort`'s cost goes: its fibre is a proposition
(sorted permutations are unique), so once one leaf is live the run owes nothing
to the rest of the tree. The branch today exhausts the tree instead.

## 4. Interaction is the operation

`fibre/src/Fibre/Interaction_TheOrbitIsTheOneQueryCaseOfTheInteractiveCoalgebraAndTheDemandIsWhatDiffers.agda:75`
`ISC`, `:81` `react`: a question returns successor, observation, event and the
continuation, coinductively. `:99` `observe`: n questions force nothing else.
`:139` `det-strategy-independent`; `:172` `counter-demand-matters`: with a real
question two strategies disagree at the first step. The demand is what differs.

`fibre/src/Fibre/CorpusInteraction.agda:17` `Point ℓ = Σ[ A ∈ Type ℓ ] A`, `:22` `Question`
is `Σ B. (A → B)`, `:28` `Receipt` the path, `:38` `run` reacts with `refl`,
`:48` `State = C.Carrier read`: the state carries its reading.

`formal/cubical/theorems/residue/Prasna_TheMachineThatAsksItsRunIsItsAnswerStreamAndSilenceOfQuestionsIsDeterminism.agda:129`
`run-is-answers : (x : X) → IExec x ≃ Answers x`: a history carries nothing beyond the
answers the environment supplied; receipts weigh nothing. `:166` `silence-is-determinism`:
every question contractible makes the run contractible.
`formal/cubical/theorems/residue/Niyati_TheMachineHasExactlyOneExecutionDeterminismIsContractibilityOfTheStream.agda`
`exec-unique`: one configuration, one history.
`formal/cubical/theorems/residue/Vishvayantra_TheTuringStepIsTheVisibleProjectionOfTheLosslessStepAndTheKeptFibreIsTheSource.agda`:
the Turing step is the visible projection of the lossless step, by `refl`.

`research/HLEVEL_OF_INTERACTION_20260913.md`: the h-level of the process space
is the h-level of the event datum. A propositional receipt gives a contractible
process (a service); a proof-relevant one gives a generator. The kernel is the
only forward-non-trivial object among the four probed.

**Reading for `hyper`.** `run` is the trivial query; `interact` is `react`
with a question per line. A run over free inputs is not deterministic: its
questions (which side of a split) are the environment's, and the space of runs
is the space of answer streams, which is what the superposition holds all at
once.

## 5. Order: commutation is the certificate, its failure is retained

`fibre/src/Fibre/Order_CommutationIsTheProofThatTheOrderWasNeverThereAndItsFailureIsRetained.agda:93`
`Commutes`, `:102` `serialisation`: for two commuting steps any interleaving
equals the normal form determined by the two counts; the word's sequence is
discarded with a proof. `:111` `interleavings-agree`. `:141`
`suc-double-not-commuting`, `:153` `order-survives`: where they do not commute,
equal counts give different results, and the sequence is part of the answer.

**Reading for `hyper`.** The schedule check is `interleavings-agree` measured:
two independent demands in either order give the same value and count. The two
sides of an identity do not commute (a dead side ends the other), so their order
is data and the term's order is kept. Measured this session: forcing the sides
in the other order changes the count; that is `order-survives`, not a defect
to hide, and not a place a coin may choose.

## 6. Cost: the ledger, the geodesic, and what cost cannot be

`research/sat_fibre/InteractionLedger.agda:13` `data Event`: HVM4's local rules,
`dupSupEqual`, `dupSupDifferent`, `dupLamUsed`, `dupLamErased`, `dupNode a`,
`appSup`, `appMatSup`, and the boolean short-circuits. `:20` `Charge`:
`interactions` and `heapWords`. `:30` `localCharge`; `:35` `dupNode a` is one
interaction and `2·a` words. **Copying a node under a duplicator is an event.**
`:74` `interactionTotal-is-length`. The closing comment: a theorem uses the
ledger after supplying the correspondence from its transitions to `Event`.

`research/sat_fibre/InteractionGeodesic.agda:14` `RandomDescent` with the
one-step `diamond`; `:27` `peel`: any available first interaction removes
exactly one unit from any terminating reduction to the same normal form; `:45`
`same-normalization-length`; `:53` `normalization-is-geodesic`. Nets have the
diamond because active pairs are disjoint.

`formal/cubical/theorems/grammar/Laghava_TheCostAndTheInverseCannotCoexistSoNoNontrivialGroupIsGradedAndTransportHasNoPrice.agda`:
an additive grading that detects the unit cannot exist on a nontrivial group,
so there is no cost function on transports; cost lives on the presentation,
where univalence cannot see it, and that is a theorem, not bookkeeping.

`research/PNP_GEODESIC_REDUCTION_20260916.md` D1: geodesic length on retained
executions is additive; the length of a minimised effect is subadditive; a run
and its reverse take time while their composed effect is the identity. D3: a
carrier equivalence supplies no equation between execution costs; cost transfers
only with a cost-preserving equivalence of costed realisations. A5: neither
`isProp E` nor the existence of a contraction supplies a time bound for
computing the centre. F1: the minimax cost of an adaptive test tree is a fibre
decomposition, `D(S) = min_q [c(q) + max_o D(S_{q,o})]`, "holds all
continuations at once".

`research/SAT_CUBICAL_GEODESIC_NOTES_20260916.md` §5: same cubical dependency,
identify and annihilate; distinct dependencies, cross and commute; an `r`-cube
has `2^r` vertices but **vertex cardinality is not execution cost**: the cube
is a compact product object, and exponential execution needs forced expansion
into inequivalent cells. §11: do not infer cost from fibre cardinality or from
dimension; distinguish reversible positive geodesic length from destruction.

**Reading for `hyper`.** The count is the ledger's; the receipts now carry
its names. The claim "the count is the geodesic" is the claim that the runtime
is a net: every rule at an active pair, no rule whose outcome depends on which
of two available pairs fires first. Independent demands are checked; the
identity's sides are the term's order. The presentation tree over independent
names is a compact cube, and a presentation that expands it (the printer
descending every side) is the presentation's demand, not the object's cost.

## 7. The chart move is the fibre law read at the output

The two charts of `sort` are §1's two readings of one Σ. `Σ B. B ≡ isort L`
binds the output: `singl (isort L)`, centre `(isort L , refl)`, cost the cost
of `isort`. `Σ B. (isort L ≡ isort B) × (sorted B ≡ True)` binds the input
through `isort`, cut down by `sorted`: contractible exactly when `isort` on
sorted lists is an equivalence onto its image. Both contractible, so the
equivalence between them is determined, and its `ua` transports the cheap
centre to the expensive chart's point by `uaβ`. `MAP.md` §0 item 3 says it:
meaning descends along the path, cost does not (Laghava); the minimum over
charts is the object's cost; the only lever is a proof.

Nothing here is written by a person. The equivalence is a declaration of a Σ
type whose components are Π, Σ and identities; the Σ splits into coordinates,
the identity is a unification cell, and the Π is inhabited at its argument's
constructors with the recursive call as the inductive hypothesis (`MAP.md`
§0.1, last sentence of the `sortCost` paragraph). `Anveshana` says why the cost
then drops: uniqueness is free, existence is the work, and existence in the
output-bound chart is `isort L` itself.

## 8. The kernel: proofs become moves, and the caller disposes

`formal/cubical/Kernel/RewriteCertificate.agda:8` `Tm`, `:14` `Step` including
`reverse` (a groupoid, not an order), `:23` `Derivation`, `:55`
`InductionCertificate` (base, and a step with the hypothesis only at the
predecessor), `:133` `induction-sound`: a certificate becomes a universally
quantified equation. `formal/cubical/Kernel/ControlledGrammar.agda:11`
`NativeOperation` with `Control` a field the caller supplies, `:27` `install`,
`:56` `advance = map execute`, `:59` `advance-preserves-branch-count`: no
dedupe, no sort, no quotient.

The four readings (descent note §4): the installed operation fires at exactly
one term (Vyapti); the derivation carries no meaning, so no semantic criterion
selects the short proof (Sesa); the counting semantics is a decategorification
and the dropped bit is a transposition (Ankapasa); every soundness field lands
in a proposition so the whole derivation type is one fibre (Asesa). Descent
note §7: ranking is the caller's act; the machine presents, the caller
disposes; the system is interactive by theorem.

`formal/cubical/kernel-flat/TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection.agda:126`
`record Encounter`, `:138` `τ`, `:164` `interact`: two locals in, two
locals and one trace out, no third party. §2: the two results need not agree
and nothing is pending. §7: two encounters at disjoint sites in the two orders
have the same endpoints, the same cost, provably different traces; §8: no
order-blind scalar has a section. `MAP.md` §0.2 is right that the kernel's
first-order frame is not this language's design; what carries over is not its
`Tm` but its shape: the trace is the object, a scalar is a projection of it, a
certified derivation is an operation.

## 9. The machine's own name

`collab/bend2-interactive-cubical/PUSC.md`: a Parallel Univalent Superposition
Computer is "a universal typed reduction machine for computational homotopy
type theory, in which higher-order sharing, correlated branching, executable
equivalence, and independent reduction coexist within the same computational
objects." Labels are operational provenance: same label, correlated pairs;
different labels, independent dimensions. The schematic judgment has four
contexts, dimensions, faces, correlated choices, variables, and the machine's
content is their compatibility equations.

`collab/bend2-interactive-cubical/CONVERGENCE.md` Part IV: `comp` reducing
fully is the contractible fibre; sticking is the non-contractible one; DUP-SUP
annihilating on equal labels is the former, commuting on different labels is
the latter, and the allocation is the leftover made physical. Part III.4: cost
is supported exactly on the non-invertible part. Part IV.4: an optimal,
groupoid-shaped reducer is the substrate the mathematics specifies; Agda paid
the execution tax (13 GB on the census).

`collab/bend2-interactive-cubical/LANGUAGE_LEVEL_CONDUCTIVE_FIBRE_INTEGRATION.md`
§4: **a proposition already supplies the observation**: for `P : X → Bool` the
fibres over `True` and `False` are the classification, no separate "solve"
opcode. §8: do not wrap every application; the semantic unit is the whole plus
an observation of it. §30: the unresolved domain must be represented by the
program (a superposed cube, a Σ, an inductive), never manufactured by
enumeration. §37: two closures must meet in ordinary execution, the lossless
observational one and the derivational one (transformations derived about the
object becoming structure of the object). §41: the final state of the Bend
side is the typed point `Σ A. A` at the root, every definition emitted with
its type, nothing generated beside it; the handwritten fibre prelude and the
compile-time derivation companions were removed as second copies.

`LIFECYCLE.rst`: the full name is Lossless Interdependent Type Theory; the
order is a productive interactive process containing finite demanded histories
whose constructed transformations return as operations; the fibre law is the
conservation account of presentation.

## 10. What `hyper/` is, in these terms

`hyper` is the substrate of §9 without Bend2 in the loop: cells over bound
dimension names, faces, the interval, transp, hcomp, Glue and ua, inductive and
higher inductive types by schema, fixed points, superpositions at bound names,
free ports, a checker on the same loop, the ledger. Its declaration mechanism
(`MAP.md` §0.1) is §1 run forward: an unknown is a coordinate (a point of a
cell), a match on a coordinate is a superposition over its constructors (the
cube's dimension made explicit), a path at a data type with coordinates decides
by cutting the cells where the sides disagree (unification), the survivors are
the fibre (§2), the census over inputs is §3, the trace is §2's trace, and the
count is §6's ledger. The step relation must be a net (§6), the presentation a
compact cube expanded only on demand (§6), the chart move §7.

What was in `hyper/cell.c` and was not this, now deleted: a scheduler of
kinds and rounds deciding when a residual identity may ask a port; a
derived-coordinate shortcut that never split a field; tables of the
constructors of Unit, Bool, Nat and List; a schedule knob. §5 says order is
either a certificate or data, never a policy, and §9 says the constructors of a
type are its declaration, so `prelude.hyper` declares the four and the runtime
and checker read them there. What remains is one rule at a match: the
scrutinee is inspected, not forced; a coordinate's head is the superposition of
its type's constructors; a computation's head is bound at its output, the
constructors superposed with the identity retained (the fibre law read at the
output, §1), and one point splits once. Identity sides are inspected and forced
only by what faces them.

What `hyper` has never done: resolve a Π-typed declaration along a free
argument. `sort L` for free `L`, `sortCost n` for free `n`, the equivalence
between the two charts of `sort` declared with no body. The mechanism is
`pi_apply` (the codomain's coordinate at the argument, the inductive hypothesis
at a field), the split of a port along its constructors, and unification; all
three exist. Whether they resolve those declarations once the scheduler is gone
is the test of whether the core is the construction.

## 11. What Bend and HVM are here

Secondary. HVM4 was dropped; Bend2 has half the shape and the rest is fought.
The ledger's alphabet in §6 is kept because it is the event alphabet of the
fibre routing (same label annihilates, different labels commute, a node under a
duplicator is copied), which `research/sat_fibre/InteractionLedger.agda:13` `data Event`
states as mathematics and CONVERGENCE Part IV reads as the contractible and the
non-contractible fibre, not because HVM is the target. The Bend ports under
`collab/bend2-interactive-cubical/port/` are a syntax layer at most; nothing in
them is a specification the runtime owes. Compatibility with Bend syntax or
SupGen as a frontend is worth attention only where it is instrumental.

*(Reading continues in the mathematics: `AdiBija`, `Universal`, `EqualitySplit`,
the Jiva bodies, the Uniqueness body, the Kernel §4 module bodies, Encounter
§4-9, MyhillNerode, Samvada, TransportDivScale, AnswerIsProjectionAtOutputSize.)*
