# SAT read through the existing universal constructions

This corrects the theoretical framing of REPORT.md and the accompanying conversation. The runtime measurements remain measurements of the emitted programs. They were not a sufficient reading of the project's existing mathematics. In particular, provenance/count/support compatibility, uniqueness of lossless completion, composition of fibre pushforwards, and the universal future-behavior quotient are already present. Calling these possible extensions was wrong.

The statements below distinguish existing terms from mathematical specializations worked out here. This document is not a new Agda verification receipt.

## The object is classified before a particular reading is chosen

[Fibre.Visvarupa_EveryFamilyIsAPullbackOfTheUniverseAndTheTowerFlattensToOne](../../fibre/src/Fibre/Visvarupa_EveryFamilyIsAPullbackOfTheUniverseAndTheTowerFlattensToOne.agda) defines

    Universal â“ = Î (X : Type â“), X
    Ï = fst

and proves `fibreOfÏ`, the canonical pullback comparison, `classifier`, `invisibleâ‰contractible`, and `flatten-correct`. A family of SAT witnesses, a family of weighted realizations, and a family of continuations are already families classified by this construction. Introducing another receiver does not enlarge the universal object. It supplies a particular classifying map and a reading.

The base matters. `invisibleâ‰contractible` is about the specified projection, not the existence of some equivalence of total spaces. The module exhibits a total space equivalent to Bool whose designated projection has an empty fibre and a two-point fibre. An arbitrary recoding of the total set is insufficient to justify a claim about that observation.

[Fibre.Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase](../../fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda) gives the next fact: for any conservative factorization, `fibre-of-run` identifies its retained family with the fibres of its actual visible map. [Uniqueness_LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleTypeAndTheMachinesIsUnique](../../formal/cubical/theorems/residue/Uniqueness_LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleTypeAndTheMachinesIsUnique.agda) strengthens this to contractibility of the entire type of lossless completions over a fixed map. Its proof passes through sections over the map, fibrewise equivalences, and univalence. Thus the residue is forced up to equivalence, rather than selected as arbitrary extra metadata.

This does not mean the fibre itself is contractible. The *space of lawful completions* is contractible even when an individual observation fibre contains many distinguishable sources. Confusing these two contractions would erase the theorem's content.

## SAT as compatibility, followed by an indexed pushforward

Here is the useful specialization, more informative than simply naming the true fibre. For a set of Boolean variables V and constraints with scopes S_j, write

    A_S = S â’ Bool
    R_j : A_(S_j) â’ Type
    Solutions = Î (x : A_V), Î  j, R_j(x restricted to S_j).

For ordinary SAT, choose R_j to be the proposition that the clause predicate evaluates to true. It is not the coproduct of all literal positions that happen to satisfy the clause. Those carry different multiplicities.

For two constraint subsystems, their local solution objects combine by agreement on their shared boundary. This is the repository's pullback construction:

    Î (a : LocalLeft), Î (b : LocalRight), restrictionLeft(a) = restrictionRight(b).

`InterdependenceIsThePullbackCouplingNeitherPartDeterminesTheWhole` explicitly retains that coupling equation. It reduces to an unrestricted product under contractibility of every coupling fibre. Shared variables cannot be silently treated as independent.

To eliminate internal coordinates I while retaining boundary B, form

    F_B(b) = Î (i : A_I), Constraint(b,i).

This is a family of complete internal realizations indexed by the surviving boundary assignment. Further elimination is already governed by [AgrayogaSanghata_ThePushforwardComposesOnTheTypeCarrierAndFiniteFubiniIsItsShadow](../../formal/cubical/theorems/walks/AgrayogaSanghata_ThePushforwardComposesOnTheTypeCarrierAndFiniteFubiniIsItsShadow.agda):

    (g âˆ˜ f)_! F â‰ g_! (f_! F).

The underlying `SankramanaSesa` equivalence sends

    (a,p) â¦ ((f a,p),(a,refl))

and reconstructs by composition of the equality witnesses. The source coordinate is retained definitionally. The pushforward theorem then uses dependent-sum associativity. This is an exact equivalence of realization types; no enumeration or scalar fold is required to state it.

Different elimination orders therefore reorganize the same indexed content. Their intermediate representations can have different costs. The equivalence explains correctness of reorganization, while the derivation receiver reads the work of carrying it out.

## Existing receivers already connect provenance, counts, and support

[Anvaya_TheProvenanceSemiringTheBooleanHomomorphismAndTheQueryLanguageAreBuiltAndTheHierarchyIsStrict](../../formal/cubical/theorems/logic/Anvaya_TheProvenanceSemiringTheBooleanHomomorphismAndTheQueryLanguageAreBuiltAndTheHierarchyIsStrict.agda) supplies `CommSemiring`, `Hom`, provenance syntax, `hom-eval`, a query language with selection/join/projection, and `query-hom`.

For a semiring homomorphism h it proves, in its actual query language,

    h(run_R(E,q,t)) = run_S(h âˆ˜ E,q,t).

It constructs positivity â•â’Bool as a homomorphism, and proves both strict collapses: provenance to multiplicity, and multiplicity to existence. `no-bag-from-set` and `no-how-from-bag` reject arbitrary reconstruction functions with the stated global recovery laws.

[ChhayaRig_TheBooleanShadowOfCountingProvenanceIsAHomomorphismWithNoHomomorphicSection](../../formal/cubical/theorems/cost/ChhayaRig_TheBooleanShadowOfCountingProvenanceIsAHomomorphismWithNoHomomorphicSection.agda) proves a different, sharper algebraic obstruction: no additive section of positivity exists. Idempotence of Boolean disjunction would force the chosen positive count to equal twice itself, hence zero. An ordinary set-theoretic section does exist (falseâ¦0, trueâ¦1); `research/BooleanProvenanceFibreConnections.agda` explicitly exhibits it and computes the shadow's fibres. These two no-recovery statements must not be conflated.

For SAT, a duplicate-free complete assignment catalogue, weighted by 1 for a satisfying assignment and 0 otherwise, gives the actual model count. Its positivity is the Boolean existence reading by the installed homomorphism theorem. A witness-labelled sum retains which assignments contributed.

A raw proof-derivation count can differ. For xâˆ¨x, the assignment x=true is one model but supports two literal-choice derivations. Forgetting that distinction before choosing a counting interface produces the wrong count. Likewise, knowing that each of two relations is nonempty does not establish that their pullback is nonempty. The shared-boundary indices must survive until the compatibility operation has occurred.

This is the exact place where the theoretical-CS literature on algebraic model counting applies. It states circuit conditions and algebraic conditions under which a structural fold computes the model-based aggregate. Decomposability, disjoint alternatives, and scope accounting govern whether multiplying/summing local readings is valid; idempotence permits some conditions to be relaxed. These are conditions on a representation and receiver, not additions to the universal family. See [Kimmig, Van den Broeck, and De Raedt, Algebraic Model Counting](https://escholarship.org/content/qt2w76d6hr/qt2w76d6hr_noSplash_cf141889983a8b7a9a0cec7d0eca4253.pdf), especially Â§Â§3.1â“3.3.

## Acyclic circuit auxiliaries are a contractible-fibre instance

This is a mathematical specialization derived here, not a newly checked module. For a finite acyclic Boolean circuit, introduce one auxiliary Boolean for each gate and require it to equal that gate's Boolean function of its inputs. For every input assignment, topological evaluation supplies an auxiliary assignment; induction over the gates proves uniqueness. Because the equality evidence is propositional, the family of gate-consistent auxiliary assignments is contractible over each input.

The existing theorem for a projection with contractible fibres therefore applies: forgetting these auxiliaries is an equivalence from the gate-consistent graph to the input assignment type. Restricting both sides to output=true preserves the corresponding satisfying-assignment equivalence. This explains why full functional gate definitions preserve model multiplicity as well as satisfiability.

A transformation that merely preserves nonemptiness need not preserve that equivalence: extra unconstrained auxiliary coordinates produce additional inhabitants. The exact distinction is already expressed by the projection and its fibres. For bounded fan-in gates, their equations also have bounded-size CNF encodings, so the gate presentation can be built with linear many constraints. That construction-size argument is separate from the fibre equivalence and follows from the local gate encoding.

## Future equivalence is already a universal machine construction

`MyhillNerodeMinimalMachine` is substantially stronger than the small injectivity lemma added in SATFibre.agda. It supplies:

- equality under every finite action word;
- the greatest behavioral congruence;
- the quotient with descended steps and observations;
- preservation of every finite behavior;
- an isomorphism between quotient paths and future-equivalence evidence;
- full abstraction and a unique mediating map from every behavioral-congruence quotient;
- refinement and pairing laws for observation interfaces.

SAT residual functions are one instance. Changing the observation from existence to counts, witnesses, or provenance changes which distinctions its continuation must preserve. The pairing law identifies the joint congruence with the intersection of the two separate congruences. The theorem already describes how demanding more observations refines the minimum faithful representation.

The weighted counterpart is present in `DSOContinuationFullAbstract`. For extended-natural cost relations on its two-point interface, Dirac continuations recover each relation entry. Equality of Bellman transformers on every continuation therefore implies equality of the relations. It also exhibits a local minimizer that differs from the continuation-adjusted minimizer. `research/BellmanFibreConnections.agda` identifies the argmin object with the relevant evaluation fibre and proves that equal-value ties can retain different witnesses.

For TSP, the visited-set/endpoint interface is justified by which continuations remain admissible. Pruning by a local scalar without the interface is precisely the kind of premature collapse the existing example refutes. The earlier work should have started from these terms.

## Cost is another structural reading, with different laws

[AdiBija_TheKernelIsInitialEveryReadingIsItsUniqueFoldSoAllPathsThroughASystemAreEnumeratedByOneRecursor](../../formal/cubical/Kernel/AdiBija_TheKernelIsInitialEveryReadingIsItsUniqueFoldSoAllPathsThroughASystemAreEnumeratedByOneRecursor.agda) proves existence and uniqueness of the fold into a receiver specifying an identity reading and an action for each generating step. Soundness, length, and signed integrals are instances. `Vivarana` bundles three such readings and separates the existing two-step and four-step coterminal histories by length while identifying their meanings.

[Laghava_TheCostAndTheInverseCannotCoexistSoNoNontrivialGroupIsGradedAndTransportHasNoPrice](../../formal/cubical/theorems/grammar/Laghava_TheCostAndTheInverseCannotCoexistSoNoNontrivialGroupIsGradedAndTransportHasNoPrice.agda) explains why these receivers cannot all descend to the same quotient. A natural-valued additive grading on a group must vanish:

    c(g)+c(gâ»Â)=c(1)=0.

With unit detection, the group would have to be trivial. The module also proves a no-factorization result for a source grading through a suitable group image. Thus execution history and its positive additive grade belong on the derivation side of the interface.

The additivity hypothesis is essential. A shortest-word length on a group is generally subadditive, not additive, and is not prohibited by this argument. A reversible program can have positive execution cost; its history followed by an inverse history is still a positive-length history even when the composite semantic operation is the identity. This is the corpus's distinction between histories and their transport reading, not an external objection to it.

Consequently the right way to connect interaction profiles is to provide the runtime receiver and its generating-step actions. The finite counters then read that execution object. My earlier account concentrated on a new random-descent theorem without adequately relating it to the installed initiality and cost results.

The classical optimal-reduction literature is directly relevant here. Asperti and Mairson prove that L©vy-family parallel beta-step counts can hide nonelementary implementation work. This does not price a particular HVM program; it requires us to identify which reduction grade we mean and count sharing work rather than equating a shared beta family with a unit machine operation. See [Parallel beta reduction is not elementary recursive](https://www.cs.unibo.it/~asperti/PAPERS/p303-asperti.pdf).

## The physics example already supplies a separating continuation

In `photon.agda`, the two Gaussian states (1,1) and (1,âˆ’1) have the same component square weights. Applying `Had.H` yields port weights (4,0) and (0,4). These outputs distinguish the projective states, and `relative-phase-survives-projectivization` proves their inequality.

Global phase, by contrast, is shown to commute with the mixer and preserve port weights, which licenses the corresponding quotient reading. The calculation is exact. It is an instance of the same requirement that a quotient respect the observations and continuations one intends to retain. This was a much more direct connection to SAT continuation equivalence than the generic energy analogy I gave.

Nor is every numerical reading a semiring homomorphism. Squared magnitude fails additivity under interference: |1+(âˆ’1)|Â²=0 while |1|Â²+|âˆ’1|Â²=2. The counting-to-support homomorphism theorem therefore does not authorize moving an intensity observation across amplitude addition. The complete object retains the information needed by the later mixer.

`PramanaPatra` makes another instance explicit: block elimination carries an effective operator, a forcing map, state reconstruction, and source correction. Its equations prove reconstruction for every source under the hidden-block inverse hypotheses. Merely retaining the reduced operator would omit part of the certificate. This is the same boundary discipline at a linear-operator interface; identifying it with Boolean elimination would require the actual algebraic interpretation.

## The whole structured dynamics travels, not just the state carrier

`photon.StructuredTransport.transport-law` quantifies over a property of the entire `FieldDynamics` package. Its path moves the operators, their laws, the solution with equation witnesses, and the continuing dynamics together. This corrects another possible understatement: transport is not restricted to preserving a final scalar answer. Once an operational semantics and its cost reading are included in a corresponding structured package, dependent properties of that package can be transported too. What must be identified is that whole package; using only an equivalence of bare state types while independently selecting target operators is a different construction.

The later completion modules preserve the same discipline. `Tower.MSDLimit` includes the equations that make successive finite views agree. `finite-towerâ‰orbit` reconstructs a complete continuing object from that coherent tower. It does not discard the coherence field. `CauchyNames` separately stores approximation moduli and tail evidence; `CauchyMap` composes moduli, and `CauchySquare` preserves commuting operator equations at the represented-point level. `GraphNormOperator` controls both a field and its generator image so the completed operator has the stated domain. Those hypotheses are computational data inside the object.

For an ongoing SAT constraint process, this distinguishes a coherent family of finite realizations from unrelated witnesses that merely satisfy separate fragments. The existing `LawfulContinuationCore.flip-has-no-coherent-section` proves the distinction constructively: its local Boolean fibres are inhabited, yet the loop transport prevents a coherent global choice. An elementary Boolean instance is the three equations x=y, y=z, z=not x: each pairwise relation is inhabited, but composition would force x=not x. The compatibility data is where the contradiction resides. This is a concrete connection between SAT, gluing, and holonomy, rather than a claim that local satisfiability automatically composes.

## Which established CS results should govern the next SAT implementation

The following connections concern particular presentations of the object, and should be used before generating another benchmark suite.

1. **Variable elimination and induced width.** Once constraints are combined along a boundary and internal variables eliminated, the largest surviving scope bounds a table representation's size. A Boolean boundary with w coordinates has 2^w entries. Dechter's bucket-elimination framework gives the corresponding structural complexity analysis for constraint, Boolean, probabilistic, and optimization tasks. It is directly pertinent to the fibre-pushforward organization. See [Bucket elimination](https://ics.uci.edu/~csp/r48b.pdf).
2. **Knowledge compilation.** Decomposability, determinism, and ordering support different queries and different succinctness guarantees. A demand-complete representation should be selected against the operations its continuation promises. Polynomial query time is measured against the compiled representation, whose size and construction also matter. See [Darwiche and Marquis](https://arxiv.org/pdf/1106.1819).
3. **Constraint-language classification.** Schaefer's dichotomy classifies fixed finite Boolean constraint languages: the six tractable conditions include 0-validity, 1-validity, Horn, dual-Horn, affine, and bijunctive structure; otherwise the associated satisfiability problem is NP-complete. This distinguishes which algebraic structure an emitted relation should expose. It is not a classification by variable count or by the number of satisfying assignments. See [Schaefer's original paper](https://www.ccs.neu.edu/home/lieber/courses/csg260/f06/materials/papers/max-sat/p216-schaefer.pdf).
4. **Proof complexity.** Resolution width constrains resolution refutation size. Applying that theorem to an interaction-net run requires a proof-system correspondence with controlled overhead; the mere presence of a pigeonhole instance does not make its HVM profile a resolution proof. See [Ben-Sasson and Wigderson](https://people.inf.ethz.ch/emo/SatSem05/Papers/BensassonWidgerson01.pdf).

These connections do not replace the universal calculus. They identify existing mathematical results about particular receivers, interfaces, and finite presentations within it.

## The lossless universal machine, read at its declared input

The `Vishvayantra â’ Nasha â’ Uniqueness â’ VerifyIsDecide â’ PNeqNPIsNotUniversal â’ PeqNPHolds` dependency chain is now part of this reading. `decide` takes a Machine and returns `(uStep mc, mc, refl)` through the lossless equivalence; `verify` projects its retained predecessor. The two directions and self-certification are exact. The completion is unique in the stated type.

`Gap` is explicitly the existence of two distinct configurations with equal images. The exhibited erasing transition has such a collision, and the completed transition cannot. These are the exact statements composed by the capstone. `VerifyIsDecide` itself explicitly distinguishes its result from a step-count theorem in an external succinct measure.

For SAT application, the important task is to specify the object supplied at the interface: formula syntax, an assignment plus its evaluation, a realization family, a compiled relation, or a carried computation answering a demand. The lossless theorem applies to the declared map with no need to invent a SAT-specific completion. The computational statement must retain that declared input and observation when relating it to a conventional complexity problem.
