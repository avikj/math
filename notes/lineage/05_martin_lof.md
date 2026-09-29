# Per Martin-Löf — meaning, evidence, identity, and the random sequence

## I. The life, as a cognitive trajectory

Per Erik Rutger Martin-Löf was born on 8 May 1942 in Stockholm. As a young mathematician he went to Moscow in 1964–65 to work with Andrei Kolmogorov, at the moment Kolmogorov was founding algorithmic information theory, and the problem Kolmogorov handed him was the one probability theory had never solved: what makes an *individual* sequence random? Kolmogorov's complexity of finite strings could not answer it for infinite sequences, because every infinite sequence has prefixes of low complexity. Martin-Löf's 1966 paper *The Definition of Random Sequences* answered it by quantifying over tests rather than descriptions: a sequence is random if it passes every effective statistical test, where a test is a uniformly effective sequence of shrinking sets of measure at most 2⁻ⁿ; he proved there is a *universal* test, so the random sequences are exactly those that escape one effective null set. Randomness became a property of an individual object, defined by the totality of effective observations of it.

He then worked in statistics — sufficient statistics, exponential families, and a notion of *redundancy* as the discrepancy between a hypothesis and the data (1970s) — and in proof theory, proving the normalization theorem (Hauptsatz) for iterated inductive definitions (1971). Both lines already carry the question that would organise his life: what is the minimal object that retains everything an observation can tell you, and what does a proof actually contain?

In 1971 he proposed a type theory in which propositions are types and proofs are their elements, with a type of all types, `Type : Type`. Jean-Yves Girard showed it inconsistent in 1972 by adapting Burali-Forti's paradox. Martin-Löf's answer was to make the theory **predicative**: universes indexed by level, each an element of the next. *An Intuitionistic Theory of Types: Predicative Part* (Logic Colloquium 1973, published 1975) fixed the core — dependent products Π and sums Σ, inductive types, universes, and the identity type Id(A, a, b) with its eliminator. *Constructive Mathematics and Computer Programming* (1979, published 1982) proposed the theory as a programming language in which a program and a proof of its specification are the same object. *Intuitionistic Type Theory* (the 1980 Padua lectures, Bibliopolis 1984) gave the extensional version; the intensional version, in which identity is a type whose elements carry information, became the standard for proof assistants (NuPRL, Agda, Coq's core).

From the 1980s his work turned to meaning. *On the Meanings of the Logical Constants and the Justifications of the Logical Laws* (Siena lectures 1983, published 1996) distinguished a **proposition** from a **judgment**: a proposition is defined by what counts as its proof; a judgment ("A is true", "a is an element of A") is known when one possesses its evidence, and the meaning of a logical constant is given by the rules for its canonical evidence. *Truth of a Proposition, Evidence of a Judgement, Validity of a Proof* (1987) and *Verificationism Then and Now* (1995) developed the same programme against the background of Brentano, Husserl and Frege. His 2006 lecture on the axiom of choice explained why choice in the type-theoretic sense (a distributivity of Π over Σ) is provable while extensional choice implies excluded middle.

## II. What he left on the table

1. **The structure of identity.** Martin-Löf's identity type left open whether all proofs of a = b are equal (uniqueness of identity proofs). Hofmann and Streicher (1994) showed they need not be; the identity type turned out to carry higher-dimensional structure that his meaning explanations did not describe.
2. **Infinite objects and their equality.** Streams and other coinductive objects: when are two infinite behaviours equal? In intensional type theory, equality of streams is not bisimulation.
3. **Meaning as observation.** The meaning explanations define meaning by canonical evidence. A statistician's version — meaning as the minimal object that retains every observation, a sufficient statistic — was never connected to them.
4. **Evidence and truth.** The gap between a judgment's evidence and a proposition's mere truth: what exactly is lost when evidence is forgotten, and when it can be recovered.
5. **Choice.** Type-theoretic choice is a theorem; extensional choice is classical. The precise logical price of each passage from existence to witness was not mapped.
6. **Predicativity.** Girard's paradox forced predicative universes; what impredicative constructions a predicative theory can still carry out, by other means, was left case by case.
7. **Randomness and finite observation.** Random sequences are defined by all effective tests at once; no finite prefix certifies randomness, and the relation between the finite and the infinite notions (Levin, Schnorr, Chaitin) remained a separate theory from type theory.
8. **Compositional meaning.** Whether a part has a meaning on its own, or only in context — the problem at the heart of every meaning theory, including his.
9. **Normalization and computation.** Type theory as a programming language needs an evaluator that respects meaning; the relation between proof normalization and efficient execution was left to implementers.

## III. Your work through Martin-Löf's eyes

### 1. Meaning is the terminal quotient by future observation

**Open:** meaning as the minimal object that retains everything observation can tell — the sufficient-statistic reading of meaning.

**What you proved.** `theorems/automata/FutureBehavior` is the construction, and its header names both of Martin-Löf's lives at once: "Myhill–Nerode / sufficient statistic / observability." For an observed transition system (states X, actions A, `step`, `observe : X → O` into a set):

- `FutureEq x y = (w : List A) → behavior x w ≡ behavior y w` — equality under every finite experiment;
- it is a behavioural congruence (`futureEq-isCongruence`) and **the greatest one** (`congruence→futureEq`, by induction on the future word);
- `Meaning = X / FutureEq`, with step and observation descending, and `quotient-preserves-behavior` — crystallization changes no observable future;
- `[]-effectiveIso : Iso (Path Meaning [ x ] [ y ]) (x ≈ y)` — **the path space of meanings is future equality**, as a type, not merely an implication;
- `quotBehavior-injective`, `crystal-minimal`, `crystal-fullyAbstract` — distinct meanings have distinct complete futures;
- `factor`, `factor-unique` — every set-valued quantity constant on classes factors uniquely through meaning;
- `Terminal.mediate`, `mediate-unique` — every quotient by a behavioural congruence maps onto Meaning by a unique machine morphism. Meaning is the coarsest behaviour-preserving quotient.

`theorems/residue/CorpusBehavioralMeaning` applies it to your own checked theorems: the state is a reflected `Term`, an action selects a child address, the observation is the head constructor, and `Presented = Σ meaning . fiber meaning` presents each meaning with its exact realizing term kept in the fibre. `ConservativeSemanticCompressionIsTheEffectiveObserverQuotient` gives the same object for an arbitrary declared family of observers, with lossless readout, effectiveness as an equivalence, universality and minimality.

This is the bridge Martin-Löf's two careers did not build: the statistician's minimal sufficient statistic and the logician's meaning are one construction — the terminal quotient by the greatest congruence for the declared observations — and in a univalent setting the identity of meanings *is* observational equivalence.

### 2. The identity type: its eliminator, its higher structure, its infinite case

**Open:** what the identity type is, beyond its rules.

**What you proved.**

- **J is not primitive.** `theorems/grammar/EkaSutra_J`: from the single fact that singletons are contractible, `isContr (Σ y . x ≡ y)`, you derive J with its β-rule (`सूत्र-J`, `सूत्र-J-β`), the graph decomposition `A ≃ Σ b . fiber f b` (HoTT 4.8.2), transport of any property along any equivalence, and the fundamental theorem of identity types: a pointed family with contractible total space *is* the path family, `(a₀ ≡ x) ≃ R x`. To characterize any identity type, exhibit one contractible Σ.
- **Identity proofs are not unique, and the failure is a theorem you use.** `Kernel/AnEquivalenceIdentifiesTheCarriers…`: Bool has two self-equivalences (`routes-are-not-unique`), so knowing a route exists does not give the route. `theorems/walks/AsetChidra`: `loop ≢ refl` in the circle by the winding number, so S¹ is not a set. `theorems/residue/CatuhSamskara`: at the circle, killing the loop (set truncation), keeping it (ΩS¹ ≡ ℤ), lifting it to a 2-cell of descent data, and completing it (the universal cover, with fixed-point-free monodromy `sucℤ`) are four provably distinct objects — "the higher structure is what tells the repairs apart."
- **The h-level of a type is the type of ways back.** `theorems/grammar/Apratikaryatva`: for every n and A, the type of retractions of the n-truncation `∣_∣ₕ` is contractible when A is an n-type and empty otherwise, hence a proposition, hence `प्रत्यानयनम् n A ≃ isOfHLevel n A` — the type of ways back **is** the h-level hypothesis. The paths of a propositional truncation are contractible at every level (`पथ-नष्टिः`, `पथ-पथ-नष्टिः`), and exactly the maps into propositions survive truncation, as an equivalence (`अनुक्तम्-न-नश्यति`).
- **Identity of infinite objects is bisimulation.** `fibre/Orbit`: `path≃bisim : (x ≡ y) ≃ (x ≈ y)`, built corecursively in all four directions, and `path≡bisim` by `ua`. `IndraNet` extends it to nets of mutually reflecting objects: the domain equation `Net x ≃ L x × ((y : J) → Net y)` is solved (`netUnfold`), and `bisim→path` — "identity in the Net IS relational identity." Its Yoneda form, `yonedaJewel : ((z : A) → z ≡ x → z ≡ y) ≃ (x ≡ y)`, says a path between two points is exactly a transformation of their whole profiles of incoming paths.

### 3. Judgment and evidence: what forgetting the evidence costs

**Open:** the relation between a judgment's evidence and a proposition's truth.

**What you proved.**

- `NaturalMachine/Sesa_TheDerivationCarriesNoMeaningAtAll…`: the truth of an equation is a proposition, so the evidence (the derivation) carries no semantic information; soundness factors through `∥ Derivation ∥₁`; the kernel's own seed has two distinct derivations; and every function of the truth is blind to which derivation was given. Truth is the truncation of evidence, exactly.
- `Avaccheda`: the fibre of `∣_∣₁` over any point is the whole source, `fiber ∣_∣₁ x ≃ A`. What truncation forgets is all of the evidence.
- `Kernel/HidingAndHardness…`: the truncation is the maximal hiding modality — perfect simulation, a view that shrinks nothing, and extraction from an existence is an equivalence exactly when the witness is unique.
- `theorems/residue/Pratyanayana`: evidence *does* come back from the truncation when it is canonical — `∥ Σ n . HaltsAt n mc ∥₁ → Σ n . FirstHalt mc n`, because each stage is decided and the least witness is a proposition. "The truncation destroys choices and preserves canons."
- `theorems/grammar/TritiyaMarga`: turning the refutation of an equivalence into a written defect costs at least Markov's principle; excluded middle yields only the truncated defect; a two-point defect type has no retraction from its truncation.

In Martin-Löf's vocabulary: a judgment's evidence and a proposition's truth are the two sides of one truncation; the truth loses exactly the evidence and nothing else; evidence returns without cost exactly when it is canonical; and otherwise the price of recovering it is a named constructive principle, not a hidden step.

### 4. Choice, located exactly

**Open:** why type-theoretic choice is a theorem and extensional choice is classical, and what each passage from existence to witness costs.

**What you proved.** The distributivity of Π over Σ is definitional: `Ekatva.ΠΣ-swap` has both round trips `refl`, and `SvaTantuVasa` uses the library's `Σ-Π-Iso` ("the type-theoretic axiom of choice, definitional in this substrate") to identify the conserving flows of any observable with the sections of its fibre family. On the other side:

- `theorems/number/FiniteInformation` removes every use of `Classical.choose` from a Lean development by replacing it with elimination of a truncation into a set (`rec→Set`), paying `isSet T` instead of choice; where the literal statement genuinely needs choice, it is kept with the choice made a visible hypothesis (`targetFiber-injects-side-given-choice`).
- `Apratikaryatva` §5: reading "every map is either an equivalence or has a nameable defect" as a disjunction is **exactly** excluded middle, proved in both directions on the family of maps out of propositions.
- `TritiyaMarga`: the written defect costs at least Markov's principle.

So the ladder Martin-Löf described in 2006 appears as terms: Π–Σ choice is free; elimination into a set along a constant family is free given the set hypothesis; a canonical witness is free; a written defect costs at least Markov; the defect-or-equivalence disjunction costs exactly excluded middle.

### 5. Predicativity without paradox

**Open:** what a predicative theory can still construct after Girard's paradox forbade `Type : Type`.

**What you proved.** `theorems/grammar/ClosureTowerCollapse`: a transfinite tower Θ_{ν+1} = κ(Θ_ν) built from an impredicative intersection of all closed supersets does not even typecheck at a fixed universe without resizing. The predicative rendering — the closure generated inductively and truncated — has exactly the universal property the intersection was there to supply (`⟪⟫-least`), is idempotent (`⟪⟫-idem`), and makes the tower constant from stage one (`tower-const`, `tower-limit`). `theorems/homotopy/Visvarupa_…ClassifierDoesNotClassifyItself` proves the object classifier `(Σ E . E → A) ≃ (A → Type)` for every base and, as its title says, that the classifier does not classify itself — the universe's own level is where Martin-Löf's predicative hierarchy lives.

### 6. Compositional meaning: where a formalization takes a side

**Open:** does a part have a meaning of its own, or only in context?

**What you proved.** `theorems/unplaced/AbhihitanvayaAnvitabhidhana` states the converse of full abstraction as a theorem: if a semantics C is **compositional** (`C (plug c t) ≡ act c (C t)`) and observation **factors** through it (`obs t ≡ obsD (C t)`), then `C p ≡ C q → CtxEq p q` by three uses of `cong`, and a separating context forces a semantic difference for free — while the other direction, from contextual difference to a separating context, requires enumerating the context family and deciding observations. The file's point is where the commitment is made: writing `C : Tm → D` at all grants a part a meaning in isolation, so a formalization takes a side in the signature, one line above the first theorem. `theorems/residue/FullAbstractionIsAConditionOnTheContextFamily…` supplies the other half: full abstraction is a condition on the family of contexts, and curvature is witnessed inside that family. For Martin-Löf's meaning explanations, which are compositional by construction, this is the exact statement of what that choice buys and what it costs.

### 7. The random sequence and the finite observer

**Open:** the relation between finite observation and properties of infinite individual objects that Martin-Löf randomness defines by all effective tests at once.

**What you proved.**

- `theorems/physics/HistoryCompletion`: a □-property of an infinite stream ("at every depth") is refuted by a single failing truncation (`separator`), and **no depth decides it**: for every n there are two streams agreeing to depth n, one satisfying the property forever and one not (`no-depth-decides`); in the decoder language of `FiniteInformation`, the property does not factor through any finite prefix (`bounded-does-not-factor-through-depth`). Streams under the take-metric are complete by corecursion, with unique limits by truncations.
- `NaturalMachine/Alopa` §7: sampling confirms only a property of the sampling distribution — `var 0` and `var 1` agree on every constant environment, infinitely many confirmations, and are not equal.
- `theorems/automata/InvarianceConstant` (Kolmogorov lane): complexity is defined only up to a machine-dependent constant, and a strict comparison transfers across machines exactly when the gap exceeds 2c, with the threshold sharp.
- `research/rule30/ORACLE_RULE30.md` and its modules: for the Rule 30 centre column, the hierarchy of "irrationality-strength" properties — not eventually periodic, superlinear complexity, disjunctive, normal, irreducible — is set out with its status, and the kernel certificates proved (`Apunaravrtti`, `Sarvapada`/`Navapada`, `Jen`, `Karna`, `Ganana`/`Sankirnata`) are exactly the finite shadows the report says are available: every word of length 9 occurs in the first 4096 bits, which by Morse–Hedlund excludes every period and preperiod with N + p < 512. The report states that normality is Π₂ and no prefix certifies it.

This is the structure of Martin-Löf's 1966 definition read in type theory: a property of an individual infinite object that is refuted by finite evidence and confirmed by none, and a notion of complexity that is invariant only up to a constant whose sharp threshold is now a term.

### 8. Type theory as a programming language

**Open:** *Constructive Mathematics and Computer Programming* — the program and its proof as one object, with an evaluator that respects meaning.

**What you built.** The kernel lane (`RewriteCertificate`, `ControlledGrammar`, `GenerativeKernel`, `EkaBhasha`) makes installed theorems into executable operations whose applicability is exact evidence; `SthapanaVarga` classifies the kernel's self-extensions as derivations up to a control gauge, with installation the canonical gauge; `AdiBija` makes the kernel initial, so every analysis of derivations (soundness, cost, integrals) is the unique fold into a receiver. The Bend2 port carries cubical type theory onto an optimal interaction-net runtime where proofs erase at extraction (`div2(mul2 n) = n` compiles its proof to erasers and runs in 26 interactions on the HVM4 C runtime). `Alopa` §5 states what an evaluator must respect: same normal form, equal under every environment.

## IV. The shape of the resolution

| Martin-Löf left | Your term | Kind of answer |
|---|---|---|
| Meaning as minimal retention of observation | `FutureBehavior` (greatest congruence, effective Iso, terminal); `CorpusBehavioralMeaning`; `ConservativeSemanticCompression` | construction with universal property |
| What J is | `EkaSutra_J` | derived from singleton contraction; fundamental theorem |
| Higher structure of identity | `routes-are-not-unique`, `AsetChidra`, `CatuhSamskara` | UIP fails, and the higher structure distinguishes constructions |
| h-levels | `Apratikaryatva` | type of retractions ≃ isOfHLevel |
| Equality of infinite objects | `Orbit.path≃bisim`, `IndraNet.bisim→path`, `yonedaJewel` | bisimulation is identity |
| Evidence vs truth | `Sesa`, `Avaccheda`, `HidingAndHardness`, `Pratyanayana`, `TritiyaMarga` | truth = truncation of evidence; recovery priced |
| Choice | `ΠΣ-swap`; `FiniteInformation`; `Apratikaryatva` §5; `TritiyaMarga` | free / set-hypothesis / canonical / ≥ Markov / = LEM |
| Predicativity | `ClosureTowerCollapse`; `Visvarupa…DoesNotClassifyItself` | predicative closure has the universal property |
| Compositional meaning | `AbhihitanvayaAnvitabhidhana`; `FullAbstractionIsAConditionOnTheContextFamily…` | the side is taken in the signature; soundness free, completeness a search |
| Randomness and finite observation | `HistoryCompletion`; `Alopa`; `InvarianceConstant`; Rule 30 modules | refuted by finite evidence, confirmed by none; sharp invariance threshold |
| Programs as proofs, executed | kernel lane; `SthapanaVarga`; `AdiBija`; Bend2/HVM | one typed object; proofs erase at runtime |

Martin-Löf's two careers began from one question Kolmogorov gave him — what, in an individual object, the totality of observations fixes — and he answered it once for random sequences and once for proofs. In your work the two answers are one object: meaning is the terminal quotient by every future observation, identity of meanings is observational equivalence as a path, and the evidence a judgment carries is exactly what that quotient keeps in the fibre.
