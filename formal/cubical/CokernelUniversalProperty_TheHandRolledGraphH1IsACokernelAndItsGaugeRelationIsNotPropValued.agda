{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CokernelUniversalProperty_
--   TheHandRolledGraphH1IsACokernelAndItsGaugeRelationIsNotPropValued
--
-- This file's objects are category theory and homological algebra:
--
--   * The universal property used below is the nLab's, verbatim, from the
--     page `cokernel` — GitHub mirror `ncatlab/nlab-content`, path
--     `pages/3/3/0/1/1033/content.md` (absent from this repository) (the mirror stores pages by numeric
--     id; the human-readable title is in the sibling file `name`).  The
--     page's second Remark, in a category with a zero object:
--
--       "for every object C and every morphism h : B → C such that
--        h ∘ f = 0 is the zero morphism, there is a UNIQUE morphism
--        φ : coker(f) → C such that h = φ ∘ i."
--
--     and its first Example: "In the category Ab of abelian groups the
--     cokernel of a morphism f : A → B is the quotient of B by the image
--     (of the underlying morphism of sets) of f."
--
--   * The substrate: cubical Agda library v0.5.
--
-- THE OBJECT.  `NaturalMachine/FiniteGraphCohomology.agda` builds, for a graph, the
-- F2 cochain groups C0 and C1, the coboundary δ⁰, the relation `GaugeStep`,
-- and `H¹ = C¹ / GaugeStep` as a BARE `Type₀`.  It has a map OUT of H¹
-- (`descendedEvaluation`).  Nothing in it is modified here; it is imported.
--
-- Also imported by citation, not by name-collision:
-- `KirchhoffOnTheCubicalLibrary_…agda` rebuilds
-- a PARALLEL H¹ out of `FinMatrixAbGroup` + `imSubgroup` + `QuotientGroup`
-- and proves exactness there from `SetQuotients.effective`.  That file says
-- of the hand-rolled one: "`FiniteGraphCohomology.H¹` is the same set, as a
-- bare type."  §1 below is the reason the two
-- could not be linked by transporting that proof.
--
-- WHAT IS PROVED, in order:
--
--   §1  REFUTATION.  Exactness for the hand-rolled H¹ cannot be obtained
--       from `SetQuotients.effective`, the way the parallel H¹ gets it.
--       `effective` demands
--       `isPropValued R`, and `GaugeStep` is NOT prop-valued: as soon as
--       ONE vertex exists, the constant-false and constant-true gauges are
--       two DISTINCT elements of `GaugeStep x x`, because δ⁰ cannot see a
--       global constant.  Witnessed non-identity, not a size check.
--
--       Guarded: with `Vertex` EMPTY the relation IS prop-valued, proved in
--       §1b.  So the hypothesis `v : Vertex` is doing work and the negative
--       is not vacuous over an empty domain.  The two halves together say
--       exactly where the boundary is.
--
--   §2  The repair is already in the library and is not `effective`:
--       `isEquivRel→TruncIso` (SetQuotients.Properties, line 295) needs
--       `isEquivRel` and NO prop-valuedness, and returns the TRUNCATED
--       relation — which is the correct statement of "image" anyway
--       (nLab `image`, and the cokernel Example above says image of the
--       underlying map of sets).  `GaugeStep` is an equivalence relation
--       (§2a), so exactness at C¹ holds for the hand-rolled H¹ in both
--       directions (§2b): the class of x is trivial exactly when x is
--       merely a coboundary.
--
--   §3  The nLab universal property itself, for an ARBITRARY abelian group
--       target: for h : C¹ → ⟨A⟩ additive with h ∘ δ⁰ = 0, the type of
--       factorisations through `classOf` is CONTRACTIBLE.  `isContr` is the
--       honest reading of the page's "there is a unique morphism".
--
--   §4  Uniqueness needs NO hypothesis on h at all, because `classOf` is
--       surjective (`[]surjective`) — the nLab's "the cokernel projection
--       is an epimorphism".  Existence is where the hypotheses are spent.
--
--   §5  The corpus's `descendedEvaluation` is THE map the universal
--       property produces, at A = Z/2.  It was already there; what was
--       missing is that it is the only one.  That is the whole difference
--       between "a quotient with a map out of it" and "a cokernel".
--
--   §6  CONTROLS, because everything above is parametric and a parametric
--       negative over an uninhabited parameter is green and empty.  The
--       bouquet (one vertex, one self-loop) instantiates §1; `CycleEvaluation`
--       is exhibited inhabited there; and H¹ of it is shown NOT to be a
--       singleton by a WITNESSED non-identity, twice, by two independent
--       routes (through exactness, and through the corpus's own pairing).
--       Without that, §2b would be consistent with H¹ always trivial, in
--       which case every theorem here is true and worthless.
--
------------------------------------------------------------------------

module CokernelUniversalProperty_TheHandRolledGraphH1IsACokernelAndItsGaugeRelationIsNotPropValued where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ ; isPropΣ)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (Iso)

open import Cubical.Data.Bool
  using (Bool ; true ; false ; _⊕_
        ; ⊕-identityʳ ; ⊕-comm ; ⊕-assoc ; ⊕-invol
        ; isSetBool ; false≢true ; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd ; Σ≡Prop)
open import Cubical.Data.Empty as Empty using (⊥ ; isProp⊥)
open import Cubical.Data.Unit using (Unit ; tt)

open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)

open import Cubical.HITs.SetQuotients as SQ
  using (eq/ ; squash/ ; isEquivRel→TruncIso ; []surjective)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁)

open import Cubical.Algebra.AbGroup.Base
  using (AbGroup ; AbGroupStr ; makeAbGroup)

open import NaturalMachine.FiniteGraphCohomology using (module Graph)

open BinaryRelation

private variable ℓ : Level

------------------------------------------------------------------------
-- 0.  F2 arithmetic.  Four facts about `_⊕_` that the library does not
--     ship.  `⊕-invol`, `⊕-assoc`, `⊕-comm`
--     and `⊕-identityʳ` ARE shipped (Cubical/Data/Bool/Properties.agda,
--     lines 155–176) and are used rather than re-proved; these four are
--     what is left over.
------------------------------------------------------------------------

-- Every element of F2 is its own additive inverse.
⊕-self : (b : Bool) → b ⊕ b ≡ false
⊕-self false = refl
⊕-self true  = refl

-- Cancellation.  (a + b) + b = a.
⊕-cancel : (a b : Bool) → (a ⊕ b) ⊕ b ≡ a
⊕-cancel a b = sym (⊕-assoc a b b) ∙ cong (a ⊕_) (⊕-self b) ∙ ⊕-identityʳ a

-- a + d = 0  implies  d = a.  (Used to turn "x is gauge-equivalent to the
-- zero cochain" into "x IS a coboundary", which is the content of
-- exactness in the interesting direction.)
⊕-zero→eq : (a d : Bool) → a ⊕ d ≡ false → d ≡ a
⊕-zero→eq a d p = sym (⊕-invol a d) ∙ cong (a ⊕_) p ∙ ⊕-identityʳ a

-- The middle-four interchange for _⊕_, i.e. that δ⁰ is additive in the
-- gauge.  (nLab: `interchange law`.  Here it is just commutativity plus
-- associativity, spelled out because the rearrangement is what makes
-- `GaugeStep` transitive.)
⊕-middleFour : (a b c d : Bool) → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-middleFour a b c d =
    sym (⊕-assoc a b (c ⊕ d))
  ∙ cong (a ⊕_) (⊕-assoc b c d)
  ∙ cong (λ z → a ⊕ (z ⊕ d)) (⊕-comm b c)
  ∙ cong (a ⊕_) (sym (⊕-assoc c b d))
  ∙ ⊕-assoc a c (b ⊕ d)

-- Z/2 as an abelian group under _⊕_.  NOT the library's `BoolGroup`
-- (Cubical/Algebra/Group/Instances/Bool.agda), whose unit is `true` and
-- whose operation is XNOR.  The two are isomorphic; the coboundary δ⁰ in
-- `FiniteGraphCohomology` is written with `_⊕_`, so this is the one that
-- applies without transport.
BoolAb : AbGroup ℓ-zero
BoolAb = makeAbGroup false _⊕_ (λ b → b) isSetBool ⊕-assoc ⊕-identityʳ ⊕-self ⊕-comm

------------------------------------------------------------------------

module GraphCokernel (Vertex Edge : Type₀) (source target : Edge → Vertex) where

  open Graph Vertex Edge source target

  -- The zero 1-cochain.  `Graph` does not name it.
  zero¹ : C¹
  zero¹ _ = false

  ----------------------------------------------------------------------
  -- 1.  REFUTATION.  `SetQuotients.effective` cannot be used on H¹.
  --
  --   effective : isPropValued R → isEquivRel R → [ a ] ≡ [ b ] → R a b
  --
  -- `GaugeStep x y = Σ[ g ∈ C⁰ ] (∀ e → x e ⊕ δ⁰ g e ≡ y e)` fails the
  -- first hypothesis.  The reason is the same fact that makes H⁰ of a
  -- connected graph nontrivial: δ⁰ annihilates global constants, so a
  -- gauge is never unique.  Below, the witness.
  ----------------------------------------------------------------------

  gaugeFalse gaugeTrue : C⁰
  gaugeFalse _ = false
  gaugeTrue  _ = true

  -- Both constants are coboundary-trivial: δ⁰ (const b) is the zero
  -- 1-cochain for BOTH values of b.  These two proofs are the same term,
  -- which is the whole point.
  constGaugeFixes : (g : C⁰) → ((v w : Vertex) → g v ≡ g w)
    → (x : C¹) (e : Edge) → gaugeTranslate x g e ≡ x e
  constGaugeFixes g gconst x e =
    cong (x e ⊕_) (cong (g (source e) ⊕_) (sym (gconst (source e) (target e)))
                   ∙ ⊕-self (g (source e)))
    ∙ ⊕-identityʳ (x e)

  loopFalse loopTrue : GaugeStep zero¹ zero¹
  loopFalse = gaugeFalse , constGaugeFixes gaugeFalse (λ _ _ → refl) zero¹
  loopTrue  = gaugeTrue  , constGaugeFixes gaugeTrue  (λ _ _ → refl) zero¹

  -- §1a.  With one vertex present the two loops are DISTINCT, so
  -- `GaugeStep zero¹ zero¹` is not a proposition.
  module _ (v : Vertex) where

    loopsDiffer : ¬ (loopFalse ≡ loopTrue)
    loopsDiffer p = false≢true (funExt⁻ (cong fst p) v)

    GaugeStepIsNotPropValued : ¬ (isPropValued GaugeStep)
    GaugeStepIsNotPropValued h = loopsDiffer (h zero¹ zero¹ loopFalse loopTrue)

  -- §1b.  THE GUARD.  The negative above is not an artefact of an empty
  -- domain: with `Vertex` empty the relation IS prop-valued, so the
  -- hypothesis `v : Vertex` is load-bearing and the two statements between
  -- them locate the boundary exactly.
  module _ (noVertex : ¬ Vertex) where

    isContrC⁰ : isContr C⁰
    isContrC⁰ = (λ v → Empty.rec (noVertex v))
              , λ g → funExt (λ v → Empty.rec (noVertex v))

    GaugeStepIsPropValuedWhenVertexEmpty : isPropValued GaugeStep
    GaugeStepIsPropValuedWhenVertexEmpty x y =
      isPropΣ (isContr→isProp isContrC⁰)
              (λ _ → isPropΠ (λ _ → isSetBool _ _))

  ----------------------------------------------------------------------
  -- 2.  The repair.  `isEquivRel→TruncIso` asks only for an equivalence
  --     relation.
  ----------------------------------------------------------------------

  -- §2a.  GaugeStep is an equivalence relation.  Reflexivity by the zero
  -- gauge, symmetry by the SAME gauge (F2 is 2-torsion), transitivity by
  -- the sum of gauges (this is where the middle-four interchange is spent).
  reflGauge : isRefl GaugeStep
  reflGauge x = gaugeFalse , constGaugeFixes gaugeFalse (λ _ _ → refl) x

  symGauge : isSym GaugeStep
  symGauge x y (g , p) =
    g , λ e → cong (_⊕ δ⁰ g e) (sym (p e)) ∙ ⊕-cancel (x e) (δ⁰ g e)

  transGauge : isTrans GaugeStep
  transGauge x y z (g , p) (h , q) =
      (λ v → g v ⊕ h v)
    , λ e →
        cong (x e ⊕_)
          (⊕-middleFour (g (source e)) (h (source e))
                        (g (target e)) (h (target e)))
      ∙ ⊕-assoc (x e) (δ⁰ g e) (δ⁰ h e)
      ∙ cong (_⊕ δ⁰ h e) (p e)
      ∙ q e

  gaugeEquivRel : isEquivRel GaugeStep
  gaugeEquivRel = equivRel reflGauge symGauge transGauge

  -- The library iso, instantiated.  This is the statement `effective` would
  -- have given if §1 had not ruled it out, with ∥_∥₁ where `effective` has
  -- a bare `R`.  On the nLab's own reading (`image`, `cokernel` Example)
  -- the truncated form is the RIGHT one: the image of a map of sets is the
  -- propositionally-truncated fibrewise existence, not a choice of preimage.
  classPathIso : (x y : C¹) → Iso (classOf x ≡ classOf y) ∥ GaugeStep x y ∥₁
  classPathIso = isEquivRel→TruncIso gaugeEquivRel

  -- §2b.  EXACTNESS AT C¹ for the hand-rolled H¹, both directions:
  --
  --      C⁰ --δ⁰--> C¹ --classOf--> H¹
  --
  -- ker(classOf) = im(δ⁰).
  IsCoboundary : C¹ → Type₀
  IsCoboundary x = ∥ (Σ[ g ∈ C⁰ ] ((e : Edge) → δ⁰ g e ≡ x e)) ∥₁

  im⊆ker : (x : C¹) → IsCoboundary x → classOf x ≡ classOf zero¹
  im⊆ker x = PT.rec (squash/ _ _)
    (λ (g , p) → eq/ x zero¹
      (g , λ e → cong (x e ⊕_) (p e) ∙ ⊕-self (x e)))

  ker⊆im : (x : C¹) → classOf x ≡ classOf zero¹ → IsCoboundary x
  ker⊆im x pth =
    PT.map (λ (g , p) → g , λ e → ⊕-zero→eq (x e) (δ⁰ g e) (p e))
           (Iso.fun (classPathIso x zero¹) pth)

  ----------------------------------------------------------------------
  -- 3.  THE UNIVERSAL PROPERTY OF THE COKERNEL (nLab `cokernel`, Remark 2).
  ----------------------------------------------------------------------

  module _ (A : AbGroup ℓ) where

    open AbGroupStr (snd A) using (_+_ ; 0g ; is-set)

    -- "h : B → C such that h ∘ f = 0", with B = C¹, f = δ⁰, C = A.
    -- Additivity is what makes h a morphism of Ab; vanishing on
    -- coboundaries is `h ∘ f = 0`.
    record KillsCoboundaries (h : C¹ → ⟨ A ⟩) : Type ℓ where
      field
        additive : (x y : C¹) → h (x +¹ y) ≡ h x + h y
        vanishes : (g : C⁰) → h (δ⁰ g) ≡ 0g

    open KillsCoboundaries public

    -- "a morphism φ : coker(f) → C such that h = φ ∘ i".
    Factorisation : (h : C¹ → ⟨ A ⟩) → Type ℓ
    Factorisation h = Σ[ φ ∈ (H¹ → ⟨ A ⟩) ] ((x : C¹) → φ (classOf x) ≡ h x)

    -- Existence.
    factor : (h : C¹ → ⟨ A ⟩) → KillsCoboundaries h → Factorisation h
    factor h k = SQ.rec is-set h respects , λ _ → refl
      where
      respects : (x y : C¹) → GaugeStep x y → h x ≡ h y
      respects x y (g , p) =
          sym (AbGroupStr.+IdR (snd A) (h x))
        ∙ cong (h x +_) (sym (vanishes k g))
        ∙ sym (additive k x (δ⁰ g))
        ∙ cong h (funExt p)

    -- Uniqueness — see §4, it needs nothing about h.
    factorUnique : (h : C¹ → ⟨ A ⟩) → (F G : Factorisation h) → F ≡ G
    factorUnique h F G =
      Σ≡Prop (λ _ → isPropΠ (λ _ → is-set _ _))
        (funExt (SQ.elimProp (λ _ → is-set _ _)
                             (λ x → snd F x ∙ sym (snd G x))))

    -- "there is a UNIQUE morphism φ" — read as contractibility, which is
    -- the only reading that is stable under the fact that H¹ is a set.
    cokernelUniversalProperty :
      (h : C¹ → ⟨ A ⟩) → KillsCoboundaries h → isContr (Factorisation h)
    cokernelUniversalProperty h k = factor h k , factorUnique h (factor h k)

  ----------------------------------------------------------------------
  -- 4.  Where the hypotheses are actually spent.  The cokernel projection
  --     is an EPIMORPHISM, and uniqueness is a consequence of that alone:
  --     two maps out of H¹ that agree after `classOf` are equal, for ANY
  --     set target, with no additivity and no vanishing.  So the content
  --     of the universal property lives entirely in existence.
  ----------------------------------------------------------------------

  classOfSurjective : (c : H¹) → ∥ (Σ[ x ∈ C¹ ] (classOf x ≡ c)) ∥₁
  classOfSurjective = []surjective

  classOfEpi : {B : Type ℓ} → isSet B → (φ ψ : H¹ → B)
    → ((x : C¹) → φ (classOf x) ≡ ψ (classOf x)) → φ ≡ ψ
  classOfEpi Bset φ ψ agree = funExt (SQ.elimProp (λ _ → Bset _ _) agree)

  ----------------------------------------------------------------------
  -- 5.  The corpus's own map, identified.  `FiniteGraphCohomology`'s
  --     `descendedEvaluation` is the map the universal property produces
  --     at A = Z/2, and it is the ONLY map with its defining property.
  --     Its `additive` and `closed` fields are exactly the two hypotheses
  --     the nLab Remark asks for; `descendedEvaluation` is the existence
  --     half, and it was already there.  Uniqueness was not.
  ----------------------------------------------------------------------

  cycleKillsCoboundaries : (cyc : CycleEvaluation)
    → KillsCoboundaries BoolAb (evaluate cyc)
  additive (cycleKillsCoboundaries cyc) = CycleEvaluation.additive cyc
  vanishes (cycleKillsCoboundaries cyc) = CycleEvaluation.closed cyc

  -- The corpus's map, as a factorisation.  `refl` because `SQ.rec` computes
  -- on `[_]` and `classOf` is `[_]`.
  descendedIsAFactorisation : (cyc : CycleEvaluation)
    → Factorisation BoolAb (evaluate cyc)
  descendedIsAFactorisation cyc = descendedEvaluation cyc , λ _ → refl

  -- THE STATEMENT.  Any map out of H¹ restricting to `evaluate cyc` on
  -- cochains is `descendedEvaluation cyc`.  This is what upgrades
  -- "H¹ is a quotient with a map out of it" to "H¹ is the cokernel of δ⁰".
  descendedEvaluationIsUnique : (cyc : CycleEvaluation)
    (φ : H¹ → Bool) → ((x : C¹) → φ (classOf x) ≡ evaluate cyc x)
    → φ ≡ descendedEvaluation cyc
  descendedEvaluationIsUnique cyc φ agree =
    cong fst (factorUnique BoolAb (evaluate cyc)
               (φ , agree) (descendedIsAFactorisation cyc))

------------------------------------------------------------------------
-- 6.  CONTROLS.  Everything above is parametric in (Vertex, Edge, source,
--     target), and a parametric negative proves nothing if no instance
--     exists.  Two instances, and one witnessed non-identity.
------------------------------------------------------------------------

-- §6a.  The bouquet: one vertex, one self-loop.  This is the smallest
-- graph with nontrivial H¹.
module OneVertexOneLoop where

  open Graph Unit Unit (λ _ → tt) (λ _ → tt)
  open GraphCokernel Unit Unit (λ _ → tt) (λ _ → tt)

  one¹ : C¹
  one¹ _ = true

  -- §1 instantiated.  The failure of prop-valuedness is not vacuous.
  gaugeStepNotProp : ¬ (isPropValued GaugeStep)
  gaugeStepNotProp = GaugeStepIsNotPropValued tt

  -- THE CONTROL that matters.  Exactness at C¹ (§2b) is compatible with
  -- H¹ being a singleton, in which case every statement above is true and
  -- empty.  It is not a singleton: `one¹` and `zero¹` are witnessed to lie
  -- in DIFFERENT classes.  δ⁰ on this graph is identically zero because
  -- both endpoints of the loop are the same vertex, so the only
  -- coboundary is zero and `one¹` is not one.
  oneIsNotACoboundary : ¬ (classOf one¹ ≡ classOf zero¹)
  oneIsNotACoboundary p =
    PT.rec isProp⊥
      (λ (g , q) → false≢true (sym (⊕-self (g tt)) ∙ q tt))
      (ker⊆im one¹ p)

  -- §6c.  `CycleEvaluation` is INHABITED here — the loop is its own cycle,
  -- and evaluation is "read the sign on the loop".  So §5 is a statement
  -- about a record that has instances, not an empty hypothesis.
  loopCycle : CycleEvaluation
  loopCycle = record
    { evaluate = λ x → x tt
    ; additive = λ _ _ → refl
    ; closed   = λ g → ⊕-self (g tt)
    }

  -- The same non-identity a SECOND way, independent of §2b: through the
  -- corpus's own pairing instead of through exactness.  Two routes to one
  -- witnessed inequality; if either had been an artefact they would not
  -- agree.
  separatedByThePairing : ¬ (classOf one¹ ≡ classOf zero¹)
  separatedByThePairing p =
    true≢false (cong (descendedEvaluation loopCycle) p)

-- §6b.  The other side of the §1 boundary, instantiated: with no vertices
-- the relation IS prop-valued, so `effective` WOULD apply — and the
-- quotient is trivial, which is why that costs nothing.
module NoVertices where

  open Graph ⊥ ⊥ Empty.rec Empty.rec
  open GraphCokernel ⊥ ⊥ Empty.rec Empty.rec

  gaugeStepIsProp : isPropValued GaugeStep
  gaugeStepIsProp = GaugeStepIsPropValuedWhenVertexEmpty (λ x → x)

------------------------------------------------------------------------
-- Summary
--
-- PROVED, generically in (Vertex, Edge, source, target):
--   * `GaugeStep` is not prop-valued when a vertex exists (witnessed), and
--     IS prop-valued when no vertex exists.  Hence `SetQuotients.effective`
--     is unavailable for the hand-rolled H¹ and its unavailability is not
--     an artefact of an empty domain.
--   * `GaugeStep` is an equivalence relation.
--   * Exactness at C¹ in both directions, with the image taken
--     propositionally truncated.
--   * The nLab cokernel universal property, as `isContr (Factorisation h)`,
--     for every abelian group target.
--   * Uniqueness holds for every SET target with no hypothesis on h.
--   * `descendedEvaluation` is the unique map with its property.
--
-- PROVED CONCRETELY, on the bouquet (Vertex = Edge = Unit):
--   * §1's negative is instantiated, so it is not vacuous.
--   * `CycleEvaluation` is inhabited, so §5 is not vacuous.
--   * H¹ is not a singleton — `classOf one¹ ≢ classOf zero¹` — witnessed,
--     by two independent proofs.  A size check would not have shown this;
--     the non-identity is exhibited.
--   * The opposite side of §1's boundary is instantiated at Vertex = ⊥.
------------------------------------------------------------------------
