{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- देश-सङ्घातः — the CENSUS composes, and the composition law is the reason
-- there is no shortest-path formulation of routing in this corpus.
--
-- WHAT WAS ALREADY THERE, and is used rather than reproved:
--   * `शेष-सङ्घातः` (SankramanaSesa) — fibres compose:
--         शेष (g ∘ f) z  ≃  Σ[ w ∈ शेष g z ] शेष f (fst w)
--   * `देश` (Loss.SakalaVikalaDesa) — the census as a TERM, three
--     constructors carrying their evidence: अवक्तव्यम् (empty fibre, nothing
--     lost, धनात्मकम्), सकलादेश (contractible), विकलादेश (two points, exhibited).
--
-- WHAT IS BUILT HERE.  The Σ-law is about FIBRES.  Its
-- lift to the CENSUS is the whole content of "what does
-- a route cost".  `WholePartialDesa` §3 exhibits the cancellation as three
-- hand-computed instances on Unit/Bool and reads the moral off them.  Here
-- it is the general mechanism, and the instances become corollaries.
--
-- THE THREE LAWS, and what each one kills.
--
-- §२ अवक्तव्य-ग्रासः — an empty OUTER fibre is ABSORBING.  ¬ शेष g z forces
--    ¬ शेष (g ∘ f) z, whatever f is.  So arbitrary loss upstream of an
--    inexpressible point is INVISIBLE in the composite.  This kills
--    monotonicity: extending a path can hide cost already paid.
--
-- §३ सकल-सङ्क्रमः — a contractible OUTER fibre is TRANSPARENT.  With centre
--    (b , p), शेष (g ∘ f) z ≃ शेष f b: the composite's census at z IS f's
--    census at b, on the nose.  This is the only case in which a scalar
--    weight would have been correct, and it is the case where the weight
--    is not needed.
--
-- §४ प्रतिहननम् — the cancellation, as a mechanism.  A CROWDED outer fibre
--    whose points have empty inner fibres except one contractible entry
--    yields a CONTRACTIBLE composite.  विकलादेश ∘ अवक्तव्यम् = सकलादेश.  Two
--    genuine defects annihilate.  §५ instantiates this at Unit → Bool →
--    Unit and recovers SakalaVikalaDesa §3's computed example as a
--    corollary of the general law rather than as a witness of it.
--
-- THE CONSEQUENCE FOR ROUTING, which is why this file exists.  A cost model
-- admits a shortest-path algorithm when costs form a graded monoid: an
-- associative accumulation, monotone under extension.  §२ refutes
-- monotonicity and §४ refutes any accumulation at all — the composite's
-- census is not a function of the two censuses, because §४'s outcome
-- depends on WHICH points of the outer fibre carry which inner fibres, data
-- that neither census records.  The correct object is not a weight but the
-- Σ itself: cost is a SECTION over the codomain, and composition is
-- dependent sum, not addition.  Dijkstra has no formulation here; the
-- routing target is `isEquiv`, which `WholePartialDesa` §4 already
-- identifies as "every point of the census is सकलादेश".
------------------------------------------------------------------------

module DesaAggregate_TheCensusComposesAndThatIsWhyCostIsNotAGradedMonoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open Iso
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv)
open import Cubical.Foundations.Transport using (transport⁻Transport)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false ; false≢true ; isSetBool)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level
    A B C : Type ℓ

------------------------------------------------------------------------
-- १ · शेष and the composition law, restated locally at the level the
-- corpus states them, so this file stands alone under the kernel.
-- (शेष-सङ्घातः is SankramanaSesa's theorem; the proof term
-- below is the same one.)
------------------------------------------------------------------------

शेष : {A B : Type ℓ} (f : A → B) → B → Type ℓ
शेष {A = A} f b = Σ[ a ∈ A ] (f a ≡ b)

module _ {A B C : Type ℓ} (f : A → B) (g : B → C) (z : C) where

  private
    fwd : शेष (λ a → g (f a)) z → Σ[ w ∈ शेष g z ] शेष f (fst w)
    fwd (a , p) = ((f a , p) , (a , refl))

    bwd : (Σ[ w ∈ शेष g z ] शेष f (fst w)) → शेष (λ a → g (f a)) z
    bwd ((b , q) , (a , p)) = (a , cong g p ∙ q)

    bwd-fwd : (x : शेष (λ a → g (f a)) z) → bwd (fwd x) ≡ x
    bwd-fwd (a , p) i = (a , sym (lUnit p) i)

    fwd-bwd : (w : Σ[ w ∈ शेष g z ] शेष f (fst w)) → fwd (bwd w) ≡ w
    fwd-bwd ((b , q) , (a , p)) = lem a b p q
      where
      lem : (a : A) (b : B) (p : f a ≡ b) (q : g b ≡ z)
          → fwd (bwd ((b , q) , (a , p))) ≡ ((b , q) , (a , p))
      lem a b p q =
        J (λ b' p' → (q' : g b' ≡ z)
              → fwd (bwd ((b' , q') , (a , p'))) ≡ ((b' , q') , (a , p')))
          (λ q' i → ((f a , lUnit q' (~ i)) , (a , refl)))
          p q

  शेष-सङ्घातः : शेष (λ a → g (f a)) z ≃ (Σ[ w ∈ शेष g z ] शेष f (fst w))
  शेष-सङ्घातः = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)

------------------------------------------------------------------------
-- २ · अवक्तव्य-ग्रासः — the empty outer fibre swallows everything upstream.
-- MONOTONICITY DIES HERE: f may lose arbitrarily much and the composite
-- records none of it.
------------------------------------------------------------------------

अवक्तव्य-ग्रासः : {A B C : Type ℓ} (f : A → B) (g : B → C) (z : C)
                → ¬ (शेष g z) → ¬ (शेष (λ a → g (f a)) z)
अवक्तव्य-ग्रासः f g z ne (a , p) = ne (f a , p)

------------------------------------------------------------------------
-- ३ · सकल-सङ्क्रमः — the contractible outer fibre is transparent.
-- The composite's census at z IS f's census at the centre.
------------------------------------------------------------------------

सकल-सङ्क्रमः : {A B C : Type ℓ} (f : A → B) (g : B → C) (z : C)
             → (c : isContr (शेष g z))
             → शेष (λ a → g (f a)) z ≃ शेष f (fst (fst c))
सकल-सङ्क्रमः f g z c =
  compEquiv (शेष-सङ्घातः f g z)
            (isoToEquiv (iso to fro to-fro fro-to))
  where
    b₀ = fst (fst c)
    to : (Σ[ w ∈ शेष g z ] शेष f (fst w)) → शेष f b₀
    to (w , r) = subst (शेष f) (cong fst (sym (snd c w))) r
    fro : शेष f b₀ → Σ[ w ∈ शेष g z ] शेष f (fst w)
    fro r = fst c , r
    to-fro : (r : शेष f b₀) → to (fro r) ≡ r
    to-fro r =
      cong (λ pth → subst (शेष f) (cong fst pth) r)
           (isProp→isSet (isContr→isProp c) (fst c) (fst c) (sym (snd c (fst c))) refl)
      ∙ substRefl {B = शेष f} r
    fro-to : (wr : Σ[ w ∈ शेष g z ] शेष f (fst w)) → fro (to wr) ≡ wr
    fro-to (w , r) =
      ΣPathP ( snd c w
             , toPathP (transport⁻Transport (cong (शेष f) (cong fst (sym (snd c w)))) r
                        ∙ refl) )

------------------------------------------------------------------------
-- ४ · प्रतिहननम् — the cancellation, as the general mechanism.
--
-- The composite is the Σ of the inner fibres over the outer fibre.  So a
-- CROWDED outer fibre contributes only at those of its points whose inner
-- fibre is inhabited: emptiness downstream DELETES points of the outer
-- fibre.  विकलादेश above ∘ अवक्तव्यम् below can be सकलादेश.
--
-- Stated as the exact criterion the Σ gives: the composite is contractible
-- exactly when the Σ is, and the Σ can be contractible while the outer
-- fibre is not.  §५ exhibits that, minimally.
------------------------------------------------------------------------

प्रतिहननम् : {A B C : Type ℓ} (f : A → B) (g : B → C) (z : C)
           → isContr (Σ[ w ∈ शेष g z ] शेष f (fst w))
           → isContr (शेष (λ a → g (f a)) z)
प्रतिहननम् f g z ic =
  isOfHLevelRespectEquiv 0 (invEquiv (शेष-सङ्घातः f g z)) ic

------------------------------------------------------------------------
-- ५ · The minimal witness, recovered as a COROLLARY of §४ rather than as
-- an example standing on its own.  SakalaVikalaDesa §3 computes these three
-- censuses by hand; here the third follows from the first two through the Σ.
------------------------------------------------------------------------

सत् : Unit → Bool
सत् _ = true

एकम् : Bool → Unit
एकम् _ = tt

-- outer (एकम् at tt) is CROWDED: false and true both sit over tt
बहिः-वाम बहिः-दक्षिण : शेष एकम् tt
बहिः-वाम   = false , refl
बहिः-दक्षिण = true  , refl

बहिः-द्वयम् : ¬ (बहिः-वाम ≡ बहिः-दक्षिण)
बहिः-द्वयम् p = false≢true (cong fst p)

-- inner over `false` is EMPTY — this is the point the Σ deletes
अन्तः-रिक्तम् : ¬ (शेष सत् false)
अन्तः-रिक्तम् (_ , p) = true≢false p

-- inner over `true` is contractible
अन्तः-सकलम् : isContr (शेष सत् true)
fst अन्तः-सकलम्          = tt , refl
snd अन्तः-सकलम् (u , p) i = tt , isSetBool true true refl p i

-- THE DELETION, isolated as its own term and structural (no `with`, per the
-- house discipline): an outer point whose inner fibre is inhabited MUST be
-- `true`.  This is exactly "emptiness downstream deletes points of the outer
-- fibre" — the mechanism of §४, at its smallest.
बिन्दु-निर्धारणम् : (b : Bool) → शेष सत् b → true ≡ b
बिन्दु-निर्धारणम् true  _ = refl
बिन्दु-निर्धारणम् false r = ⊥-rec (अन्तः-रिक्तम् r)

-- the Σ therefore has exactly one inhabitant — and the reason is the
-- Carrier law itself: after the deletion, what remains is literally
-- `singl true`, contractible with no hypothesis (पुनरागमन).  So the
-- annihilation of two defects is not a coincidence of this example; it is
-- `isContrSingl` showing through.
संहति-Iso-वाहकः : Iso (Σ[ w ∈ शेष एकम् tt ] शेष सत् (fst w)) (singl true)
Iso.fun      संहति-Iso-वाहकः ((b , q) , (u , p)) = b , p
Iso.inv      संहति-Iso-वाहकः (b , p)             = (b , refl) , (tt , p)
Iso.rightInv संहति-Iso-वाहकः (b , p)             = refl
Iso.leftInv  संहति-Iso-वाहकः ((b , q) , (u , p)) i =
  (b , isSetUnit tt tt refl q i) , (tt , p)

संहति-सकलम् : isContr (शेष (λ u → एकम् (सत् u)) tt)
संहति-सकलम् =
  प्रतिहननम् सत् एकम् tt
    (isOfHLevelRespectEquiv 0
      (invEquiv (isoToEquiv संहति-Iso-वाहकः))
      (isContrSingl true))

------------------------------------------------------------------------
--     the census is not a function of the two censuses.§४
--
-- §४ is stated as "if the Σ is contractible then the composite is".  It is
-- NOT a function from (देश g z) and (देश f) to (देश (g ∘ f) z), and no such
-- function exists: §५'s outcome depends on WHICH point of the outer fibre
-- carries the empty inner fibre, and a census records only that the outer
-- fibre is crowded, not which of its points are which.  That is precisely
-- why cost here is a  and not a weight.
------------------------------------------------------------------------
