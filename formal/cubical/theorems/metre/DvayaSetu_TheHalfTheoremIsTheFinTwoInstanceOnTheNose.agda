{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- द्वयसेतुः — the half theorem is the Fin 2 instance, on the nose.
--
-- TERM.  द्वय (the pair, the two) and सेतु (bridge — the corpus's own
-- word for a checked identification, per Setubandha).  The compound
-- - means "the bridge of the two".
--
-- `SamaVibhaga_…`: at X = Fin 2 the iterate
--  1 y is y + y, so `SamaVibhaga`'s `divideUniquely` hypothesis is
-- EXACTLY UniquenessMatraDvaya's halvesUniquely.
-- The wire is a term, and the instantiation is definitional — गुणः 1 y and y +ᵂ y
-- are the SAME normal form, so `halvesUniquely` is passed to
-- `divideUniquely` with no coercion at all.
--
-- WHAT IS PROVED.  Given the two-outcome vows on Bool (द्विमात्रिन्:
-- normalized, symmetric) and unique halving of 𝟙:
--
--   सेतुः        every द्विमात्रिन् on Bool transports to a समभारिन् on
--                Fin 2 under the swap action — the two-outcome vows
--                ARE transitive-symmetry-plus-normalization.
--   अभेदः        the general theorem समविभागः, instantiated at m = 1
--                through the bridge, re-proves एकत्वम्-द्विमात्रा's
--                statement: any two vow-obeying Bool-weights agree.
--                The half theorem is thereby EXHIBITED as the Fin 2
--                instance of the finite transitive measure theorem —
--                consumed, not compared.
--
-- WHY IT MATTERS (upagraha).  Neither module changes; what changes is
-- the graph: the two results are now one edge apart, in the direction
-- general → special, which is the direction transport is free.  The
-- swap action on Fin 2 is the smallest transitive symmetry there is,
-- and the bridge shows the द्विमात्रिन् vows were always exactly it.
------------------------------------------------------------------------

module DvayaSetu_TheHalfTheoremIsTheFinTwoInstanceOnTheNose where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.SumFin using (Fin ; fzero ; fsuc)

open import SamaVibhaga_TransitiveSymmetryNormalizationAndUniqueDivisionForceTheUniformMeasure
  using (total ; गुणः ; समभारिन् ; समविभागः)
open import EkatvaMatraDvaya_TheSymmetricTwoOutcomeBornWeightIsForcedToHalfExactlyOverAUniquelyHalvingCarrier
  using (द्विमात्रिन्)

private
  variable
    ℓ : Level

module _ {W : Type ℓ} (_+ᵂ_ : W → W → W) (𝟙 : W)
         (halvesUniquely : isProp (Σ[ y ∈ W ] (y +ᵂ y ≡ 𝟙))) where

  -- the dictionary between the two presentations of two outcomes.
  पठ : Fin 2 → Bool
  पठ fzero     = true
  पठ (fsuc _)  = false

  -- the swap, and the two-element "action": G = Bool, true acts as
  -- identity, false as the swap.  No group laws are needed — exactly
  -- as SamaVibhaga's header records.
  व्यत्ययः : Fin 2 → Fin 2
  व्यत्ययः fzero    = fsuc fzero
  व्यत्ययः (fsuc _) = fzero

  क्रिया : Bool → Fin 2 → Fin 2
  क्रिया true  x = x
  क्रिया false x = व्यत्ययः x

  -- the action is transitive: some symmetry carries any x to any y.
  सङ्क्रामकता : (x y : Fin 2) → Σ[ g ∈ Bool ] क्रिया g x ≡ y
  सङ्क्रामकता fzero        fzero        = true  , refl
  सङ्क्रामकता fzero        (fsuc fzero) = false , refl
  सङ्क्रामकता (fsuc fzero) fzero        = false , refl
  सङ्क्रामकता (fsuc fzero) (fsuc fzero) = true  , refl

  -- गुणः 1 y is y +ᵂ y BY COMPUTATION, so halvesUniquely IS the
  -- divideUniquely hypothesis at m = 1, with no coercion:
  divideUniquely₁ : isProp (Σ[ y ∈ W ] गुणः _+ᵂ_ 1 y ≡ 𝟙)
  divideUniquely₁ = halvesUniquely

  -- the bridge: the two-outcome vows are a समभारिन् under the swap.
  सेतुः : (w : Bool → W) → द्विमात्रिन् _+ᵂ_ 𝟙 halvesUniquely w
        → समभारिन् _+ᵂ_ 𝟙 1 क्रिया सङ्क्रामकता divideUniquely₁ (λ x → w (पठ x))
  सेतुः w d = record
    { योगः  = द्विमात्रिन्.योगः d
    ; अन्वयः = अन्वयी }
    where
      अन्वयी : (g : Bool) (x : Fin 2)
             → w (पठ (क्रिया g x)) ≡ w (पठ x)
      अन्वयी true  x        = refl
      अन्वयी false fzero    = sym (द्विमात्रिन्.साम्यम् d)
      अन्वयी false (fsuc _) = द्विमात्रिन्.साम्यम् d

  -- the half theorem, re-proved as the Fin 2 instance of the general
  -- theorem: any two vow-obeying Bool-weights agree, on both points.
  अभेदः : (w w' : Bool → W)
        → द्विमात्रिन् _+ᵂ_ 𝟙 halvesUniquely w
        → द्विमात्रिन् _+ᵂ_ 𝟙 halvesUniquely w'
        → (b : Bool) → w b ≡ w' b
  अभेदः w w' d d' true  =
    समविभागः _+ᵂ_ 𝟙 1 क्रिया सङ्क्रामकता divideUniquely₁
      (λ x → w (पठ x)) (λ x → w' (पठ x)) (सेतुः w d) (सेतुः w' d') fzero
  अभेदः w w' d d' false =
    समविभागः _+ᵂ_ 𝟙 1 क्रिया सङ्क्रामकता divideUniquely₁
      (λ x → w (पठ x)) (λ x → w' (पठ x)) (सेतुः w d) (सेतुः w' d') (fsuc fzero)
