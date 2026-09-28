{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- भार-आवृत्ति — भारवत्याः गणना-क्रियायाः तन्तुः शिरो-भारेण भिद्यते ।
--
-- (the fibre of a weighted counting map splits by the head's weight.)
--
-- ────────────────────────────────────────────────────────────────────
-- `Avrtti_…agda` § treats `length`:
-- `length` charges one per constructor so its fibre recurrence has no
-- guard, while a WEIGHTED map does.  This writes the general weighted
-- emitter.
--
-- THE SHAPE.  A first guess
-- is
--
--     fiber f n ≃ Σ[ x ∈ X ] Σ[ m ∈ ℕ ] (w x + m ≡ n) × fiber f m
--
-- which cannot hold as stated: the empty list inhabits `fiber f 0` and
-- has no head `x` to produce.  The nil case is a SEPARATE SUMMAND, and
-- the honest decomposition is a coproduct — §२ below.  With it the
-- recurrence is exact and both round trips close by `refl`, because
-- `f (x ∷ xs)` reduces to `w x + f xs` definitionally and no fitting
-- proof has to be constructed at all.
--
-- AND WHY §५'s `Σ[ m ]` FORM IS EQUIVALENT ANYWAY, which is worth saying
-- because it is the corpus's own law: `Σ[ m ∈ ℕ ] (f xs ≡ m) × …` carries
-- a `singl (f xs)`, which is contractible, so the `m` and its witness
-- contract away and the form collapses to §२'s.  The intermediate value
-- rides free — `fibre/src/Loss/Carrier.agda`, and `Lekha_…agda` for the
-- same fact at length.
------------------------------------------------------------------------

module Bharavrtti_TheWeightedCountingMapsFibreDecomposesByHeadWeightAndTheNilCaseIsASeparateSummand where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; fiber)
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv ; Iso)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

private variable ℓ : Level

module _ {X : Type ℓ} (w : X → ℕ) where

------------------------------------------------------------------------
-- १ · भार-गणना — the weighted counting map: charge `w x` per element.
------------------------------------------------------------------------

  भारः : List X → ℕ
  भारः []       = 0
  भारः (x ∷ xs) = w x + भारः xs

------------------------------------------------------------------------
-- २ · आवृत्तिः — the fibre decomposes: the nil case, or a head with its
--     weight fitting into what remains.
--
-- Both round trips are `refl`: `भारः (x ∷ xs)` reduces to `w x + भारः xs`,
-- so the "fitting proof" §५ expected to construct is the SAME path,
-- carried across unchanged.
------------------------------------------------------------------------

  भार-आवृत्तिः : (n : ℕ)
    → fiber भारः n ≃ ((0 ≡ n) ⊎ (Σ[ x ∈ X ] Σ[ xs ∈ List X ] (w x + भारः xs ≡ n)))
  भार-आवृत्तिः n = isoToEquiv (iso भङ्गः सङ्घातः निवृत्तिः प्रत्यावृत्तिः)
    where
      भङ्गः : fiber भारः n → ((0 ≡ n) ⊎ (Σ[ x ∈ X ] Σ[ xs ∈ List X ] (w x + भारः xs ≡ n)))
      भङ्गः ([]     , p) = inl p
      भङ्गः (x ∷ xs , p) = inr (x , xs , p)

      सङ्घातः : ((0 ≡ n) ⊎ (Σ[ x ∈ X ] Σ[ xs ∈ List X ] (w x + भारः xs ≡ n))) → fiber भारः n
      सङ्घातः (inl p)            = [] , p
      सङ्घातः (inr (x , xs , q)) = (x ∷ xs) , q

      निवृत्तिः : (y : _) → भङ्गः (सङ्घातः y) ≡ y
      निवृत्तिः (inl p)            = refl
      निवृत्तिः (inr (x , xs , q)) = refl

      प्रत्यावृत्तिः : (y : fiber भारः n) → सङ्घातः (भङ्गः y) ≡ y
      प्रत्यावृत्तिः ([]     , p) = refl
      प्रत्यावृत्तिः (x ∷ xs , p) = refl


------------------------------------------------------------------------
-- ३ · आवृत्तिः विना अपवर्तनेन — the recurrence with NO subtraction.
--
-- The usual weighted recurrence is written with `n ∸ w x`, which over ℕ
-- is truncated and needs a guard that `w x ≤ n`.  Clearing it the way
-- `CompositionSemiring.agda` clears bhvan -- move the subtraction across
-- rather than truncate -- gives a statement with no monus, no guard, and
-- no side condition: the fibre is a coproduct of SHIFTED fibres.
--
-- `ANEKANTA.md` (absent from this repository) §7's lesson, on a different object: a statement forced
-- into the poorer language got stronger, because the guard was an
-- artefact of the subtraction and not of the mathematics.
------------------------------------------------------------------------

  शिष्ट-भारः : X → List X → ℕ
  शिष्ट-भारः x xs = w x + भारः xs

  भार-आवृत्तिः-निरपवर्तना : (n : ℕ)
    → fiber भारः n ≃ ((0 ≡ n) ⊎ (Σ[ x ∈ X ] fiber (शिष्ट-भारः x) n))
  भार-आवृत्तिः-निरपवर्तना = भार-आवृत्तिः
