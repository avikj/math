{-# OPTIONS --cubical --safe #-}
--
-- ओजयुग्म — oja / yugma, odd and even.  The Jaina canon classifies a rāśi by
-- its remainder — the fourfold kṛtayugma / tryoja / dvāparayugma / kalyoja of
-- the Bhagavat Stra (Vykhyprajapti), with the oja/yugma pair also in the
-- Sthnga; the canon as redacted at Valabh, c. 5th c. CE, the material
-- older.  What is taken is the term for the parity of a count.
--
-- WHAT THIS CHECKS, and where its two halves come from.
--
-- The Lean lane carries a tensor `squarefreeChargeCube n`
-- (`formal/lean/Pairfield/PrimeChargeArbitraryRank.lean`) on n squarefree
-- prime places, whose CP rank is exactly n.  Its definition, transcribed:
--
--     signFactor   b = if b then -1 else 1
--     activeFactor b = if b then  1 else 0
--     chargeTerm marked = one pure term: activeFactor at the marked place,
--                         signFactor at every other place
--     squarefreeChargeCube n x = Σ over marked of that pure term at x
--
-- the critical affine arithmetic system, its grading operator Ω, and the
-- parity character λ = (−1)^Ω — the torus evaluated at (−1,−1,…).  Theorem F
-- says every gauge-charged observable has equilibrium expectation exactly
-- zero, which is the sieve parity barrier.
--
-- BillIsItsGradedForm.md` (absent from this repository) claims those are one charge, and marks the claim an
-- IDENTIFICATION exhibited on index sets and signs rather than a checked map.
-- This module removes that qualification for the algebraic half, on a list of
-- places rather than `Fin n → Bool`:
--
--     आवेशः bs ≡ - (pos (ओजः bs) · पर्यायः bs)
--
-- the squarefree charge is the active-place count times the parity character,
-- negated.  So the tensor whose rank is exactly n and the graded object of
-- Theorem F are one function of the places, and r = 0 — the twirl's neutral
-- sector — is the statement that this function's expectation vanishes.
module OjaYugma_TheSquarefreeChargeIsTheActivePlaceCountTimesTheParityCharacter where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Int
  using (ℤ; pos; -_; _+_; _·_; -Involutive; -DistR·; ·DistL+; pos+; pos0+)

-- ---------------------------------------------------------------- one place
-- A list of Bool assigns active/inactive to finitely many ordered prime
-- places: the same data as the Lean lane's `Fin n → Bool`, folded.

-- signFactor, at one place.
चिह्नम् : Bool → ℤ
चिह्नम् true  = - (pos (suc zero))
चिह्नम् false = pos (suc zero)

-- activeFactor, at one place.
सक्रियम् : Bool → ℤ
सक्रियम् true  = pos (suc zero)
सक्रियम् false = pos zero

-- ------------------------------------------------------- the three functions

-- Theorem F's grading operator Ω: how many places are active.
ओजः : List Bool → ℕ
ओजः [] = zero
ओजः (true ∷ bs) = suc (ओजः bs)
ओजः (false ∷ bs) = ओजः bs

-- Theorem F's parity character λ = (−1)^Ω, as the product of the place signs.
पर्यायः : List Bool → ℤ
पर्यायः [] = pos (suc zero)
पर्यायः (b ∷ bs) = चिह्नम् b · पर्यायः bs

-- The squarefree charge.  Read one place at a time, the Lean lane's sum over
-- `marked : Fin n` says exactly this: either the head is the marked place —
-- activeFactor there, the sign on all the rest, which is `सक्रियम् b · पर्यायः bs`
-- — or the marked place is in the tail and the head contributes its sign.
आवेशः : List Bool → ℤ
आवेशः [] = pos zero
आवेशः (b ∷ bs) = सक्रियम् b · पर्यायः bs + चिह्नम् b · आवेशः bs

-- ------------------------------------------------- the two heads, computed
-- Named so the induction below reads as algebra rather than as unfolding.
-- Three are definitional; the fourth needs `pos0+`, because `_+_` on ℤ
-- recurses on its right argument and `pos 0 + z` is not `z` on the nose.

पर्यायः-सत् : (bs : List Bool) → पर्यायः (true ∷ bs) ≡ - (पर्यायः bs)
पर्यायः-सत् bs = refl

पर्यायः-असत् : (bs : List Bool) → पर्यायः (false ∷ bs) ≡ पर्यायः bs
पर्यायः-असत् bs = refl

आवेशः-सत् : (bs : List Bool)
  → आवेशः (true ∷ bs) ≡ पर्यायः bs + (- (आवेशः bs))
आवेशः-सत् bs = refl

आवेशः-असत् : (bs : List Bool) → आवेशः (false ∷ bs) ≡ आवेशः bs
आवेशः-असत् bs = sym (pos0+ (आवेशः bs))

-- ------------------------------------------------------------- the identity
--
--     charge  =  − Ω · λ
--
-- one line of the Lean lane's tensor and one line of GAUGE.md (absent from this repository)'s graded
-- object, shown to be the same function of the places.

ओजयुग्म-नियमः : (bs : List Bool)
  → आवेशः bs ≡ - (pos (ओजः bs) · पर्यायः bs)
ओजयुग्म-नियमः [] = refl
ओजयुग्म-नियमः (false ∷ bs) = आवेशः-असत् bs ∙ ओजयुग्म-नियमः bs
ओजयुग्म-नियमः (true ∷ bs) =
  आवेशः (true ∷ bs)
    ≡⟨ आवेशः-सत् bs ⟩
  पर्यायः bs + (- (आवेशः bs))
    ≡⟨ cong (λ z → पर्यायः bs + (- z)) (ओजयुग्म-नियमः bs) ⟩
  पर्यायः bs + (- (- (pos (ओजः bs) · पर्यायः bs)))
    ≡⟨ cong (पर्यायः bs +_) (-Involutive (pos (ओजः bs) · पर्यायः bs)) ⟩
  पर्यायः bs + (pos (ओजः bs) · पर्यायः bs)
    ≡⟨ sym (·DistL+ (pos (suc zero)) (pos (ओजः bs)) (पर्यायः bs)) ⟩
  (pos (suc zero) + pos (ओजः bs)) · पर्यायः bs
    ≡⟨ cong (_· पर्यायः bs) (sym (pos+ (suc zero) (ओजः bs))) ⟩
  pos (suc (ओजः bs)) · पर्यायः bs
    ≡⟨ sym (-Involutive (pos (suc (ओजः bs)) · पर्यायः bs)) ⟩
  - (- (pos (suc (ओजः bs)) · पर्यायः bs))
    ≡⟨ cong -_ (-DistR· (pos (suc (ओजः bs))) (पर्यायः bs)) ⟩
  - (pos (suc (ओजः bs)) · (- (पर्यायः bs))) ∎
