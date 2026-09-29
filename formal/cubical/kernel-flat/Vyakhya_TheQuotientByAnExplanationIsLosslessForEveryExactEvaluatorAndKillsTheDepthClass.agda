{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- व्याख्या — the explanation, as a quotient.
--
-- MulyaVinimaya ends on a prophecy: Derivation has no 2-cells, so
-- when an explanation later fills the diamond's loop, the depth class
-- is exactly what it must kill or account for.  This module fills it
-- and watches what dies.
--
-- The explanation is a 2-cell identifying the two coterminal
-- schedules of the diamond — imposed here as a set-quotient of the
-- trace space, which is precisely the synthesis's definition of
-- semantic compression: quotient by the distinctions the admissible
-- observers cannot detect.  Declare the admissible observers to be
-- the EXACT evaluators (the endpoint utilities), and:
--
--   §1  THE QUOTIENT IS LOSSLESS FOR EVERY PROTECTED OBSERVER: for
--       any potential φ, the pairing ∫ (d′ φ) factors through the
--       quotient, with the factorization computing on constructors —
--       Stokes is exactly the descent condition, twice.
--
--   §2  AND IT KILLS THE DEPTH CLASS: no function on the quotient
--       restricts to ∫ गभीरता on traces.  The two identified
--       schedules carry depths 2 and 1, the quotient makes them one
--       point, and 2 ≡ 1 is refuted in ℕ.
--
-- So admitting the explanation and protecting the depth observer are
-- incompatible, as a theorem: the nonzero cycle integral of
-- MulyaVinimaya is not merely a curiosity about one loop — it is the
-- exact obstruction to this compression.  Filling the loop is the
-- decision to demote depth from the protected class; keeping depth
-- protected is the decision that these two schedules shall remain
-- two.  The machine holds both consequences; the choice of observer
-- class is the caller's, which is where the synthesis says it must
-- live (the dangerous act is not quotienting — it is quotienting
-- before declaring the observers).
--
------------------------------------------------------------------------

module Vyakhya_TheQuotientByAnExplanationIsLosslessForEveryExactEvaluatorAndKillsTheDepthClass where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; snotz ; injSuc)
open import Cubical.Data.Int using (ℤ ; pos ; _-_ ; injPos)
open import Cubical.Data.Int.Properties using (isSetℤ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.HITs.SetQuotients using (_/_ ; [_] ; eq/ ; rec)

open import Kernel.RewriteCertificate using (Tm ; Derivation)
open import MulyaVinimaya_TheValueOfATraceIsItsPairingWithAnEvaluatorPotentialsTelescopeAndADepthEvaluatorHasNonzeroCycleIntegral
  using ( Evaluator ; ∫ ; d′ ; telescope
        ; गभीरता ; t₀ ; nf ; scheduleA ; scheduleB ; depthA ; depthB )

------------------------------------------------------------------------
-- ० · The explanation: the relation that fills the diamond.
------------------------------------------------------------------------

Traces : Type₀
Traces = Derivation t₀ nf

-- the 2-cell, as a relation: exactly the identification of the two
-- schedules, nothing else.
R : Traces → Traces → Type₀
R p q = (p ≡ scheduleA) × (q ≡ scheduleB)

-- the compressed trace space.
Explained : Type₀
Explained = Traces / R

------------------------------------------------------------------------
-- १ · Every exact evaluator factors through the compression.
------------------------------------------------------------------------

-- Stokes makes both schedules — and hence any two coterminal traces —
-- carry the same exact value; that IS the descent condition.
exactAgrees : (φ : Tm → ℤ) (p q : Traces) → R p q
  → ∫ (d′ φ) p ≡ ∫ (d′ φ) q
exactAgrees φ p q (pA , qB) =
  cong (∫ (d′ φ)) pA
  ∙ telescope φ (d′ φ) (λ _ → refl) scheduleA
  ∙ sym (telescope φ (d′ φ) (λ _ → refl) scheduleB)
  ∙ cong (∫ (d′ φ)) (sym qB)

-- the factorization, computing on constructors: the exact observer
-- read through the quotient is the exact observer.
exactDescends : (φ : Tm → ℤ) → Explained → ℤ
exactDescends φ = rec isSetℤ (∫ (d′ φ)) (exactAgrees φ)

exactFactors : (φ : Tm → ℤ) (p : Traces)
  → exactDescends φ [ p ] ≡ ∫ (d′ φ) p
exactFactors φ p = refl

------------------------------------------------------------------------
-- २ · The depth observer does not survive the compression.
------------------------------------------------------------------------

-- in the compressed space the two schedules are one point…
identified : Path Explained [ scheduleA ] [ scheduleB ]
identified = eq/ scheduleA scheduleB (refl , refl)

-- …so any function of the compressed trace that restricts to the
-- depth pairing forces 2 ≡ 1 in ℕ.
depthKilled :
  Σ[ g ∈ (Explained → ℤ) ] ((p : Traces) → g [ p ] ≡ ∫ गभीरता p) → ⊥
depthKilled (g , restricts) =
  snotz (injSuc (injPos two≡one))
  where
    two≡one : pos 2 ≡ pos 1
    two≡one =
      sym depthA
      ∙ sym (restricts scheduleA)
      ∙ cong g identified
      ∙ restricts scheduleB
      ∙ depthB
