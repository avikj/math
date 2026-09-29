{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

-- 𝒦 := ∂ ∘ Γ   and the trichotomy of ρ(D𝒦).
--
--   ρ < 1   विघ्नक्षयः        `decay`      : the orbit reaches 0 in finite time
--   ρ = 1   सीमानुनादः        `resonance`  : the orbit is stationary
--   ρ > 1   विघ्नशाखीकरणम्    `branching`  : the orbit never reaches 0
--
-- The three cases are theorems about one ℕ-valued obstruction measure ∂ and
-- one response Γ; the spectral radius is not measured, it is the sign of the
-- step.  Nothing here is a fit.

module KFlow where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; snotz)
open import Cubical.Data.Nat.Order
  using (_<_ ; _≤_ ; zero-≤ ; suc-≤-suc ; pred-≤-pred ; ¬-<-zero ; ≤-trans ; <-trans ; ≤<-trans)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

-- ∂ ∘ Γ, already evaluated: one step of the obstruction measure.
𝒦 : Type₀
𝒦 = ℕ → ℕ

iterate : 𝒦 → ℕ → ℕ → ℕ
iterate f zero n = n
iterate f (suc k) n = iterate f k (f n)

--------------------------------------------------------------------------
-- ρ < 1
--------------------------------------------------------------------------

Contracting : 𝒦 → Type₀
Contracting f = (n : ℕ) → 0 < n → f n < n

≤zero→≡zero : (n : ℕ) → n ≤ 0 → n ≡ 0
≤zero→≡zero zero _ = refl
≤zero→≡zero (suc n) p = ⊥.rec (¬-<-zero p)

decay-fuel :
    (f : 𝒦) → Contracting f
  → (fuel n : ℕ) → n ≤ fuel
  → Σ[ k ∈ ℕ ] iterate f k n ≡ 0
decay-fuel f c fuel zero _ = 0 , refl
decay-fuel f c zero (suc n) p = ⊥.rec (snotz (≤zero→≡zero (suc n) p))
decay-fuel f c (suc fuel) (suc n) p =
  let step : f (suc n) < suc n
      step = c (suc n) (suc-≤-suc zero-≤)

      shrink : f (suc n) ≤ n
      shrink = pred-≤-pred step

      room : f (suc n) ≤ fuel
      room = ≤-trans shrink (pred-≤-pred p)

      rest : Σ[ k ∈ ℕ ] iterate f k (f (suc n)) ≡ 0
      rest = decay-fuel f c fuel (f (suc n)) room
  in suc (fst rest) , snd rest

-- विघ्नक्षयः : a strictly contracting response annihilates every obstruction.
decay : (f : 𝒦) → Contracting f → (n : ℕ) → Σ[ k ∈ ℕ ] iterate f k n ≡ 0
decay f c n = decay-fuel f c n n (0 , refl)

--------------------------------------------------------------------------
-- ρ = 1
--------------------------------------------------------------------------

Stationary : 𝒦 → ℕ → Type₀
Stationary f n = f n ≡ n

-- सीमानुनादः : the orbit is the point; no response is left to apply.
resonance :
    (f : 𝒦) (n : ℕ) → Stationary f n
  → (k : ℕ) → iterate f k n ≡ n
resonance f n s zero = refl
resonance f n s (suc k) = cong (iterate f k) s ∙ resonance f n s k

--------------------------------------------------------------------------
-- ρ > 1
--------------------------------------------------------------------------

Expanding : 𝒦 → Type₀
Expanding f = (n : ℕ) → 0 < n → n < f n

expand-positive :
    (f : 𝒦) → Expanding f
  → (k n : ℕ) → 0 < n → 0 < iterate f k n
expand-positive f e zero n p = p
expand-positive f e (suc k) n p =
  expand-positive f e k (f n) (<-trans p (e n p))

-- विघ्नशाखीकरणम् : no finite number of responses closes an expanding
-- obstruction, so the branch is permanent, not a slow decay.
branching :
    (f : 𝒦) → Expanding f
  → (k n : ℕ) → 0 < n → ¬ (iterate f k n ≡ 0)
branching f e k n p q = ¬-<-zero (subst (0 <_) q (expand-positive f e k n p))

------------------------------------------------------------------------
-- Two facts about how these theorems are USED, checked in
-- `OneStepDecidesResonanceAndNoPrefixDecidesDecay`:
--
--   oneStepIsStationary : iterate f 1 n ≡ n → Stationary f n
--       the converse of `resonance`'s hypothesis, definitionally.  So
--       ONE comparison decides the whole orbit, and a runner comparing
--       many consecutive iterates is doing redundant work.
--
--   noPrefixDecidesDecay : (N : ℕ) → …
--       for EVERY prefix length N there is a CONTRACTING map (the
--       predecessor) and a start whose orbit shows no zero within N and
--       is zero at N+1.  So no finite prefix decides `decay`, and no
--       larger constant repairs it — the statement is quantified over N.
--       What decides it is `Contracting f`, this module's own
--       hypothesis.
--
-- Compare `machine/QuestionMachine.hs` (absent from this repository), whose `flowVerdict` branches
-- on 64 iterates with no hypothesis on f, and whose header describes the
-- file as a replay of proved statements.  That one function is not; the
-- gap is exactly the hypothesis this module requires and a run cannot
-- check.
------------------------------------------------------------------------
