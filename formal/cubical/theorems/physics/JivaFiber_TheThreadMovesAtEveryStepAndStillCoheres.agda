{-# OPTIONS --cubical --safe #-}

-- JivaTantu_TheThreadMovesAtEveryStepAndStillCoheres
--
-- जीव-तन्तुः — jīva, the living one (Umāsvāti, तत्त्वार्थसूत्र, opening
-- adhyāyas, ~2nd–5th c. CE: the knower persisting through karmic change);
-- tantu, thread (ordinary ; the weaver's word for continuity,
-- attested of the sacrificial line in the gveda).
-- The compound is built here for U0022
-- (collab/upstream/raw/U0022.txt (absent from this repository)).  What is
-- taken is the exact position being checked: the jīva persists AND changes —
-- against both the eternalist and the annihilationist reading — and this
-- module is that position as theorems about one term.
--
-- U0022's line:
--     "The living thread — the jīva — is a section through the changing
--      family: j_n ∈ M_n with τ_n(j_n) ≃ j_{n+1} ...  Continuity does
--      not require abandonment of change; change does not require
--      annihilation of continuity."
--
-- WHAT IS PROVED, smallest inhabited instance:
--   §1  Tantu: a family M : ℕ → Type with step maps τ; a thread is a
--       pointwise inhabitant TOGETHER WITH the section law at every
--       step.  The coherences are data, not side conditions.
--   §2  गतिः: over the constant family ℤ with τ = sucℤ, the thread
--       j n = pos n; its section law holds by refl.
--   §3  स्थैर्यं-निषिद्धम्: for EVERY thread over this τ, no two
--       consecutive moments are equal — j n ≡ j (suc n) would make an
--       integer its own successor.  So over this family a section
--       exists (§2) and immutability is uninhabitable (§3): continuity
--       and change in one checked object.  That is the whole claim.

module JivaFiber_TheThreadMovesAtEveryStepAndStillCoheres where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; sucℤ ; injPos ; injNegsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

-- ── §1 · the thread through a changing family ────────────────────────────

Tantu : (M : ℕ → Type) (τ : (n : ℕ) → M n → M (suc n)) → Type
Tantu M τ = Σ[ j ∈ ((n : ℕ) → M n) ] ((n : ℕ) → τ n (j n) ≡ j (suc n))

-- ── §2 · the living instance: the family whose step is succession ────────

गतिः : Tantu (λ _ → ℤ) (λ _ → sucℤ)
गतिः = (λ n → pos n) , (λ n → refl)

-- ── §3 · every thread over this step law moves at every step ─────────────

private
  predℕ : ℕ → ℕ
  predℕ zero    = zero
  predℕ (suc m) = m

  न-स्वोत्तरः : (n : ℕ) → ¬ (n ≡ suc n)
  न-स्वोत्तरः zero    p = snotz (sym p)
  न-स्वोत्तरः (suc n) p = न-स्वोत्तरः n (cong predℕ p)

  -- no integer is its own successor: sucℤ (pos n) = pos (suc n) and
  -- sucℤ (negsuc (suc m)) = negsuc m reduce both cases to ℕ; the
  -- boundary case negsuc zero ↦ pos zero crosses constructors, where
  -- a pos/negsuc discriminator closes it.
  भेदः : ℤ → ℕ
  भेदः (pos _)    = zero
  भेदः (negsuc _) = suc zero

  न-स्व-उत्तरः : (z : ℤ) → ¬ (z ≡ sucℤ z)
  न-स्व-उत्तरः (pos n)          q = न-स्वोत्तरः n (injPos q)
  न-स्व-उत्तरः (negsuc zero)    q = snotz (cong भेदः q)
  न-स्व-उत्तरः (negsuc (suc m)) q = न-स्वोत्तरः m (sym (injNegsuc q))

स्थैर्यं-निषिद्धम् : (t : Tantu (λ _ → ℤ) (λ _ → sucℤ))
                   (n : ℕ) → ¬ (fst t n ≡ fst t (suc n))
स्थैर्यं-निषिद्धम् t n p = न-स्व-उत्तरः (fst t n) (p ∙ sym (snd t n))

-- corollary at the exhibited thread, the concrete heartbeat of §2:
प्रतिक्षणं-चलति : (n : ℕ) → ¬ (fst गतिः n ≡ fst गतिः (suc n))
प्रतिक्षणं-चलति = स्थैर्यं-निषिद्धम् गतिः
