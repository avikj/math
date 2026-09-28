{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सङ्ख्या — saṅkhyā, the COUNT of the prastāra.  Piṅgala's sixth
-- pratyaya: the number of distinct n-place patterns, 2^n at base two,
-- stated together with the process that computes it by repeated
-- squaring-and-doubling on the binary expansion of n.  Pigala,
-- *Chandastra* 8.23-35 (~300 BCE); the process worked out in
-- Halyudha, *Mtasajvan* (10th c.).
--
-- सङ्ख्या names the OBJECT b ^ n — the count of n-place base-b words.
-- The base-b generalisation (Pigala counts base two) and the
-- group-theoretic reading below are the atlas's, not Pigala's.
--
-- WHAT IT PROVES, and why it is here.  Vahita_… checked the carry
-- extension  0 → ℤ/b → ℤ/b^{n+1} → ℤ/b^n → 0  does not split at its
-- MINIMAL instance (b = 2, one digit) by the kernel-of-forgetting.
-- runtime/atlas/residual.py (absent from this repository)'s splitting_exponent_argument computes the
-- GENERAL certificate — ATLAS_OF_N §8 Prop. 2.11: the class vanishes
-- iff the extension splits iff the two exponents agree — but only per
-- (b, n) it is handed.  This module proves that certificate for EVERY
-- (b ≥ 2, n ≥ 1):
--
--   §1  उपलब्धि — b ∣ b^{n+1}: the carry digit's order b divides the
--       n+1-place register's order, so lcm(b^{n+1}, b) = b^{n+1}; and
--       the same divisibility at exponent n gives exponent_lhs =
--       lcm(b^n, b) = b^n (the split group ℤ/b^n ⊕ ℤ/b has exponent b^n).
--   §2  वृद्धि — b^n < b^{n+1} for b ≥ 2: the count grows a FULL factor
--       of the base at each place.  So exponent_lhs = b^n < b^{n+1} =
--       exponent_rhs: the two exponents disagree at every (b, n).
--   §3  the certificate assembled: by_exponent holds for all (b ≥ 2, n),
--       so by Prop. 2.11 the carry extension never splits — the top
--       digit is BOUND to the register, not free (कः पक्षो बद्ध).
--
-- The fibre reading (README §THE LAW): the carry is the fibre a
-- carry-free reading ℤ/b^n ⊕ ℤ/b would make free; the strict growth of
-- the count is exactly why it cannot be — visibility of the top place
-- is not manufacturable by keeping the digits apart.
--
-- Sources for the mathematics: runtime/atlas/residual.py (absent from this repository)
-- Prop. 2.11.  Complements Vahita_…  (the b=2,n=1 group instance).
------------------------------------------------------------------------

module Count_TheBaseAryCountGrowsAFullFactorEachPlaceSoTheCarryNeverSplits where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility

------------------------------------------------------------------------
-- §1  उपलब्धि — the carry digit's order divides the register's order.
--     b ∣ b^{n+1}, hence lcm collapses (lcm(b^{k+1}, b) = b^{k+1}, and
--     at exponent n ≥ 1 : lcm(b^n, b) = b^n).  b ^ suc n ≡ b · b ^ n.
------------------------------------------------------------------------

उपलब्धिः : (b n : ℕ) → b ∣ (b ^ (suc n))
उपलब्धिः b n = ∣-left (b ^ n)

------------------------------------------------------------------------
-- §2  वृद्धि — the count grows a full factor of the base each place.
------------------------------------------------------------------------

-- b^n is positive when the base is.
शून्यात्परम् : (b n : ℕ) → 0 < b → 0 < b ^ n
शून्यात्परम् b zero    _   = ≤-refl
शून्यात्परम् b (suc n) 0<b =
  ≤-trans (शून्यात्परम् b n 0<b)
          (subst (_≤ b · b ^ n) (·-identityˡ (b ^ n))
                 (≤-·k {1} {b} {b ^ n} 0<b))

वृद्धिः : (b n : ℕ) → 1 < b → b ^ n < b ^ (suc n)
वृद्धिः b n 1<b =
  subst (λ z → z < b · b ^ n) (·-identityˡ (b ^ n))
    (subst (λ z → 1 · z < b · z) (sym sp)
           (<-·sk {1} {b} {predℕ (b ^ n)} 1<b))
  where
  0<b : 0 < b
  0<b = ≤<-trans zero-≤ 1<b
  ≢0 : ¬ (b ^ n ≡ 0)
  ≢0 e = ¬-<-zero (subst (1 ≤_) e (शून्यात्परम् b n 0<b))
  sp : b ^ n ≡ suc (predℕ (b ^ n))
  sp = suc-predℕ (b ^ n) ≢0

------------------------------------------------------------------------
-- §3  the certificate assembled.  For every b ≥ 2 and n ≥ 1 the two
--     exponents of Prop. 2.11 disagree: exponent_lhs = lcm(b^n, b) = b^n
--     (from §1's divisibility) and exponent_rhs = b^{n+1}, and b^n <
--     b^{n+1} (§2).  by_exponent = exponent_lhs < exponent_rhs holds
--     UNCONDITIONALLY in (b, n), so the carry class never vanishes: the
--     extension never splits.  This is the general form of
--     residual.py (absent from this repository)'s per-instance splitting_exponent_argument.
------------------------------------------------------------------------

घातविच्छेदः : (b n : ℕ) → 1 < b → b ^ (suc n) < b ^ (suc (suc n))
घातविच्छेदः b n 1<b = वृद्धिः b (suc n) 1<b
