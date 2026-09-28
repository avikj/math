{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ConstantBoundNotFunctionBound
--
-- A CONSTANT that cannot be improved by a constant, and a FUNCTION that
-- improves it.  The quantifier the summary moved, made a type.
--
-- `collab/messages/workers/20260812T144712.509661Z--claude_aime_body--
-- 0003.md` (absent from this repository)):
--
--   "Φ₇(2)=127 prime … Φ₁₇(2)=131071 prime … So Y≥1 is sharp, **no
--    function of (b,n) improves it**."
--
-- The two witnesses are correct and establish that the CONSTANT bound 1
-- cannot be raised to a constant > 1.  They do not establish the
-- quantified claim about FUNCTIONS of (b,n): the audit's refutation is
-- Φ₁₁(2) = 2047 = 23·89, where the yield is 2, so the function equal to
-- 2 at (2,11) and 1 elsewhere is a valid bound strictly better than the
-- constant.  The three arithmetic facts:
-- 2⁷−1 = 127 and 2¹⁷−1 = 131071 are prime, 2¹¹−1 = 2047
-- = 23·89, and for prime n the primitive part Φ_n(2) is all of 2ⁿ−1.
--
-- NO LEXICAL SIGNATURE.  "No function of (b,n) improves it" and "the
-- constant 1 cannot be improved" share no distinguishing word; the
-- defect is a quantifier promotion inside a sentence in which every
-- word is correct.
--
-- HEADLINE TERMS
--   Y                      the yield, with its three known values
--   constant-sharp         no CONSTANT bound exceeds 1
--   Y-is-a-bound           Y itself is a valid function bound
--   Y-improves            ... and exceeds 1 at (2,11)
--   dropped-scope-false    so "no function improves it" implies ⊥
--
-- The companion control is
-- `NaturalMachine/Control/FunctionBoundFromConstant.agda`.
------------------------------------------------------------------------

module ConstantBoundNotFunctionBound where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl ; ¬m<m)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)

------------------------------------------------------------------------
-- 0.  The yield.  Only the three arguments the source sentence uses are
--     distinguished: Y(2,11) = 2 because 2047 = 23·89, and the two
--     Mersenne-prime arguments (2,7), (2,17) give 1, as does every
--     other argument in this model.

Y : ℕ → ℕ → ℕ
Y _ 11 = 2
Y _ _  = 1

Y-at-7  : Y 2 7  ≡ 1
Y-at-7  = refl

Y-at-17 : Y 2 17 ≡ 1
Y-at-17 = refl

Y-at-11 : Y 2 11 ≡ 2
Y-at-11 = refl

------------------------------------------------------------------------
-- 1.  The two kinds of bound.

ConstantBound : ℕ → Type
ConstantBound c = (b n : ℕ) → c ≤ Y b n

FunctionBound : (ℕ → ℕ → ℕ) → Type
FunctionBound F = (b n : ℕ) → F b n ≤ Y b n

------------------------------------------------------------------------
-- 2.  What the two Mersenne witnesses DO prove: no constant beats 1.

constant-sharp : (c : ℕ) → ConstantBound c → c ≤ 1
constant-sharp c cb = subst (c ≤_) Y-at-7 (cb 2 7)

------------------------------------------------------------------------
-- 3.  What they do NOT prove: a function bound that beats it.

Y-is-a-bound : FunctionBound Y
Y-is-a-bound b n = ≤-refl

Y-improves : Σ[ b ∈ ℕ ] Σ[ n ∈ ℕ ] (2 ≤ Y b n)
Y-improves = 2 , 11 , subst (2 ≤_) (sym Y-at-11) ≤-refl

dropped-scope-false :
  ((F : ℕ → ℕ → ℕ) → FunctionBound F → (b n : ℕ) → F b n ≤ 1) → ⊥
dropped-scope-false claim = ¬m<m (claim Y Y-is-a-bound 2 11)
