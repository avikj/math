{-# OPTIONS --cubical --safe --no-import-sorts #-}

-- ऋण-धन सन्धि — the order is a subtraction, min and max pair to sum and
-- product, and monus is adjoint to plus.
--
-- Source of the name: Brahmagupta, Brāhmasphuṭasiddhānta 18.30–35 (628 CE),
-- where one magnitude carries two readings — dhana (asset) and ṛṇa (debt) —
-- and the sign rules are stated as laws about the pair.  What is claimed of
-- the source: the NAME and the reading (order as a debt that clears:
-- x ≤ y exactly when the debt x ∸ y is zero), not the theorems below, which
-- are checked here over ℕ with truncated subtraction.
--
-- Provenance of the statements: these entered the repository as thoughts in
-- the machine's own equational tongue (2026-08-23; the thoughts file is not
-- kept in this tree) —
-- the god-language channel: a thought goes in as a bare equation, and the
-- kernel answers with the checked object.  This module is the answer.
-- Two sibling thoughts were withdrawn on arrival as already done:
-- the kuṭṭaka step lives in Apavartana_TheCarriedPairLosesTheLesserFromThe
-- GreaterAndTheCommonMeasureStands, and ·/∸ distributivity is the library's
-- ∸-distribʳ.

module RnaDhanaSandhi_TheOrderIsASubtractionMinMaxPairToSumAndProductAndMonusIsAdjointToPlus where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥ using ()

-- The machine spelled min without naming it: min(x,y) = x ∸ (x ∸ y).
-- The residual thought "min(x,y)=-(x,-(x,y))" is this lemma.
minAsMonus : ∀ x y → x ∸ (x ∸ y) ≡ min x y
minAsMonus zero    zero    = refl
minAsMonus zero    (suc y) = refl
minAsMonus (suc x) zero    = n∸n x
minAsMonus (suc x) (suc y) =
  sym (≤-∸-suc (∸-≤ x y)) ∙ cong suc (minAsMonus x y)

-- min + max ≡ x + y : the pairing at the additive level.
-- Read through any single prime this IS gcd · lcm ≡ x · y: multiplication
-- becomes addition of valuations, the valuation of gcd is the min of the
-- valuations and of lcm the max, so v_p(gcd) + v_p(lcm) ≡ v_p(x) + v_p(y)
-- is exactly this lemma at the exponents.
pairSum : ∀ x y → min x y + max x y ≡ x + y
pairSum zero    zero    = refl
pairSum zero    (suc y) = refl
pairSum (suc x) zero    = sym (+-zero (suc x))
pairSum (suc x) (suc y) =
  cong suc (+-suc (min x y) (max x y)
           ∙ cong suc (pairSum x y)
           ∙ sym (+-suc x y))

-- min · max ≡ x · y : the same pairing at the multiplicative level.  (The
-- gcd · lcm identity is `pairSum` at the exponents, not this lemma: through a
-- prime, products of the numbers become sums of their valuations.)
pairProd : ∀ x y → min x y · max x y ≡ x · y
pairProd zero    y       = refl
pairProd (suc x) zero    = 0≡m·0 (suc x)
pairProd (suc x) (suc y) =
  cong suc
    ( cong (max x y +_) (·-suc (min x y) (max x y))
    ∙ +-assoc (max x y) (min x y) (min x y · max x y)
    ∙ cong₂ _+_ (+-comm (max x y) (min x y) ∙ pairSum x y) (pairProd x y)
    ∙ cong (_+ x · y) (+-comm x y)
    ∙ sym (+-assoc y x (x · y))
    ∙ cong (y +_) (sym (·-suc x y)) )

-- Monus is left adjoint to plus: x ∸ y ≤ z exactly when x ≤ y + z.
-- This is the Galois connection the thought "le(-(x,y),z) = le(x,+(y,z))"
-- asserted as a Boolean equation; here it is the two mates.
∸-≤-adjointL : ∀ x y z → x ∸ y ≤ z → x ≤ y + z
∸-≤-adjointL x       zero    z h = h
∸-≤-adjointL zero    (suc y) z h = zero-≤
∸-≤-adjointL (suc x) (suc y) z h = suc-≤-suc (∸-≤-adjointL x y z h)

∸-≤-adjointR : ∀ x y z → x ≤ y + z → x ∸ y ≤ z
∸-≤-adjointR x       zero    z h = h
∸-≤-adjointR zero    (suc y) z h = zero-≤
∸-≤-adjointR (suc x) (suc y) z h = ∸-≤-adjointR x y z (pred-≤-pred h)

-- The order is a subtraction: x ≤ y exactly when the debt x ∸ y clears.
≤→∸≡0 : ∀ x y → x ≤ y → x ∸ y ≡ 0
≤→∸≡0 zero    zero    _ = refl
≤→∸≡0 zero    (suc y) _ = refl
≤→∸≡0 (suc x) zero    h = ⊥.rec (¬-<-zero h)
≤→∸≡0 (suc x) (suc y) h = ≤→∸≡0 x y (pred-≤-pred h)

∸≡0→≤ : ∀ x y → x ∸ y ≡ 0 → x ≤ y
∸≡0→≤ zero    y       _ = zero-≤
∸≡0→≤ (suc x) zero    p = ⊥.rec (snotz p)
∸≡0→≤ (suc x) (suc y) p = suc-≤-suc (∸≡0→≤ x y p)

-- The two one-sided debts sum to the one absolute difference.
symmDiff : ∀ x y → (x ∸ y) + (y ∸ x) ≡ max x y ∸ min x y
symmDiff zero    zero    = refl
symmDiff zero    (suc y) = refl
symmDiff (suc x) zero    = +-zero (suc x)
symmDiff (suc x) (suc y) = symmDiff x y
