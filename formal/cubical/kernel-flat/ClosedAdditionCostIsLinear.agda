{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ClosedAdditionCostIsLinear
--
-- Widening WindingCostIsUnarySize past the single-variable case: reducing a
-- fully CLOSED sum `unary a + unary b` to its normal form takes b+1 steps —
-- linear in the second operand's symbolic (unary) size, with no free
-- variables anywhere. Same winding-as-cost picture, now for closed terms.
------------------------------------------------------------------------

module ClosedAdditionCostIsLinear where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Kernel.RewriteCertificate
open import WindingCostIsUnarySize using (unary ; iterSuc ; len ; underSuc ; len-underSuc)

-- reduce (unary a + unary b) to sucᵇ (unary a), its normal form
addClosed : (a b : ℕ) → Derivation (add (unary a) (unary b)) (iterSuc b (unary a))
addClosed a zero    = then-step (add-zero (unary a)) (done (unary a))
addClosed a (suc m) = then-step (add-suc (unary a) (unary m)) (underSuc (addClosed a m))

-- cost = b+1, linear in the second operand's unary size
len-addClosed : (a b : ℕ) → len (addClosed a b) ≡ suc b
len-addClosed a zero    = refl
len-addClosed a (suc m) =
  cong (λ (k : ℕ) → suc k) (len-underSuc (addClosed a m) ∙ len-addClosed a m)
