{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अनिर्धारित — neither channel inverts the sign section, and the host
-- already held the reason as theorems.  The two conjectured identities
-- augment (sign b) ≡ b and relative (sign b) ≡ b fail; the host's own
-- `augment-sign` proves the first composite is CONSTANTLY zero, and
-- `relative-sign` proves the second is the doubling map.  So both
-- close as road two, each with its smallest witness at b = pos 1:
-- the composites hit 0 and 2 respectively, never 1.
------------------------------------------------------------------------

module Ratri.Anirdharita_ChargeTwoHistories_AugmentRelativeSign where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; snotz; znots)
open import Cubical.Data.Int using (ℤ; pos; injPos)
open import Cubical.Data.Empty as Empty using (⊥)
open import ChargeTwoHistories
  using (augment; relative; sign; augment-sign; relative-sign)

one : ℤ
one = pos 1

-- augment ∘ sign is constantly zero (host theorem), and 0 ≢ 1 in ℤ:
augment-NOT-DETERMINED : augment (sign one) ≡ one → ⊥
augment-NOT-DETERMINED p = znots (injPos (sym (augment-sign one) ∙ p))

-- relative ∘ sign doubles (host theorem), and 2 ≢ 1 in ℤ:
predℕ : ℕ → ℕ
predℕ 0 = 0
predℕ (suc n) = n

relative-NOT-DETERMINED : relative (sign one) ≡ one → ⊥
relative-NOT-DETERMINED p =
  snotz (cong predℕ (injPos (sym (relative-sign one) ∙ p)))
