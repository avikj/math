{-# OPTIONS --cubical --safe --guardedness #-}
module Ratri.Anirdharita_NaturalMachine-ArityOfRepair_Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import ArityOfRepair

censusR0 censusR1 : Bounds
censusR0 = record { lo = 0 ; hi = 0 }
censusR1 = record { lo = 1 ; hi = 0 }

censusAgree-0 : Bounds.hi censusR0 ≡ Bounds.hi censusR1
censusAgree-0 = refl

-- THE VERDICT.  Green here means the field is NOT determined:
-- two inhabitants agree on every other field and are distinct.
NOT-DETERMINED : censusR0 ≡ censusR1 → ⊥
NOT-DETERMINED censusP = znots (cong Bounds.lo censusP)
