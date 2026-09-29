{-# OPTIONS --cubical --safe --guardedness #-}
module Ratri.Anirdharita_EGBRootedNet_Jewel where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import RootedNet

censusR0 censusR1 : Jewel
censusR0 = record { centre = 0 ; radius = 0 }
censusR1 = record { centre = 1 ; radius = 0 }

censusAgree-0 : Jewel.radius censusR0 ≡ Jewel.radius censusR1
censusAgree-0 = refl

-- THE VERDICT.  Green here means the field is NOT determined:
-- two inhabitants agree on every other field and are distinct.
NOT-DETERMINED : censusR0 ≡ censusR1 → ⊥
NOT-DETERMINED censusP = znots (cong Jewel.centre censusP)
