{-# OPTIONS --cubical --safe --guardedness #-}
module Ratri.Anirdharita_NaturalMachine-MachineLoop_LoopState_NirdharanaPthreeP where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import MachineLoop

censusR0 censusR1 : LoopState
censusR0 = record { vocab = 0 ; horizon = 0 ; invented = 0 }
censusR1 = record { vocab = 0 ; horizon = 0 ; invented = 1 }

censusAgree-0 : LoopState.vocab censusR0 ≡ LoopState.vocab censusR1
censusAgree-0 = refl

censusAgree-1 : LoopState.horizon censusR0 ≡ LoopState.horizon censusR1
censusAgree-1 = refl

-- THE VERDICT.  Green here means the field is NOT determined:
-- two inhabitants agree on every other field and are distinct.
NOT-DETERMINED : censusR0 ≡ censusR1 → ⊥
NOT-DETERMINED censusP = znots (cong LoopState.invented censusP)
