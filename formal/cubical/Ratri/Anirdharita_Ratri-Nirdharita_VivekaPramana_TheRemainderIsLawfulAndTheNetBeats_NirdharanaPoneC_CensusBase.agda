{-# OPTIONS --cubical --safe --guardedness #-}
module Ratri.Anirdharita_Ratri-Nirdharita_VivekaPramana_TheRemainderIsLawfulAndTheNetBeats_NirdharanaPoneC_CensusBase where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Ratri.Nirdharita_VivekaPramana_TheRemainderIsLawfulAndTheNetBeats_

censusR0 censusR1 : CensusBase
censusR0 = record { सम = 0 ; वाम = 0 }
censusR1 = record { सम = 1 ; वाम = 0 }

censusAgree-0 : CensusBase.वाम censusR0 ≡ CensusBase.वाम censusR1
censusAgree-0 = refl

-- THE VERDICT.  Green here means the field is NOT determined:
-- two inhabitants agree on every other field and are distinct.
NOT-DETERMINED : censusR0 ≡ censusR1 → ⊥
NOT-DETERMINED censusP = znots (cong CensusBase.सम censusP)
