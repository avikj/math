{-# OPTIONS --cubical --safe --guardedness #-}
module Ratri.Anirdharita_NaturalMachine-RewriteCertificateMul_Env where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import RewriteCertificateMul

censusR0 censusR1 : Env
censusR0 = record { x = 0 ; y = 0 ; z = 0 ; u = 0 ; v = 0 ; w = 0 }
censusR1 = record { x = 0 ; y = 0 ; z = 0 ; u = 0 ; v = 1 ; w = 0 }

censusAgree-0 : Env.x censusR0 ≡ Env.x censusR1
censusAgree-0 = refl

censusAgree-1 : Env.y censusR0 ≡ Env.y censusR1
censusAgree-1 = refl

censusAgree-2 : Env.z censusR0 ≡ Env.z censusR1
censusAgree-2 = refl

censusAgree-3 : Env.u censusR0 ≡ Env.u censusR1
censusAgree-3 = refl

censusAgree-4 : Env.w censusR0 ≡ Env.w censusR1
censusAgree-4 = refl

-- THE VERDICT.  Green here means the field is NOT determined:
-- two inhabitants agree on every other field and are distinct.
NOT-DETERMINED : censusR0 ≡ censusR1 → ⊥
NOT-DETERMINED censusP = znots (cong Env.v censusP)
