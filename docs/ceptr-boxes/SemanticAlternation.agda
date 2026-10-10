{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module SemanticAlternation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; idEquiv ; invEquiv ; compEquiv)
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua ; uaβ ; EquivContr)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Relation.Nullary using (¬_)

-- two symbols over one structure.
data Age : Type where
  age : ℕ → Age

data ShoeSize : Type where
  size : ℕ → ShoeSize

years : Age → ℕ
years (age n) = n

units : ShoeSize → ℕ
units (size n) = n

-- a symbol IS an identification with its structure, held as data.
ageStructure : Age ≃ ℕ
ageStructure = isoToEquiv (iso years age (λ n → refl) λ { (age n) → refl })

sizeStructure : ShoeSize ≃ ℕ
sizeStructure = isoToEquiv (iso units size (λ n → refl) λ { (size n) → refl })

-- a transcoder: down one symbol to the structure, up the other.
transcoder : Age ≃ ShoeSize
transcoder = compEquiv ageStructure (invEquiv sizeStructure)

-- transcoding is transport along it, and it computes.
transcode : Age → ShoeSize
transcode = transport (ua transcoder)

transcodeComputes : (n : ℕ) → transcode (age n) ≡ size n
transcodeComputes n = uaβ transcoder (age n)

-- the structure alone fixes no symbol: ℕ carries a self-identification
-- that is not the identity, so "same structure" names no transcoder.
swap : ℕ → ℕ
swap zero          = suc zero
swap (suc zero)    = zero
swap (suc (suc n)) = suc (suc n)

swap-swap : (n : ℕ) → swap (swap n) ≡ n
swap-swap zero          = refl
swap-swap (suc zero)    = refl
swap-swap (suc (suc n)) = refl

swapEquiv : ℕ ≃ ℕ
swapEquiv = isoToEquiv (iso swap swap swap-swap swap-swap)

swapIsNotTheIdentity : ¬ swapEquiv ≡ idEquiv ℕ
swapIsNotTheIdentity p = snotz (cong (λ e → equivFun e zero) p)

structureFixesNoSymbol : ¬ isProp (ℕ ≃ ℕ)
structureFixesNoSymbol ip = swapIsNotTheIdentity (ip swapEquiv (idEquiv ℕ))

-- so there are two transcoders Age → ShoeSize, and they disagree.
otherTranscoder : Age ≃ ShoeSize
otherTranscoder = compEquiv ageStructure (compEquiv swapEquiv (invEquiv sizeStructure))

transcodersDisagree : ¬ transcoder ≡ otherTranscoder
transcodersDisagree p =
  snotz (sym (cong (λ e → units (equivFun e (age zero))) p))

-- but a symbol TOGETHER WITH its reading of the structure is unique:
-- the space of (type, identification with ℕ) is a point.
oneSymbolOverTheStructure : isContr (Σ[ S ∈ Type ] (S ≃ ℕ))
oneSymbolOverTheStructure = EquivContr ℕ
