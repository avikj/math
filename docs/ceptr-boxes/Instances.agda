{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Univalence using (ua)

private
  variable
    ℓ : Level

-- a running instance: its present state and the rest of its running,
-- as one object rather than a family indexed by time.
record Instance (A : Type ℓ) : Type ℓ where
  coinductive
  field
    here : A
    next : Instance A
open Instance

unfold : {A : Type ℓ} (Φ : A → A) → A → Instance A
here (unfold Φ a) = a
next (unfold Φ a) = unfold Φ (Φ a)

-- synchrony: agreement now, and synchrony of what follows.
record _≈_ {A : Type ℓ} (x y : Instance A) : Type ℓ where
  coinductive
  field
    ≈here : here x ≡ here y
    ≈next : next x ≈ next y
open _≈_

bisim : {A : Type ℓ} {x y : Instance A} → x ≈ y → x ≡ y
here (bisim p i) = ≈here p i
next (bisim p i) = bisim (≈next p) i

path→bisim : {A : Type ℓ} {x y : Instance A} → x ≡ y → x ≈ y
≈here (path→bisim p) = λ i → here (p i)
≈next (path→bisim p) = path→bisim (λ i → next (p i))

iso1 : {A : Type ℓ} {x y : Instance A} (p : x ≡ y) → bisim (path→bisim p) ≡ p
here (iso1 p i j) = here (p j)
next (iso1 p i j) = iso1 (λ i → next (p i)) i j

iso2 : {A : Type ℓ} {x y : Instance A} (p : x ≈ y) → path→bisim (bisim p) ≡ p
≈here (iso2 p i) = ≈here p
≈next (iso2 p i) = iso2 (≈next p) i

-- TWO INSTANCES ARE ONE RECEPTOR EXACTLY WHEN THEY RUN IN SYNCHRONY:
-- identity of instances is bisimulation, by univalence.
path≃bisim : {A : Type ℓ} {x y : Instance A} → (x ≡ y) ≃ (x ≈ y)
path≃bisim = isoToEquiv (iso path→bisim bisim iso2 iso1)

path≡bisim : {A : Type ℓ} {x y : Instance A} → (x ≡ y) ≡ (x ≈ y)
path≡bisim = ua path≃bisim
