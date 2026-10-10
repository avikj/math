{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Provenance where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; invEq ; idEquiv ; secEq ; retEq)
open import Cubical.Foundations.Univalence using (ua ; uaβ ; ~uaβ)
open import Cubical.Data.Bool using (Bool ; true ; false ; notEquiv ; true≢false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' ℓ'' : Level

-- two grades of agreement between two nodes.  IDENTIFIED: the carriers
-- are identified.  SOURCED: and the identification respects where each
-- side says its element came from.
Identified : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
Identified A B = A ≃ B

Sourced : {A : Type ℓ} {B : Type ℓ'} {G : Type ℓ''}
  → (A → G) → (B → G) → Identified A B → Type (ℓ-max ℓ ℓ'')
Sourced {A = A} pA pB e = (a : A) → pB (equivFun e a) ≡ pA a

-- transport along an identification computes, both ways, and the
-- round trip is exhibited: the identification is held, not cited.
cross : {A B : Type ℓ} → Identified A B → A → B
cross e a = transport (ua e) a

crossComputes : {A B : Type ℓ} (e : Identified A B) (a : A) → cross e a ≡ equivFun e a
crossComputes e a = uaβ e a

back : {A B : Type ℓ} → Identified A B → B → A
back e b = transport (sym (ua e)) b

backComputes : {A B : Type ℓ} (e : Identified A B) (b : B) → back e b ≡ invEq e b
backComputes e b = ~uaβ e b

thereAndBack : {A B : Type ℓ} (e : Identified A B) (a : A) → back e (cross e a) ≡ a
thereAndBack e a =
  backComputes e (cross e a) ∙ cong (invEq e) (crossComputes e a) ∙ retEq e a

-- THE THEOREM.  One identification — the identity, the least
-- contentious there is — and two peers recording different sources
-- for the same element.  The identification is silent about it.
sourceA sourceB : Bool → Bool
sourceA _ = true
sourceB _ = false

theCarriersAreIdentified : Identified Bool Bool
theCarriersAreIdentified = idEquiv Bool

theSourcesDisagree : Sourced sourceA sourceB theCarriersAreIdentified → ⊥
theSourcesDisagree m = true≢false (sym (m true))

-- no function takes an identification of carriers to an agreement of
-- sources: provenance is carried alongside, or it is gone.
provenanceIsNotCarried :
  ({A B G : Type} (pA : A → G) (pB : B → G) (e : Identified A B) → Sourced pA pB e) → ⊥
provenanceIsNotCarried f = theSourcesDisagree (f sourceA sourceB theCarriersAreIdentified)

-- and the ends do not determine the route: knowing that two copies are
-- identifiable does not hand you the identification.
routesAreNotUnique : ¬ (idEquiv Bool ≡ notEquiv)
routesAreNotUnique p = true≢false (cong (λ q → equivFun q true) p)

-- so the object a peer must keep is the triple, not the value.
record Transport (A B : Type ℓ) : Type ℓ where
  constructor _⟨_⟩_
  field
    from : A
    via  : Identified A B
    to   : B

carry : {A B : Type ℓ} (e : Identified A B) (a : A) → Transport A B
carry e a = a ⟨ e ⟩ cross e a
