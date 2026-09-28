{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Atomic observation is preserved exactly when the response square
-- commutes.  For a changed response type, an injective comparison map
-- is SUFFICIENT for the same biconditional (`square→satisfaction`
-- takes it as a hypothesis).  It is not shown to be necessary.
------------------------------------------------------------------------

module AtomicSatisfaction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_ ; _,_)

private
  variable
    ℓX ℓX′ ℓQ ℓY ℓY′ : Level

module SameResponses
  {X : Type ℓX} {X′ : Type ℓX′} {Q : Type ℓQ}
  (Y : Q → Type ℓY)
  (r : (q : Q) → X → Y q)
  (r′ : (q : Q) → X′ → Y q)
  (s : X′ → X)
  where

  ResponseSquare : Type _
  ResponseSquare = (q : Q) (x′ : X′) → r′ q x′ ≡ r q (s x′)

  _⊨_ : X → ((q : Q) → Y q) → Type _
  x ⊨ atom = (q : Q) → r q x ≡ atom q

  _⊨′_ : X′ → ((q : Q) → Y q) → Type _
  x′ ⊨′ atom = (q : Q) → r′ q x′ ≡ atom q

  -- Point atoms retain the quantifier order of the prose theorem: an
  -- outcome may be chosen separately for each probe and revised state.
  SatisfactionInvariant : Type _
  SatisfactionInvariant =
    (x′ : X′) (q : Q) (y : Y q) →
      (r′ q x′ ≡ y → r q (s x′) ≡ y)
      × (r q (s x′) ≡ y → r′ q x′ ≡ y)

  square→satisfaction : ResponseSquare → SatisfactionInvariant
  square→satisfaction square x′ q y =
    ((λ revised≡y → sym (square q x′) ∙ revised≡y) ,
     (λ old≡y → square q x′ ∙ old≡y))

  satisfaction→square : SatisfactionInvariant → ResponseSquare
  satisfaction→square invariant q x′ =
    snd (invariant x′ q (r q (s x′))) refl

module ChangedResponses
  {X : Type ℓX} {X′ : Type ℓX′} {Q : Type ℓQ}
  (Y : Q → Type ℓY) (Y′ : Q → Type ℓY′)
  (r : (q : Q) → X → Y q)
  (r′ : (q : Q) → X′ → Y′ q)
  (s : X′ → X)
  (j : (q : Q) → Y q → Y′ q)
  where

  ResponseSquare : Type _
  ResponseSquare = (q : Q) (x′ : X′) → r′ q x′ ≡ j q (r q (s x′))

  InjectiveComparisons : Type _
  InjectiveComparisons =
    (q : Q) {y z : Y q} → j q y ≡ j q z → y ≡ z

  SatisfactionInvariant : Type _
  SatisfactionInvariant =
    (x′ : X′) (q : Q) (y : Y q) →
      (r′ q x′ ≡ j q y → r q (s x′) ≡ y)
      × (r q (s x′) ≡ y → r′ q x′ ≡ j q y)

  square→satisfaction :
    InjectiveComparisons → ResponseSquare → SatisfactionInvariant
  square→satisfaction injective square x′ q y =
    ((λ revised≡jy →
        injective q (sym (square q x′) ∙ revised≡jy)) ,
     (λ old≡y → square q x′ ∙ cong (j q) old≡y))

  satisfaction→square : SatisfactionInvariant → ResponseSquare
  satisfaction→square invariant q x′ =
    snd (invariant x′ q (r q (s x′))) refl
