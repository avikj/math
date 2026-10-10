{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Scape where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_ ; fiber)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)

-- 1 · A SCAPE INDEXED ON AN INTERNAL PROPERTY is the partition of the
--     collection by that property: over each index value, the entries
--     that carry it, each with its proof.  The collection is recovered
--     exactly from its scape.

Scape : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → B → Type (ℓ-max ℓ ℓ')
Scape f b = fiber f b           -- Σ[ a ∈ A ] (f a ≡ b)

scapeOf : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
        → A ≃ (Σ[ b ∈ B ] Scape f b)
scapeOf f = isoToEquiv (iso (λ a → f a , a , refl)
                            (λ (b , a , p) → a)
                            (λ (b , a , p) i → p i , a , λ j → p (i ∧ j))
                            (λ a → refl))

-- 2 · THE SCAPE ALGEBRA.  Indexing by a composite is indexing by the
--     outer index, then by the inner one inside each cell.

compose : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
          (f : A → B) (g : B → C) (c : C)
        → Scape (g ∘ f) c ≃ (Σ[ w ∈ Scape g c ] Scape f (fst w))
compose {ℓ} {ℓ'} {ℓ''} {A} {B} {C} f g c = isoToEquiv (iso to from to-from from-to)
  where
  Cells : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  Cells = Σ[ w ∈ Scape g c ] Scape f (fst w)
  to : Scape (g ∘ f) c → Cells
  to (a , p) = (f a , p) , (a , refl)
  from : Cells → Scape (g ∘ f) c
  from ((b , q) , (a , r)) = a , cong g r ∙ q
  pack : (a : A) → g (f a) ≡ c → Cells
  pack a s = (f a , s) , (a , refl)
  lem : (a : A) (b : B) (r : f a ≡ b) (q : g b ≡ c)
      → Path Cells (pack a (cong g r ∙ q)) ((b , q) , (a , r))
  lem a b r = J (λ b' r' → (q' : g b' ≡ c)
                         → Path Cells (pack a (cong g r' ∙ q')) ((b' , q') , (a , r')))
                (λ q' → cong (pack a) (sym (lUnit q'))) r
  to-from : (w : Cells) → to (from w) ≡ w
  to-from ((b , q) , (a , r)) = lem a b r q
  from-to : (w : Scape (g ∘ f) c) → from (to w) ≡ w
  from-to (a , p) = cong (a ,_) (sym (lUnit p))

-- crossing two scapes: indexing by both properties at once is the
-- intersection of the two cells.
meet : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
       (f : A → B) (g : A → C) (b : B) (c : C)
     → Scape (λ a → f a , g a) (b , c) ≃ (Σ[ a ∈ A ] (f a ≡ b) × (g a ≡ c))
meet f g b c = isoToEquiv (iso (λ (a , p) → a , cong fst p , cong snd p)
                               (λ (a , p , q) → a , λ i → p i , q i)
                               (λ _ → refl) (λ _ → refl))

-- 3 · THE TRANSFORMATIONAL MAPS.  Direct, combined, computed, and the
--     one that drops a field: each is a map, each map's loss is its
--     scape, and dropping a field forgets exactly the whole collection.

drop : {ℓ : Level} {A : Type ℓ} → A → Unit
drop _ = tt

dropForgetsEverything : {ℓ : Level} {A : Type ℓ} → Scape (drop {A = A}) tt ≃ A
dropForgetsEverything = isoToEquiv (iso fst (λ a → a , refl)
                                        (λ a → refl)
                                        (λ (a , p) → cong (a ,_) (isSetUnit tt tt refl p)))

-- uncombining f(C) → A, B: an entry chosen in every cell of a map's
-- scape is exactly a section of the map.
uncombine : {ℓ ℓ' : Level} {A : Type ℓ} {C : Type ℓ'} (c : A → C)
          → ((x : C) → Scape c x) ≃ (Σ[ s ∈ (C → A) ] ((x : C) → c (s x) ≡ x))
uncombine c = isoToEquiv (iso (λ k → (λ x → fst (k x)) , (λ x → snd (k x)))
                              (λ (s , h) x → s x , h x)
                              (λ _ → refl) (λ _ → refl))
