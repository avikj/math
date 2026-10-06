{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module SATFibre where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool using (Bool ; false ; true)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
import photon as P

data Bits : ℕ → Type where
  nil : Bits zero
  cons : {n : ℕ} → Bool → Bits n → Bits (suc n)

-- The true fibre is the satisfying assignment together with its evidence.
SAT : {n : ℕ} → (Bits n → Bool) → Type
SAT f = fiber f true

partition : {n : ℕ} (f : Bits n → Bool) → Bits n ≃ Σ Bool (fiber f)
partition = P.Fibre.lossless

-- Reproduce the entire labelled Boolean cube and map the observation over
-- it. No assignment-selection policy or backtracking procedure is defined.
-- This tree is a denotation of the runtime SUP object, not its heap layout.
data BoolCube (A : Type) : ℕ → Type where
  leaf : A → BoolCube A zero
  fork : {n : ℕ} → BoolCube A n → BoolCube A n → BoolCube A (suc n)

mapCube : {A B : Type} {n : ℕ} → (A → B) → BoolCube A n → BoolCube B n
mapCube f (leaf a) = leaf (f a)
mapCube f (fork l r) = fork (mapCube f l) (mapCube f r)

at : {A : Type} {n : ℕ} → BoolCube A n → Bits n → A
at (leaf a) nil = a
at (fork l r) (cons false xs) = at l xs
at (fork l r) (cons true xs) = at r xs

at-map : {A B : Type} {n : ℕ} (f : A → B) (c : BoolCube A n) (xs : Bits n)
  → at (mapCube f c) xs ≡ f (at c xs)
at-map f (leaf a) nil = refl
at-map f (fork l r) (cons false xs) = at-map f l xs
at-map f (fork l r) (cons true xs) = at-map f r xs

reproduce : (n : ℕ) → BoolCube (Bits n) n
reproduce zero = leaf nil
reproduce (suc n) = fork (mapCube (cons false) (reproduce n))
                        (mapCube (cons true) (reproduce n))

reproduce-exact : (n : ℕ) (xs : Bits n) → at (reproduce n) xs ≡ xs
reproduce-exact zero nil = refl
reproduce-exact (suc n) (cons false xs) =
  at-map (cons false) (reproduce n) xs ∙ cong (cons false) (reproduce-exact n xs)
reproduce-exact (suc n) (cons true xs) =
  at-map (cons true) (reproduce n) xs ∙ cong (cons true) (reproduce-exact n xs)

reduce-carried : {n : ℕ} (f : Bits n → Bool) → BoolCube (P.Carrier.Carrier f) n
reduce-carried {n} f = mapCube (P.Carrier.descend f) (reproduce n)

reduction-exact : {n : ℕ} (f : Bits n → Bool) (xs : Bits n)
  → at (reduce-carried f) xs ≡ P.Carrier.descend f xs
reduction-exact {n} f xs = at-map (P.Carrier.descend f) (reproduce n) xs
  ∙ cong (P.Carrier.descend f) (reproduce-exact n xs)

-- Every specified assignment evolution survives the carrier presentation.
module Continuing {n : ℕ} (f : Bits n → Bool) (step : Bits n → Bits n) where
  retained-future : (a : Bits n)
    → P.Orbit.mapO (P.Carrier.carry-transport f) (P.Orbit.unfold step a)
      ≡ P.Orbit.unfold (P.Carrier.Φ-carrier f step) (P.Carrier.descend f a)
  retained-future = P.Nucleus.transport-orbit f step

-- A fixed-order residual's meaning is its complete suffix behaviour.
Residual : ℕ → Type
Residual n = Bits n → Bool

same-future-is-path : {n : ℕ} (f g : Residual n)
  → ((xs : Bits n) → f xs ≡ g xs) → f ≡ g
same-future-is-path f g = funExt

cofactor : {n : ℕ} → Residual (suc n) → Bool → Residual n
cofactor f b xs = f (cons b xs)

same-future-steps : {n : ℕ} (f g : Residual (suc n))
  → f ≡ g → (b : Bool) → cofactor f b ≡ cofactor g b
same-future-steps f g p b = cong (λ h → cofactor h b) p

-- Any exact representation must separate distinguishable residuals.
-- Applied to a finite reachable set, this is the injection/lower-bound
-- argument behind minimum width at each fixed-order decision layer.
module Minimal {n : ℕ} (S : Type) (encode : Residual n → S)
  (decode : S → Residual n)
  (faithful : (f : Residual n) → decode (encode f) ≡ f) where
  code-equality-implies-future-equality : (f g : Residual n)
    → encode f ≡ encode g → f ≡ g
  code-equality-implies-future-equality f g p =
    sym (faithful f) ∙ cong decode p ∙ faithful g

  distinguishable-cannot-merge : (f g : Residual n) (xs : Bits n)
    → (f xs ≡ g xs → ⊥)
    → encode f ≡ encode g → ⊥
  distinguishable-cannot-merge f g xs apart p =
    apart (cong (λ h → h xs) (code-equality-implies-future-equality f g p))

-- An exhaustive binary decision tree has this many leaves. This is a
-- representation-specific count, not an HVM interaction-count theorem.
leaves : ℕ → ℕ
leaves zero = 1
leaves (suc n) = leaves n + leaves n
