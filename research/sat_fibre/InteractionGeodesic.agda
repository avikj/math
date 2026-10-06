{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module InteractionGeodesic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using (⊥)

-- The local interaction-net diamond, stated at the exact one-step grade.
-- The theorem is generic; a concrete HVM correspondence must instantiate
-- Step and discharge this hypothesis for the selected runtime/demand rules.
module RandomDescent (S : Type) (Step : S → S → Type)
  (diamond : {s a b : S} → Step s a → Step s b
    → (a ≡ b) ⊎ (Σ[ c ∈ S ] (Step a c × Step b c))) where

  data Trace : ℕ → S → S → Type where
    done : {s : S} → Trace zero s s
    stepTrace : {n : ℕ} {s u t : S} → Step s u → Trace n u t → Trace (suc n) s t

  Normal : S → Type
  Normal t = (u : S) → Step t u → ⊥

  -- Any available first interaction removes exactly one unit from any
  -- terminating reduction to the same normal form. It cannot make a detour.
  peel : {n : ℕ} {s u t : S} → Step s u → Trace (suc n) s t
    → Normal t → Trace n u t
  peel {zero} jump (stepTrace first done) normal with diamond first jump
  ... | inl same = subst (λ v → Trace zero v _) same done
  ... | inr (z , left , right) = Empty.rec (normal z left)
  peel {suc n} jump (stepTrace first rest) normal with diamond first jump
  ... | inl same = subst (λ v → Trace (suc n) v _) same rest
  ... | inr (z , left , right) = stepTrace right (peel left rest normal)

  -- Random descent: all complete reductions of THIS OBJECT to THIS normal
  -- form have the same length, not merely the same semantic answer.
  normal-length-zero : {n : ℕ} {s t : S} → Normal s → Trace n s t → n ≡ zero
  normal-length-zero normal done = refl
  normal-length-zero normal (stepTrace first rest) = Empty.rec (normal _ first)

  zero-endpoints : {s t : S} → Trace zero s t → s ≡ t
  zero-endpoints done = refl

  same-normalization-length : {n m : ℕ} {s t : S}
    → Trace n s t → Trace m s t → Normal t → n ≡ m
  same-normalization-length done other normal = sym (normal-length-zero normal other)
  same-normalization-length {m = zero} (stepTrace first rest) other normal =
    Empty.rec (normal _ (subst (λ s → Step s _) (zero-endpoints other) first))
  same-normalization-length {m = suc m} (stepTrace first rest) other normal =
    cong suc (same-normalization-length rest (peel first other normal) normal)

  normalization-is-geodesic : {n m : ℕ} {s t : S}
    → Trace n s t → Trace m s t → Normal t → n ≤ m
  normalization-is-geodesic chosen competitor normal =
    subst (_ ≤_) (same-normalization-length chosen competitor normal) ≤-refl
