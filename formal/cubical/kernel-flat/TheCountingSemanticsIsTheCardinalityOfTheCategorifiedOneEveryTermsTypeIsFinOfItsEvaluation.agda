{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheCountingSemanticsIsTheCardinalityOfTheCategorifiedOneEveryTermsTypeIsFinOfItsEvaluation
--
-- The categorified interpretation ⟦_⟧ sends
-- zero ↦ ⊥, suc ↦ Unit ⊎ −, add ↦ ⊎ — which is EXACTLY the structure of
-- `Cubical.Data.SumFin`'s `Fin` (Fin 0 = ⊥, Fin (suc n) = Unit ⊎ Fin n).
-- So if each variable is interpreted as `Fin` of its numeric value
-- (finEnv), then for EVERY term t and environment ρ,
--
--     ⟦ t ⟧ (finEnv ρ)  ≃  Fin (eval t ρ).
--
-- No `ClosedTm` restriction is needed: interpreting `var` as `Fin (x ρ)`
-- makes the base case `Fin (eval var ρ)` on the nose.  The counting
-- semantics `eval` is therefore the CARDINALITY (the decategorification,
-- π₀ of a finite type) of the categorified semantics ⟦_⟧ — the "keeps a
-- cardinality and drops the bijection" claim, made precise.
--
-- WHAT IS PROVEN, --safe, no postulates, structural:
--   finSum   Fin m ⊎ Fin n ≃ Fin (m + n)  (induction on m; reassociation).
--   card     (t : Tm)(ρ : Env) → ⟦ t ⟧ (finEnv ρ) ≃ Fin (eval t ρ)  — every
--            term's type-interpretation is Fin of its evaluation.
--   cardPath the same as a PATH between types, by univalence:
--            ⟦ t ⟧ (finEnv ρ) ≡ Fin (eval t ρ).
--
-- READING.  This does not contradict §4/§5 of the decategorification
-- module: ⟦_⟧ has MORE than a cardinality (it carries the transposition a
-- count cannot — comm-loop), but its cardinality IS `eval`.  Both hold:
-- the categorified semantics refines the counting one, and the counting
-- one is its cardinality.  Bhskara's akapa distinction (the count of
-- arrangements vs. an arrangement) as a checked equivalence.
------------------------------------------------------------------------

module TheCountingSemanticsIsTheCardinalityOfTheCategorifiedOneEveryTermsTypeIsFinOfItsEvaluation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; idEquiv ; compEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Unit using (Unit)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Sum.Properties
  using (⊎-equiv ; ⊎-swap-≃ ; ⊎-assoc-≃ ; ⊎-IdR-⊥-≃)
open import Cubical.Data.SumFin using (Fin)   -- Fin 0 = ⊥ ; Fin (suc n) = Unit ⊎ Fin n

open import Kernel.RewriteCertificate using (Tm ; var ; yvar ; zvar ; uvar ; vvar ; wvar
                                     ; zero ; suc ; add ; Env ; env ; eval)
open import TheCountingSemanticsIsADecategorificationAndTheBitItDropsIsASymmetry
  using (TEnv ; tenv ; ⟦_⟧)

open Env
open TEnv

------------------------------------------------------------------------
-- Fin distributes over + as a ⊎ (structural on m; reassociation only).
------------------------------------------------------------------------

⊥⊎ : {B : Type₀} → (⊥ ⊎ B) ≃ B
⊥⊎ = compEquiv ⊎-swap-≃ ⊎-IdR-⊥-≃

finSum : (m n : ℕ) → (Fin m ⊎ Fin n) ≃ Fin (m + n)
finSum zero    n = ⊥⊎
finSum (suc m) n = compEquiv ⊎-assoc-≃ (⊎-equiv (idEquiv Unit) (finSum m n))

------------------------------------------------------------------------
-- interpret each of the six coordinates as Fin of its numeric value.
------------------------------------------------------------------------

finEnv : Env → TEnv
finEnv ρ = tenv (Fin (x ρ)) (Fin (y ρ)) (Fin (z ρ))
                (Fin (u ρ)) (Fin (v ρ)) (Fin (w ρ))

------------------------------------------------------------------------
-- every term's type-interpretation is Fin of its evaluation.
------------------------------------------------------------------------

card : (t : Tm) (ρ : Env) → ⟦ t ⟧ (finEnv ρ) ≃ Fin (eval t ρ)
card var   ρ = idEquiv _
card yvar  ρ = idEquiv _
card zvar  ρ = idEquiv _
card uvar  ρ = idEquiv _
card vvar  ρ = idEquiv _
card wvar  ρ = idEquiv _
card zero  ρ = idEquiv _
card (suc t)   ρ = ⊎-equiv (idEquiv Unit) (card t ρ)
card (add l r) ρ =
  compEquiv (⊎-equiv (card l ρ) (card r ρ)) (finSum (eval l ρ) (eval r ρ))

-- and, by univalence, a path between the two interpretations.
cardPath : (t : Tm) (ρ : Env) → ⟦ t ⟧ (finEnv ρ) ≡ Fin (eval t ρ)
cardPath t ρ = ua (card t ρ)
