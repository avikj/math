{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheCountingSemanticsIsTheCardinalityOfTheTypeSemantics
--
-- The bridge between `TheCountingSemanticsIsADecategorification⟦`'s two
-- semantics: ⟦t⟧ and eval t are related by cardinality.
--
-- THE CLAIM, made precise: `eval` is the CARDINALITY of `⟦_⟧`. Interpret
-- each of the six variable coordinates not by a number but by a finite type
-- OF that number's cardinality — `canonical ρ` sends `var` to `Fin (x ρ)`,
-- etc. Then the categorified semantics of any term is a finite type, and its
-- size is exactly the counting semantics:
--
--     ⟦ t ⟧ (canonical ρ)  ≃  Fin (eval t ρ).
--
-- So `eval = |·| ∘ ⟦_⟧` at finite environments: the counting semantics is
-- the decategorified shadow (the cardinality realization) of the type
-- semantics, and the bijection `⟦_⟧` keeps is exactly the structure the
-- cardinality forgets. Read against the motive picture: `⟦_⟧` is the middle,
-- `eval` is a realization, and `Fin (eval t)` is that realization named.
--
-- The proof is short because cubical's `SumFin.Fin` is DEFINED with the same
-- clauses as `⟦_⟧`: `Fin 0 = ⊥`, `Fin (suc n) = ⊤ ⊎ Fin n`. So `zero` and
-- `suc` are definitional and only `add` needs a lemma — `SumFin⊎≃`, the
-- library's `(Fin m ⊎ Fin n) ≃ Fin (m + n)`.
------------------------------------------------------------------------

module TheCountingSemanticsIsTheCardinalityOfTheTypeSemantics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; idEquiv ; compEquiv)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Unit using (Unit)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Sum.Properties using (⊎-equiv)
open import Cubical.Data.SumFin using (Fin ; SumFin⊎≃)

open import Kernel.RewriteCertificate
open import TheCountingSemanticsIsADecategorificationAndTheBitItDropsIsASymmetry
  using (TEnv ; tenv ; ⟦_⟧)

------------------------------------------------------------------------
-- §1  The finite environment of a numeric one : each coordinate becomes a
--     finite type of the stated cardinality.
------------------------------------------------------------------------

canonical : Env → TEnv
canonical ρ = tenv (Fin (x ρ)) (Fin (y ρ)) (Fin (z ρ))
                   (Fin (u ρ)) (Fin (v ρ)) (Fin (w ρ))
  where open Env

------------------------------------------------------------------------
-- §2  The bridge : the type semantics, counted, is the counting semantics.
------------------------------------------------------------------------

counting-is-cardinality-of-the-type-semantics :
  (t : Tm) (ρ : Env) → ⟦ t ⟧ (canonical ρ) ≃ Fin (eval t ρ)
counting-is-cardinality-of-the-type-semantics var  ρ = idEquiv _
counting-is-cardinality-of-the-type-semantics yvar ρ = idEquiv _
counting-is-cardinality-of-the-type-semantics zvar ρ = idEquiv _
counting-is-cardinality-of-the-type-semantics uvar ρ = idEquiv _
counting-is-cardinality-of-the-type-semantics vvar ρ = idEquiv _
counting-is-cardinality-of-the-type-semantics wvar ρ = idEquiv _
counting-is-cardinality-of-the-type-semantics zero ρ = idEquiv _
counting-is-cardinality-of-the-type-semantics (suc t) ρ =
  ⊎-equiv (idEquiv Unit) (counting-is-cardinality-of-the-type-semantics t ρ)
counting-is-cardinality-of-the-type-semantics (add l r) ρ =
  compEquiv
    (⊎-equiv (counting-is-cardinality-of-the-type-semantics l ρ)
             (counting-is-cardinality-of-the-type-semantics r ρ))
    (SumFin⊎≃ (eval l ρ) (eval r ρ))
