{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- व्याप्तिः — pervasion.  The seven-gate installer's own license
-- (runtime/crystallize/install.py (absent from this repository), G3), as a
-- checked term:
--
--   "the generalised statement is an identity between two polynomials in
--    the free commutative ring ℤ[#0,#1,…], which is initial among
--    commutative ℤ-algebras.  An identity there maps to an identity under
--    every substitution of ring elements."
--
-- The operative mathematics is the SUBSTITUTION LEMMA — evaluation
-- commutes with substitution — and its corollary: an identity holding at
-- every assignment (the generic point) still holds after ANY substitution
-- of expressions for variables, at every assignment.  Proving a lemma at
-- fresh indeterminates and then firing it on compound arguments never
-- seen during mining is exactly this pervasion.  व्याप्ति is Nyāya's name
-- for the license — the concomitance that carries the seen (the generic
-- instance) to the unseen (every instance); the installer's G3+G7 is an
-- anumna and this is its vypti, checked.
--
-- PROVED:
--   §1  the expression language: variables, ℤ-literals, ⊕, ⊗ — the same
--       shape crystallize/derivation.py (absent from this repository) mines (I/V/S/P nodes).
--   §2  eval-subst : eval (subst t σ) ρ ≡ eval t (eval∘σ at ρ)  — the
--       substitution lemma, by induction (the substitute's VALUE is the
--       value at the substituted assignment: sthnivat, for values).
--   §3  pervade : an identity at every assignment survives every
--       substitution — the G3 license.  Two applications of §2 around
--       the hypothesis at the composite assignment.
------------------------------------------------------------------------

module Vyapti_AnIdentityAtTheGenericPointPervadesEveryInstanceSoTheSevenGatesLicenseIsATheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (ℤ; _+_; _·_)

------------------------------------------------------------------------
-- §1 · the expression language over countably many variables.
data Expr : Type where
  var : ℕ → Expr
  lit : ℤ → Expr
  _⊕_ : Expr → Expr → Expr
  _⊗_ : Expr → Expr → Expr

-- an assignment of values to variables, and evaluation.
Assign : Type
Assign = ℕ → ℤ

eval : Expr → Assign → ℤ
eval (var i)   ρ = ρ i
eval (lit z)   ρ = z
eval (s ⊕ t)   ρ = eval s ρ + eval t ρ
eval (s ⊗ t)   ρ = eval s ρ · eval t ρ

-- substitution of expressions for variables.
Subst : Type
Subst = ℕ → Expr

subst∘ : Expr → Subst → Expr
subst∘ (var i) σ = σ i
subst∘ (lit z) σ = lit z
subst∘ (s ⊕ t) σ = subst∘ s σ ⊕ subst∘ t σ
subst∘ (s ⊗ t) σ = subst∘ s σ ⊗ subst∘ t σ

------------------------------------------------------------------------
-- §2 · THE SUBSTITUTION LEMMA: evaluating a substituted expression is
-- evaluating the original at the substituted assignment.
eval-subst : (t : Expr) (σ : Subst) (ρ : Assign)
           → eval (subst∘ t σ) ρ ≡ eval t (λ i → eval (σ i) ρ)
eval-subst (var i) σ ρ = refl
eval-subst (lit z) σ ρ = refl
eval-subst (s ⊕ t) σ ρ = cong₂ _+_ (eval-subst s σ ρ) (eval-subst t σ ρ)
eval-subst (s ⊗ t) σ ρ = cong₂ _·_ (eval-subst s σ ρ) (eval-subst t σ ρ)

------------------------------------------------------------------------
-- §3 · PERVASION — the G3 license.  An identity at the generic point
-- (every assignment) holds after every substitution, at every assignment:
-- the installed lemma is sound on compound arguments never seen during
-- mining.
pervade : (s t : Expr)
        → ((ρ : Assign) → eval s ρ ≡ eval t ρ)
        → (σ : Subst) (ρ : Assign)
        → eval (subst∘ s σ) ρ ≡ eval (subst∘ t σ) ρ
pervade s t identity σ ρ =
  eval-subst s σ ρ
  ∙ identity (λ i → eval (σ i) ρ)
  ∙ sym (eval-subst t σ ρ)
