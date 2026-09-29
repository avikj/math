{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SubsetSumOverKernel
--
-- Subset-sum encoded over the ACTUAL kernel (RewriteCertificate): the
-- selected weights are built into a `Tm`, and the sum is obtained through
-- the kernel's own projection `eval` and its derivations — not stdlib
-- recursion. The arithmetic lives in the kernel.
--
-- The two halves:
--
--  · `sumTerm xs sel` is the kernel term adding the selected unary
--    weights. `eval-sumTerm` proves the kernel's projection computes the
--    subset sum: `eval (sumTerm xs sel) ρ ≡ selSum xs sel`. Verification of
--    a handed selection is the kernel reading off a value — a projection.
--
--  · `verify-over-kernel` decides, through the kernel's `eval`, whether a
--    given selection hits the target. One pass over the term.
--
-- The kernel's `eval`/derivations reduce a GIVEN
-- term; they do not range over selections. `Solvable` below is a Σ over
-- `List Bool`, and nothing in the kernel projects its witness. Over the
-- UNARY kernel a decision procedure exists at cost O(n · t) — the
-- textbook pseudo-polynomial dynamic program — which is polynomial in the
-- unary input and exponential in the standard binary input; that is weak
-- NP-completeness, not P=NP, and it does not touch strongly NP-complete
-- problems.
------------------------------------------------------------------------

module SubsetSumOverKernel where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; discreteℕ)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (Σ ; _,_)
open import Cubical.Relation.Nullary using (Dec)

open import Kernel.RewriteCertificate using (Tm ; zero ; suc ; add ; eval ; Env)
open import WindingCostIsUnarySize using (unary)

------------------------------------------------------------------------
-- §1  The instance's arithmetic, built as a kernel term.
------------------------------------------------------------------------

-- the sum of the selected weights, as a stdlib ℕ (the specification)
selSum : List ℕ → List Bool → ℕ
selSum []       _            = 0
selSum (x ∷ xs) (true  ∷ bs) = x + selSum xs bs
selSum (x ∷ xs) (false ∷ bs) = selSum xs bs
selSum (x ∷ xs) []           = 0

-- the SAME sum, built as a kernel `Tm` out of `add`, `suc`, `zero`
sumTerm : List ℕ → List Bool → Tm
sumTerm []       _            = zero
sumTerm (x ∷ xs) (true  ∷ bs) = add (unary x) (sumTerm xs bs)
sumTerm (x ∷ xs) (false ∷ bs) = sumTerm xs bs
sumTerm (x ∷ xs) []           = zero

------------------------------------------------------------------------
-- §2  The kernel's projection computes the subset sum.
------------------------------------------------------------------------

private
  eval-unary : (n : ℕ) (ρ : Env) → eval (unary n) ρ ≡ n
  eval-unary zero    ρ = refl
  eval-unary (suc n) ρ = cong suc (eval-unary n ρ)

-- eval — the kernel's forgetful projection — reads the subset sum off the
-- term. Verifying a handed selection is a projection, one pass.
eval-sumTerm : (xs : List ℕ) (sel : List Bool) (ρ : Env)
  → eval (sumTerm xs sel) ρ ≡ selSum xs sel
eval-sumTerm []       _            ρ = refl
eval-sumTerm (x ∷ xs) (true  ∷ bs) ρ =
  cong₂ _+_ (eval-unary x ρ) (eval-sumTerm xs bs ρ)
eval-sumTerm (x ∷ xs) (false ∷ bs) ρ = eval-sumTerm xs bs ρ
eval-sumTerm (x ∷ xs) []           ρ = refl

-- decide, through the kernel, whether a GIVEN selection hits the target
verify-over-kernel : (xs : List ℕ) (t : ℕ) (sel : List Bool) (ρ : Env)
  → Dec (eval (sumTerm xs sel) ρ ≡ t)
verify-over-kernel xs t sel ρ = discreteℕ (eval (sumTerm xs sel) ρ) t

------------------------------------------------------------------------
-- §3  Solvability is a Σ over selections — no kernel term projects it.
------------------------------------------------------------------------

Solvable : List ℕ → ℕ → (ρ : Env) → Type
Solvable xs t ρ = Σ (List Bool) (λ sel → eval (sumTerm xs sel) ρ ≡ t)
