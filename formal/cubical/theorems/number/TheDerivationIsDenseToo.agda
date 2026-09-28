{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheDerivationIsDenseToo
--
-- A companion to `NumberIsExponentialInDerivation`: the derivation is dense.
--
-- ────────────────────────────────────────────────────────────────────
-- THE BOUND, AND WHAT IT DOES NOT COVER
--
-- That module proves `suc e ≤ b ^ e` — the numeric factor is exponential
-- in the exponent it encodes.  A coordinatewise bound does not by itself
-- account for the gap between what the walk carries and what
-- distinguishing k inputs requires, because it says nothing about HOW
-- MANY COORDINATES there are.
--
-- And there are many.  cap(k) = lcm(1..k) is divisible by every prime
-- p ≤ k, so its derivation has a nonzero entry at every such p:
--
--     the walk's derivation is DENSE.
--
-- `cap-is-dense` below checks this for the walk's frontier-8 state
-- against the basis 2,3,5,7 — every coordinate nonzero, support 4 out of
-- 4.  So the derivation is not a compact object either.  Its coordinate
-- count grows with the number of primes below the frontier, and the
-- exponential saving `suc e ≤ b ^ e` buys nothing across coordinates,
-- only within one.
--
-- ────────────────────────────────────────────────────────────────────
-- THE VERDICT
--
--   the numeric encoding is A mechanism of the walk's size.  Whether it
--   is THE mechanism depends on comparing a sum of exponents against a
--   count of primes, which is exactly the Chebyshev-type input the
--   other module does not use.
--
-- The estimate is unavailable in this lane, and quoting it would be the
-- error CLAUDE.md (absent from this repository) forbids.
------------------------------------------------------------------------

module TheDerivationIsDenseToo where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; snotz)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Relation.Nullary using (¬_)

open import SumProductTorus using (Exp ; val ; primes4)

------------------------------------------------------------------------
-- 1.  Density and support
------------------------------------------------------------------------

Dense : (bs : List ℕ) → Exp bs → Type
Dense []       _        = Unit
Dense (b ∷ bs) (x , xs) = (¬ (x ≡ 0)) × Dense bs xs

support : (bs : List ℕ) → Exp bs → ℕ
support []       _        = 0
support (b ∷ bs) (x , xs) = step x + support bs xs
  where
  step : ℕ → ℕ
  step zero    = 0
  step (suc _) = 1

------------------------------------------------------------------------
-- 2.  A dense derivation has full support: one entry per basis element
------------------------------------------------------------------------

dense→full : (bs : List ℕ) (u : Exp bs) → Dense bs u → support bs u ≡ length bs
dense→full []       _        _        = refl
dense→full (b ∷ bs) (zero  , xs) (nz , ds) = Empty.rec (nz refl)
  where open import Cubical.Data.Empty as Empty using (⊥)
dense→full (b ∷ bs) (suc x , xs) (nz , ds) = cong suc (dense→full bs xs ds)

------------------------------------------------------------------------
-- 3.  The walk's state is dense.
--
-- cap 8 = 840 = 2³·3·5·7 — every prime ≤ 8 appears, because every prime
-- p ≤ k divides lcm(1..k) for the trivial reason that p is one of the
-- numbers being joined.
------------------------------------------------------------------------

cap8 : Exp primes4
cap8 = 3 , 1 , 1 , 1 , tt

cap8-is-840 : val primes4 cap8 ≡ 840
cap8-is-840 = refl

cap-is-dense : Dense primes4 cap8
cap-is-dense = snotz , snotz , snotz , snotz , tt

cap-support-is-full : support primes4 cap8 ≡ length primes4
cap-support-is-full = dense→full primes4 cap8 cap-is-dense

cap-support-is-four : support primes4 cap8 ≡ 4
cap-support-is-four = cap-support-is-full

------------------------------------------------------------------------
-- 4.  The verdict, in one line.
--
-- The number is exponential in each exponent (previous module) AND the
-- derivation has one exponent per prime below the frontier (here).  The
-- first is a saving within a coordinate; the second is a cost across
-- them; and which dominates is a question about ∑_{p≤k} versus π(k) that
-- neither module answers.
------------------------------------------------------------------------
