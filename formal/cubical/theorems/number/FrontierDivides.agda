{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FrontierDivides
--
-- Half of the universal property `FrontierList` §6 names.
--
-- CLAUDE.md (absent from this repository): this lane has no LCM module, so lcm facts are stated by the
-- universal property.  For `prodOf (frontierList k)` that is two halves:
--
--   (a) every m ≤ k divides it;
--   (b) it divides every common multiple of 1 … k.
--
-- (b) is here, in the general form, and it is a fold of one lemma this
-- repository already has.
--
-- ────────────────────────────────────────────────────────────────────
-- THE STATEMENT
--
--     frontier-divides :
--       (es : List Entry) → AllPrime es → Distinct es
--       → (N : ℕ) → AllDivide es N → prodOf es ∣ N
--
-- If every prime power in the frontier divides `N`, so does their
-- product.  The induction step is exactly `FinCardinality.gauss` —
-- coprime divisors multiply — with the coprimality supplied by
-- `FrontierCount.headCoprime`, which is the `bez-mul` fold.
------------------------------------------------------------------------

module FrontierDivides where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _·_ ; _^_)
open import Cubical.Data.Nat.Divisibility using (_∣_ ; ∣-oneˡ)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)

open import FinCardinality using (gauss)
open import FrontierCount
  using (Entry ; prodOf ; AllPrime ; Distinct ; headCoprime)

------------------------------------------------------------------------
-- 1.  Every prime power in the frontier divides N
------------------------------------------------------------------------

AllDivide : List Entry → ℕ → Type
AllDivide []             _ = Unit
AllDivide ((p , i) ∷ es) N = ((p ^ i) ∣ N) × AllDivide es N

------------------------------------------------------------------------
-- 2.  THE HALF THAT LANDS: coprime divisors multiply, folded
------------------------------------------------------------------------

frontier-divides :
  (es : List Entry) → AllPrime es → Distinct es
  → (N : ℕ) → AllDivide es N → prodOf es ∣ N
frontier-divides []             _           _              N _          = ∣-oneˡ N
frontier-divides ((p , i) ∷ es) (pp , rest) (fresh , dist) N (d , ds) =
  gauss (p ^ i) (prodOf es) N
        (headCoprime p i pp es rest fresh)
        d
        (frontier-divides es rest dist N ds)

------------------------------------------------------------------------
-- 3.  So the frontier product is minimal among common multiples of its
--     own prime powers — the half of the universal property that does not
--     need factorisation.
--
-- Combined with `FrontierCount.frontier-count`, the picture at a frontier
-- is: the residue vector has exactly `prodOf es` values (CRT), and
-- `prodOf es` divides anything all the prime powers divide (here).  That
-- every `m ≤ k` is among the things the prime powers cover is the other
-- half, §4.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 4.  The other half: `FrontierDividesHard`.
--
-- `FrontierDividesHard` proves
--
--     frontier-divides-hard :
--       0 < m → m ≤ k → m ∣ prodOf (frontierList k)
--
-- by strong induction on m, peeling one prime at a time with
-- `CoprimeSplitting.primeDivisor` and `PFreePart`, and closing each step
-- with `FinCardinality.gauss` — the same Gauss this module's own half
-- uses — supplied by `PrimeCofactorCoprime`.
--
-- The ingredients it uses:
--
--   * the specification and fuel bound of `FrontierList.logOf`
--     (`ExponentBound`);
--   * membership of (p , logOf p k) in `frontierList k` (`FrontierMember`);
--   * isGCD (p^a) m' 1 from p ∤ m', which is three lines
--     (`PrimeCofactorCoprime`).
--
-- With both halves in place, `prodOf (frontierList k)` satisfies the
-- universal property of lcm(1 … k), which is how CLAUDE.md (absent from this repository) requires lcm
-- facts be stated in a lane with no LCM module.
------------------------------------------------------------------------
