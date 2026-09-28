{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S12CyclotomicChain
--
-- The reindexing that turns the unbounded lifting-the-exponent answer
-- into a BOUNDED sequence of local contributions, and the uniqueness of
-- that bounded sequence.
--
-- Setting (see collab/swarm/2026-08-14/swarm-0814-12-cyclotomic-comb.md (absent from this repository)).
-- Fix an odd prime p and an integer a with p ∤ a; let d = ord_p(a) and
-- e = v_p(a^d − 1) ≥ 1.  Lifting-the-exponent says
--
--     v_p(a^n − 1) = e + v_p(n)   when d ∣ n,   and 0 otherwise.
--
-- The divisors of n = d·p^j that carry any p-adic content are exactly
-- d·p^0, …, d·p^j (a CHAIN, not a general divisor lattice), and the
-- factorisation a^n − 1 = ∏_{m ∣ n} Φ_m(a) makes v_p additive along it.
-- So the arithmetic reduces, exactly, to a statement about partial sums
-- of one sequence indexed by the chain position k = 0,1,2,….  That
-- sequence is
--
--     cyc e k  =  v_p(Φ_{d·p^k}(a))  =  e (k = 0),  1 (k ≥ 1).
--
-- Four theorems, no postulates:
--
--   lteFromCyc   chain (cyc e) j ≡ e + j
--                — the unbounded LTE answer IS the j-th partial sum of
--                  the bounded local sequence.  The indicator [d ∣ n]
--                  has disappeared into the indexing.
--
--   cycUnique    chain g j ≡ e + j for all j  ⟹  g ≡ cyc e
--                — the bounded decomposition is not one choice among
--                  many: the LTE law determines each tooth uniquely.
--
--   cycBound     cyc e k ≤ suc e
--                — every local contribution is bounded by the
--                  observation depth K = e+1 of R0025 Theorem 2.  On the
--                  cyclotomic chart, cost ≥ answer is restored.
--
--   chainGrows   j ≤ chain (cyc e) j
--                — while the SUM is unbounded.  R0025(3)'s "depth ≠
--                  answer" is exactly this gap, and it is an artefact of
--                  reading a^n − 1 whole rather than tooth by tooth.
--
-- Nothing here is measured.  `chain` is the p-chain restriction of the
-- divisor sum; the arithmetic input (that the chain is the whole support
-- and that its length is v_p(n)) is proved in the note, not assumed here.
------------------------------------------------------------------------

module Swarm.S12CyclotomicChain where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-zero ; +-suc
                                   ; +-comm ; inj-m+)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Sigma using (_,_)

------------------------------------------------------------------------
-- The chain and its teeth
------------------------------------------------------------------------

-- chain g j = g 0 + g 1 + ⋯ + g j : the divisor sum restricted to the
-- p-chain d, d·p, …, d·p^j, which is where all the p-adic content sits.
chain : (ℕ → ℕ) → ℕ → ℕ
chain g zero    = g zero
chain g (suc j) = chain g j + g (suc j)

-- The cyclotomic tooth sequence: v_p(Φ_{d·p^k}(a)).
cyc : ℕ → ℕ → ℕ
cyc e zero    = e
cyc e (suc _) = 1

------------------------------------------------------------------------
-- 1.  The reindexing identity
------------------------------------------------------------------------

lteFromCyc : ∀ e j → chain (cyc e) j ≡ e + j
lteFromCyc e zero    = sym (+-zero e)
lteFromCyc e (suc j) =
    cong (_+ 1) (lteFromCyc e j)
  ∙ +-comm (e + j) 1
  ∙ sym (+-suc e j)

------------------------------------------------------------------------
-- 2.  Uniqueness of the bounded decomposition
------------------------------------------------------------------------

cycUnique : ∀ (g : ℕ → ℕ) (e : ℕ)
          → (∀ j → chain g j ≡ e + j)
          → ∀ k → g k ≡ cyc e k
cycUnique g e h zero    = h zero ∙ +-zero e
cycUnique g e h (suc j) = inj-m+ step
  where
    step : (e + j) + g (suc j) ≡ (e + j) + 1
    step =
        cong (_+ g (suc j)) (sym (h j))
      ∙ h (suc j)
      ∙ +-suc e j
      ∙ sym (+-comm (e + j) 1)

------------------------------------------------------------------------
-- 3.  Bounded teeth, unbounded sum
------------------------------------------------------------------------

-- Every tooth is at most the observation depth K = e + 1.
cycBound : ∀ e k → cyc e k ≤ suc e
cycBound e zero    = 1 , refl
cycBound e (suc _) = e , +-comm e 1

-- The partial sums are cofinal in ℕ: the whole-object answer is unbounded.
chainGrows : ∀ e j → j ≤ chain (cyc e) j
chainGrows e j = e , sym (lteFromCyc e j)

------------------------------------------------------------------------
-- 4.  The p = 2 branch: the same comb with a two-term head
------------------------------------------------------------------------
--
-- For a odd, d = ord₂(a) = 1, and the chain is 1, 2, 4, 8, ….  Its
-- teeth are v₂(Φ₁(a)) = v₂(a−1) = e₋, v₂(Φ₂(a)) = v₂(a+1) = e₊, and
-- v₂(Φ_{2^k}(a)) = v₂(a^{2^{k−1}} + 1) = 1 for k ≥ 2 (a^{2^{k−1}} is an
-- odd square, ≡ 1 mod 8, so the successor is ≡ 2 mod 4).  Summing the
-- chain up to k = v₂(n) reproduces R0025 Theorem 1's p = 2 clause,
--
--     v₂(a^n − 1) = e₋ + e₊ + v₂(n) − 1   (n even),
--
-- so the branch that R0025's preservation ledger flags as "genuinely
-- different in shape" is, on the cyclotomic chart, the same shape with
-- one extra head term.  The classification of tooth sequences over all
-- primes is therefore exhaustive: a head of length 1 (p odd) or 2
-- (p = 2), then constantly 1.

cyc₂ : ℕ → ℕ → ℕ → ℕ
cyc₂ em ep zero          = em
cyc₂ em ep (suc zero)    = ep
cyc₂ em ep (suc (suc _)) = 1

-- chain (cyc₂ e₋ e₊) (suc j) ≡ (e₋ + e₊) + j, i.e. at n with v₂(n) = suc j.
lteFromCyc₂ : ∀ em ep j → chain (cyc₂ em ep) (suc j) ≡ (em + ep) + j
lteFromCyc₂ em ep zero    = sym (+-zero (em + ep))
lteFromCyc₂ em ep (suc j) =
    cong (_+ 1) (lteFromCyc₂ em ep j)
  ∙ +-comm ((em + ep) + j) 1
  ∙ sym (+-suc (em + ep) j)

cyc₂Bound : ∀ em ep k → cyc₂ em ep k ≤ suc (em + ep)
cyc₂Bound em ep zero          = suc ep , cong suc (+-comm ep em)
cyc₂Bound em ep (suc zero)    = suc em , refl
cyc₂Bound em ep (suc (suc _)) = em + ep , +-comm (em + ep) 1
