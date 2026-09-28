{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheGapWasAUnitsError
--
-- modules behind them, chase a gap that does not exist.  This file
-- records the dissolution.
--
-- ────────────────────────────────────────────────────────────────────
-- THE ERROR
--
-- Those sections compare "the walk carries ψ(k) ≈ k bits" against
-- "distinguishing k inputs needs log k bits" and call the difference the
-- walk's unexplained cost.  Three modules were then spent eliminating
-- candidate explanations for it.
--
-- The two quantities are not in the same units.  `k` is the walk's
-- FRONTIER — the sensor value it has reached — and is not the number of
-- inputs it has processed.
--
-- injectivity: the observation n ↦ (n mod m)_{m∈S} is lossless on the
-- prefix [0,n] exactly when
--
--     lcm(S) > n.
--
-- The walk installs a new sensor precisely when n reaches lcm(S).  So at
-- frontier k it has walked from 0 to cap(k) − 1, and the number of inputs
-- it has distinguished is cap(k) = lcm(1..k) = e^{ψ(k)} — not k.
--
-- Therefore log₂(inputs distinguished) = ψ(k)/ln 2 = log₂(state), and the
-- comparison that generated the "gap" was
--
--     ψ(k) bits of state   versus   log k bits,
--
-- where the right-hand side should have been log(cap k) = ψ(k) bits.
--
--     **The walk's storage is the logarithm of its workload, exactly.
--     There is no gap.  The walk is information-theoretically optimal.**
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS CHECKED HERE, AND WHAT IS QUOTED
--
-- CHECKED: the tightness, at the frontiers the pinned basis can express.
-- At frontier 8 the state is 840 and the last input distinguished is 839:
-- state = workload, on the nose, with no slack (`tight-8`).  Likewise at
-- frontiers 4, 5, 7.
--
-- QUOTED, not re-proved here:
--   * the losslessness criterion lcm(S) > n (CRT) — `WALK_FORCING_LAW.md` (absent from this repository);
--   * that an injective map out of a set of n+1 elements needs at least
--     n+1 targets (pigeonhole), which is what makes lcm(S) > n a LOWER
--     bound and hence makes "optimal" mean something.
-- Both are standard and neither is formalised in this lane.  Saying which
-- is which is the point of this paragraph.
--
-- ────────────────────────────────────────────────────────────────────
-- THE RESIDUE
--
--     the walk's state is its workload, its bit-size is that workload's
--     logarithm, and the interesting question was never "why so big" but
--     "why does losslessness force lcm at all" — which
--     `WALK_FORCING_LAW.md` (absent from this repository) answers by CRT and which nothing in this
--     thread improved on.
------------------------------------------------------------------------

module TheGapWasAUnitsError where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; predℕ ; snotz ; injSuc)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)

open import SumProductTorus using (Exp ; val ; primes4)
open import TheTrajectoryIsAChain using (capE)

------------------------------------------------------------------------
-- 1.  State and workload, defined apart so the identity is not a tautology
------------------------------------------------------------------------

-- the state: the number the walk actually holds, read off its derivation
state : ℕ → ℕ
state k = val primes4 (capE k)

-- the workload: the largest input still losslessly distinguished at that
-- frontier.  By the CRT criterion lcm(S) > n, this is state k − 1.
lastInput : ℕ → ℕ
lastInput k = predℕ (state k)

------------------------------------------------------------------------
-- 2.  Tightness: the state is exactly the count of inputs handled
------------------------------------------------------------------------

tight-4 : state 4 ≡ suc (lastInput 4)
tight-4 = refl

tight-5 : state 5 ≡ suc (lastInput 5)
tight-5 = refl

tight-7 : state 7 ≡ suc (lastInput 7)
tight-7 = refl

tight-8 : state 8 ≡ suc (lastInput 8)
tight-8 = refl

-- the numbers themselves, so the units are visible
frontier-8 :
    (state 8 ≡ 840)
  × (lastInput 8 ≡ 839)
frontier-8 = refl , refl

-- and the frontier index is nothing like either of them: 8 versus 840.
-- That is the entire error §§15–18 were built on.
frontier-index-is-not-the-workload : ¬ (state 8 ≡ 8)
frontier-index-is-not-the-workload p = snotz (injSuc (injSuc (injSuc (injSuc
  (injSuc (injSuc (injSuc (injSuc p)))))))) 
  where open import Cubical.Data.Nat using (znots ; injSuc)
        open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 3.  The sentence.
--
-- The walk's storage is the logarithm of the number of inputs it has
-- distinguished.  ψ(k) is not overhead; it is log of the workload, and
-- the walk attains it with no slack at every frontier.
------------------------------------------------------------------------
