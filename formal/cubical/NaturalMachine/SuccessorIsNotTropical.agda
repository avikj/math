{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.SuccessorIsNotTropical
--
-- Companion to `SumProductTorus`.  There the multiplicative world was
-- shown to be the tropical world in disguise: derivations add, numbers
-- multiply; derivations take pointwise max, numbers take lcm; and the two
-- cohere by max-over-plus.  In that chart multiplication is trivial.
--
-- This module says what the chart costs, and the answer is sharp:
--
--     the successor has NO locality in it whatsoever.
--
-- Not "is complicated".  Consecutive integers are coprime, so the
-- derivations of n and n+1 share **not one coordinate**.  Every single
-- step along ℕ is a total jump in the chart where multiplication is easy.
-- The two structures on the same set do not merely fail to commute — they
-- have disjoint support at every step.
--
-- That is this repository's central difficulty, stated exactly and
-- elementarily.  Sieve and multiplicative methods live in the tropical
-- chart because that is where their objects are simple; additive
-- questions — Goldbach, gaps, pairs — are questions about the successor;
-- and the successor is the one map with no expression there.  The
-- "parity barrier" is a chart incompatibility, and `disjoint-support`
-- below is its whole content.
--
-- Nothing here is deep.  `gcd(n, n+1) = 1` is known to every schoolchild
-- who has thought about it for a minute.  What is not standard is
-- reading it as the obstruction: the fact everyone knows IS the barrier
-- everyone describes, once you notice that the multiplicative world is a
-- chart and ask what fails to transport.
------------------------------------------------------------------------

module NaturalMachine.SuccessorIsNotTropical where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import NaturalMachine.WalkJumps using (IsPrime ; prime-¬∣1)

------------------------------------------------------------------------
-- 1.  Consecutive integers have no common divisor but 1
--
-- ℕ has no subtraction, so the usual one-line proof is unavailable and
-- the argument goes through the witnesses: n = a·d and n+1 = b·d force
-- a < b, and then b = j + (a+1) makes (j+1)·d = 1 by cancellation.
------------------------------------------------------------------------

cd-consecutive : (d n : ℕ) → d ∣ n → d ∣ suc n → d ∣ 1
cd-consecutive d n d∣n d∣sn = go (∣-untrunc d∣n) (∣-untrunc d∣sn)
  where
  go : Σ[ a ∈ ℕ ] (a · d ≡ n) → Σ[ b ∈ ℕ ] (b · d ≡ suc n) → d ∣ 1
  go (a , pa) (b , pb) = ∣ suc j , unit ∣₁
    where
    key : b · d ≡ suc (a · d)
    key = pb ∙ cong suc (sym pa)

    ad<bd : (a · d) < (b · d)
    ad<bd = subst (suc (a · d) ≤_) (sym key) ≤-refl

    a<b : a < b
    a<b with splitℕ-≤ b a
    ... | inl b≤a = Empty.rec (¬m<m (≤<-trans (≤-·k b≤a) ad<bd))
    ... | inr p    = p

    j : ℕ
    j = a<b .fst

    pj : j + suc a ≡ b
    pj = a<b .snd

    step2 : (j · d) + ((suc a) · d) ≡ suc (a · d)
    step2 = ·-distribʳ j (suc a) d ∙ cong (_· d) pj ∙ key

    step3 : ((j · d) + d) + (a · d) ≡ 1 + (a · d)
    step3 = sym (+-assoc (j · d) d (a · d)) ∙ step2

    step4 : (j · d) + d ≡ 1
    step4 = inj-+m step3

    unit : (suc j) · d ≡ 1
    unit = +-comm d (j · d) ∙ step4

------------------------------------------------------------------------
-- 2.  THE OBSTRUCTION.  No prime divides two consecutive integers, so
--     the derivations of n and n+1 share no coordinate at all.
------------------------------------------------------------------------

disjoint-support :
  (p n : ℕ) → IsPrime p → p ∣ n → ¬ (p ∣ suc n)
disjoint-support p n pp p∣n p∣sn =
  prime-¬∣1 p pp (cd-consecutive p n p∣n p∣sn)

-- read the other way: whatever the walk knows about n — its entire
-- installed state, every register — tells it nothing whatsoever about
-- n+1's registers, because they are a disjoint set of coordinates.
successor-shares-nothing :
  (p n : ℕ) → IsPrime p → p ∣ suc n → ¬ (p ∣ n)
successor-shares-nothing p n pp p∣sn p∣n =
  disjoint-support p n pp p∣n p∣sn

------------------------------------------------------------------------
-- 3.  Three concrete failures of transport, by computation.
--
--     Divisibility is the tropical order (pointwise ≤ on derivations);
--     lcm is the tropical join.  The successor respects neither.  These
--     are exact evaluations, not measurements.
------------------------------------------------------------------------

-- the successor does not preserve the divisibility order: 2 ∣ 4 but 3 ∤ 5
suc-breaks-order-lhs : 2 ∣ 4
suc-breaks-order-lhs = ∣ 2 , refl ∣₁

-- 3·c ≡ 5 has no solution: c = 0 gives 0, c = 1 gives 3, c = 2 gives 6,
-- and c ≥ 3 gives at least 9.  Four cases, all by peeling successors.
suc-breaks-order-rhs : ¬ (3 ∣ 5)
suc-breaks-order-rhs h with ∣-untrunc h
... | (zero                    , p) = znots p
... | (suc zero                , p) = znots (injSuc (injSuc (injSuc p)))
... | (suc (suc zero)          , p) =
      snotz (injSuc (injSuc (injSuc (injSuc (injSuc p)))))
... | (suc (suc (suc c))       , p) =
      snotz (injSuc (injSuc (injSuc (injSuc (injSuc p)))))

-- and it does not commute with the join:
--   lcm 2 3 = 6, and its successor is 7,
--   while lcm (suc 2) (suc 3) = lcm 3 4 = 12.
-- One step in ℕ, and the tropical join lands somewhere unrelated.
join-does-not-follow : ¬ (7 ≡ 12)
join-does-not-follow p =
  znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc p)))))))

------------------------------------------------------------------------
-- 4.  What this says, for the record.
--
-- `SumProductTorus` gives ℕ's multiplicative structure a chart in which
-- it is free: derivations under +, join under max, the two cohering
-- tropically.  Every multiplicative question becomes easy there.
--
-- `disjoint-support` says the successor is invisible in that chart, in
-- the strongest possible sense — not distorted, not expensive, but
-- supported on coordinates disjoint from the ones it came from.
--
-- So the two structures ℕ carries are not two views of one object that
-- some clever transport will reconcile.  There is a chart for each, and
-- the transition map between them has no locality at any point.  Every
-- method that works multiplicatively is working in one chart, every
-- additive question is asked in the other, and nothing carries across
-- because at every single step the coordinates are disjoint.
--
-- The honest consequence: looking for the obstruction inside either
-- chart is looking in the wrong place.  It is not in the sieve and it is
-- not in the walk — both are single-chart objects, and this module says
-- what happens between charts.  The object to build is the transition
-- itself.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 5.  Scope of §4.
--
-- §4 above reads `disjoint-support` as "the parity barrier is a chart
-- incompatibility" and calls it "its whole content".  That reading is
-- scoped: the theorem is about ℕ **with the
-- successor**, whose generator 1 is a unit and therefore multiplicatively
-- invisible by construction.  It is not a theorem about arithmetic
-- carrying two structures.
--
-- `NaturalMachine.PythagoreanTransition` keeps the ring and changes the
-- additive law to Brahmagupta's composition (bhvan at D = −1, 628 CE).
-- There the successor's analogue satisfies
--
--     N (u ⊗ g) ≡ N u · N g
--
-- — multiplication by a constant in the very chart where ℕ's successor
-- has no support at all.  Total locality against zero locality, same
-- chart.  So the incompatibility measured here belongs to the line.
--
-- The closing sentence of §4 — "the object to build is the transition
-- itself" — is answered there by `gen-hom`: squaring is a monoid
-- homomorphism from the parameter chart to the triple chart, so Euclid's
-- parametrisation IS the transition, with no defect.
--
-- See notes/THE_BARRIER_BELONGS_TO_THE_LINE.md (absent from this repository).
------------------------------------------------------------------------
