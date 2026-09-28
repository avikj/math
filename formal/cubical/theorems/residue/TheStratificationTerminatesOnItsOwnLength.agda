{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheStratificationTerminatesOnItsOwnLength
--
-- With the measure of `TheRemainderIsStrictlyShorterSoTheStratificationHasAMeasure`
-- in hand the recursion is four lines and its termination is one
-- induction.  The LAYER properties are in the modules cited at the end.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   leftover / strata     the fuelled iteration: peel the maximal
--                         layer, recurse on the remainder
--   lengthZeroGivesNil    a list of length ≤ 0 is empty
--   fuelSuffices          if the fuel is at least the length, the
--                         iteration exhausts the archive
--   theStratificationTerminates
--                         hence `leftover (lengthL xs) xs ≡ []` — the
--                         archive's OWN LENGTH is enough fuel
--
-- The induction is that measure applied once per step:
-- `theRemainderIsStrictlyShorter` turns `lengthL (x ∷ xs) ≤ suc n` into
-- `lengthL (remainder (x ∷ xs)) ≤ n`, which is exactly the recursive
-- call's obligation.  Nothing else is needed.
--
-- ────────────────────────────────────────────────────────────────────
-- NO NOVELTY.  Fuelled recursion with the fuel bounded by a decreasing
-- measure is the standard way to write a well-founded loop without
-- well-founded machinery.
------------------------------------------------------------------------

module TheStratificationTerminatesOnItsOwnLength where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order
  using (_≤_ ; _<_ ; ≤-refl ; ≤-trans ; pred-≤-pred ; ¬-<-zero)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Empty as ⊥ using (⊥)

open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (stratum)
open import TheRemainderIsStrictlyShorterSoTheStratificationHasAMeasure
  using (lengthL ; remainder ; theRemainderIsStrictlyShorter)

------------------------------------------------------------------------
-- 1.  The iteration
------------------------------------------------------------------------

leftover : ℕ → List (List ℕ) → List (List ℕ)
leftover zero    xs       = xs
leftover (suc n) []       = []
leftover (suc n) (x ∷ xs) = leftover n (remainder (x ∷ xs))

strata : ℕ → List (List ℕ) → List (List (List ℕ))
strata zero    xs       = []
strata (suc n) []       = []
strata (suc n) (x ∷ xs) = stratum (x ∷ xs) ∷ strata n (remainder (x ∷ xs))

------------------------------------------------------------------------
-- 2.  Its own length is enough fuel
------------------------------------------------------------------------

lengthZeroGivesNil : (xs : List (List ℕ)) → lengthL xs ≤ 0 → xs ≡ []
lengthZeroGivesNil []       _ = refl
lengthZeroGivesNil (x ∷ xs) h = ⊥.rec (¬-<-zero h)

fuelSuffices :
  (n : ℕ) (xs : List (List ℕ)) → lengthL xs ≤ n → leftover n xs ≡ []
fuelSuffices zero    xs       h = lengthZeroGivesNil xs h
fuelSuffices (suc n) []       _ = refl
fuelSuffices (suc n) (x ∷ xs) h =
  fuelSuffices n (remainder (x ∷ xs))
    (pred-≤-pred (≤-trans (theRemainderIsStrictlyShorter x xs) h))

theStratificationTerminates :
  (xs : List (List ℕ)) → leftover (lengthL xs) xs ≡ []
theStratificationTerminates xs = fuelSuffices (lengthL xs) xs ≤-refl

------------------------------------------------------------------------
-- ORDER, first half: every remainder member is strictly dominated, in
-- `EveryRemainderMemberIsStrictlyDominated`:
--
--   filterOutOnlyKeepsNonSatisfiers   the complement keeps exactly what
--                                     fails the predicate
--   anyToMember                       an `Any` yields its witness WITH
--                                     the membership `anyToΣ` discards
--   everyRemainderMemberIsStrictlyDominated
--                                     every member of `remainder xs` is
--                                     strictly dominated by a member OF
--                                     `xs`
--
-- THE DOUBLE NEGATION IS THE WHOLE DIFFICULTY AND IT IS DECIDED AWAY.
-- `IsParetoMaximal v xs` is `¬ Any (StrictlyDominatedBy v) xs`, so failing
-- it gives `¬ ¬ Any …`.  The dominator is recovered only because
-- `decAny decStrictlyDominatedBy` makes that `Any` decidable, hence
-- stable.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- COVERAGE and DISJOINTNESS AT ONE STEP, in
-- `OneStepCoverageAndDisjointnessOfTheLayer`:
--
--   memberOfFilterSatisfies / memberOfFilterOutFails
--   memberSplits       every member of `xs` is in the filter or its
--                      complement
--   noMemberInBoth     and never in both
--   layerCovers / layerIsDisjoint   the same at `stratum` / `remainder`
--
-- One step is the right unit here, because `strata` peels a layer and
-- recurses on EXACTLY the complement these two are about.  Both are
-- proved for an arbitrary decidable predicate and instantiated once —
-- nothing about Pareto maximality is used, only that the two filters
-- are complementary, which is why each is three lines.
--
------------------------------------------------------------------------
