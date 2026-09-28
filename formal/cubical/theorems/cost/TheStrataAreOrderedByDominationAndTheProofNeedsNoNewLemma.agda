{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheStrataAreOrderedByDominationAndTheProofNeedsNoNewLemma
--
-- DARWIN §5.2's ORDER property, in full: every member of a later
-- stratum is strictly dominated by a member of an earlier one.
--
-- ────────────────────────────────────────────────────────────────────
-- **The argument never needs
-- the later strata's MAXIMALITY.**  It needs only their MEMBERSHIP in
-- the remainder, and `strataSound` — proved for
-- coverage — already gives exactly that.  Membership in the peeled
-- archive is all the one-step theorem asks of its input.  So no new
-- lemma exists in this module: the whole content is `strataSound`
-- composed with `everyRemainderMemberIsBeatenByAStratumMember`, plus
-- the same recursive bookkeeping already used for pairwise
-- disjointness.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   Beats ys zs        every member of zs is strictly dominated by
--                      some member of ys
--   AllBeaten / Ordered
--                      recursive families over the list of strata, no
--                      indices, matching the shape of `Pairwise`
--   headBeatsEveryLaterStratum
--                      the head stratum beats every member of every
--                      later one
--   theStrataAreOrdered
--                      `Ordered (strata n xs)` for every fuel and
--                      archive
--
-- With `theStratificationCovers` and `theStrataArePairwiseDisjoint`,
-- DARWIN §5.2's three output properties — COVERAGE, DISJOINTNESS,
-- ORDER — are now all checked over this corpus's own
-- `stratum`/`remainder`.
--
-- NO NOVELTY.  This is the defining property of non-dominated sorting
-- (Goldberg 1989; Deb et al. 2002's fast-non-dominated-sort).
------------------------------------------------------------------------

module TheStrataAreOrderedByDominationAndTheProofNeedsNoNewLemma where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_)
open import Cubical.Data.Unit using (Unit ; tt)

open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (StrictlyDominatedBy ; stratum)
open import TheRemainderIsStrictlyShorterSoTheStratificationHasAMeasure
  using (remainder)
open import TheStratificationTerminatesOnItsOwnLength
  using (strata)
open import OneStepCoverageAndDisjointnessOfTheLayer
  using (Mem)
open import TheStratificationCoversAndItsStrataArePairwiseDisjoint
  using (MemSome ; strataSound)
open import EveryRemainderMemberIsBeatenByAStratumMember
  using (everyRemainderMemberIsBeatenByAStratumMember)

------------------------------------------------------------------------
-- 1.  The families
------------------------------------------------------------------------

Beats : List (List ℕ) → List (List ℕ) → Type
Beats ys zs =
  (v : List ℕ) → Mem v zs
  → Σ[ w ∈ List ℕ ] (Mem w ys × StrictlyDominatedBy v w)

AllBeaten : List (List ℕ) → List (List (List ℕ)) → Type
AllBeaten ys []         = Unit
AllBeaten ys (zs ∷ sss) = Beats ys zs × AllBeaten ys sss

Ordered : List (List (List ℕ)) → Type
Ordered []         = Unit
Ordered (ys ∷ sss) = AllBeaten ys sss × Ordered sss

------------------------------------------------------------------------
-- 2.  The head stratum beats every member of every later one
------------------------------------------------------------------------

headBeatsEveryLaterStratum :
  (n : ℕ) (xs : List (List ℕ)) (v : List ℕ)
  → MemSome v (strata n (remainder xs))
  → Σ[ w ∈ List ℕ ] (Mem w (stratum xs) × StrictlyDominatedBy v w)
headBeatsEveryLaterStratum n xs v k =
  everyRemainderMemberIsBeatenByAStratumMember xs v
    (strataSound n (remainder xs) v k)

beatsFromTheUnion :
  (ys : List (List ℕ)) (sss : List (List (List ℕ)))
  → ((v : List ℕ) → MemSome v sss
       → Σ[ w ∈ List ℕ ] (Mem w ys × StrictlyDominatedBy v w))
  → AllBeaten ys sss
beatsFromTheUnion ys []         h = tt
beatsFromTheUnion ys (zs ∷ sss) h =
    (λ v m → h v (inl m))
  , beatsFromTheUnion ys sss (λ v k → h v (inr k))

------------------------------------------------------------------------
-- 3.  ORDER, over the whole stratification
------------------------------------------------------------------------

theStrataAreOrdered : (n : ℕ) (xs : List (List ℕ)) → Ordered (strata n xs)
theStrataAreOrdered zero    xs       = tt
theStrataAreOrdered (suc n) []       = tt
theStrataAreOrdered (suc n) (x ∷ xs) =
    beatsFromTheUnion (stratum (x ∷ xs)) (strata n (remainder (x ∷ xs)))
      (headBeatsEveryLaterStratum n (x ∷ xs))
  , theStrataAreOrdered n (remainder (x ∷ xs))
