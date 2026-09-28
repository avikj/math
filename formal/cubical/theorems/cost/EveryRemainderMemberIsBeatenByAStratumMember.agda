{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- EveryRemainderMemberIsBeatenByAStratumMember
--
-- DARWIN §5.2's ORDER property, second half.  `EveryRemainderMember-
-- IsStrictlyDominated` proved that a member of the remainder is beaten
-- by SOMETHING in the archive.  That is not the ordering statement: the
-- something might itself be in the remainder, and then the strata are
-- not ordered by domination at all.  What is needed, and proved here:
--
--   every member of the remainder is beaten by a member of the
--   STRATUM.
--
-- ────────────────────────────────────────────────────────────────────
-- THE ARGUMENT.
--
-- No well-founded measure on ℕ over a finite list is needed.  The
-- chain-climbing argument — v is beaten by u, u may be beaten by u′,
-- iterate and hope it stops — is not the only route; the shorter one:
--
--   apply `maximalExists` to the SUBLIST of elements that beat v.
--
-- `maximalExists` performs the finite induction, once, for the
-- non-empty-stratum theorem; it costs nothing to point it at a
-- different list.  The maximal element OF THAT SUBLIST is maximal in
-- the whole archive — because anything beating it would, by
-- transitivity, also beat v and hence lie in the sublist.  That is the
-- whole proof.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   above v xs        the elements of xs that strictly dominate v
--   memberIntoFilter  the converse of `memberOfFilterSatisfies`: a
--                     member satisfying the predicate is a member of
--                     the filtrate (arbitrary decidable predicate)
--   maximalOfNonEmpty `maximalExists` with the non-emptiness supplied
--                     by a membership rather than by a cons pattern
--   aboveMaximalIsGloballyMaximal
--                     maximal in `above v xs` ⇒ maximal in xs
--   theDominatorCanBeChosenMaximal
--                     any dominator of v can be replaced by one in the
--                     stratum
--   everyRemainderMemberIsBeatenByAStratumMember
--                     hence the ordering statement
--
-- The ordering statement is the ONE-STEP ordering:
-- stratum 1 beats every member of the remainder, and since the next
-- stratum is computed from that remainder, each stratum beats
-- everything below it AT ITS OWN LEVEL.  The transitive statement over
-- `strata` — that stratum i beats every member of stratum j for every
-- j > i — is `theStrataAreOrdered` in
-- `TheStrataAreOrderedByDominationAndTheProofNeedsNoNewLemma`, which
-- composes `strataSound` with the theorem here.
--
-- This is the standard fact that the non-dominated front
-- of a finite set dominates everything else in it (Goldberg 1989; Deb
-- et al. 2002), and the sublist argument is the usual one.
------------------------------------------------------------------------

module EveryRemainderMemberIsBeatenByAStratumMember where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet
  using (Any ; memberToAny)
open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (filterDec ; StrictlyDominatedBy ; decStrictlyDominatedBy
        ; IsParetoMaximal ; stratum ; stratumKeepsEveryMaximal)
open import TheRemainderIsStrictlyShorterSoTheStratificationHasAMeasure
  using (remainder)
open import ANonEmptyArchiveHasANonEmptyStratum
  using (maximalExists ; ⊏-trans)
open import EveryRemainderMemberIsStrictlyDominated
  using (anyToMember ; everyRemainderMemberIsStrictlyDominated)
open import OneStepCoverageAndDisjointnessOfTheLayer
  using (Mem ; memberOfFilterSatisfies)
open import TheStratificationCoversAndItsStrataArePairwiseDisjoint
  using (filterDecSubset)

private
  variable
    A : Type

------------------------------------------------------------------------
-- 1.  Into the filtrate — the converse of memberOfFilterSatisfies
------------------------------------------------------------------------

memberIntoFilter :
  (P : A → Type) (d : (a : A) → Dec (P a)) (xs : List A) (a : A)
  → Mem a xs → P a → Mem a (filterDec P d xs)
memberIntoFilter P d []       a e p = ⊥.rec e
memberIntoFilter P d (x ∷ xs) a m p with d x
memberIntoFilter P d (x ∷ xs) a (inl q) p | yes _ = inl q
memberIntoFilter P d (x ∷ xs) a (inr r) p | yes _ =
  inr (memberIntoFilter P d xs a r p)
memberIntoFilter P d (x ∷ xs) a (inl q) p | no ¬px =
  ⊥.rec (¬px (subst P (sym q) p))
memberIntoFilter P d (x ∷ xs) a (inr r) p | no _ =
  memberIntoFilter P d xs a r p

------------------------------------------------------------------------
-- 2.  The elements that beat v, and a maximal one among them
------------------------------------------------------------------------

above : List ℕ → List (List ℕ) → List (List ℕ)
above v xs = filterDec (StrictlyDominatedBy v) (decStrictlyDominatedBy v) xs

maximalOfNonEmpty :
  (ys : List (List ℕ)) (a : List ℕ) → Mem a ys
  → Σ[ m ∈ List ℕ ] (Mem m ys × IsParetoMaximal m ys)
maximalOfNonEmpty []       a e = ⊥.rec e
maximalOfNonEmpty (y ∷ ys) a _ = maximalExists y ys

------------------------------------------------------------------------
-- 3.  Maximal in the sublist is maximal in the archive
------------------------------------------------------------------------

aboveMaximalIsGloballyMaximal :
  (v : List ℕ) (xs : List (List ℕ)) (w : List ℕ)
  → StrictlyDominatedBy v w
  → IsParetoMaximal w (above v xs) → IsParetoMaximal w xs
aboveMaximalIsGloballyMaximal v xs w vw maxA anyxs
  with anyToMember (StrictlyDominatedBy w) xs anyxs
... | (z , mz , wz) =
  maxA (memberToAny (StrictlyDominatedBy w) z (above v xs)
         (memberIntoFilter (StrictlyDominatedBy v) (decStrictlyDominatedBy v)
                           xs z mz (⊏-trans v w z vw wz))
         wz)

------------------------------------------------------------------------
-- 4.  So the dominator can always be taken from the stratum
------------------------------------------------------------------------

theDominatorCanBeChosenMaximal :
  (xs : List (List ℕ)) (v u : List ℕ)
  → Mem u xs → StrictlyDominatedBy v u
  → Σ[ w ∈ List ℕ ] (Mem w (stratum xs) × StrictlyDominatedBy v w)
theDominatorCanBeChosenMaximal xs v u mu vu
  with maximalOfNonEmpty (above v xs) u
         (memberIntoFilter (StrictlyDominatedBy v) (decStrictlyDominatedBy v)
                           xs u mu vu)
... | (w , mw , maxw) =
    w
  , stratumKeepsEveryMaximal xs w
      (filterDecSubset (StrictlyDominatedBy v) (decStrictlyDominatedBy v) xs w mw)
      (aboveMaximalIsGloballyMaximal v xs w
        (memberOfFilterSatisfies (StrictlyDominatedBy v)
                                 (decStrictlyDominatedBy v) xs w mw)
        maxw)
  , memberOfFilterSatisfies (StrictlyDominatedBy v)
                            (decStrictlyDominatedBy v) xs w mw

------------------------------------------------------------------------
-- 5.  ORDER, one step
------------------------------------------------------------------------

everyRemainderMemberIsBeatenByAStratumMember :
  (xs : List (List ℕ)) (v : List ℕ)
  → Mem v (remainder xs)
  → Σ[ w ∈ List ℕ ] (Mem w (stratum xs) × StrictlyDominatedBy v w)
everyRemainderMemberIsBeatenByAStratumMember xs v mem
  with everyRemainderMemberIsStrictlyDominated xs v mem
... | (u , mu , vu) = theDominatorCanBeChosenMaximal xs v u mu vu
