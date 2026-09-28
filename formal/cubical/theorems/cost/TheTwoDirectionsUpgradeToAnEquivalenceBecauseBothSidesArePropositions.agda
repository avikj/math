{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheTwoDirectionsUpgradeToAnEquivalenceBecauseBothSidesArePropositions
--
-- ON THE NAME.  Checked before naming: `.claude/hooks/priority-ledger.txt` (absent from this repository)
-- (CURRENT header) and `.claude/hooks/european-frame.txt` (absent from this repository); `formal/` and
-- invented.**  Counting how many members of a finite collection satisfy
-- a predicate is Jaina enumerative territory (*Anuyogadvra*,
-- *Sthnga*) and I have NOT established that as the source of
-- anything here; the h-level argument is Voevodsky's substrate, which
-- this repository declares as a tool and not a frame.  A  label
-- would assert a provenance nobody checked.
--
-- ────────────────────────────────────────────────────────────────────
-- THE AUDIT.  Target: `RateOneIsExactlyTheUniversalClaim`, an
-- `Exactly` — a biconditional claim.
--
-- **THE TITLE IS EARNED, IN THE WEAK SENSE, AND THAT WAS THE QUESTION
-- ASKED.**  Both directions are there: `allGivesFullCount` and
-- `fullCountGivesAll`, each a plain induction on the list.  Nothing is
-- assumed, nothing is smuggled, and neither direction is more expensive
-- than the other — which is what diagnostic (1) predicts when the two
-- sides are joined by an INDUCTION rather than by an implication
-- assumed or a path given.
--
-- **BUT THE MODULE SAYS SOMETHING STRONGER THAN IT PROVES, AND IT IS
-- TRUE, AND IT IS FREE.**  Its §2 heading is *"The universal claim and
-- rate one are the same claim"*, and its prose says `count bs ≡ length
-- bs` and `All bs` "are the same claim".  Two implications are not
-- sameness — they are logical equivalence, and for general types that
-- is strictly weaker than identity of the propositions.  §"WHAT IS
--
-- **HERE THE STRONGER READING HOLDS, AND THE REASON IS AN H-LEVEL, NOT
-- AN INDUCTION.**  `count bs ≡ length bs` is a path in ℕ and ℕ is a
-- set, so it is a proposition.  `All bs` is an iterated product of
-- paths in `Bool` and `Bool` is a set, so it is a proposition too.  Two
-- propositions that imply each other are EQUIVALENT — `propBiimpl→Equiv`
-- — so §2's two functions do assemble into `All bs ≃ (count bs ≡ length
-- bs)`, and the module's own prose was right by an argument it did not
-- give.
--
-- **THE POINT IS NOT THAT IT WAS WRONG.**  It is that "the same claim"
-- has two readings that read identically in prose, exactly like `free`
-- did at 28e9a0a4, and the one that holds here holds for a reason —
-- both sides being propositions — that fails as soon as the population
-- carries data rather than Booleans.  Over `List A` with `A` a general
-- type, `All` need not be a proposition and the upgrade is unavailable.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   isPropAll        `All bs` is a proposition, by induction with
--                    `isProp×` and `isSetBool`
--   isPropRateOne    so is `count bs ≡ length bs`, by `isSetℕ`
--   allIsRateOne     hence `All bs ≃ (count bs ≡ length bs)`, with the
--                    audited module's two functions REUSED, not
--                    restated
------------------------------------------------------------------------

module TheTwoDirectionsUpgradeToAnEquivalenceBecauseBothSidesArePropositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; propBiimpl→Equiv)
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Data.Nat using (ℕ ; isSetℕ)
open import Cubical.Data.Bool using (Bool ; true ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; isPropUnit)

open import RateOneIsExactlyTheUniversalClaim
  using (All ; count ; length ; allGivesFullCount ; fullCountGivesAll)

------------------------------------------------------------------------
-- 1.  Both sides are propositions
------------------------------------------------------------------------

isPropAll : (bs : List Bool) → isProp (All bs)
isPropAll []       = isPropUnit
isPropAll (b ∷ bs) = isProp× (isSetBool b true) (isPropAll bs)

isPropRateOne : (bs : List Bool) → isProp (count bs ≡ length bs)
isPropRateOne bs = isSetℕ (count bs) (length bs)

------------------------------------------------------------------------
-- 2.  So the two directions are an equivalence, not merely a pair
------------------------------------------------------------------------

allIsRateOne : (bs : List Bool) → All bs ≃ (count bs ≡ length bs)
allIsRateOne bs =
  propBiimpl→Equiv
    (isPropAll bs)
    (isPropRateOne bs)
    (allGivesFullCount bs)
    (fullCountGivesAll bs)
