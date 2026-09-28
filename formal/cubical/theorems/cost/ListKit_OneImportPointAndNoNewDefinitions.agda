{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ListKit_OneImportPointAndNoNewDefinitions
--
-- ON THE NAME.  **This file is plumbing** —
-- `Any`, `Mem`, filters over lists — with no source in any tradition
-- and no mathematical content of its own, so it takes an English name
-- and says why.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS, AND WHAT IT DELIBERATELY IS NOT.
--
-- A factoring fact: eleven modules import a file named for a position in
-- the saptabhag, and most of them want only `Any`, `decAny` and
-- `memberToAny` — list plumbing that landed there because that is where
-- it was first needed.  The corpus also carries **`All` three times and
-- `Mem` four times**, in modules named for unrelated theorems.
--
-- This module is ONE IMPORT POINT for the canonical copies.  It
-- **defines nothing**: every name below is re-exported from where it
-- already lives, so importing it cannot create a fourth copy of
-- anything, and deleting it would break nothing but convenience.
--
-- **`All` IS DELIBERATELY ABSENT.**  There are three definitions —
-- `TheParetoStratumIsDecidableAndTheFilterIsExact.All`,
-- `OrderAstiNasti_AnEnumerableRemedySetKillsTheFourthCorner.All`
-- (identical), `EveryRemainderMemberIsStrictlyDominated.AllL` (same
-- again, different name), and `RateOneIsExactlyTheUniversalClaim.All`
-- (a different, `Bool`-specific thing).  Re-exporting one would pick a
-- winner.
------------------------------------------------------------------------

module ListKit_OneImportPointAndNoNewDefinitions where

open import OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet public
  using (Any ; decAny ; memberToAny)
open import ANonEmptyArchiveHasANonEmptyStratum public
  using (anyMap)
open import EveryRemainderMemberIsStrictlyDominated public
  using (anyToMember)
open import OneStepCoverageAndDisjointnessOfTheLayer public
  using (Mem ; memberOfFilterSatisfies ; memberOfFilterOutFails
        ; memberSplits ; noMemberInBoth)
open import TheStratificationCoversAndItsStrataArePairwiseDisjoint public
  using (MemSome ; filterDecSubset ; filterOutSubset)
open import EveryRemainderMemberIsBeatenByAStratumMember public
  using (memberIntoFilter)
open import TheStratumRankExistsAndDominationStrictlyLowersIt public
  using (memberIntoFilterOut)
open import TheParetoStratumIsDecidableAndTheFilterIsExact public
  using (filterDec ; filterDecOnlyKeepsSatisfiers ; filterDecKeepsEverySatisfier)
open import TheRemainderIsStrictlyShorterSoTheStratificationHasAMeasure public
  using (filterOut ; lengthL ; partitionLength
        ; nonEmptyFilterShortensTheComplement)
