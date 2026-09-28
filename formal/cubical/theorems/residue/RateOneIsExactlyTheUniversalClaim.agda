{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- RateOneIsExactlyTheUniversalClaim
--
-- The count is here, over a finite population as a `List Bool`, and it
-- gives the comparison exactly: the universal claim IS the rate-one
-- case, and every strictly lower rate has tolerance.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   countIsAtMostLength   the rate is a rate: count ≤ length
--   allGivesFullCount     the Π forces count ≡ length
--   fullCountGivesAll     and is forced by it
--
-- Together: `count xs ≡ length xs` and `All isTrue xs` are the same
-- claim.  So `DARWIN_GODEL_MATH.md` (absent from this repository) §7's label criterion is not a
-- different KIND of criterion from its thresholds — it is the threshold
-- at 1, where the tolerance is zero.  §4 exhibits a population where a
-- strictly lower threshold survives a failure that kills the Π, which is
-- what "tolerable benchmark noise" means and why the label admits none.
------------------------------------------------------------------------

module RateOneIsExactlyTheUniversalClaim where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; injSuc)
open import Cubical.Data.Nat.Order using (_≤_ ; _<_ ; ≤-refl ; ≤-suc ; suc-≤-suc ; ¬m<m)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  A finite population, the universal claim, and the count
------------------------------------------------------------------------

All : List Bool → Type
All []       = Unit
All (b ∷ bs) = (b ≡ true) × All bs

count : List Bool → ℕ
count []           = 0
count (true  ∷ bs) = suc (count bs)
count (false ∷ bs) = count bs

length : List Bool → ℕ
length []       = 0
length (_ ∷ bs) = suc (length bs)

countIsAtMostLength : (bs : List Bool) → count bs ≤ length bs
countIsAtMostLength []           = ≤-refl
countIsAtMostLength (true  ∷ bs) = suc-≤-suc (countIsAtMostLength bs)
countIsAtMostLength (false ∷ bs) = ≤-suc (countIsAtMostLength bs)

------------------------------------------------------------------------
-- 2.  The universal claim and rate one are the same claim
------------------------------------------------------------------------

allGivesFullCount : (bs : List Bool) → All bs → count bs ≡ length bs
allGivesFullCount []           _        = refl
allGivesFullCount (true  ∷ bs) (_ , as) = cong suc (allGivesFullCount bs as)
allGivesFullCount (false ∷ bs) (e , _)  = ⊥.rec (falseIsNotTrue e)
  where
    isFalse : Bool → Type
    isFalse false = Unit
    isFalse true  = ⊥

    falseIsNotTrue : ¬ (false ≡ true)
    falseIsNotTrue p = transport (cong isFalse p) tt

fullCountGivesAll : (bs : List Bool) → count bs ≡ length bs → All bs
fullCountGivesAll []           _ = tt
fullCountGivesAll (true  ∷ bs) e = refl , fullCountGivesAll bs (injSuc e)
fullCountGivesAll (false ∷ bs) e =
  ⊥.rec (¬m<m (subst (_≤ length bs) e (countIsAtMostLength bs)))

------------------------------------------------------------------------
-- 3.  So the label criterion is the threshold at 1
--
-- `count bs ≡ length bs` is a statement about a rate, and §2 says it is
-- the universal claim verbatim.  A label is therefore the degenerate
-- threshold — the one where a single failure moves the count off the
-- length and there is nothing left to tolerate.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 4.  And a strictly lower threshold survives what kills it
------------------------------------------------------------------------

population : List Bool
population = true ∷ false ∷ []

theUniversalClaimFails : ¬ All population
theUniversalClaimFails (_ , (e , _)) = transport (cong isFalse e) tt
  where
    isFalse : Bool → Type
    isFalse false = Unit
    isFalse true  = ⊥

butOneStillPasses : 1 ≤ count population
butOneStillPasses = ≤-refl

theThresholdAtOneAndBelow :
  (¬ All population) × (1 ≤ count population)
theThresholdAtOneAndBelow = theUniversalClaimFails , butOneStillPasses


------------------------------------------------------------------------
-- "More than half", as `MajorityLiesStrictlyBetweenAllAndSome` states it:
--
--   Majority bs = length bs < 2 · count bs
--
-- and it separates three claim-shapes with two populations rather than
-- one, because one population cannot exhibit strictness on both sides:
--
--   majorityWithoutAll       2 of 3: the majority holds, the Π fails
--   positiveWithoutMajority  1 of 3: the existential holds, majority fails
--
-- So the three shapes are pairwise distinct at the thresholds shown, and
-- the rate-one case proved here (`fullCountGivesAll`) is the top of that
-- ordering, not a point on a continuum that was never exhibited.
--
------------------------------------------------------------------------
