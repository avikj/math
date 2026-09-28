{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- MajorityLiesStrictlyBetweenAllAndSome
--
-- Majority is stated here, and the three claim-shapes are separated by two
-- populations: majority holds where the universal claim fails, and
-- fails where the existential holds.  So the tolerances are strictly
-- ordered and `DARWIN_GODEL_MATH.md` (absent from this repository) §7's mixture of a label criterion
-- with rate thresholds is a mixture of genuinely different strengths,
-- not a stylistic one.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   majorityWithoutAll        `true ∷ true ∷ false ∷ []`
--                             — 2 of 3, so `3 < 4`; the Π fails
--   positiveWithoutMajority   `true ∷ false ∷ false ∷ []`
--                             — 1 of 3, so `3 < 2` is refuted; the
--                             existential still holds
--
-- With `RateOneIsExactlyTheUniversalClaim`'s equivalence (rate one IS
-- the Π), the three sit in order and each separation is witnessed.
------------------------------------------------------------------------

module MajorityLiesStrictlyBetweenAllAndSome where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-comm ; injSuc ; snotz)
open import Cubical.Data.Nat.Order using (_≤_ ; _<_)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import RateOneIsExactlyTheUniversalClaim
  using (All ; count ; length)

------------------------------------------------------------------------
-- 1.  The middle threshold, written without division
------------------------------------------------------------------------

Majority : List Bool → Type
Majority bs = length bs < 2 · count bs

Some : List Bool → Type
Some bs = 1 ≤ count bs

private
  isFalse : Bool → Type
  isFalse false = Unit
  isFalse true  = ⊥

  falseIsNotTrue : ¬ (false ≡ true)
  falseIsNotTrue p = transport (cong isFalse p) tt

------------------------------------------------------------------------
-- 2.  Majority holds where the universal claim fails
------------------------------------------------------------------------

twoOfThree : List Bool
twoOfThree = true ∷ true ∷ false ∷ []

majorityHolds : Majority twoOfThree
majorityHolds = 0 , refl

universalFails : ¬ All twoOfThree
universalFails (_ , (_ , (e , _))) = falseIsNotTrue e

majorityWithoutAll : (Majority twoOfThree) × (¬ All twoOfThree)
majorityWithoutAll = majorityHolds , universalFails

------------------------------------------------------------------------
-- 3.  The existential holds where majority fails
------------------------------------------------------------------------

oneOfThree : List Bool
oneOfThree = true ∷ false ∷ false ∷ []

someHolds : Some oneOfThree
someHolds = 0 , refl

majorityFails : ¬ Majority oneOfThree
majorityFails (k , p) = snotz (injSuc (injSuc (sym (+-comm k 4) ∙ p)))

positiveWithoutMajority : (Some oneOfThree) × (¬ Majority oneOfThree)
positiveWithoutMajority = someHolds , majorityFails

------------------------------------------------------------------------
-- 4.  The reading
--
-- `RateOneIsExactlyTheUniversalClaim` showed the label criterion is the
-- threshold at 1.  §2 and §3 show the thresholds below it are not all
-- the same: majority separates from the universal claim, and the bare
-- existential separates from majority.  So §7's list mixes at least
-- three strengths, and calling a label-failure "noise" would be reading
-- the strongest of them as the weakest.
--
-- Two populations are two populations; the general theorem over all
-- thresholds is `TheThresholdOrderIsTotalAndTheClaimIsAntitone`, below.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The general family is in `TheThresholdOrderIsTotalAndTheClaimIsAntitone`.
-- It states the family rather than exhibiting populations:
--
--   AtLeast p q bs        = p · length bs ≤ suc q · count bs
--   (p , q) ⊑ (p' , q')   = p · suc q' ≤ p' · suc q
--
--   ⊑-total          ANY two thresholds are comparable -- the chain,
--                    proved with no population in sight
--   atLeastAntitone  higher threshold ⇒ lower threshold, for EVERY
--                    population at once
--   allIsThresholdOne / thresholdOneFromAll
--                    the Π is exactly the top element (1 , 0)
--
-- so every fraction is analysed, by one theorem, and §2 and §4 above
-- become two instances of it rather than the evidence for it.
--
-- RELATION to the module above.  `Majority` here is
-- STRICT (length < 2 · count); `AtLeast 1 1` there is the non-strict
-- "at least half", which is weaker.  `≤` is a total PREORDER and not an
-- order: (1,1) and (2,3) name one rate and stay two pairs.
-- And the converse of antitone fails -- `majorityWithoutAll` above
-- is the witness that it fails -- so the chain orders the CLAIMS, not
-- the populations.
------------------------------------------------------------------------
