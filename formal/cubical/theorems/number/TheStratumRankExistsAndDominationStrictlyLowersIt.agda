{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheStratumRankExistsAndDominationStrictlyLowersIt
--
-- ON THE NAME, since this repository's rule is to lead with the
-- tradition's term.  **There is
-- no Indian source term for this object and none is invented.**  The
-- object is the rank of a candidate in iterated non-dominated sorting
-- — Goldberg 1989, and the fast-non-dominated-sort of Deb, Pratap,
-- Agarwal & Meyarivan 2002 — and that is where it comes from.  The
-- naming rule's own guard says to say so rather than to attach a
--  label to material that is not Indian; this file is an
-- instance of that guard, and the English name is a decision, not a
-- default.  (Where the same corpus DOES have the term — ṛṇa-dhana for
-- the debt/asset reading, samacchheda for equalising divisors — the
-- files carry it.)
--
-- WHAT IS PROVED
--
--   rank n xs v       the index of v's stratum: 0 if v is maximal in
--                     the archive, else one more than its rank in the
--                     remainder.  Fuel-recursive, no `Fin`, no
--                     well-founded recursion
--   memberIntoFilterOut
--                     a member failing the predicate is a member of the
--                     complement (arbitrary decidable predicate)
--   rankDominatorIsSmaller
--                     **if w strictly dominates v and both are in the
--                     archive, then `rank w < rank v`** — given enough
--                     fuel, which is `lengthL xs ≤ n`
--
-- **WHY THE FUEL HYPOTHESIS IS NOT A BLEMISH.**  At `n = 0` the rank of
-- everything is 0 and the statement would be false; the hypothesis
-- `lengthL xs ≤ n` makes that case VACUOUS rather than excluded,
-- because a list of length ≤ 0 is empty and has no members.  The same
-- hypothesis is what `fuelSuffices` already needed for termination, so
-- the rank costs no new assumption.
--
-- **WHAT THE RANK BUYS OVER "SOME EARLIER STRATUM".**  A number, hence
-- a comparison that composes: from `rank w < rank v` and
-- `rank z < rank w` one gets `rank z < rank v` by transitivity on ℕ,
-- whereas "beaten by a member of an earlier stratum" needs the whole
-- stratification to chain.  It is also the form in which selection
-- pressure is usually stated.
------------------------------------------------------------------------

module TheStratumRankExistsAndDominationStrictlyLowersIt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order
  using (_≤_ ; _<_ ; zero-≤ ; suc-≤-suc ; pred-≤-pred ; ≤-trans)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet
  using (memberToAny)
open import OneStepCoverageAndDisjointnessOfTheLayer using (Mem)
open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (StrictlyDominatedBy ; IsParetoMaximal ; decIsParetoMaximal)
open import TheRemainderIsStrictlyShorterSoTheStratificationHasAMeasure
  using (lengthL ; filterOut ; remainder ; theRemainderIsStrictlyShorter)
open import TheStratificationTerminatesOnItsOwnLength
  using (lengthZeroGivesNil)

private
  variable
    A : Type

------------------------------------------------------------------------
-- 1.  Into the complement
------------------------------------------------------------------------

memberIntoFilterOut :
  (P : A → Type) (d : (a : A) → Dec (P a)) (xs : List A) (a : A)
  → Mem a xs → ¬ P a → Mem a (filterOut P d xs)
memberIntoFilterOut P d []       a e       ¬p = ⊥.rec e
memberIntoFilterOut P d (x ∷ xs) a m       ¬p with d x
memberIntoFilterOut P d (x ∷ xs) a (inl q) ¬p | yes px =
  ⊥.rec (¬p (subst P q px))
memberIntoFilterOut P d (x ∷ xs) a (inr r) ¬p | yes _ =
  memberIntoFilterOut P d xs a r ¬p
memberIntoFilterOut P d (x ∷ xs) a (inl q) ¬p | no _ = inl q
memberIntoFilterOut P d (x ∷ xs) a (inr r) ¬p | no _ =
  inr (memberIntoFilterOut P d xs a r ¬p)

------------------------------------------------------------------------
-- 2.  The rank
------------------------------------------------------------------------

rank : ℕ → List (List ℕ) → List ℕ → ℕ
rank zero    xs       v = 0
rank (suc n) []       v = 0
rank (suc n) (x ∷ xs) v with decIsParetoMaximal v (x ∷ xs)
... | yes _ = 0
... | no  _ = suc (rank n (remainder (x ∷ xs)) v)

------------------------------------------------------------------------
-- 3.  A dominator has strictly smaller rank
------------------------------------------------------------------------

rankDominatorIsSmaller :
  (n : ℕ) (xs : List (List ℕ)) (v w : List ℕ)
  → lengthL xs ≤ n
  → Mem v xs → Mem w xs → StrictlyDominatedBy v w
  → rank n xs w < rank n xs v
rankDominatorIsSmaller zero    xs       v w h memV memW sd =
  ⊥.rec (subst (Mem v) (lengthZeroGivesNil xs h) memV)
rankDominatorIsSmaller (suc n) []       v w h memV memW sd = ⊥.rec memV
rankDominatorIsSmaller (suc n) (x ∷ xs) v w h memV memW sd
  with decIsParetoMaximal v (x ∷ xs)
... | yes vmax =
  ⊥.rec (vmax (memberToAny (StrictlyDominatedBy v) w (x ∷ xs) memW sd))
... | no ¬vmax with decIsParetoMaximal w (x ∷ xs)
...   | yes _    = suc-≤-suc zero-≤
...   | no ¬wmax =
  suc-≤-suc
    (rankDominatorIsSmaller n (remainder (x ∷ xs)) v w
      (pred-≤-pred (≤-trans (theRemainderIsStrictlyShorter x xs) h))
      (memberIntoFilterOut (λ u → IsParetoMaximal u (x ∷ xs))
        (λ u → decIsParetoMaximal u (x ∷ xs)) (x ∷ xs) v memV ¬vmax)
      (memberIntoFilterOut (λ u → IsParetoMaximal u (x ∷ xs))
        (λ u → decIsParetoMaximal u (x ∷ xs)) (x ∷ xs) w memW ¬wmax)
      sd)
