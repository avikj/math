{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- EveryRemainderMemberIsStrictlyDominated
--
-- The Pareto stratification has three properties of the OUTPUT:
--   COVERAGE, DISJOINTNESS, and ORDER: a member of an earlier layer
--   relates by domination to a member of a later one, which is the
--   property that makes 'stratification' mean what §5.2 wants.
-- ORDER is the one that matters, and this is its first half.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   filterOutOnlyKeepsNonSatisfiers
--                the complement of the filter keeps exactly what fails
--                the predicate — the mirror of the soundness lemma the
--                measure module already had
--   anyToMember  an `Any` yields a witness TOGETHER WITH its membership,
--                which plain `anyToΣ` discards
--   everyRemainderMemberIsStrictlyDominated
--                every member of `remainder xs` is strictly dominated
--                by a member OF `xs`
--
-- **The double negation is the whole difficulty and it is decidable
-- away.**  `IsParetoMaximal v xs` is `¬ Any (StrictlyDominatedBy v) xs`,
-- so failing it gives `¬ ¬ Any …`, not `Any …`.  The dominator is
-- recovered only because `decAny decStrictlyDominatedBy` makes that `Any`
-- DECIDABLE, hence stable.
------------------------------------------------------------------------

module EveryRemainderMemberIsStrictlyDominated where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no ; Dec→Stable)

open import OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet
  using (Any ; decAny)
open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (StrictlyDominatedBy ; decStrictlyDominatedBy ; IsParetoMaximal
        ; decIsParetoMaximal)
open import TheRemainderIsStrictlyShorterSoTheStratificationHasAMeasure
  using (filterOut ; remainder)

private
  variable
    A : Type

------------------------------------------------------------------------
-- 1.  The complement keeps exactly the non-satisfiers
------------------------------------------------------------------------

AllL : (P : A → Type) → List A → Type
AllL P []       = Unit
AllL P (x ∷ xs) = P x × AllL P xs

filterOutOnlyKeepsNonSatisfiers :
  (P : A → Type) (d : (a : A) → Dec (P a)) (xs : List A)
  → AllL (λ a → ¬ P a) (filterOut P d xs)
filterOutOnlyKeepsNonSatisfiers P d []       = tt
filterOutOnlyKeepsNonSatisfiers P d (x ∷ xs) with d x
... | yes _ = filterOutOnlyKeepsNonSatisfiers P d xs
... | no ¬p = ¬p , filterOutOnlyKeepsNonSatisfiers P d xs

allAtMemberL :
  (P : A → Type) (xs : List A) (a : A)
  → AllL P xs → Any (λ y → y ≡ a) xs → P a
allAtMemberL P []       a _          e       = ⊥.rec e
allAtMemberL P (x ∷ xs) a (p , _)    (inl q) = subst P q p
allAtMemberL P (x ∷ xs) a (_ , rest) (inr m) = allAtMemberL P xs a rest m

------------------------------------------------------------------------
-- 2.  An Any yields its witness together with the membership
------------------------------------------------------------------------

anyToMember :
  (P : A → Type) (xs : List A)
  → Any P xs → Σ[ x ∈ A ] ((Any (λ y → y ≡ x) xs) × P x)
anyToMember P []       e       = ⊥.rec e
anyToMember P (x ∷ xs) (inl p) = x , (inl refl , p)
anyToMember P (x ∷ xs) (inr a) with anyToMember P xs a
... | (w , (mem , p)) = w , (inr mem , p)

------------------------------------------------------------------------
-- 3.  So nothing dropped from a layer was undominated
------------------------------------------------------------------------

everyRemainderMemberIsStrictlyDominated :
  (xs : List (List ℕ)) (v : List ℕ)
  → Any (λ y → y ≡ v) (remainder xs)
  → Σ[ w ∈ List ℕ ]
      ((Any (λ y → y ≡ w) xs) × StrictlyDominatedBy v w)
everyRemainderMemberIsStrictlyDominated xs v mem =
  anyToMember (StrictlyDominatedBy v) xs dominated
  where
    notMaximal : ¬ IsParetoMaximal v xs
    notMaximal =
      allAtMemberL (λ u → ¬ IsParetoMaximal u xs)
        (filterOut (λ u → IsParetoMaximal u xs)
                   (λ u → decIsParetoMaximal u xs) xs)
        v
        (filterOutOnlyKeepsNonSatisfiers (λ u → IsParetoMaximal u xs)
                                         (λ u → decIsParetoMaximal u xs) xs)
        mem

    dominated : Any (StrictlyDominatedBy v) xs
    dominated =
      Dec→Stable (decAny (StrictlyDominatedBy v) (decStrictlyDominatedBy v) xs)
                 notMaximal
