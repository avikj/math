{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheParetoStratumIsDecidableAndTheFilterIsExact
--
-- A Pareto stratification EXISTS constructively for an arbitrary
-- archive: the decision on `≼` exists, and with it the stratum is not
-- merely a specification but a computed list.  That matters for
-- `DARWIN_GODEL_MATH.md` (absent from this repository) §5.2 in a way
-- `AParetoFitnessHasNoBestAndEveryScalarisationAddsADecision` could not
-- say: §5.2's controller "first selects a Pareto stratum S" and samples
-- inside it, and a controller cannot select what it cannot compute.
-- That module proves there is no best to pick; this one proves
-- the thing §5.2 picks INSTEAD is constructible.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   dec≤ / dec≼             the product order on fitness vectors is
--                           decidable, from `splitℕ-≤` alone
--   decStrictlyDominatedBy    hence so is strict domination
--   decIsParetoMaximal      hence so is Pareto-maximality against a
--                           finite archive, reusing `decAny`
--   filterDec               the stratum, as a list
--   stratumOnlyKeepsMaximal    soundness — everything kept is maximal
--   stratumKeepsEveryMaximal   completeness — nothing maximal is dropped
--
-- Soundness and completeness together are why "the filter is exact":
-- the computed stratum and the specified stratum have the same members,
-- so §5.2's first stage denotes.
--
-- ────────────────────────────────────────────────────────────────────
-- NO NOVELTY.  Decidability of a product order from decidability of its
-- factors, and the soundness/completeness of a decidable filter, are
-- elementary.
------------------------------------------------------------------------

module TheParetoStratumIsDecidableAndTheFilterIsExact where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_≤_ ; _<_ ; <-asym ; splitℕ-≤)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet
  using (Any ; decAny)
open import AParetoFitnessHasNoBestAndEveryScalarisationAddsADecision
  using (_≼_)

private
  variable
    A : Type

------------------------------------------------------------------------
-- 1.  The order is decidable
------------------------------------------------------------------------

dec≤ : (m n : ℕ) → Dec (m ≤ n)
dec≤ m n with splitℕ-≤ m n
... | inl p = yes p
... | inr q = no (<-asym q)

dec≼ : (v w : List ℕ) → Dec (v ≼ w)
dec≼ []       []       = yes tt
dec≼ []       (_ ∷ _)  = no (λ z → z)
dec≼ (_ ∷ _)  []       = no (λ z → z)
dec≼ (x ∷ xs) (y ∷ ys) with dec≤ x y
... | no ¬p = no (λ r → ¬p (fst r))
... | yes p with dec≼ xs ys
...   | yes q = yes (p , q)
...   | no ¬q = no (λ r → ¬q (snd r))

decNeg : {B : Type} → Dec B → Dec (¬ B)
decNeg (yes b) = no (λ n → n b)
decNeg (no ¬b) = yes ¬b

------------------------------------------------------------------------
-- 2.  Hence Pareto-maximality against a finite archive is decidable
------------------------------------------------------------------------

-- `StrictlyDominatedBy v w`: w beats v (v ≼ w, and not the reverse).  The
-- name was `StrictlyDominates`, which read the arguments backwards.
StrictlyDominatedBy : List ℕ → List ℕ → Type
StrictlyDominatedBy v w = (v ≼ w) × (¬ (w ≼ v))

decStrictlyDominatedBy : (v w : List ℕ) → Dec (StrictlyDominatedBy v w)
decStrictlyDominatedBy v w with dec≼ v w
... | no ¬p = no (λ r → ¬p (fst r))
... | yes p with decNeg (dec≼ w v)
...   | yes ¬q = yes (p , ¬q)
...   | no ¬¬q = no (λ r → ¬¬q (snd r))

IsParetoMaximal : List ℕ → List (List ℕ) → Type
IsParetoMaximal v xs = ¬ Any (StrictlyDominatedBy v) xs

decIsParetoMaximal :
  (v : List ℕ) (xs : List (List ℕ)) → Dec (IsParetoMaximal v xs)
decIsParetoMaximal v xs =
  decNeg (decAny (StrictlyDominatedBy v) (decStrictlyDominatedBy v) xs)

------------------------------------------------------------------------
-- 3.  The stratum, as a computed list
------------------------------------------------------------------------

All : (P : A → Type) → List A → Type
All P []       = Unit
All P (x ∷ xs) = P x × All P xs

filterDec :
  (P : A → Type) → ((a : A) → Dec (P a)) → List A → List A
filterDec P d []       = []
filterDec P d (x ∷ xs) with d x
... | yes _ = x ∷ filterDec P d xs
... | no  _ = filterDec P d xs

filterDecOnlyKeepsSatisfiers :
  (P : A → Type) (d : (a : A) → Dec (P a)) (xs : List A)
  → All P (filterDec P d xs)
filterDecOnlyKeepsSatisfiers P d []       = tt
filterDecOnlyKeepsSatisfiers P d (x ∷ xs) with d x
... | yes p = p , filterDecOnlyKeepsSatisfiers P d xs
... | no  _ = filterDecOnlyKeepsSatisfiers P d xs

filterDecKeepsEverySatisfier :
  (P : A → Type) (d : (a : A) → Dec (P a)) (xs : List A) (a : A)
  → Any (λ y → y ≡ a) xs → P a → Any (λ y → y ≡ a) (filterDec P d xs)
filterDecKeepsEverySatisfier P d []       a e        pa = ⊥.rec e
filterDecKeepsEverySatisfier P d (x ∷ xs) a (inl q)  pa with d x
... | yes _ = inl q
... | no ¬p = ⊥.rec (¬p (subst P (sym q) pa))
filterDecKeepsEverySatisfier P d (x ∷ xs) a (inr m)  pa with d x
... | yes _ = inr (filterDecKeepsEverySatisfier P d xs a m pa)
... | no  _ = filterDecKeepsEverySatisfier P d xs a m pa

------------------------------------------------------------------------
-- 4.  So §5.2's first stage denotes
------------------------------------------------------------------------

stratum : List (List ℕ) → List (List ℕ)
stratum xs = filterDec (λ v → IsParetoMaximal v xs) (λ v → decIsParetoMaximal v xs) xs

stratumOnlyKeepsMaximal :
  (xs : List (List ℕ)) → All (λ v → IsParetoMaximal v xs) (stratum xs)
stratumOnlyKeepsMaximal xs =
  filterDecOnlyKeepsSatisfiers (λ v → IsParetoMaximal v xs)
                               (λ v → decIsParetoMaximal v xs) xs

stratumKeepsEveryMaximal :
  (xs : List (List ℕ)) (v : List ℕ)
  → Any (λ y → y ≡ v) xs → IsParetoMaximal v xs
  → Any (λ y → y ≡ v) (stratum xs)
stratumKeepsEveryMaximal xs v =
  filterDecKeepsEverySatisfier (λ u → IsParetoMaximal u xs)
                               (λ u → decIsParetoMaximal u xs) xs v

------------------------------------------------------------------------
-- Non-emptiness of the stratum for a non-empty archive is proved in
-- `ANonEmptyArchiveHasANonEmptyStratum`:
--
--   ⊏-irrefl / ⊏-trans   strict domination; transitivity is NOT
--                        inherited from `≼-trans`, the negative half
--                        has to be argued
--   anyMap               `Any` is functorial in its predicate
--   maximalExists        every non-empty archive has a member maximal
--                        in it — list induction, DECIDING at each step
--                        whether the tail's maximum beats the head; if
--                        it does, the HEAD is maximal, because anything
--                        beating the head would beat it by transitivity
--   stratumIsNonEmpty    hence `stratum (x ∷ xs)` has a member
--
-- The decision that makes the induction constructive is
-- `decStrictlyDominatedBy` above; without it this would need excluded
-- middle, which is the point of having proved decidability first.
------------------------------------------------------------------------
