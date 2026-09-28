{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ANonEmptyArchiveHasANonEmptyStratum
--
-- `TheParetoStratumIsDecidableAndTheFilterIsExact` computed the maximal
-- layer.  For the empty archive it is empty; for a non-empty archive
-- non-emptiness needs an argument, made here.
--
-- Non-emptiness is not decoration.  DARWIN §5.2's controller "first
-- selects a Pareto stratum S" and then samples inside it; a stratum
-- that could be empty is a selection step that could have nothing to
-- sample from, which is a live failure mode for a scheduler and not a
-- pedantic gap.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   ⊏-irrefl            nothing strictly dominates itself
--   ⊏-trans             strict domination is transitive — needed, and
--                       NOT implied by `≼-trans` alone: the negative
--                       half is what does the work
--   anyMap              a pointwise implication maps over `Any`
--   maximalExists       EVERY non-empty archive has a member that is
--                       Pareto-maximal in it, by list induction with a
--                       decision at each step
--   stratumIsNonEmpty   hence the computed stratum of a non-empty
--                       archive has a member
--
-- The induction is the whole content: given a maximal `m` of the tail,
-- DECIDE whether `m` strictly dominates the head.  If not, `m` is still
-- maximal.  If it does, the HEAD is maximal — because anything beating
-- the head would beat `m` by transitivity, contradicting `m`'s
-- maximality.  That second branch is why `⊏-trans` is needed at all.
--
-- ────────────────────────────────────────────────────────────────────
-- NO NOVELTY.  "A finite non-empty set has a maximal element for a
-- decidable partial order" is elementary; it is proved here because the
-- constructive proof needs the decision
-- `TheParetoStratumIsDecidableAndTheFilterIsExact` supplies rather than
-- excluded middle.
------------------------------------------------------------------------

module ANonEmptyArchiveHasANonEmptyStratum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet
  using (Any)
open import AParetoFitnessHasNoBestAndEveryScalarisationAddsADecision
  using (_≼_ ; ≼-refl ; ≼-trans)
open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (StrictlyDominatedBy ; IsParetoMaximal ; decStrictlyDominatedBy
        ; stratum ; stratumKeepsEveryMaximal)

------------------------------------------------------------------------
-- 1.  Strict domination is irreflexive and transitive
--
-- Transitivity is not inherited from `≼-trans`: the negative component
-- has to be argued, and it is where the antisymmetric shape of `≼`
-- would otherwise be missed.
------------------------------------------------------------------------

⊏-irrefl : (v : List ℕ) → ¬ StrictlyDominatedBy v v
⊏-irrefl v (_ , ¬le) = ¬le (≼-refl v)

⊏-trans :
  (u v w : List ℕ)
  → StrictlyDominatedBy u v → StrictlyDominatedBy v w → StrictlyDominatedBy u w
⊏-trans u v w (uv , ¬vu) (vw , ¬wv) =
  ≼-trans u v w uv vw , λ wu → ¬wv (≼-trans w u v wu uv)

------------------------------------------------------------------------
-- 2.  Any is functorial in the predicate
------------------------------------------------------------------------

anyMap :
  {A : Type} {P Q : A → Type}
  → ((a : A) → P a → Q a) → (xs : List A) → Any P xs → Any Q xs
anyMap f []       e       = ⊥.rec e
anyMap f (x ∷ xs) (inl p) = inl (f x p)
anyMap f (x ∷ xs) (inr a) = inr (anyMap f xs a)

------------------------------------------------------------------------
-- 3.  Every non-empty archive has a maximal member
------------------------------------------------------------------------

maximalExists :
  (x : List ℕ) (xs : List (List ℕ))
  → Σ[ m ∈ List ℕ ]
      ((Any (λ y → y ≡ m) (x ∷ xs)) × IsParetoMaximal m (x ∷ xs))
maximalExists x [] =
  x , (inl refl , λ where (inl sd) → ⊏-irrefl x sd)
maximalExists x (y ∷ ys) with maximalExists y ys
... | (m , (mem , max)) with decStrictlyDominatedBy m x
...   | no ¬beat = m , (inr mem , λ where
                          (inl sd)  → ¬beat sd
                          (inr rest) → max rest)
...   | yes beat = x , (inl refl , λ where
                          (inl sd)   → ⊏-irrefl x sd
                          (inr rest) →
                            max (anyMap (λ w xw → ⊏-trans m x w beat xw)
                                        (y ∷ ys) rest))

------------------------------------------------------------------------
-- 4.  Hence the computed stratum is non-empty
------------------------------------------------------------------------

stratumIsNonEmpty :
  (x : List ℕ) (xs : List (List ℕ))
  → Σ[ m ∈ List ℕ ] Any (λ y → y ≡ m) (stratum (x ∷ xs))
stratumIsNonEmpty x xs with maximalExists x xs
... | (m , (mem , max)) =
  m , stratumKeepsEveryMaximal (x ∷ xs) m mem max

------------------------------------------------------------------------
-- A STRATIFICATION — removing the layer and repeating — needs a
-- termination argument on the archive's length.  That argument is the
-- DECREASING MEASURE, built in
-- `TheRemainderIsStrictlyShorterSoTheStratificationHasAMeasure`:
--
--   filterOut / partitionLength   the filter and its complement
--                                 PARTITION the list, so their lengths
--                                 sum to the whole
--   memberMakesItNonEmpty
--   nonEmptyFilterShortensTheComplement
--   theRemainderIsStrictlyShorter instantiated at the Pareto stratum,
--                                 USING `stratumIsNonEmpty` above
--
-- THE DEPENDENCY CHAIN, WHICH CAN BE TAKEN IN NO OTHER ORDER:
-- decidability of the order gives a computable stratum; the computable
-- stratum plus a decision gives non-emptiness CONSTRUCTIVELY;
-- non-emptiness gives the strict decrease.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The theorems above are about a vector all of whose coordinates point
-- the same way, while §5.2's objectives include quantities to be
-- MINIMISED.  `maximalExists` transfers to MIXED vectors in
-- `RnaDhana_TheParetoMaximumTransfersToCostCoordinates`.
--
-- `mixedMaximalExists` proves that a non-empty archive of MIXED
-- benefit/cost vectors has a member nothing beats, by calling
-- `maximalExists` above on the flipped archive and pulling the result
-- back.  Nothing about maximality is re-proved there.
--
-- Two things about the price:
--
--   * The bound is needed only in the NEGATIVE half — soundness of the
--     flip is unconditional, and it is turning "the flipped z does not
--     beat the flipped u" back into "z does not beat u" that needs a
--     cap on u.  Since u is a member, an archive-wide bound suffices.
--   * The pull-back cannot go through the flipped element, because the
--     flip is not injective; it goes through `anyMapBack`, which
--     recovers a member of the ORIGINAL archive whose flip is the
--     maximal element found.
------------------------------------------------------------------------
