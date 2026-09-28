{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AParetoFitnessHasNoBestAndEveryScalarisationAddsADecision
--
-- §5.2 lists eight objectives, and says the
-- controller "maintains Pareto strata" and samples WITHIN a stratum.
-- The design is stated; the reason it must be that shape is not.
--
-- It is forced, and the two halves are checked here.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   ≼-refl / ≼-trans / ≼-antisym
--       the pointwise (product) order on fitness vectors is a partial
--       order — antisymmetry included, so it really is an order and not
--       merely a preorder, unlike the threshold ⊑ elsewhere in this
--       corpus
--   incomparable
--       (2,0) and (0,3) dominate each other in neither direction, so
--       the order is NOT total and "the best node" does not denote
--   sumIsMonotone
--       a scalarisation cannot CONTRADICT dominance …
--   scalarisationDecidesAnIncomparablePair
--       … but it does DECIDE the incomparable pair above: sum says
--       2 < 3 where the objectives say nothing
--   monotoneStrictnessRefutesDominance
--       and generally, for any monotone f, `f v < f w` refutes `w ≼ v`
--       — which is exactly the strength a scalarisation has and no more
--
-- **So a scalar fitness is a strict extension of the objective order,
-- and every such extension is a CHOICE that the objectives do not
-- license.**  That is why §5.2's two-stage shape — pick a stratum, then
-- sample inside it — is not a refinement of "pick the best": there is
-- no best to pick, and any rule that produces one has smuggled in a
-- preference ordering under the name of a measurement.
--
-- §2's seam 3, checked in
-- `AscendingFirstIsTheWorstUnlessTheArchiveIsConstant`, is a bug in a
-- branch that assumes a TOTAL order on accuracy.  §5.2 says the fitness
-- is a vector.  Those two facts sit in one note: the seam is in code
-- selecting by a scalar, and the design section says the scalar does not
-- exist.  The two sections are about the same missing total order.
--
-- ────────────────────────────────────────────────────────────────────
-- The product order, its failure of totality, and the fact
-- that monotone scalarisations are strict extensions are standard
-- multi-objective optimisation, going back to Pareto (`Cours
-- d'économie politique`, 1896) and Edgeworth before him.
------------------------------------------------------------------------

module AParetoFitnessHasNoBestAndEveryScalarisationAddsADecision where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm ; snotz)
open import Cubical.Data.Nat.Order
  using (_≤_ ; _<_ ; ≤-refl ; ≤-trans ; ≤-antisym ; ≤-+-≤ ; ¬m<m)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  The product order on fitness vectors
------------------------------------------------------------------------

_≼_ : List ℕ → List ℕ → Type
[]       ≼ []       = Unit
[]       ≼ (_ ∷ _)  = ⊥
(_ ∷ _)  ≼ []       = ⊥
(x ∷ xs) ≼ (y ∷ ys) = (x ≤ y) × (xs ≼ ys)

≼-refl : (v : List ℕ) → v ≼ v
≼-refl []       = tt
≼-refl (x ∷ xs) = ≤-refl , ≼-refl xs

≼-trans : (u v w : List ℕ) → u ≼ v → v ≼ w → u ≼ w
≼-trans []       []       []       _          _          = tt
≼-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (le , les) (le' , les') =
  ≤-trans le le' , ≼-trans xs ys zs les les'

≼-antisym : (v w : List ℕ) → v ≼ w → w ≼ v → v ≡ w
≼-antisym []       []       _          _          = refl
≼-antisym (x ∷ xs) (y ∷ ys) (le , les) (ge , ges) =
  cong₂ _∷_ (≤-antisym le ge) (≼-antisym xs ys les ges)

------------------------------------------------------------------------
-- 2.  It is not total, so "the best node" does not denote
------------------------------------------------------------------------

yieldFirst costFirst : List ℕ
yieldFirst = 2 ∷ 0 ∷ []
costFirst  = 0 ∷ 3 ∷ []

¬2≤0 : ¬ (2 ≤ 0)
¬2≤0 (k , e) = snotz (sym (+-comm k 2) ∙ e)

¬3≤0 : ¬ (3 ≤ 0)
¬3≤0 (k , e) = snotz (sym (+-comm k 3) ∙ e)

incomparable : (¬ (yieldFirst ≼ costFirst)) × (¬ (costFirst ≼ yieldFirst))
incomparable = (λ p → ¬2≤0 (fst p)) , (λ p → ¬3≤0 (fst (snd p)))

------------------------------------------------------------------------
-- 3.  A scalarisation cannot contradict dominance
------------------------------------------------------------------------

sum : List ℕ → ℕ
sum []       = 0
sum (x ∷ xs) = x + sum xs

sumIsMonotone : (v w : List ℕ) → v ≼ w → sum v ≤ sum w
sumIsMonotone []       []       _          = ≤-refl
sumIsMonotone (x ∷ xs) (y ∷ ys) (le , les) =
  ≤-+-≤ le (sumIsMonotone xs ys les)

-- the general strength of ANY monotone scalarisation, and its limit
monotoneStrictnessRefutesDominance :
  (f : List ℕ → ℕ)
  → ((v w : List ℕ) → v ≼ w → f v ≤ f w)
  → (v w : List ℕ) → f v < f w → ¬ (w ≼ v)
monotoneStrictnessRefutesDominance f mono v w lt dom =
  ¬m<m (≤-trans lt (mono w v dom))

------------------------------------------------------------------------
-- 4.  But it decides a pair the objectives leave undecided
------------------------------------------------------------------------

sumOrdersThem : sum yieldFirst < sum costFirst
sumOrdersThem = 0 , refl

scalarisationDecidesAnIncomparablePair :
    (¬ (yieldFirst ≼ costFirst))
  × (¬ (costFirst ≼ yieldFirst))
  × (sum yieldFirst < sum costFirst)
scalarisationDecidesAnIncomparablePair =
  fst incomparable , snd incomparable , sumOrdersThem

------------------------------------------------------------------------
-- The decision on `≼`, and the constructive existence of a Pareto
-- stratification for an arbitrary archive, are proved in
-- `TheParetoStratumIsDecidableAndTheFilterIsExact`:
--
--   dec≤ / dec≼≼           from `splitℕ-≤` alone
--   decStrictlyDominatedBy
--   decIsParetoMaximal     against a finite archive, reusing `decAny`
--   stratum                the maximal layer, as a COMPUTED list
--   stratumOnlyKeepsMaximal / stratumKeepsEveryMaximal
--                          sound and complete, so the computed stratum
--                          and the specified one have the same members
--
-- Here: there is no best to pick.  There: the thing §5.2 picks INSTEAD — "the
-- controller first selects a Pareto stratum S" — is constructible, and
-- a controller cannot select what it cannot compute.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §5.2's objectives include wall time, tokens, and dollar cost, which
-- are to be MINIMISED; nothing above flips any coordinate, so the
-- theorems are about a vector all of whose coordinates point the same
-- way, and applying them needs the costs negated first.  The min-plus
-- line shows twice that reversing an order is load-bearing, so the flip
-- has its own theorem, in
-- `FlippingACostCoordinateIsSoundButNotFaithful`.
--
--   Vec ds / Dom ds   vectors over a DIRECTION list, and MIXED
--                     dominance: `≤` at a benefit coordinate, `≥` at a
--                     cost coordinate — what §5.2 actually means
--   ∸-antitone        from the monus adjunction on the min-plus line
--   flipWith cap      `cap ∸ x` at a cost coordinate
--   flipIsSound       mixed dominance IMPLIES ordinary `≼` of the
--                     flipped vectors, so §§1–4 above transfer
--   flipIsNotFaithful and the CONVERSE FAILS: at `cap = 3` the costs
--                     `5` and `7` both flip to `0`
--
-- **"Negated first" is half true.**  Flipping suffices to
-- APPLY these theorems — soundness is the only direction that needs.
-- It does NOT suffice to transport a conclusion back, because the cap
-- identifies every cost above it.  The honest form is "negate the
-- costs, and pick a cap above every cost you will ever compare", which
-- is a modelling obligation and not a rewriting step.
--
------------------------------------------------------------------------
