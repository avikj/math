{-# OPTIONS --cubical --safe --no-import-sorts #-}
------------------------------------------------------------------------
-- सम-सङ्ख्या — the corpus's `_~_` is same-multiset wherever that is
-- statable.
--
-- On a discrete step type, `_~_` is EXACTLY equal counts.  The
-- proof is composition — `_~_` and `_≈_` have the same four constructors
-- (walked both ways), `_≈_` gives equal counts (`Uniqueness`), equal counts
-- build a `Perm` (`Uniqueness`, using the decidable equality), and a `Perm`
-- is an adjacent chain (`TheUsualReasons`).  So the relation is not finer
-- than same-multiset: it is same-multiset.
------------------------------------------------------------------------
module SamaCount_TheCorpusRelationIsExactlySameCountOnADiscreteStepTypeSoItIsNotFinerThanSameMultiset where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Relation.Nullary using (Discrete)

open import OrderIndependenceTransfersAlongAnyNumberOfSteps using (Step)
open import PairwiseCommutationGivesEveryOrder using (_~_ ; ~nil ; ~cons ; ~swap ; ~trans)
open import TheUsualReasonsMadeExplicitTheInductivePermutationRelationEmbedsInAdjacentTranspositions
  using (_≈_ ; ≈nil ; ≈cons ; ≈swap ; ≈trans ; toCorpusRelation ; permIsAnAdjacentChain)
open import Ekatva_TheFirmFactorisationIsUniqueTwoPrimeListsWithOneProductAreAPermutationSoTheValuationIsWellDefinedAndPermIsExactlySameCount
  using (module Bahulya)

module _ {S T : Type} (C : S → T) where

  -- the constructor-for-constructor walk in the other direction
  fromCorpusRelation : {xs ys : List (Step C)} → _~_ C xs ys → xs ≈ ys
  fromCorpusRelation ~nil         = ≈nil
  fromCorpusRelation (~cons r)    = ≈cons (fromCorpusRelation r)
  fromCorpusRelation ~swap        = ≈swap
  fromCorpusRelation (~trans r s) = ≈trans (fromCorpusRelation r) (fromCorpusRelation s)

  module _ (_≟_ : Discrete (Step C)) where
    open Bahulya _≟_

    count : Step C → List (Step C) → ℕ
    count = गणना

    ~→sameCount : {xs ys : List (Step C)} → _~_ C xs ys
                → (s : Step C) → count s xs ≡ count s ys
    ~→sameCount r = ≈-count (fromCorpusRelation r)

    sameCount→~ : (xs ys : List (Step C))
                → ((s : Step C) → count s xs ≡ count s ys) → _~_ C xs ys
    sameCount→~ xs ys h = toCorpusRelation C (permIsAnAdjacentChain (count-perm xs ys h))
