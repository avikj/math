{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S04ApohaFiniteCompletion
--
-- An exact reading of the phrase "completion along finite stages" in
-- S04Apoha.  Prefix k contains the observations 0,...,k-1.  A witnessed
-- horizon separation has finite support, and every finite-stage separation
-- gives a horizon witness.  Extracting such a finite stage from mere failure
-- of horizon indistinguishability is equivalent to Markov's Principle.
------------------------------------------------------------------------

module Swarm.S04ApohaFiniteCompletion where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (¬_; yes; no)
open import Apoha using (MP; Witnessed; MP→Witnessed; Witnessed→MP)

private
  variable
    ℓ : Level

HorizonInd : {X : Type ℓ} → (ℕ → X → Bool) → X → X → Type
HorizonInd O x y = (n : ℕ) → O n x ≡ O n y

HorizonSep : {X : Type ℓ} → (ℕ → X → Bool) → X → X → Type
HorizonSep O x y = Σ[ n ∈ ℕ ] (¬ (O n x ≡ O n y))

module Prefix {X : Type ℓ} (O : ℕ → X → Bool) (x y : X) where

  -- `Ind< k` and `Sep< k` see exactly indices 0,...,k-1.
  Ind< : ℕ → Type
  Ind< zero    = Unit
  Ind< (suc k) = Ind< k × (O k x ≡ O k y)

  Sep< : ℕ → Type
  Sep< zero    = ⊥
  Sep< (suc k) = Sep< k ⊎ (¬ (O k x ≡ O k y))

  -- The directed-system map: a separator already visible at stage k remains
  -- visible after adjoining observation k.
  sepStep : {k : ℕ} → Sep< k → Sep< (suc k)
  sepStep = inl

  horizonInd→prefixInd : HorizonInd O x y → (k : ℕ) → Ind< k
  horizonInd→prefixInd h zero    = tt
  horizonInd→prefixInd h (suc k) = horizonInd→prefixInd h k , h k

  allPrefixInd→horizonInd : ((k : ℕ) → Ind< k) → HorizonInd O x y
  allPrefixInd→horizonInd h n = snd (h (suc n))

  stageSep→horizonSep : {k : ℕ} → Sep< k → HorizonSep O x y
  stageSep→horizonSep {zero} s = ⊥.rec s
  stageSep→horizonSep {suc k} (inl s) = stageSep→horizonSep s
  stageSep→horizonSep {suc k} (inr d) = k , d

  horizonSep→stageSep : HorizonSep O x y → Σ[ k ∈ ℕ ] Sep< k
  horizonSep→stageSep (n , d) = suc n , inr d

  -- Stage choice is redundant, so the two types are not asserted to be an
  -- isomorphism.  The horizon witness is nevertheless a retract of the
  -- disjoint union of stages.
  horizonSepRetract : (s : HorizonSep O x y)
    → stageSep→horizonSep (snd (horizonSep→stageSep s)) ≡ s
  horizonSepRetract (n , d) = refl

  -- Without MP, failure of global agreement gives only double-negated
  -- existence of a finite stage carrying a separator.
  ¬horizonInd→¬¬stageSep :
      ¬ HorizonInd O x y → ¬ ¬ (Σ[ k ∈ ℕ ] Sep< k)
  ¬horizonInd→¬¬stageSep notInd noStage = notInd agree
    where
      agree : HorizonInd O x y
      agree n with O n x ≟ O n y
      ... | yes p = p
      ... | no d  = ⊥.rec (noStage (suc n , inr d))

------------------------------------------------------------------------
-- The exact completion principle and its constructive strength.
------------------------------------------------------------------------

FiniteStageWitnessed : Type₁
FiniteStageWitnessed =
  (X : Type) (O : ℕ → X → Bool) (x y : X)
  → ¬ HorizonInd O x y
  → Σ[ k ∈ ℕ ] Prefix.Sep< O x y k

MP→FiniteStageWitnessed : MP → FiniteStageWitnessed
MP→FiniteStageWitnessed mp X O x y notInd =
  Prefix.horizonSep→stageSep O x y (MP→Witnessed mp X O x y notInd)

FiniteStageWitnessed→Witnessed : FiniteStageWitnessed → Witnessed
FiniteStageWitnessed→Witnessed finite X O x y notInd =
  Prefix.stageSep→horizonSep O x y (snd (finite X O x y notInd))

FiniteStageWitnessed→MP : FiniteStageWitnessed → MP
FiniteStageWitnessed→MP finite =
  Witnessed→MP (FiniteStageWitnessed→Witnessed finite)
