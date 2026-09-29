{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- प्रक्षेप-सङ्ख्या — the census of a projection's fibre IS the discarded
-- factor's cardinality, and the untruncated अभिज्ञान that the census
-- alone withholds is here supplied.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS JOINS.
--
-- Two fibre enzymes in this corpus speak about the same object and
-- neither imports the other:
--
--   `SankhyaTantu_…`  for ANY map between finite sets gives the सङ्ख्या
--       — the fibre's cardinality, `card (fiber f b)` — but not the
--       अभिज्ञान, the untruncated identification `fibre ≃ Fin k`:
--       `isFinSet X = Σ[n] ∥ X ≃ Fin n ∥₁`, so the equivalence sits
--       behind a propositional truncation and is available only for a
--       CONCRETE map.  That gap is the corpus's standing distinction
--       between counting a loss and naming it.
--
--   `PraksepaTantu_…`  for the projection `fst : A × B → A` gives exactly
--       the naming the census withholds: `fiber fst a ≃ B`, untruncated,
--       for arbitrary A and B, no h-level hypothesis — the discarded
--       factor itself, in hand.
--
-- At a projection the two meet.  `SankhyaTantu.सङ्ख्या` reports a NUMBER
-- for `fiber fst a`; `PraksepaTantu.वाम-तन्तुः-≃` says that fibre IS `B`.
-- So the number is forced: it is `card B`.  And the truncated part of
-- SankhyaTantu's सूत्र ८ caveat is discharged AT THIS MAP, because a
-- projection is concrete — the अभिज्ञान exists and is supplied, not
-- merely the count.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED, for finite sets A, B : FinSet ℓ and P = A × B.
--
--  §१  वाम-सङ्ख्या : SankhyaTantu.सङ्ख्या P A fst a ≡ card B.
--      The census of `fst`'s fibre at any `a` is the cardinality of the
--      discarded second factor.  Proof: `cardEquiv` fed PraksepaTantu's
--      equivalence — a receipt (identification), not a bound.
--  §२  दक्षिण-सङ्ख्या : SankhyaTantu.सङ्ख्या P B snd b ≡ card A.
--      The mirror, for `snd`.
--  §३  वाम-अभिज्ञानम् / दक्षिण-अभिज्ञानम् : the UNTRUNCATED equivalences
--      `fiber fst a ≃ B .fst`, `fiber snd b ≃ A .fst`, named here as the
--      अभिज्ञान SankhyaTantu says the general count cannot give and this
--      concrete map can.
--
-- TERM.  सङ्ख्या — number, count, enumeration; the fourth of Piṅgala's
-- pratyayas (छन्दःशास्त्रम् ch. 8, ~300 BCE: how many forms there are).
-- प्रक्षेप — casting/projecting.  अभिज्ञान — recognition, a token by
-- which a thing is identified (σύμβολον), the corpus's word for an
-- untruncated fibre-with-a-standard-type as opposed to its mere census.
-- LIMIT: no source states a fibre, a cardinality of a fibre, or an
-- equivalence; the mathematics is cubical (Voevodsky), the one admitted
-- non-Indian substrate.  The terms are borrowed in their exact senses
-- and nothing is attributed to any text.
------------------------------------------------------------------------

module PraksepaCount_TheProjectionsFibreCensusIsTheDiscardedFactorAndTheAbhijnanaIsSupplied where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; fiber)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Data.Sigma using (_×_ ; fst ; snd)
open import Cubical.Data.FinSet using (FinSet ; card)
open import Cubical.Data.FinSet.Constructors using (isFinSet×)
open import Cubical.Data.FinSet.Cardinality using (cardEquiv)

import PraksepaFiber_TheFiberOfAProjectionIsTheDiscardedFactor as प्र
import CountFiber_TheFiberOfAFiniteSourceMapIsFiniteAndItsCardinalityIsTheReceipt as स

private variable ℓ : Level

module _ (A B : FinSet ℓ) where

  -- the finite product P = A × B, whose two projections are the maps in play
  P : FinSet ℓ
  P = (A .fst × B .fst) , isFinSet× A B

  ------------------------------------------------------------------------
  -- ३ · अभिज्ञान — the untruncated identifications, in hand at a
  -- concrete map, which the general census (SankhyaTantu) withholds.
  ------------------------------------------------------------------------
  वाम-अभिज्ञानम् : (a : A .fst) → fiber (fst {A = A .fst} {B = λ _ → B .fst}) a ≃ B .fst
  वाम-अभिज्ञानम् a = प्र.वाम-तन्तुः-≃ a

  दक्षिण-अभिज्ञानम् : (b : B .fst) → fiber (snd {A = A .fst} {B = λ _ → B .fst}) b ≃ A .fst
  दक्षिण-अभिज्ञानम् b = प्र.दक्षिण-तन्तुः-≃ b

  ------------------------------------------------------------------------
  -- १ · वाम-सङ्ख्या — the census of fst's fibre is card B.
  --
  -- `स.सङ्ख्या P A fst a` is definitionally `card (fiber fst a , …)`.
  -- `cardEquiv` turns the अभिज्ञान into equality of counts: the receipt
  -- is an identification, never a bound.
  ------------------------------------------------------------------------
  वाम-सङ्ख्या : (a : A .fst) → स.सङ्ख्या P A fst a ≡ card B
  वाम-सङ्ख्या a = cardEquiv (स.तन्तुः P A fst a) B ∣ वाम-अभिज्ञानम् a ∣₁

  ------------------------------------------------------------------------
  -- २ · दक्षिण-सङ्ख्या — the census of snd's fibre is card A.
  ------------------------------------------------------------------------
  दक्षिण-सङ्ख्या : (b : B .fst) → स.सङ्ख्या P B snd b ≡ card A
  दक्षिण-सङ्ख्या b = cardEquiv (स.तन्तुः P B snd b) A ∣ दक्षिण-अभिज्ञानम् b ∣₁
