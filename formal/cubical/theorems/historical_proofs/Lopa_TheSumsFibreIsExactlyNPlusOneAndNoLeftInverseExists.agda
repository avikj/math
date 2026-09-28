{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- लोपः — अदर्शनं लोपः ।  यत् तिष्ठति योगः, कः नश्यति भेदः ।
--
-- (what survives is the sum; what is destroyed is the split.)
--
-- ────────────────────────────────────────────────────────────────────
-- THE TERM, ITS TEXT AND ITS DATE.
--
-- **लोप** · lopa, elision.  Pāṇini, *Aṣṭādhyāyī* **1.1.60**, अदर्शनं लोपः —
-- "lopa is non-appearance" (~500 BCE).  The grammar's own name for a
-- licensed step after which something that was in the form is not in the
-- form.  Its companion **1.1.62**, प्रत्ययलोपे प्रत्ययलक्षणम् — "when an
-- affix has been elided, the operations conditioned by the affix still
-- apply" — is why the term fits this module rather than merely decorating
-- it: Pini's system does not merely delete, it RECORDS what the deleted
-- element conditioned.  §३ below is that recording, as a fibre.
--
-- ────────────────────────────────────────────────────────────────────
-- WHY THIS EDGE AND NOT ANOTHER.
--
-- `machine/Setubandha_…hs` built the graph of the corpus's checked
-- identifications; every edge in it is invertible.
-- `machine/Lopa_TheIrreversibleEdgesAreTheOtherGraphAndTheyRunOneWay.hs` (absent from this repository)
-- built the other graph — 1054 one-way edges over 474 nodes, against 88
-- invertible edges over 120 — and 1036 of those 1054 came back UNDECIDED
-- because no syntactic rule can name a fibre.
--
-- This is one of the ones that can be named, and it is the sharpest,
-- because the naming was ALREADY IN THE CORPUS TWICE and nothing had put
-- the two together:
--
--   `LosslessReturn_…TransportGivesIt.योग : ℕ × ℕ → ℕ`, योग x = fst x + snd x
--   `PairsSummingTo.Pairs n = Σ[ ab ∈ ℕ × ℕ ] (fst ab + snd ab ≡ n)`
--   `PairsSummingTo.pairsFin : (n : ℕ) → Pairs n ≃ SumFin (suc n)`
--
-- `Pairs n` IS `fiber योग n`, on the nose (§१, and it is `refl`).  So the
-- elision performed by addition already had its fibre counted, exactly, in
-- a module written for the metrical antidiagonal of Pigala's prastra and
-- never connected to the map whose loss it measures.  No module in this
-- corpus imports both files.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED.
--
--  §१  fiber योग n ≡ Pairs n.  Definitional; the identification is refl.
--  §२  fiber योग n ≃ SumFin (suc n).  The loss at n is EXACTLY n+1-fold.
--      Not "at least", not measured — the equivalence is `pairsFin`.
--  §३  The three verdicts of `Avaccheda_…` / `Tantujala_…`, all three
--      decided at this one edge, which is what makes it worth writing:
--        रिक्तम्  NEVER — योग is surjective, witness given.
--        एकम्    at n = 0 and nowhere else.
--        बहु     at every n = suc k, with two named histories exhibited
--                and their non-identity proved.
--      A two-valued verdict cannot say this; it would report "not
--      contractible" at every suc k and at ⊥ alike.
--  §४  THERE IS NO TRANSPORT IN THE LOSSY DIRECTION, and this is the
--      content of road two rather than a gap in the module: no
--      `g : ℕ → ℕ × ℕ` is a left inverse of योग.  Proved, not asserted.
--  §५  The अवच्छेद decomposition at this edge: (Σ n) fiber योग n ≃ ℕ × ℕ.
--      The pair IS (its sum, which pair of that sum) — यत् तिष्ठति /
--      कः नश्यति, as one equivalence.
------------------------------------------------------------------------

module Lopa_TheSumsFibreIsExactlyNPlusOneAndNoLeftInverseExists where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; invEquiv ; fiber)
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-zero ; znots)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; Σ-syntax)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.SumFin using () renaming (Fin to SumFin)

open import PairsSummingTo using (Pairs ; pairsFin)
open import LosslessReturn_TheHandProofWasUnnecessaryAndTransportGivesIt using (योग)
import Avaccheda_TheCutsBoundaryIsTheBaseAndMemoryIsTheFibreFailingToBeContractible as अव

------------------------------------------------------------------------
-- १ · तादात्म्यम् — the fibre of the sum IS the antidiagonal.
--
-- `योग x = fst x + snd x` and `Pairs n = Σ[ ab ∈ ℕ × ℕ ] (fst ab + snd ab
-- ≡ n)`, so `fiber योग n` unfolds to `Pairs n` with no work at all.  That
-- the identification is `refl` is the finding, not a weakness of it: two
-- modules written for unrelated purposes had already defined the same
-- type, one as a loss and one as a count, and neither imported the other.
------------------------------------------------------------------------

लोपस्य-तन्तुः : (n : ℕ) → fiber योग n ≡ Pairs n
लोपस्य-तन्तुः n = refl

------------------------------------------------------------------------
-- २ · गणना — and it is counted exactly.
--
-- This is `pairsFin`, a structural
-- induction with no truncated subtraction, in
-- `PairsSummingTo`, written for the metrical antidiagonal.
-- This module points it at the map.
--
-- THE MEASUREMENT ROAD ONE CANNOT MAKE.  Setubandha's edges all have
-- contractible fibres, so its cut indicator is the constant 0.  Here the
-- fibre over n has exactly n+1 elements: the defect is not a bit, it is
-- an unbounded function of the boundary datum.
------------------------------------------------------------------------

तन्तु-गणना : (n : ℕ) → fiber योग n ≃ SumFin (suc n)
तन्तु-गणना n = pairsFin n

------------------------------------------------------------------------
-- ३ · त्रयो भङ्गाः — all three verdicts, at one edge.
------------------------------------------------------------------------

-- रिक्तम् NEVER.  योग is surjective: (n , 0) lands on n.
न-रिक्तम् : (n : ℕ) → fiber योग n
न-रिक्तम् n = (n , 0) , +-zero n

-- एकम् at n = 0, and the witness is transported along §२.
isContrSumFin1 : isContr (SumFin 1)
isContrSumFin1 = inl tt , λ { (inl tt) → refl ; (inr ()) }

एकम्-शून्ये : isContr (fiber योग 0)
एकम्-शून्ये = isOfHLevelRespectEquiv 0 (invEquiv (तन्तु-गणना 0)) isContrSumFin1

-- बहु at every successor.  Two histories with the same sum, named.
वामम् : (n : ℕ) → fiber योग (suc n)
वामम् n = (0 , suc n) , refl

दक्षिणम् : (n : ℕ) → fiber योग (suc n)
दक्षिणम् n = (suc n , 0) , +-zero (suc n)

-- and they are not the same history: the left component separates them.
वाम≢दक्षिण : (n : ℕ) → ¬ (वामम् n ≡ दक्षिणम् n)
वाम≢दक्षिण n p = znots (cong (λ z → fst (fst z)) p)

बहु-सर्वत्र : (n : ℕ) → ¬ isContr (fiber योग (suc n))
बहु-सर्वत्र n c = वाम≢दक्षिण n (isContr→isProp c (वामम् n) (दक्षिणम् n))

-- THE दुर्नय, made concrete.  A two-valued verdict returns the same
-- answer at `fiber योग (suc n)` — many histories, memory required — as it
-- would at a profile nothing reaches.  §३ of `Avaccheda_…` says this in
-- general; here it is at a map the corpus actually uses.

------------------------------------------------------------------------
-- ४ · न प्रत्यानयनम् — and there is no road back.
--
-- No `g : ℕ → ℕ × ℕ` is a left inverse of योग.  The proof is §३'s two
-- histories: they have the same sum, so any left inverse would identify
-- them, and §३ proved they are not identical.  Note that `योग (0 , 1)`
-- and `योग (1 , 0)` are both `1` DEFINITIONALLY — `_+_` recurses on its
-- first argument — so `s (0 , 1)` and `s (1 , 0)` are two paths out of
-- the same `g 1` and compose with no coercion.
------------------------------------------------------------------------

न-प्रत्यानयनम् : (g : ℕ → ℕ × ℕ)
              → ((x : ℕ × ℕ) → g (योग x) ≡ x) → ⊥
न-प्रत्यानयनम् g s = znots (cong fst (sym (s (0 , 1)) ∙ s (1 , 0)))

------------------------------------------------------------------------
-- ५ · अवच्छेदः — यत् तिष्ठति, कः नश्यति, as one equivalence.
--
-- `Avaccheda_…§१` proves `(Σ[ b ∈ B ] fiber f b) ≃ A` for every `f`.  At
-- योग that reads: a pair of naturals IS (its sum, together with which
-- pair of that sum it was).  The first coordinate is what the boundary
-- retains — यत् तिष्ठति; the second is what it does not — कः नश्यति; and
-- §२ says the second has exactly `sum + 1` possible values.
--
-- The elision is therefore not a defect of the pair type.  Nothing is
-- missing from `ℕ × ℕ`; what is lost is lost by the MAP, and §२ says
-- exactly how much, at every boundary datum separately.
------------------------------------------------------------------------

अवच्छेदः-योगे : (Σ[ n ∈ ℕ ] fiber योग n) ≃ (ℕ × ℕ)
अवच्छेदः-योगे = अ.अवच्छेदः योग
  where module अ = अव

