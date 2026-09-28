{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- मूलवाक्यम् · PROVENANCE OF THE NAME.
--
-- क्रम · नास्ति — two terms, one from each half of the सप्तभङ्गी apparatus.
--
--   स्यान्नास्ति, the second भङ्ग: in some respect, it is not.  **Samantabhadra,
--   *ptamms* 14-24 (~6th c. CE); Akalaka, *Laghyastraya* (~8th c.);
--   rooted in Umsvti, *Tattvrthastra* 5.31-32 (~2nd-5th c.).**
--
--   क्रमार्पण versus सहार्पण — presentation in SUCCESSION versus SIMULTANEOUSLY.
--   **Akalaka, *Laghyastraya* (~8th c.); Vidynandin,
--   *Tattvrthalokavrttika* (~9th c.).**  This is the load-bearing one:
--   अस्ति and नास्ति asserted in succession give the third भङ्ग and are
--   expressible; asserted together they give अवक्तव्य, the fourth, which is
--   neither unknown nor undefined nor empty but a positive fourth position.
--   The distinction is what makes seven positions and not four.
--
-- The sevenfold division and the क्रम/सह distinction are
-- theirs, stated as doctrine; the theorems here are about what the fourth
-- corner can and cannot be over particular index types in cubical type
-- theory, and they are this repository's.
--
------------------------------------------------------------------------
-- TheFourthCornerIsRefutedUnderPointwiseStability
--
-- `SamayikaAndNityaAreIndependent` proved three of four corners.
-- The fourth is refuted under one named hypothesis, and the hypothesis is
-- exactly a stability, pointwise in the remedy:
--
--   fourthCornerRefutedUnderPointwiseStability :
--     ((r : R) → Stable (Σ[ i ∈ I ] bad i r))
--     → ¬ ((¬ सामयिक bad) × (¬ नित्य bad))
--
-- ────────────────────────────────────────────────────────────────────
-- WHERE THE CONSTRUCTIVE ARGUMENT STOPS, AND WHAT FILLS THE GAP
--
-- §2 is unconditional: if no single remedy clears every instance, then
-- for EVERY remedy some instance survives it — under a double negation.
-- That is a one-line contrapositive and needs nothing.
--
-- The double negation is the whole gap.  `नित्य` asks for the surviving
-- instance itself, and §2 delivers only `¬ ¬ Σ`.  §3 closes it with
-- stability of that Σ at each remedy — which `Dec` supplies, and which
-- is precisely the "positive pole is a search" side of the axis this
-- corpus keeps meeting.  §4 then refutes the fourth corner.
------------------------------------------------------------------------

module OrderAstiNasti_TheFourthCornerIsRefutedUnderPointwiseStability where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import AnuktaAvaktavya using (सामयिक ; नित्य)
open import SamayikaAndNityaAreIndependent using (UniversalRemedy)

private
  variable
    ℓ : Level

Stable : Type ℓ → Type ℓ
Stable A = ¬ ¬ A → A

------------------------------------------------------------------------
-- 1.  A universal remedy is one that clears every instance
--
-- (the definition is `SamayikaAndNityaAreIndependent`'s; repeated here
-- only in words)
------------------------------------------------------------------------

-- if one exists, the temporary reading holds at every instance
universalRemedyGivesSamayika :
  {I R : Type} (bad : I → R → Type)
  → UniversalRemedy bad → सामयिक bad
universalRemedyGivesSamayika bad (r , clears) i = r , clears i

------------------------------------------------------------------------
-- 2.  No universal remedy ⇒ every remedy is survived, under ¬¬
------------------------------------------------------------------------

noUniversalRemedyGivesPointwiseDoubleNegation :
  {I R : Type} (bad : I → R → Type)
  → ¬ UniversalRemedy bad
  → (r : R) → ¬ ¬ (Σ[ i ∈ I ] bad i r)
noUniversalRemedyGivesPointwiseDoubleNegation bad noUR r nn =
  noUR (r , λ i b → nn (i , b))

------------------------------------------------------------------------
-- 3.  Pointwise stability turns that into नित्य
------------------------------------------------------------------------

pointwiseStabilityGivesNitya :
  {I R : Type} (bad : I → R → Type)
  → ((r : R) → Stable (Σ[ i ∈ I ] bad i r))
  → ¬ UniversalRemedy bad → नित्य bad
pointwiseStabilityGivesNitya bad stab noUR r =
  stab r (noUniversalRemedyGivesPointwiseDoubleNegation bad noUR r)

------------------------------------------------------------------------
-- 4.  Hence the fourth corner is refuted
--
-- `¬ सामयिक` kills any universal remedy (§1), §3 then produces `नित्य`,
-- and that contradicts `¬ नित्य`.
------------------------------------------------------------------------

fourthCornerRefutedUnderPointwiseStability :
  {I R : Type} (bad : I → R → Type)
  → ((r : R) → Stable (Σ[ i ∈ I ] bad i r))
  → ¬ ((¬ सामयिक bad) × (¬ नित्य bad))
fourthCornerRefutedUnderPointwiseStability bad stab (noSam , noNit) =
  noNit (pointwiseStabilityGivesNitya bad stab
          (λ ur → noSam (universalRemedyGivesSamayika bad ur)))

------------------------------------------------------------------------
-- 5.  What this settles
--
-- SETTLED: with the Σ stable at each remedy — which a decision at each
-- remedy supplies — the four corners are three.  So the fourth corner,
-- if it exists at all, exists only where some `Σ[ i ] bad i r` is not
-- stable, i.e. where finding a surviving instance is a genuine search.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The hypothesis is DISCHARGED, not weakened, in
--   `TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet`:
--
--   Enumerated Ix = Σ[ xs ∈ List Ix ] ((i : Ix) → Any (_≡ i) xs)
--
-- — a list of instances plus a proof that nothing is outside it, with
-- no cardinality, no `Fin`, and no decidable equality on Ix.  Then
--
--   decΣOverEnumerated   Σ[ i ] P i is DECIDABLE
--   fourthCornerRefutedOverEnumerableDecidable
--                        so §4 applies with NOTHING assumed
--
-- §5 read the hypothesis as "finding a surviving instance is not a
-- genuine search".  Over an enumerable family with decidable badness it
-- is not a search, it is a scan.  So the fourth corner needs an
-- instance family that is not enumerable, OR a badness that is not
-- decidable — which is a much smaller place to look than "some Σ is
-- unstable".
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ON THE NAME.
-- `KramaSaha_TheFourthCornerIWasNamingIsTheSequentialPosition` (absent from this repository) proves
-- this line's "fourth corner" is a product of two independent
-- negations and that simultaneous refusal collapses into the
-- sequential pair, so the position is the THIRD bhaṅga —
-- स्यात्-अस्ति-नास्ति, asserted क्रमेण — and not avaktavya.
------------------------------------------------------------------------
