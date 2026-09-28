{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अवच्छेदकम् — त्रुटेः तन्तुः सर्वं मूलम् ; सन्धेः परिच्छेदः लब्धः ।
--
-- (the delimitor: the truncation's fibre is the WHOLE source, and the
--  seam's criterion is thereby available.)
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS PROVES.
--
-- `fibre/src/Loss/WholePartialDesa_…` makes the fibre
-- diagnosis a TERM — `देश f b` with three constructors, अवक्तव्यम् (empty
-- fibre: nothing lost, the medium has no name for b, धनात्मकम्),
-- सकलादेश (contractible: one utterance carries all), विकलादेश (two points
-- not identified: the loss, exhibited).  It refuses to add a fourth,
-- and it says exactly why:
--
--     "Adding a constructor for a distinction that has no criterion
--      would be the same दुर्नय this module exists to repair, one level
--      down: a name doing the work of a proof."
--
-- The distinction it refuses is between the note's levels ३ and ४ — both
-- crowded fibres, both landing in विकलादेश.  Level ३ is recoverable only
-- by outside supply; level ४ is नष्टि, अप्रतिकार्या.  And the obvious
-- criterion FAILS to separate them: `¬ Σ[ψ] (ψ ∘ collapse ≡ id)` holds of
-- both.
--
-- The criterion proposed for the seam is the SIZE of the fibre relative
-- to the source:
--
--     (x : ∥ A ∥₁) → fibre ∣_∣₁ x ≃ A
--
-- §न below proves that line.
--
-- ────────────────────────────────────────────────────────────────────
--
-- ESTABLISHED (§२): for propositional truncation, EVERY fibre is
-- equivalent to the whole source.  Not merely non-contractible, and not
-- merely large: the fibre IS the source, so nothing whatsoever downstream
-- of the map can see which point it came from.
--
-- NOT ESTABLISHED: that this is what makes truncation अप्रतिकार्या.  §३
-- below and `SapeksaNirapeksa_…` refute the proposed criterion — it holds
-- of the one-bit map `Bool → Unit` too, because it reads only the
-- propositionality of the TARGET.  What the scale wants is uniform in A:
-- there is no function `(A : Type) → ∥ A ∥₁ → A` (HoTT book Ex. 3.11);
-- no per-map fibre criterion reaches that quantifier.
--
-- ────────────────────────────────────────────────────────────────────
-- THE TERM.  अवच्छेदक — Nyāya's "delimitor", the property that fixes the
-- exact extent of a relation or an absence (Gaṅgeśa, तत्त्वचिन्तामणि,
-- 14th c., and the Navya-Nyya technical apparatus after him; the
-- corpus's own `interactive/Abhava_TheAbsenceCarriesItsPratiyoginAndItsSearched
-- Domain.hs` (absent from this repository) and `AbhavaAvacchedaka.agda` use it in that sense).
-- The word is taken for one property — that a relation is
-- not stated until its extent is — which is exactly what the seam was
-- missing and what §२ supplies.
------------------------------------------------------------------------

module Avacchedaka_TheTruncationsFibreIsTheWholeSourceAndTheSeamHasItsCriterion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; fiber ; isEquiv)
open import Cubical.Foundations.HLevels using (isProp→isContrPath)
open import Cubical.Data.Sigma using (Σ-contractSnd ; Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- १ · तन्तुः — the fibre of the truncation unit over a point of ∥ A ∥₁.
--     Written out rather than left as `fiber ∣_∣₁ x`, so the statement
--     below is legible without unfolding.
------------------------------------------------------------------------

त्रुटि-तन्तुः : {A : Type ℓ} → ∥ A ∥₁ → Type ℓ
त्रुटि-तन्तुः {A = A} x = Σ[ a ∈ A ] (∣ a ∣₁ ≡ x)

------------------------------------------------------------------------
--   §§-  THE THEOREM.
--
--     Every fibre of ∣_∣₁ is equivalent to the whole source.
--
-- ∥ A ∥₁ is a proposition, so each of its path types is CONTRACTIBLE
-- (isProp→isContrPath), so the second component of the Σ contributes
-- nothing and contracts away (Σ-contractSnd), leaving A itself.
--
-- Read against `Residue_…`: the residual over a target point is what the
-- target forgot there.  Here it forgot everything — the residual is not a
-- part of the source, it is the source.  So no map out of the target can
-- ever distinguish two points of A, because the target's every point
-- stands over all of A at once.
------------------------------------------------------------------------

सर्व-तन्तुः : {A : Type ℓ} (x : ∥ A ∥₁) → त्रुटि-तन्तुः x ≃ A
सर्व-तन्तुः {A = A} x =
  Σ-contractSnd (λ a → isProp→isContrPath isPropPropTrunc ∣ a ∣₁ x)

-- the same statement in the library's own vocabulary, so a reader looking
-- for `fiber` finds it
सर्व-तन्तुः-fiber : {A : Type ℓ} (x : ∥ A ∥₁) → fiber ∣_∣₁ x ≃ A
सर्व-तन्तुः-fiber = सर्व-तन्तुः

------------------------------------------------------------------------
-- ३ · परिच्छेदः — the criterion, stated as a predicate so it can be used
--     rather than admired, and applied to the archetype.
--
--     "The loss is total at b" := the residual over b is the whole source.
--
-- सर्वहानिः does NOT separate the levels.  It holds of `सर्वैकम् : Bool → Unit`, the
-- map that drops exactly one bit — `Residue_…` §5, at level
-- न of a five-level scale.  `Unit` is a proposition,
-- so the path component of the fibre contracts and the fibre is `Bool`,
-- the whole source.  The proof is §२'s proof with `isPropUnit` for
-- `isPropPropTrunc`, which is why: this criterion reads propositionality
-- of the TARGET, and both targets are props.
--
-- The refutation, with three more, is
-- `SapeksaNirapeksa_TheLossLevelIsNotAPropertyOfTheMapAloneAndTheFibreCriterionFailsOnItsOwnArchetype`.
-- §२ there shows it is not a stray instance — `∥ Bool ∥₁ ≃ Unit` and the
-- triangle commutes, so at `A = Bool` the level-४ archetype IS the
-- level-२ archetype, and the two fibre censuses are pointwise equivalent.
------------------------------------------------------------------------

सर्वहानिः : {A B : Type ℓ} → (A → B) → B → Type ℓ
सर्वहानिः {A = A} f b = fiber f b ≃ A

-- propositional truncation loses totally, at every point of its target
त्रुटिः-सर्वहानिः : {A : Type ℓ} (x : ∥ A ∥₁) → सर्वहानिः ∣_∣₁ x
त्रुटिः-सर्वहानिः = सर्व-तन्तुः-fiber

------------------------------------------------------------------------
--   The seam, and the refutation of the criterion.
--
-- `` is satisfied by
-- the corpus's own level-न archetype;
-- and the level-३ half of the scale — a proper fibre, with something
-- out of the source still seeing the difference — is satisfied at the
-- level-४ archetype and is vacuous wherever the fibre is crowded.  Both
-- halves are refuted in
-- `SapeksaNirapeksa_TheLossLevelIsNotAPropertyOfTheMapAloneAndTheFibre
-- CriterionFailsOnItsOwnArchetype`, which also exhibits the same map
-- under two retained contexts with opposite verdicts — so the level is
-- not a property of the map, and no per-map criterion can complete the
-- scale.
------------------------------------------------------------------------
