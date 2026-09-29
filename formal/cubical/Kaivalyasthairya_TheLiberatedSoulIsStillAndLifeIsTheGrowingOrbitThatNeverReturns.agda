{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- कैवल्यस्थैर्यम् — the liberated soul is STILL, and life is the growing
-- orbit that never returns.  Two nayas, both checked; the machine holds both.
--
-- WHAT THIS HOLDS.  Kevalajnana/Avarana celebrated the equivalence — the
-- perfect mirror, every fibre whole, no loss.  Areturn_…agda's header
-- names the price of that celebration: "a system with nothing left
-- unreturned is a dead system", citing Dhruva — if the cognition loses
-- nothing (isEquiv) every flow conserving it is the identity.  So kevala is
-- STILLNESS, not life:
--
--   कैवल्य-स्थैर्यम् — a kevalin jīva (उपयोगः an equivalence) admits no
--       nontrivial internal motion: every flow on its holding that leaves
--       its cognition unchanged IS the identity (Dhruva, at the jva).
--
-- and life is the OTHER naya, equally checked:
--
--   जीवन-चलनम् — the bhāvanā orbit strictly grows and never returns
--       (Areturn.अपुनरागमनम्) — a non-equivalence, and THAT non-return
--       is the generativity.  Brahmagupta's rule, iterated, visits no value
--       twice: the soul that breeds is the veiled, moving, growing one.
--
-- So the still mirror (kevala, isEquiv, no motion — Dhruva सूत्र १४) and the
-- living orbit (bhvan, growth, non-return — Areturn) are two nayas.
-- The siddha is motionless at the summit; the sasric jva moves and
-- generates.  Neither collapses the other: reading kevala as the goal makes
-- the machine "report exhaustion as progress" (Areturn's warning);
-- reading growth as mere debt treats generativity as a defect.  syt.
------------------------------------------------------------------------

module Kaivalyasthairya_TheLiberatedSoulIsStillAndLifeIsTheGrowingOrbitThatNeverReturns where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Relation.Nullary using (¬_)

import Jiva_TheSoulIsCognitionBoundByKarmaAndLiberationIsTheEquivalenceThatSeesTheWorldAsItself as J
import Dhruva_TheSymmetryLivesInTheFibreAndWithoutALossThereIsNoSymmetry as D
import NoReturn_TheCompositionOrbitStrictlyGrowsSoItNeverReturnsAndThatIsTheGenerativity as Ap

------------------------------------------------------------------------
-- १ · कैवल्य-स्थैर्यम् — the liberated soul is still.
--     A flow on the holding that leaves the cognition unchanged is आत्म-गतिः;
--     if the soul is kevalin, that flow can only be the identity.
------------------------------------------------------------------------

आत्म-गतिः : (j : J.जीवः) → (J.धारणा j → J.धारणा j) → Type
आत्म-गतिः j Φ = D.संरक्षणम् (J.उपयोगः j) Φ

कैवल्य-स्थैर्यम् : (j : J.जीवः) → isEquiv (J.उपयोगः j)
              → (Φ : J.धारणा j → J.धारणा j) → आत्म-गतिः j Φ
              → (a : J.धारणा j) → Φ a ≡ a
कैवल्य-स्थैर्यम् j e Φ cons = D.नष्ट-अभावे-गति-अभावः (J.उपयोगः j) Φ e cons

-- सिद्धः, the liberated identity-soul, is still: any flow conserving its
-- cognition is the identity.  Motionless at the summit.
सिद्ध-स्थैर्यम् : (Φ : Bool → Bool)
             → आत्म-गतिः J.सिद्धः Φ → (a : Bool) → Φ a ≡ a
सिद्ध-स्थैर्यम् = कैवल्य-स्थैर्यम् J.सिद्धः (J.मोक्षः J.सिद्धः J.सिद्धस्य-निर्जरा)

------------------------------------------------------------------------
-- २ · जीवन-चलनम् — life is the other naya: the orbit that never returns.
--     Re-exported so the two stand side by side and neither is collapsed.
------------------------------------------------------------------------

जीवन-चलनम् : ¬ (Ap.नव-हरः 3 2 ≡ 2)
जीवन-चलनम् = Ap.मूल-अपुनरागमनम्
