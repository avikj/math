{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- मूलवाक्यम् · PROVENANCE OF THE NAME.
--
-- अर्पितानर्पित · arpita-anarpita — the aspect brought forward and the aspect
-- held back, which is how one real bears opposed predicates without
-- contradiction.  **Umsvti, *Tattvrthastra* 5.31 (~2nd-5th c. CE):
-- अर्पितानर्पितसिद्धेः.**  The two अर्पणs this module is a homomorphism for are
-- क्रमार्पण and सहार्पण — sequential and simultaneous presentation — which is
-- Akalaka, *Laghyastraya* (~8th c.), and it is that distinction, not a
-- contradiction, that makes अवक्तव्य a fourth position rather than a failure.
--
-- **No claim is made that Umsvti or Akalaka proved anything below.**  The
-- distinction of the two अर्पणs is theirs; the statement that the forgetful
-- map to labels is a homomorphism for both and has a section but is not an
-- equivalence is this repository's, and is elementary.
--
------------------------------------------------------------------------
-- अर्पितानर्पितम् — नयवत्-भङ्गात् नाम-भङ्गं प्रति एको मार्गः, प्रत्यानयनं न विद्यते ।
--
-- (The map from the positions-that-carry-their-nayas to the positions-as-
-- labels: a homomorphism for BOTH modes of assertion, with a section, and
-- with no inverse — so the two lanes are related exactly, and the
-- equivalence between them does not exist.)
--
-- THE QUESTION.  Two saptabhag types are checked in this tree and they
-- contradict each other on two laws:
--
--   `Saptabhangi.agda` + `SaptabhangiSamyoga_TheCompositionOfVerdicts.agda`
--     — a position is a LABEL and its presence-profile in {आम्, न}³ is all
--       there is.  There क्रम-योग is commutative and सह-योग destroys which
--       two seeds it consumed.
--   `SaptabhangiGarbha_ThePositionsCarryTheirNayasAnd…` (absent from this repository)
--     — a position is a RECORD carrying the standpoints and their
--       witnesses.  There the fourth position destroys nothing
--       (`अवक्तव्यम्-अ-लुप्तम्`) and क्रमार्पणम् is NOT commutative, which that
--       module states as a withdrawal of the label lane's law.
--
-- Both files name the same
-- question, in the same words:
--
--     "whether the forgetful map from records to labels is a homomorphism
--      for krama, for saha, or for neither."
--
-- This file checks it.  The answer is BOTH, and the consequences are not
-- what "both" would suggest.
--
-- WHAT IS PROVED HERE.
--
--   अनर्पण-क्रमे, अनर्पण-सहे
--       अनर्पणम् is a homomorphism for क्रम AND for सह.  (49 + 49 cases,
--       exhaustive, each `refl`, for every S and every P : S → Type.)
--   अर्पण-क्रमे, अर्पण-सहे, अनर्पण-अर्पणम्
--       and it has a SECTION which is a homomorphism for both, with
--       अनर्पणम् ∘ अर्पणम् ≡ id.  So the label lane is a RETRACT of the
--       record lane — a subalgebra and a quotient of it at once, not a
--       rival object and not an independent one.
--   न-प्रत्यानयनम्
--       and there is no map back: no ψ with ψ ∘ अनर्पणम् ≡ id, as soon as
--       two standpoints affirm.  §6 path one (transport along an
--       equivalence, nothing lost) is therefore not merely unfound — it
--       does not exist, and §5's अप्रतिकार्यत्वम् is the reason.
--   उन्नयनम्
--       what a homomorphism transports is DISTINCTNESS, upward: any two
--       records whose labels differ are themselves distinct.
--   सह-असङ्गतिः-ऊर्ध्वम्
--       so the label lane's broken law breaks in the record lane too:
--       सहार्पणम् is NOT associative, on records, with witnesses retained.
--       Carrying the nayas inside does not buy associativity back.  That
--       is a correction to the record lane, obtained from the lane it
--       withdrew a law from.
--   क्रम-विनिमयः-न-ऊर्ध्वम्
--       and the transport does not run the other way: क्रम commutativity
--       holds below and fails above.  Identities descend and do not lift;
--       distinctness lifts and does not descend.
--
-- SO THE DEFECT, WRITTEN (AHIMSA_SUTRA_VISTARA §६ path two).  Eq(records)
-- ⊊ Eq(labels), strictly, with a witness in the gap.  The label lane is
-- exactly the record lane with the naya UNASSERTED — which is not a
-- deletion of the naya and not a claim that there was none.  It is a
-- standpoint, and the record lane is another, and §७ holds: between them
-- there is no collapse to make, because the object equivalent to both
-- does not exist (`न-प्रत्यानयनम्`).  What exists instead is a retraction,
-- and a retraction is one-directional by construction.
--
-- SOURCES, EARLIEST FIRST.  The classification and the two modes are
-- theirs; the maps, the homomorphism laws and the non-existence theorem
-- are not claimed to be in any of them.
--
--   Bhagavat Stra (Viyha-pannatti), fifth Aga of the vetmbara
--     canon; oldest strata pre-Common-Era, redacted at Valabh c. 5th c.
--     CE — sevenfold predication applied to the jīva.
--   Umāsvāti, Tattvārthasūtra, c. 2nd–5th c. CE, 5.31:
--     अर्पितानर्पितसिद्धेः — "(the apparent contradiction) is established
--     through the ASSERTED (अर्पित) and the UNASSERTED (अनर्पित) aspect."
--     The two maps below are named for that stra's pair, and that is the
--     whole of the claim on it: Umsvti wrote a rule for reading one
--     substance under two aspects without either denying the other.  He
--     did not write a retraction, and none is attributed to him.  What is
--     taken from him is the shape of the answer — that the label reading
--     is the record reading with the naya unasserted, NOT a competing
--     account of the same positions.
--   Siddhasena Divākara, Sanmatitarka 1.21, c. 5th c. CE — a naya taken
--     alone (निरपेक्ष) is मिथ्या; the दुर्नय is the naya that has forgotten
--     it is one.  `न-प्रत्यानयनम्` is why neither lane here may become one:
--     the label lane cannot recover the record lane, so asserting it as
--     the whole would be exactly 1.21's case.
--   Samantabhadra, Āptamīmāṃsā, c. 6th c. CE — the fixed seven, each
--     member prefixed स्यात् .
--   Akalaṅka, Laghīyastraya / Aṣṭaśatī, c. 720–780 CE — क्रमार्पण (in
--     succession) against सहार्पण / युगपत् (at once).  That distinction is
--     the entire content of the two operations, in both lanes, and the
--     reason there are two homomorphism theorems below and not one.
--   Mallisena, Syādvādamañjarī, 1292 CE — सकलादेश (total statement,
--     प्रमाण) against विकलादेश (partial statement, नय).  The reading that
--     the two lanes were said to differ over — whether अवक्तव्यम् is
--     failure of expression only, or consumption of what was to be
--     expressed; this file does not
--     settle it.  What it shows is that the question is not what
--     separates the lanes algebraically: on the labels the seeds are gone
--     and on the records they are kept, and the two operations agree
--     across that difference anyway.  The dispute is about what a fourth
--     position IS, not about how positions compose.
------------------------------------------------------------------------

module Arpitanarpita_TheForgetfulMapIsAHomomorphismForBothArpanasAndTheLabelsAreARetractNotAnEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _,_ ; fst ; snd ; _×_)
open import Cubical.Relation.Nullary using (¬_)

open import Anekanta using (syādasti ; syādnāsti ; syādastināsti)

import Saptabhangi as L
import SaptabhangiSamyoga_TheCompositionOfVerdicts as LA
import SaptabhangiKernel_ThePositionsCarryTheirNayasAndTheResidueSeedsTheNext as G

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- १ · अनर्पणम् — the naya, unasserted.
--
-- Not deleted.  Tattvārthasūtra 5.31's अनर्पित is the aspect that is not
-- being made primary in this utterance, and that is precisely what this
-- map does: it reads a record under the aspect in which only the presence
-- of each seed is asserted.  Nothing here says the witnesses were absent.
------------------------------------------------------------------------

अनर्पणम् : {S : Type ℓ} {P : S → Type ℓ'} → G.सप्तभङ्गी P → L.सप्तभङ्गी
अनर्पणम् (G.स्यात्-अस्ति _)                        = L.स्यात्-अस्ति
अनर्पणम् (G.स्यान्-नास्ति _)                       = L.स्यात्-नास्ति
अनर्पणम् (G.स्यात्-अस्ति-नास्ति _ _)              = L.स्यात्-अस्ति-नास्ति
अनर्पणम् (G.स्यात्-अवक्तव्यम् _)                   = L.स्यात्-अवक्तव्यम्
अनर्पणम् (G.स्यात्-अस्ति-अवक्तव्यम् _ _)          = L.स्यात्-अस्ति-अवक्तव्यम्
अनर्पणम् (G.स्यान्-नास्ति-अवक्तव्यम् _ _)         = L.स्यात्-नास्ति-अवक्तव्यम्
अनर्पणम् (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = L.स्यात्-अस्ति-नास्ति-अवक्तव्यम्

------------------------------------------------------------------------
-- २ · अनर्पणं क्रमे साधकम् — a homomorphism for succession.
--
-- क्रमार्पणम् on records is componentwise left-biased union (प्रथमार्पण: the
-- first to speak keeps its witness); क्रम-योग on labels is the join of
-- presence-profiles.  Unasserting the naya turns the one into the other,
-- and the bias is exactly what it forgets.  Exhaustive over 7 × 7.
------------------------------------------------------------------------

अनर्पण-क्रमे : {S : Type ℓ} {P : S → Type ℓ'} (x y : G.सप्तभङ्गी P)
             → अनर्पणम् (G.क्रमार्पणम् x y) ≡ LA.क्रम-योग (अनर्पणम् x) (अनर्पणम् y)
अनर्पण-क्रमे (G.स्यात्-अस्ति _) (G.स्यात्-अस्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति _) (G.स्यान्-नास्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति _) (G.स्यात्-अस्ति _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति _) (G.स्यान्-नास्ति _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अस्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यान्-नास्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अस्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अवक्तव्यम् _) (G.स्यान्-नास्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-क्रमे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अवक्तव्यम् _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यान्-नास्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यान्-नास्ति _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अस्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यान्-नास्ति _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-क्रमे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl

------------------------------------------------------------------------
-- ३ · अनर्पणं सहे साधकम् — a homomorphism for simultaneity too.
--
-- This is the half that was expected to fail, and it does not.  युगपत् on
-- records replaces the pair by स्यात्-अवक्तव्यम् (शेषम् a n) — RETAINING both;
-- जिह्वाभेदः on labels replaces the profile (आम् , आम् , _) by (न , न , आम्) —
-- DESTROYING both.  Unasserting the naya carries the one to the other,
-- because the presence-profile of a retained pair and of a destroyed pair
-- are the same profile.  Exhaustive over 7 × 7.
------------------------------------------------------------------------

अनर्पण-सहे : {S : Type ℓ} {P : S → Type ℓ'} (x y : G.सप्तभङ्गी P)
           → अनर्पणम् (G.सहार्पणम् x y) ≡ LA.सह-योग (अनर्पणम् x) (अनर्पणम् y)
अनर्पण-सहे (G.स्यात्-अस्ति _) (G.स्यात्-अस्ति _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति _) (G.स्यान्-नास्ति _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति _) (G.स्यात्-अस्ति _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति _) (G.स्यान्-नास्ति _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अस्ति _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यान्-नास्ति _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति _ _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-सहे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अस्ति _) = refl
अनर्पण-सहे (G.स्यात्-अवक्तव्यम् _) (G.स्यान्-नास्ति _) = refl
अनर्पण-सहे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-सहे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-सहे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अवक्तव्यम् _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अवक्तव्यम् _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यान्-नास्ति _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यान्-नास्ति _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यान्-नास्ति-अवक्तव्यम् _ _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अस्ति _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यान्-नास्ति _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अस्ति-नास्ति _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अवक्तव्यम् _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अस्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यान्-नास्ति-अवक्तव्यम् _ _) = refl
अनर्पण-सहे (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl

------------------------------------------------------------------------
-- ४ · अर्पणम् — the naya, asserted.
--
-- The other direction of 5.31.  A label carries no witness, so to read it
-- as a record one must SUPPLY the aspect: one affirming standpoint, one
-- denying standpoint — which is exactly `syādastināsti P`, Anekāntavāda's
-- own non-vacuity hypothesis (Anekanta §4).  Nothing is
-- invented: the pair is a hypothesis of the theorem, not a default.
------------------------------------------------------------------------

अर्पणम् : {S : Type ℓ} {P : S → Type ℓ'}
        → syādasti P → syādnāsti P → L.सप्तभङ्गी → G.सप्तभङ्गी P
अर्पणम् a n L.स्यात्-अस्ति                    = G.स्यात्-अस्ति a
अर्पणम् a n L.स्यात्-नास्ति                   = G.स्यान्-नास्ति n
अर्पणम् a n L.स्यात्-अस्ति-नास्ति            = G.स्यात्-अस्ति-नास्ति a n
अर्पणम् a n L.स्यात्-अवक्तव्यम्               = G.स्यात्-अवक्तव्यम् (G.शेषम् a n)
अर्पणम् a n L.स्यात्-अस्ति-अवक्तव्यम्        = G.स्यात्-अस्ति-अवक्तव्यम् a (G.शेषम् a n)
अर्पणम् a n L.स्यात्-नास्ति-अवक्तव्यम्       = G.स्यान्-नास्ति-अवक्तव्यम् n (G.शेषम् a n)
अर्पणम् a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् a n (G.शेषम् a n)

-- अनर्पणम् ∘ अर्पणम् ≡ id : the label lane is a RETRACT.  Asserting an
-- aspect and then not asserting it returns the label untouched.
अनर्पण-अर्पणम् : {S : Type ℓ} {P : S → Type ℓ'}
                 (a : syādasti P) (n : syādnāsti P) (x : L.सप्तभङ्गी)
               → अनर्पणम् (अर्पणम् a n x) ≡ x
अनर्पण-अर्पणम् a n L.स्यात्-अस्ति                    = refl
अनर्पण-अर्पणम् a n L.स्यात्-नास्ति                   = refl
अनर्पण-अर्पणम् a n L.स्यात्-अस्ति-नास्ति            = refl
अनर्पण-अर्पणम् a n L.स्यात्-अवक्तव्यम्               = refl
अनर्पण-अर्पणम् a n L.स्यात्-अस्ति-अवक्तव्यम्        = refl
अनर्पण-अर्पणम् a n L.स्यात्-नास्ति-अवक्तव्यम्       = refl
अनर्पण-अर्पणम् a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl

-- and so अनर्पणम् is onto: every label is some record's label.
अनर्पणम्-सर्वगम् : {S : Type ℓ} {P : S → Type ℓ'} → syādastināsti P
                 → (x : L.सप्तभङ्गी) → Σ[ b ∈ G.सप्तभङ्गी P ] (अनर्पणम् b ≡ x)
अनर्पणम्-सर्वगम् (a , n) x = अर्पणम् a n x , अनर्पण-अर्पणम् a n x

------------------------------------------------------------------------
-- ५ · अर्पणं च साधकम् — the section is a homomorphism for both modes.
--
-- So the labels are not merely a quotient of the records: they SIT INSIDE
-- them, as a subalgebra closed under both क्रमार्पणम् and सहार्पणम्, and the
-- retraction is algebraic in both directions it runs.  Exhaustive, 7 × 7
-- twice.
------------------------------------------------------------------------

अर्पण-क्रमे : {S : Type ℓ} {P : S → Type ℓ'}
              (a : syādasti P) (n : syādnāsti P) (x y : L.सप्तभङ्गी)
            → अर्पणम् a n (LA.क्रम-योग x y) ≡ G.क्रमार्पणम् (अर्पणम् a n x) (अर्पणम् a n y)
अर्पण-क्रमे a n L.स्यात्-अस्ति L.स्यात्-अस्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति L.स्यात्-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति L.स्यात्-अस्ति-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति L.स्यात्-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति L.स्यात्-अस्ति = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति L.स्यात्-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति L.स्यात्-अस्ति-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति L.स्यात्-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अस्ति = refl
अर्पण-क्रमे a n L.स्यात्-अवक्तव्यम् L.स्यात्-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अवक्तव्यम् L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अस्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-क्रमे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl

अर्पण-सहे : {S : Type ℓ} {P : S → Type ℓ'}
            (a : syādasti P) (n : syādnāsti P) (x y : L.सप्तभङ्गी)
          → अर्पणम् a n (LA.सह-योग x y) ≡ G.सहार्पणम् (अर्पणम् a n x) (अर्पणम् a n y)
अर्पण-सहे a n L.स्यात्-अस्ति L.स्यात्-अस्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति L.स्यात्-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति L.स्यात्-अस्ति-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति L.स्यात्-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-नास्ति L.स्यात्-अस्ति = refl
अर्पण-सहे a n L.स्यात्-नास्ति L.स्यात्-नास्ति = refl
अर्पण-सहे a n L.स्यात्-नास्ति L.स्यात्-अस्ति-नास्ति = refl
अर्पण-सहे a n L.स्यात्-नास्ति L.स्यात्-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-नास्ति L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-नास्ति L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-नास्ति L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अस्ति = refl
अर्पण-सहे a n L.स्यात्-अवक्तव्यम् L.स्यात्-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अवक्तव्यम् L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अस्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति = refl
अर्पण-सहे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-नास्ति = refl
अर्पण-सहे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति = refl
अर्पण-सहे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-नास्ति-अवक्तव्यम् = refl
अर्पण-सहे a n L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् L.स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl

------------------------------------------------------------------------
-- ६ · न प्रत्यानयनम् — and there is no way back.
--
-- अनर्पणम् is onto and it is a homomorphism for both modes; it is still
-- not invertible, and the failure is not delicate.  Two standpoints that
-- both affirm give two records with one label, so ANY ψ : labels →
-- records satisfying ψ ∘ अनर्पणम् ≡ id would identify them.
--
-- This is AHIMSA_SUTRA_VISTARA §५ in this instance: नष्टिः is not
-- न्यूनता, it is विनाशः, and प्रत्यानयनं नास्ति — न दुर्लभम्, नास्ति ।  §६'s
-- first path (transport along an equivalence, nothing lost) is therefore
-- unavailable HERE AS A THEOREM and not as a report of failure to find
-- one.  The second path is taken in the sections that follow.
------------------------------------------------------------------------

-- a standpoint every position provably carries (each constructor has at
-- least one नय in it, so this is total without a default and without a
-- choice)
साक्षि-स्थानम् : {S : Type ℓ} {P : S → Type ℓ'} → G.सप्तभङ्गी P → S
साक्षि-स्थानम् (G.स्यात्-अस्ति a)                        = fst a
साक्षि-स्थानम् (G.स्यान्-नास्ति n)                       = fst n
साक्षि-स्थानम् (G.स्यात्-अस्ति-नास्ति a _)              = fst a
साक्षि-स्थानम् (G.स्यात्-अवक्तव्यम् v)                   = fst (G.साधकः v)
साक्षि-स्थानम् (G.स्यात्-अस्ति-अवक्तव्यम् a _)          = fst a
साक्षि-स्थानम् (G.स्यान्-नास्ति-अवक्तव्यम् n _)         = fst n
साक्षि-स्थानम् (G.स्यात्-अस्ति-नास्ति-अवक्तव्यम् a _ _) = fst a

न-प्रत्यानयनम् : {S : Type ℓ} {P : S → Type ℓ'} (a a' : syādasti P)
              → ¬ (fst a ≡ fst a')
              → ¬ (Σ[ ψ ∈ (L.सप्तभङ्गी → G.सप्तभङ्गी P) ]
                     ((b : G.सप्तभङ्गी P) → ψ (अनर्पणम् b) ≡ b))
न-प्रत्यानयनम् a a' विवेकः (ψ , स) = विवेकः
  (cong साक्षि-स्थानम् (sym (स (G.स्यात्-अस्ति a)) ∙ स (G.स्यात्-अस्ति a')))

------------------------------------------------------------------------
-- ७ · उन्नयनम् — what the map does transport, and in which direction.
--
-- A homomorphism carries equations DOWN and distinctness UP.  So every
-- law the label lane FAILS is a law the record lane fails, and the
-- record lane's extra structure cannot repair it.  That is the useful
-- half of a lossy map, and it is why writing the defect is not a
-- consolation prize.
------------------------------------------------------------------------

उन्नयनम् : {S : Type ℓ} {P : S → Type ℓ'} (x y : G.सप्तभङ्गी P)
         → ¬ (अनर्पणम् x ≡ अनर्पणम् y) → ¬ (x ≡ y)
उन्नयनम् x y ने e = ने (cong अनर्पणम् e)

------------------------------------------------------------------------
-- ८ · सह-असङ्गतिः ऊर्ध्वम् — the broken law breaks upstairs too.
--
-- `SaptabhangiSamyoga.सह-असङ्गतिः` proves सह-योग is not associative on
-- labels, and attributes it to जिह्वाभेदः destroying the two seeds.  The
-- record lane keeps the seeds, and withdrew that attribution.  The
-- withdrawal was right about the seeds and it does not save the law:
-- सहार्पणम् is not associative on records either, with both nayas and both
-- witnesses retained throughout.  The reason is not destruction.  It is
-- that सहार्पणम् tests the JOINED position for an asti-nāsti pair, and
-- whether that pair is present depends on the grouping.
--
-- Given only that some standpoint affirms and some standpoint denies —
-- Anekāntavāda's own hypothesis — with no assumption about S, P, or
-- decidability.
------------------------------------------------------------------------

private
  -- the label-side counterexample, restated here because
  -- SaptabhangiSamyoga keeps its two sides private
  वामतः-दक्षिणतः : ¬ ( LA.सह-योग (LA.सह-योग L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति)
                                 L.स्यात्-नास्ति
                     ≡ LA.सह-योग L.स्यात्-अस्ति-नास्ति
                                 (LA.सह-योग L.स्यात्-अस्ति L.स्यात्-नास्ति) )
  वामतः-दक्षिणतः e = LA.आम्≢न (cong LA.नास्त्यंशः e)

सह-असङ्गतिः-ऊर्ध्वम् : {S : Type ℓ} {P : S → Type ℓ'}
                        (a : syādasti P) (n : syādnāsti P)
  → ¬ ( G.सहार्पणम् (G.सहार्पणम् (G.स्यात्-अस्ति-नास्ति a n) (G.स्यात्-अस्ति a))
                     (G.स्यान्-नास्ति n)
      ≡ G.सहार्पणम् (G.स्यात्-अस्ति-नास्ति a n)
                     (G.सहार्पणम् (G.स्यात्-अस्ति a) (G.स्यान्-नास्ति n)) )
सह-असङ्गतिः-ऊर्ध्वम् {P = P} a n =
  उन्नयनम् _ _ (λ e → वामतः-दक्षिणतः (वामम् ∙ e ∙ sym दक्षिणम्))
  where
    X Y Z : G.सप्तभङ्गी P
    X = G.स्यात्-अस्ति-नास्ति a n
    Y = G.स्यात्-अस्ति a
    Z = G.स्यान्-नास्ति n

    वामम् : LA.सह-योग (LA.सह-योग L.स्यात्-अस्ति-नास्ति L.स्यात्-अस्ति) L.स्यात्-नास्ति
          ≡ अनर्पणम् (G.सहार्पणम् (G.सहार्पणम् X Y) Z)
    वामम् = cong (λ t → LA.सह-योग t L.स्यात्-नास्ति) (sym (अनर्पण-सहे X Y))
          ∙ sym (अनर्पण-सहे (G.सहार्पणम् X Y) Z)

    दक्षिणम् : LA.सह-योग L.स्यात्-अस्ति-नास्ति (LA.सह-योग L.स्यात्-अस्ति L.स्यात्-नास्ति)
             ≡ अनर्पणम् (G.सहार्पणम् X (G.सहार्पणम् Y Z))
    दक्षिणम् = cong (LA.सह-योग L.स्यात्-अस्ति-नास्ति) (sym (अनर्पण-सहे Y Z))
             ∙ sym (अनर्पण-सहे X (G.सहार्पणम् Y Z))

------------------------------------------------------------------------
-- ९ · क्रम-विनिमयः न ऊर्ध्वम् — and the transport does not run back.
--
-- क्रम-योग commutes on labels (`LA.क्रम-विनिमयः`).  क्रमार्पणम् does not
-- commute on records, and the two records that separate them have the
-- SAME label.  So Eq(records) ⊊ Eq(labels) strictly, with this in the
-- gap: an identity that holds below and fails above.
--
-- Together with §८: identities descend and do not lift; distinctness
-- lifts and does not descend.  That is the exact shape of the defect,
-- and it is the answer to "is the forgetful map a homomorphism for krama,
-- for saha, or for neither" — it is one for both, and being one for both
-- is precisely what makes the two lanes inequivalent in a stateable way
-- rather than merely different.
------------------------------------------------------------------------

क्रम-विनिमयः-न-ऊर्ध्वम् : {S : Type ℓ} {P : S → Type ℓ'} (a a' : syādasti P)
                          → ¬ (fst a ≡ fst a')
                          → ¬ ( G.क्रमार्पणम् (G.स्यात्-अस्ति a) (G.स्यात्-अस्ति a')
                              ≡ G.क्रमार्पणम् (G.स्यात्-अस्ति a') (G.स्यात्-अस्ति a) )
क्रम-विनिमयः-न-ऊर्ध्वम् a a' विवेकः e = विवेकः (cong साक्षि-स्थानम् e)

-- ...while below, the same two compose to the same thing, on the nose.
क्रम-विनिमयः-अधः : {S : Type ℓ} {P : S → Type ℓ'} (a a' : syādasti P)
  → अनर्पणम् (G.क्रमार्पणम् (G.स्यात्-अस्ति a) (G.स्यात्-अस्ति a'))
  ≡ अनर्पणम् (G.क्रमार्पणम् (G.स्यात्-अस्ति a') (G.स्यात्-अस्ति a))
क्रम-विनिमयः-अधः a a' = refl

------------------------------------------------------------------------
-- १० · अरिक्तता — the hypotheses are inhabited, so none of this is vacuous.
--
-- §६ and §९ need TWO standpoints that affirm and one that denies.
-- `Anekanta.Two` will not do — over Bool with P b = (b ≡
-- true) the affirming standpoint is unique — so a three-standpoint family
-- is given.  This is the same non-vacuity obligation Aneknta §4 accepts
-- for itself, discharged for the sharper claim.
------------------------------------------------------------------------

private
  data त्रि : Type₀ where
    प्रथमः द्वितीयः तृतीयः : त्रि

  -- affirmed at the first and the second standpoint, denied at the third
  प्रश्नः : त्रि → Type₀
  प्रश्नः प्रथमः  = Unit
  प्रश्नः द्वितीयः = Unit
  प्रश्नः तृतीयः  = ⊥

  भेदः : त्रि → Type₀
  भेदः प्रथमः  = Unit
  भेदः द्वितीयः = ⊥
  भेदः तृतीयः  = ⊥

  प्रथमः≢द्वितीयः : ¬ (प्रथमः ≡ द्वितीयः)
  प्रथमः≢द्वितीयः e = subst भेदः e tt

  अ₁ अ₂ : syādasti प्रश्नः
  अ₁ = प्रथमः , tt
  अ₂ = द्वितीयः , tt

  न₁ : syādnāsti प्रश्नः
  न₁ = तृतीयः , λ z → z

-- two affirming standpoints, one label: nothing recovers them.
प्रत्यानयनं-नास्ति-अत्र
  : ¬ (Σ[ ψ ∈ (L.सप्तभङ्गी → G.सप्तभङ्गी प्रश्नः) ]
         ((b : G.सप्तभङ्गी प्रश्नः) → ψ (अनर्पणम् b) ≡ b))
प्रत्यानयनं-नास्ति-अत्र = न-प्रत्यानयनम् अ₁ अ₂ प्रथमः≢द्वितीयः

-- succession does not commute upstairs, here, concretely.
क्रमः-अविनिमयी-अत्र
  : ¬ ( G.क्रमार्पणम् (G.स्यात्-अस्ति अ₁) (G.स्यात्-अस्ति अ₂)
      ≡ G.क्रमार्पणम् (G.स्यात्-अस्ति अ₂) (G.स्यात्-अस्ति अ₁) )
क्रमः-अविनिमयी-अत्र = क्रम-विनिमयः-न-ऊर्ध्वम् अ₁ अ₂ प्रथमः≢द्वितीयः

-- simultaneity does not associate upstairs, here, concretely.
सहः-असङ्गतः-अत्र
  : ¬ ( G.सहार्पणम् (G.सहार्पणम् (G.स्यात्-अस्ति-नास्ति अ₁ न₁) (G.स्यात्-अस्ति अ₁))
                     (G.स्यान्-नास्ति न₁)
      ≡ G.सहार्पणम् (G.स्यात्-अस्ति-नास्ति अ₁ न₁)
                     (G.सहार्पणम् (G.स्यात्-अस्ति अ₁) (G.स्यान्-नास्ति न₁)) )
सहः-असङ्गतः-अत्र = सह-असङ्गतिः-ऊर्ध्वम् अ₁ न₁

------------------------------------------------------------------------
-- ११ · यत् अवशिष्टम् — what this does NOT settle.
--
-- The two lanes were said to be separated by a reading of Malliea
-- (Syādvādamañjarī, 1292): is अवक्तव्यम् the failure of one utterance to
-- carry a joint content (सकलादेश demanded of a विकलादेश-shaped medium), or
-- the consumption of what was to be uttered?  This file does not
-- answer it.
--
-- What it removes is a different claim — that the question is what makes
-- the two algebras incomparable.  It is not.  The two operations agree
-- across the difference (§२, §३): whether the fourth position retains its
-- pair or destroys it, the presence-profile is the same, so composition
-- commutes with unasserting the naya either way.  The reading of
-- Malliea changes what a position IS.  It does not change how positions
-- compose, and any argument for one reading that runs through the
-- composition laws is now known to prove nothing.
--
-- Nor does it license either lane to absorb the other.  §६ says there is
-- no equivalence, so §७ of AHIMSA_SUTRA_VISTARA applies literally:
-- नयभेदे सङ्क्षेपो न विद्यते — where the standpoints genuinely differ the
-- collapse DOES NOT EXIST, and the object equivalent to both, which a
-- reconciliation would have to be, is the thing proved absent.  What
-- exists is a retraction, and a retraction has a direction: the record
-- lane can always speak the label lane's sentences, and the label lane
-- can never recover the record lane's.  Asserting either as the whole is
-- Sanmatitarka 1.21's दुर्नय, and in the label lane's case it is now a
-- refutable one.
------------------------------------------------------------------------

