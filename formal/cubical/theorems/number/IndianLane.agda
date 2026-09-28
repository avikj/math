{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- IndianLane — the lane aggregate.
--
-- This aggregate runs:
--
--     cd formal/cubical && agda IndianLane.agda      # must exit 0
------------------------------------------------------------------------

module IndianLane where

-- RYABHAA, ryabhaya, Gaitapda 32-33 (499); Bhskara I's bhya
-- (629).  The pulverizer, and the descent as a vall of quotients.
import Kuttaka

-- BRAHMAGUPTA, Brhmasphuasiddhnta 18 (628).  Bhvan over an arbitrary
-- commutative ring; subtraction-free over ℕ as a semiring identity; and as
-- a typed OPERATION on solutions, which is what "production" names.
import Composition
-- The same composition made into an OBJECT rather than restated as a law:
-- the invariant lives in the type, so an unlawful card is not rejected but
-- UNSAYABLE, and the single move भावना carries the norm in its own type.
-- Eight moves from the one obvious card at D = 2 reach (577, 408), which is
-- Baudhāyana's √2 -- Śulbasūtra 1.61–62, c. 800 BCE, older than the
-- composition law it is reached by.
import CompositionKrida
import CompositionSemiring
import CompositionGenerative

-- The cycle's step with every subtraction cleared, so a concrete run is
-- certifiable in arithmetic the kernel actually computes.
import CakravalaNat

-- JAYADEVA (~950, via Udayadivkara 1073); BHSKARA II, Bjagaita (1150):
-- the cakravla step, and why Bhskara needs only ONE congruence.
import CakravalaDescent

-- The choice rule's PAYLOAD: |k| ≤ 2√D is preserved by the step, so the
-- wheel turns inside a fixed window.
import CakravalaBound

-- EMITTED BY THE REACTOR (machine/NalandaEmit.hs (absent from this repository)) and checked here: the
-- cakravala's answer for D = 61 as a term, not a printed number.
import CakravalaWitness

-- The flagship residual closed by a lemma transcribed from the machine's own
import SeamClosed

-- The WHOLE trace corpus in one module, generated: TraceLibrary reads the
-- machine's own discarded trace-replay proofs back, deduplicates them by
-- declaration, and makes them citable by name.

-- PIGALA, Chandastra (~300 BCE), with Virahka (~700) and Halyudha
-- (10th c.): the mtr recurrence, binary enumeration of metres.
import Pingala

-- PINI, Adhyy (~500 BCE): the ivastras as a pratyhra machine,
-- and the rule-conflict machinery -- utsarga/apavda, the elsewhere
-- condition, asiddhatva, anuvtti.
import Sivasutra
-- Optimality for Sivasutra.agda, the lower-bound half: classes sharing
-- one anubandha are a ⊆-chain, so a ⊆-antichain of classes forces that many
-- markers, in ANY order.  Four for the vowel classes; the order attains four.
import PratyaharaLaghava_TheMarkerCountIsForcedByTheAntichain
import Panini
import ElsewhereCondition

-- PĀṆINI 8.2.1 पूर्वत्रासिद्धम् as a TERMINATION technique, with the
-- impossibility half: the tripd's own 8.2.39/8.4.56 cycle admits no
-- strict order in which every rule decreases -- so no reduction order,
-- hence no RPO/KBO/polynomial/matrix interpretation, hence no Knuth-Bendix
-- completion.  Asiddhatva terminates it anyway, by constraining which
-- rules may OBSERVE which outputs rather than by a decreasing measure.
-- The witness is not invented: it is what machine/Astadhyayi.hs (absent from this repository) does
-- deriving vk from vc, and what its asiddhaAudit refuses.
import Asiddhatva

-- The OTHER device, 6.4.22 असिद्धवदत्राभात् (mutual invisibility inside
-- 6.4.22–6.4.129, rules applying as if simultaneously), against 8.2.1's
-- ordered regime at the one site where the difference is visible: three
-- tripādī rules offer at the same position in tat + jalam, and क्रम gives
-- the attested tajjalam while सह gives tadjalam, which  has not.
-- Both regimes COMPUTED from one act table.  So पूर्वत्रासिद्धम् is
-- load-bearing and is the ordered device -- evidence reached from the
-- rules, not from the stra text.
import AsiddhavatRegime

-- UMĀSVĀTI, Tattvārthasūtra 1.5: नामस्थापनाद्रव्यभावतस्तन्न्यासः -- the
-- fourfold placing, as an indexed sameness relation.
import Niksepa

-- Jain epistemology and mathematics.  Anekntavda as a TOTAL generator
-- (no rejection path); the taxonomy of the unbounded, sakhyta /
-- asakhyta / ananta; abhva with its avacchedaka.
import Anekanta
import JainCount
import AbhavaAvacchedaka

-- PIṄGALA, Chandaḥśāstra ch. 8 (c. 300–200 BCE), the six pratyaya; with
-- Virahāṅka, Vṛttajātisamuccaya ch. 6 (c. 600–800 CE) for the mātrāmeru
-- and Halāyudha, Mṛtasañjīvanī (10th c.) on 8.34–8.35 for the triangular
-- array.  naa and uddia are proved mutually inverse, each implemented
-- independently rather than one transported along the other; and the
-- recurrences are FORCED by the counting problem for an arbitrary counting
-- function, not read off a definition.
import PingalaPrastara
-- नष्टोद्दिष्टम् — पिङ्गलस्य नष्ट/उद्दिष्ट स्थान-पृथक्-छेदेषु विस्तारितौ, परस्पर-प्रतिलोमौ (अङ्कस्थान rs ≃ Fin (सङ्ख्या rs)) ;
-- मेरु-पङ्क्तिः एक-पङ्क्त्या जन्यते, मात्रामेरुः युगलेन ।  एतत् machine/Prastara_*.hs-मध्ये चलति ।
import NastaUddista_TheRankUnrankAlgebraTheMachineRunsOn
-- संख्या-पङ्क्ति-सेतुः — पिङ्गलस्य संख्या-प्रत्ययः = मेरु-पङ्क्ति-योगः (count n = ∑ₖ C(n,k))
import PrastaraPankti

-- The saptabhag: Bhagavat Stra (pre-CE strata, redacted c. 5th c.);
-- Umsvti, Tattvrthastra 1.6, 1.33, 5.29, 5.31; Siddhasena Divkara,
-- Sanmatitarka 1.21 and 1.28 (c. 5th c.); Samantabhadra, ptamms
-- (c. 6th c.); Akalaṅka, Laghīyastraya (c. 720–780) for the argument that
-- the number is EXACTLY seven; Mallisena, Sydvdamajar (1292) for
-- sakaldea against vikaldea.  avaktavyam is proved well-defined,
-- decidable, realised, and NOT the denotation of any single standpointed
-- utterance -- which is what machine/Obstruction.hs (absent from this repository) was groping toward
-- when it invented `Unparsed`.
import SaptabhangiNaya

-- MĀDHAVA of Saṅgamagrāma (c. 1340–1425) and the Kerala school; jīva
-- (the sine-chord); the aa reading of the truth-instrument.
import Madhava
import Jiva
import AmshaSatyayantra

-- अनुक्तम् is not अवक्तव्यम्, and the difference is a swapped quantifier.
-- Satyayantra.agda glossed its third position as avaktavyam; Purnata
-- proves that position सामयिक (for every instance SOME grant removes
-- it) and SaptabhangiNaya proves the fourth bhaṅga नित्य (for every
-- single utterance SOME profile survives it).  Dual shapes, one word.
-- Akalaṅka's kramārpaṇa against sahārpaṇa, Laghīyastraya c. 720–780.
import AnuktaAvaktavya

-- The two saptabhag modules:
-- Saptabhangi.agda (क्रम-सह-भेदः, that the sequential bhaṅga is
-- not the simultaneous one, and दुर्नयः, that ANY two-valued verdict
-- identifies two of the three seeds by pigeonhole) and
-- SaptabhangiNaya.agda.  AnuktaAvaktavya §7 holds both and draws
-- the distinction that keeps them from contradicting: content is
-- reachable by a pair, position is not reachable by sequencing.
import Saptabhangi

-- The machine's own material read back: the curriculum its obligations
-- demand, descent by distinction, and return.
import BhedaDescent
import LosslessReturn

------------------------------------------------------------------------
-- Two correctors.
--
-- `NaturalMachine/SamayikaAndNityaAreIndependent.agda` and
-- `NaturalMachine/TheFourthCornerIsRefutedUnderPointwiseStability.agda` (absent from this repository).
--
-- In general:
-- an aggregate is not only a list of what to check.  It is the only place
-- in a module system where mutually uncitable results can be held
-- together.  Every pair (claim, refutation-that-uses-the-claim) in this
-- corpus has this shape.
------------------------------------------------------------------------

import SamayikaAndNityaAreIndependent
import OrderAstiNasti_TheFourthCornerIsRefutedUnderPointwiseStability

------------------------------------------------------------------------
-- Tantrayukti_ARetractionThatIsNotStrictIsNotARetraction imports both
-- AnuktaAvaktavya and the two modules that refute it, which no one of
-- them can do, and holds the objection and the survivor in one checked
-- record.  Kauilya, Arthastra 15.1; Caraka Sahit, Siddhisthna 12.
------------------------------------------------------------------------

import Tantrayukti_ARetractionThatIsNotStrictIsNotARetraction

------------------------------------------------------------------------
-- The dispute, not the blend.
--
-- ApohaParyaya_… makes the Bauddha argue against a Jaina construction
-- already in this corpus, and exhibits the incompatibility WITHOUT
-- resolving it.  Modern treatments blend the two schools
-- into one "Indic" toolkit, which discards the dispute, and the dispute
-- is the content — CLAUDE.md (absent from this repository)'s mining directive, one level up.
--
-- Dignāga, Pramāṇasamuccaya (c. 480–540); Dharmakīrti, Pramāṇavārttika
-- (c. 600–660); Śāntarakṣita, Tattvasaṅgraha (c. 750).  Against Umāsvāti,
-- Tattvārthasūtra 5.29 and 5.31; Akalaṅka (c. 720–780); Vidyānanda,
-- Aasahasr (c. 850); Prabhcandra, Prameyakamalamrtaa (c. 1000).
------------------------------------------------------------------------

import ApohaParyaya_WhetherConceptualContentIsNegativeIsWhatTheTwoSchoolsActuallyDispute

------------------------------------------------------------------------
-- The fitness condition on absence.
--
-- Anupalabdhi_… adds the slot the corpus's absence machinery did not have.
-- `AbhavaAvacchedaka` and `TheAnuyogitaAvacchedakaIsADistinctSlot`
-- carry the Navya-Nyāya slots — pratiyogin, anuyogin, avacchedaka — and none
-- of them carries the EXTENT SEARCHED, which is what makes non-apprehension a
-- prama instead of an excuse.  The theorem is one line and the
-- counterexample is the content: a search that is clean over a real, non-empty
-- examined region while the absence is false.
--
-- Kumrila Bhaa, lokavrttika, Abhvapariccheda (c. 7th c.), for
-- anupalabdhi as a separate prama; Prabhkara refuses it as separate and
-- folds it into perception; both impose yogynupalabdhi, and it is the
-- condition and not the count of pramas that this file formalises.  Nothing
-- in it is Jaina, and it says so: syd-nsti with its fourfold ground is a
-- different construction and the exchange between the two schools is exhibited
-- rather than settled, in the Haskell lane.
------------------------------------------------------------------------

import Anupalabdhi_TheFitnessIsWhatMakesNonApprehensionKnowledge
