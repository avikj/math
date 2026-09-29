{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सिद्धान्त — the settled conclusion.  THE LOSSLESS-MACHINE PAPER IN
-- ONE MODULE: EVERY CLAIM, ONE TERM.
--
-- Abstract 25 makes claims; this module binds each to its checked
-- term by name, so the paper's table of contents is itself checked.
-- A claim that drifted from its theorem would fail to typecheck here.
------------------------------------------------------------------------

module Siddhanta_TheLosslessMachinePaperInOneModuleEveryClaimOneTerm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; fiber ; invEq)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; suc ; _+_)
open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Maybe using (just)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.SetQuotients using (_/_ ; [_])
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

open import Vishvayantra_TheTuringStepIsTheVisibleProjectionOfTheLosslessStepAndTheKeptFibreIsTheSource
open import AnulomaViloma_TheTraceComposesTheCompletedRunRunsBackwardsByReflAndWhenTheMachineHaltsIsAProposition
open import Ekatva_LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleTypeAndTheMachinesIsUnique
open import Vrddhi_AVerifiedProgramTheSuccessorMachineAddsOneStrokeAndItsCertificateIsAFibrePoint
open import Vistara_ThePaddingLemmaABehaviorHasUnboundedlyManyProgramsSoTheCodeIsNotDeterminedByTheRun
open import Nasha_TheVisibleStepDestroysInformationAndTheCompletedStepCannotByConstruction
open import Samasa_ProgramsComposeTheSequencedTableRunsItsFirstPhaseThenHandsTheTapeToTheSecondAtTheRetireState
open import DviVrddhi_TheComposedSuccessorAddsTwoTheCertificatesConcatenateAndTheStepCountsAdd
open import Niyati_TheMachineHasExactlyOneExecutionDeterminismIsContractibilityOfTheStream
open import Reflection_TheBehaviorIsASetQuotientOfTheCodeItsFibreIsInfiniteAndTheLosslessTraceIsAPoint
open import Vikarna_TheDiagonalConfigurationMapThatNoProgramStepsSoUniversalityDemandsAChangeOfRepresentation
open import Avinimaya_TheMachinesStepsAreAllUnitaryWhenCompletedAndStillDoNotExchange
open import Transport_TheMachineIsItsCompletedSelfAsAnIdentificationInTheUniverseAndTheIdentificationComputes
open import TrtiyoMargoNaVidyate_EachStepIsATransportOrASilenceWithItsWitnessAndTheLimitIsNoThirdRoad
open import Pratyanayana_TheFirstHaltingTimeComesBackFromTheTruncationBecauseMinimalityMakesItCanonical
open import Sambandha_TheRelationalProgramWithUniqueAnswersIsTheMapSoAllThreePresentationsCollapseOntoOneFunction
open import Prashna_TheInteractiveMachineStrictlyContainsTheTuringMachineAndDeterminismIsExactlyTheCollapse
open import Sakshin_ReceiptedAnswersCollapseEveryQuestionAlphabetSoFreedomLivesOnlyInTheUnwitnessedEvent

------------------------------------------------------------------------
-- §1  The projection and its law.
------------------------------------------------------------------------

-- Ordinary UTM = forget trace ∘ lossless step, definitionally.
claim-projection : (mc : Machine) →
  fst (equivFun (LawfulStep.complete universal) mc) ≡ uStep mc
claim-projection = turing-is-the-projection

-- The commuting field is exactly strong enough: any lawful trace
-- family is the fibre family.
claim-trace-is-fibre : {X : Type} (L : LawfulStep X) (x : X) →
  LawfulStep.Trace L x ≃ fiber (LawfulStep.step L) x
claim-trace-is-fibre = trace-is-fiber

------------------------------------------------------------------------
-- §2  Losslessness is a property.
------------------------------------------------------------------------

claim-contractible : {A B : Type} (f : A → B) → isContr (Lossless f)
claim-contractible = losslessness-is-a-property

claim-lawful-are-maps : {A : Type} → LawfulStep A ≃ (A → A)
claim-lawful-are-maps = lawful-steps-are-the-maps

------------------------------------------------------------------------
-- §3  The ledger's algebra, and the clock.
------------------------------------------------------------------------

claim-reverse-is-refl : (n : ℕ) (mc : Machine) →
  invEq (run-lossless n) (run n mc , mc , refl) ≡ mc
claim-reverse-is-refl = source-recovered

claim-halting-time-prop : (mc : Machine) → isProp (Σ ℕ (FirstHalt mc))
claim-halting-time-prop = halting-time-is-a-proposition

claim-clock-needs-no-choice : (mc : Machine) →
  ∥ Σ ℕ (λ n → HaltsAt n mc) ∥₁ → Σ ℕ (FirstHalt mc)
claim-clock-needs-no-choice = the-clock-needs-no-choice

claim-one-execution : (mc : Machine) → isContr (Exec mc)
claim-one-execution = one-execution

------------------------------------------------------------------------
-- §4  Code against behavior.
------------------------------------------------------------------------

claim-step-forgets : Σ Machine (λ x → Σ Machine (λ y →
  (¬ x ≡ y) × (uStep x ≡ uStep y)))
claim-step-forgets = the-step-forgets

claim-diagonal : ¬ (Σ Code (λ M → (c : Conf) →
  snd (uStep (M , c)) ≡ diag c))
claim-diagonal = diagonal-escapes

claim-one-point-many-codes : (r : Rule) (M' : Code) →
  Σ (ℕ → Code) (λ codes →
    ((j k : ℕ) → codes j ≡ codes k → j ≡ k)
    × ((j k : ℕ) → Path Beh [ codes j ] [ codes k ]))
claim-one-point-many-codes = one-point-many-codes

------------------------------------------------------------------------
-- §5  Composition, exchange, the crossing, the doctrine.
------------------------------------------------------------------------

claim-double-increment : (n : ℕ) →
  snd (run (suc n + 2) (twice , unary n)) ≡ (2 , 1 ∷ ones n , 1 , [])
claim-double-increment = double-increment

claim-no-exchange : Σ Code (λ M₁ → Σ Code (λ M₂ →
  (Conf ≃ Σ Conf (fiber (stepOf M₁)))
  × ((Conf ≃ Σ Conf (fiber (stepOf M₂)))
  × (¬ ((c : Conf) → stepOf M₁ (stepOf M₂ c) ≡ stepOf M₂ (stepOf M₁ c))))))
claim-no-exchange =
  fst steps-do-not-exchange , fst (snd steps-do-not-exchange) ,
  fst (snd (snd steps-do-not-exchange)) ,
  fst (snd (snd (snd steps-do-not-exchange))) ,
  snd (snd (snd (snd steps-do-not-exchange)))

claim-crossing-computes : (mc : Machine) →
  transport machine≡completed mc ≡ (uStep mc , mc , refl)
claim-crossing-computes = crossing-computes

claim-no-third-road : (mc : Machine) →
  (Σ Conf (λ c' → δ (fst mc) (snd mc) ≡ just c')) ⊎ Halted mc
claim-no-third-road = no-third-road

------------------------------------------------------------------------
-- §6  The three grammars, one function; and the exact collapse.
------------------------------------------------------------------------

claim-relations-are-maps : {A B : Type} →
  (Σ (A → B → Type) Fun) ≃ (A → B)
claim-relations-are-maps = relational-programs-are-maps

claim-deterministic-collapse : (mc : Machine) → isContr (DetISC mc)
claim-deterministic-collapse = deterministic-collapse

claim-receipts-collapse-general : (Q' : Type) (act : Machine → Q' → Machine)
  (s : Machine) → isContr (RecISC Q' act s)
claim-receipts-collapse-general = receipts-collapse

claim-strictly-wider : ¬ isContr (FreeISC (incr , unary 0))
claim-strictly-wider = interaction-is-strictly-wider
