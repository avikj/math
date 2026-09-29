{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- शून्यभारः — यन्त्रस्य आज्ञाः शून्यभाराः ; घातः तु स्व-आवृत्त्या तस्मात् बहिः ।
--
-- (the instruction set carries zero charge; the power map sits off it by
--  exactly its own period.)
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS.  One edge, between three modules.  Two existing
-- theorems are composed and the composite is instantiated once.  The
-- whole file is the composition.
--
--   `Machine_…`          Program A B = A ≃ B — every instruction of this
--                       computer is an equivalence.
--   `SvaFiberVasa_…`    ध्रुव-बिन्दुः : isEquiv f → isContr (Σ[ Φ ] संरक्षणम् f Φ)
--                       — a lossless observable's conserving-flow space
--                       is a POINT (itself `invIso Σ-Π-Iso` evaluated).
--   `GhataFiber_…`      powg = घात g in C₃, whose fibre over ε is not
--                       contractible: 0, 3 and 6 all land there.
--
-- §१ composes the first two: **every instruction of the machine has a
-- contractible space of conserving flows.**  The groupoid has exactly one
-- conserving flow at each of its own operations, and it is the identity.
-- No gauge freedom, no charge, nothing conserved — because nothing is
-- hidden.  `Dhruva_…`'s सूत्र read at the machine: no loss, no symmetry,
-- and the machine is all equivalences.
--
-- §२–३ exhibit the contrast at the map the crypto arc runs on, and the
-- contrast is what keeps §१ from being vacuous.  Translation by the
-- ORDER conserves `powg`, and it is not the identity flow, so `powg`'s
-- conserving-flow space is not a point — hence `powg` is not an
-- instruction of this machine.  §४ is that as a one-line corollary.
--
-- WHAT THE JOIN SAYS, and it is a reading of the terms and not a further
-- theorem: by `वासः` a conserving flow IS a section of the map's own
-- fibre family, so the flow `n ↦ 3 + n` is the section `a ↦ (3 + a , …)`
-- — at every exponent, the NEXT exponent with the same public value.
-- That section is the discrete log's ambiguity, and it is also the map's
-- symmetry.  **The thing an attacker cannot recover and the thing that
-- can move without being seen are one fibre.**
--
-- ────────────────────────────────────────────────────────────────────
--
-- TERM.  शून्य-भार is `Dhruva_…` §३'s own compound for a contractible
-- fibre carrying no charge, and is reused rather than coined.  आवृत्ति
-- (period, recurrence) is ordinary.
------------------------------------------------------------------------

module Sunyabhara_TheInstructionSetIsTheZeroChargePoleAndTheDiscreteLogSitsOffItByItsOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; isEquiv ; equivFun ; fiber)
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Properties using (znots)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

open import Dhruva_TheSymmetryLivesInTheFibreAndWithoutALossThereIsNoSymmetry
  using (संरक्षणम्)
open import SvaFiberVasa_TheConservingFlowsOfAnyObservableAreTheSectionsOfItsOwnFibers
  using (ध्रुव-बिन्दुः ; तादात्म्यम् ; वासः)
open import Machine_TheComputerIsTheGroupoidOfProofsOfTransportNotTheMonoidOfIrreversibleSteps
  using (Program ; चालनम्)
open import GhataFiber_TheDiscreteLogIsTheFiberOfPingalasPowerAndShorsPeriodQueryIsWhatReadsIt
  using (powg ; εC)
open import BijamulaKrida_AConcreteKeypairRunsInACyclicGroupWhereTheModThatExhaustsTheHeapIsNotNeeded
  using (C₃ ; e₀ ; g ; g² ; _∘_)

private variable ℓ : Level

------------------------------------------------------------------------
-- १ · THE MACHINE'S POLE.  Every instruction has a contractible space of
--     conserving flows: one flow, the identity, no charge.
--
-- One line, and that is the point — `Program` is `_≃_`, and a lossless
-- observable's flow space is `isContr` by `SvaFiberVasa`.
------------------------------------------------------------------------

यन्त्र-शून्य-भारः : {A B : Type ℓ} (p : Program A B)
                 → isContr (Σ[ Φ ∈ (A → A) ] संरक्षणम् (चालनम् p) Φ)
यन्त्र-शून्य-भारः p = ध्रुव-बिन्दुः (चालनम् p) (snd p)

-- and therefore the only conserving flow of an instruction is the
-- identity, pointwise — `SvaFiberVasa`'s containment check, read here.
यन्त्रे-न-गतिः : {A B : Type ℓ} (p : Program A B)
              → (Φ : A → A) → संरक्षणम् (चालनम् p) Φ → (a : A) → Φ a ≡ a
यन्त्रे-न-गतिः p = तादात्म्यम् (चालनम् p) (snd p)

------------------------------------------------------------------------
-- २ · THE CONTRAST.  Translation by the order conserves the power map.
--
-- `घात g 3 ≡ ε` is refl in `BijamulaKrida`, so three successor steps
-- prepend g³.  What is needed is g³ acting as the unit ON EVERY
-- ELEMENT: three cases, each `refl`, and then the period law is
-- `cong` of it.  `g³ ≡ ε` and `∀ x. g³ ∘ x ≡ x` are two statements
-- and only the second reduces under a bound exponent.
------------------------------------------------------------------------

त्रिघात-एकम् : (x : C₃) → g ∘ (g ∘ (g ∘ x)) ≡ x
त्रिघात-एकम् e₀ = refl
त्रिघात-एकम् g  = refl
त्रिघात-एकम् g² = refl

आवृत्तिः : (n : ℕ) → powg (3 + n) ≡ powg n
आवृत्तिः n = त्रिघात-एकम् (powg n)

-- the flow itself, and its conservation witness
आवृत्ति-प्रवाहः : ℕ → ℕ
आवृत्ति-प्रवाहः n = 3 + n

आवृत्ति-संरक्षणम् : संरक्षणम् powg आवृत्ति-प्रवाहः
आवृत्ति-संरक्षणम् = आवृत्तिः

------------------------------------------------------------------------
-- ३ · TWO FLOWS, SO NOT A POINT.  The identity flow and the period flow
--     are both conserving and are distinct at 0.
------------------------------------------------------------------------

एक-प्रवाहः : Σ[ Φ ∈ (ℕ → ℕ) ] संरक्षणम् powg Φ
एक-प्रवाहः = idfun ℕ , λ _ → refl

आवृत्ति-प्रवाह-युग्मम् : Σ[ Φ ∈ (ℕ → ℕ) ] संरक्षणम् powg Φ
आवृत्ति-प्रवाह-युग्मम् = आवृत्ति-प्रवाहः , आवृत्ति-संरक्षणम्

द्वौ-प्रवाहौ : ¬ (एक-प्रवाहः ≡ आवृत्ति-प्रवाह-युग्मम्)
द्वौ-प्रवाहौ p = znots (cong (λ σ → σ .fst 0) p)

घात-न-शून्य-भारः : ¬ isContr (Σ[ Φ ∈ (ℕ → ℕ) ] संरक्षणम् powg Φ)
घात-न-शून्य-भारः c =
  द्वौ-प्रवाहौ (sym (c .snd एक-प्रवाहः) ∙ c .snd आवृत्ति-प्रवाह-युग्मम्)

------------------------------------------------------------------------
-- ४ · THE COROLLARY.  So the power map is not an instruction of this
--     machine — not "hard to invert", but not in the instruction set at
--     all, and §२ names by how much: its own period.
------------------------------------------------------------------------

घातः-न-आज्ञा : ¬ (Σ[ p ∈ Program ℕ C₃ ] (चालनम् p ≡ powg))
घातः-न-आज्ञा (p , q) =
  घात-न-शून्य-भारः
    (subst (λ h → isContr (Σ[ Φ ∈ (ℕ → ℕ) ] संरक्षणम् h Φ)) q
           (यन्त्र-शून्य-भारः p))

------------------------------------------------------------------------
-- ५ · शेषः —— the reading in the header.
--
-- `वासः powg` carries आवृत्ति-प्रवाह-युग्मम् to the section
-- `a ↦ (3 + a , आवृत्तिः a)`: at every exponent, the next exponent with
-- the same public value.  That section is a point of the same fibre
-- family whose non-contractibility at ε is `GhataFiber.तन्तुः-द्विपदः`.
-- The two are the same family; the sentence "the ambiguity and the
-- symmetry are one object" says that and no more.
------------------------------------------------------------------------
