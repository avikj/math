{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- लाघव — economy, the cost of a presentation.
--
-- TERM.  लाघव (lāghava) is the grammarians' own word for economy of
-- statement, in the tradition's own slogan
--
--     अर्धमात्रालाघवेन पुत्रोत्सवं मन्यन्ते वैयाकरणाः
--     "grammarians rejoice at the saving of half a mora as at the birth
--      of a son"
--
-- — a *paribhāṣā*-literature commonplace, NOT a sūtra of the Aṣṭādhyāyī,
-- and this file claims no stra.  The word is used for what it means
-- there: a measure that lives on the PRESENTATION and adds when
-- presentations are concatenated.  The group theory below originates
-- elsewhere and is not dressed in a borrowed name; only the measure
-- carries the tradition's word, because only the measure is its idea.
--
-- ────────────────────────────────────────────────────────────────────
-- THE MASTER THEOREM, in one sentence:
--
--     A COST AND AN INVERSE CANNOT COEXIST.
--
-- and its two halves are the two halves of this repository.
--
-- §2  A structure that is merely GRADED cannot be inverted — no function
--     whatsoever, not merely no obvious one.
-- §3  A structure that CAN be inverted has no COST — every cost on it
--     is identically zero, hence (by the cost's own unit-detection) the
--     structure is trivial.  Contrapositive: A NONTRIVIAL GROUP IS NOT
--     GRADED.
--
-- THE TWO HALVES DO NOT NEED THE SAME HYPOTHESIS, and the asymmetry is
-- the finding, not an artefact of how it was written.  §1 therefore
-- splits the notion in two:
--
--   `Matra`   a grading: it adds under composition.
--   `Laghava` a grading that ALSO detects the unit.
--
-- §2 takes a `Matra`.  Adding up is already enough to forbid an inverse:
-- composition can only accumulate, and the unit accumulates nothing.
-- §3 takes a `Laghava`, and needs the second field — without a cost that
-- recognises the unit it is measuring from, "everything has cost zero"
-- says nothing about what everything IS.
--
-- §4 and §5 are the two instances that matter here, and they are the two
-- objects this corpus is built out of:
--
--     TRANSPORT  `X ≃ X` under compEquiv is a group (`invEquiv` fills the
--                inverse, `invEquiv-is-rinv` on the nose).  Bool has a
--                self-equivalence that is not the identity.  Therefore
--                THERE IS NO COST FUNCTION ON THE TRANSPORTS OF Bool.
--
--     THE KERNEL `Derivation A A` under `⊕` has `len`, which adds under
--                concatenation — a `Matra`.  Therefore, by §2, no
--                function inverts it.  (Only a `Matra`: §5 records why
--                the unit-detection field is refused here by cubical
--                Agda in BOTH directions, and why §2 does not want it.)
--
-- WHAT THIS SETTLES.  "Cost is not a univalent
-- invariant — it lives on the presentation, which univalence discards"
-- has been carried in this corpus as a note and a slogan.  §4 is its
-- proof, and the proof is not about presentations at all: univalence
-- makes equivalent types EQUAL, so a univalent invariant is a function
-- on the groupoid of transports, and §3 says that groupoid — being a
-- nontrivial group — admits no grading.  The cost is not discarded by
-- univalence as a matter of bookkeeping.  IT CANNOT EXIST THERE.
--
-- WHERE THE PIECES WERE.  Each of the following is now an instance and
-- none of them cited another:
--
--   AvrttiResidue_…  `the-kernel-carries-no-inverse` — §2 at `len`.
--   Machine_…      `यन्त्रम् : GroupoidMachine (X ≃ X)` — §3's hypothesis.
--   Avirodha_…    "strictly a category, weakly a groupoid; the gap is
--                 the śeṣa" — §2 and §3 are what the gap IS.
--   Laghava
--                 `laghava-does-not-factor` — size does not factor
--                 through meaning.  That is the same refusal one level
--                 down: meaning is where the presentation is discarded,
--                 as `ua` is where the transport is.
--   Samyoge_…     "no grading function on maps that both respects
--                 composition and detects loss" — §3 stated for the
--                 monoid of MAPS instead of the monoid of routes.  Its
--                 witness `Unit → Bool → Unit ≡ id` is exactly a
--                 non-unit element of measure zero.
--
------------------------------------------------------------------------

module Laghava_TheCostAndTheInverseCannotCoexistSoNoNontrivialGroupIsGradedAndTransportHasNoPrice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; idEquiv ; equivFun)
open import Cubical.Data.Nat using (ℕ ; snotz ; _+_ ; +-zero ; inj-m+)
import Cubical.Data.Nat as N
open import Cubical.Data.Bool using (Bool ; true ; false ; notEquiv ; false≢true)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.Unit using (Unit ; tt)

open import Kernel.RewriteCertificate using (Tm ; Derivation ; done ; then-step)
open import Kernel.Residue_TheDerivationCarriesNoMeaningAtAllSoAllOfItIsRemainderAndNoSemanticCriterionSelectsTheShortOne
  using (len)
open import Machine_TheComputerIsTheGroupoidOfProofsOfTransportNotTheMonoidOfIrreversibleSteps
  using (MonoidMachine)
open import AvrttiResidue_TheKernelFillsTheMonoidStrictlyAndCarriesNoGroupoidSoTheRoundTripIsTheResidue
  using (A ; आवृत्तिः ; आवृत्तम् ; आवृत्तस्य-मात्रा ; len-⊕ ; एकत्वम्)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §0  Two facts about ℕ, proved rather than imported under a guessed
--     name, because the whole theorem rests on them and on nothing else.
------------------------------------------------------------------------

-- A sum that vanishes has a vanishing left summand.  This is the ONLY
-- property of ℕ the theorem uses: that it has no negatives.
वाम-शून्यम् : (m n : ℕ) → m + n ≡ N.zero → m ≡ N.zero
वाम-शून्यम् N.zero    n _ = refl
वाम-शून्यम् (N.suc m) n p = ⊥rec (snotz p)

-- and a number equal to its own double is zero.
द्विगुण-शून्यम् : (n : ℕ) → n ≡ n + n → n ≡ N.zero
द्विगुण-शून्यम् n p = sym (inj-m+ (+-zero n ∙ p))

------------------------------------------------------------------------
-- §1  A COST.  A grading that adds under composition and detects the
--     unit.  Both fields are essential and neither is decoration:
--     without `sayoge` a cost says nothing about composites, and
--     without `nye` the constant-zero function is a cost on
--     everything and the theorem is empty.
------------------------------------------------------------------------

-- THE GRADING alone: it adds under composition.  That is all §2 needs,
-- and saying so is not tidiness — it is the asymmetry of the theorem.
record Matra {Op : Type ℓ} (M : MonoidMachine Op) : Type ℓ where
  open MonoidMachine M
  field
    मात्रा   : Op → ℕ
    संयोगे   : (x y : Op) → मात्रा (seq x y) ≡ मात्रा x + मात्रा y

-- A COST is a grading that additionally DETECTS THE UNIT.  Without that
-- second field the constant-zero function is a grading on everything and
-- §3 is empty; with it, §3 turns a group into the trivial group.
record Laghava {Op : Type ℓ} (M : MonoidMachine Op) : Type ℓ where
  open MonoidMachine M
  field
    मूलम्   : Matra M
  open Matra मूलम् public
  field
    शून्ये   : (x : Op) → मात्रा x ≡ N.zero → x ≡ noop

-- The unit is free, and this is FORCED — not an axiom of either record.
-- `noop ⊕ noop ≡ noop` makes its cost equal to its own double.
अनोपस्य-मात्रा-शून्या :
  {Op : Type ℓ} (M : MonoidMachine Op) (L : Matra M)
  → Matra.मात्रा L (MonoidMachine.noop M) ≡ N.zero
अनोपस्य-मात्रा-शून्या M L =
  द्विगुण-शून्यम् (मात्रा noop)
    ( sym (cong मात्रा (unitL noop)) ∙ संयोगे noop noop )
  where open MonoidMachine M
        open Matra L

------------------------------------------------------------------------
-- §2  A COST REFUSES EVERY INVERSE.
--
--     Not "the obvious inverse fails".  No function at all: composition
--     can only ADD cost, and the unit has none, so nothing with cost can
--     ever be composed back to the unit.  ONE costly element is enough.
------------------------------------------------------------------------

-- NOTE THE HYPOTHESIS: `Matra`, not `Laghava`.  Unit-detection is not
-- used, and this is content.  Merely GRADING a structure already forbids
-- its inversion; only the converse (§3) needs the cost to recognise the
-- unit it is measuring distance from.
मात्रा-प्रतिलोमं-निषेधति :
  {Op : Type ℓ} (M : MonoidMachine Op) (L : Matra M)
  → (x : Op) → ¬ (Matra.मात्रा L x ≡ N.zero)
  → (inv : Op → Op)
  → ((y : Op) → MonoidMachine.seq M y (inv y) ≡ MonoidMachine.noop M)
  → ⊥
मात्रा-प्रतिलोमं-निषेधति M L x costly inv law =
  costly (वाम-शून्यम् (मात्रा x) (मात्रा (inv x))
           ( sym (संयोगे x (inv x))
           ∙ cong मात्रा (law x)
           ∙ अनोपस्य-मात्रा-शून्या M L ))
  where open Matra L

------------------------------------------------------------------------
-- §3  AN INVERSE REFUSES EVERY COST.
--
--     The converse, and the half that reaches univalence.  If the
--     structure inverts, every element has cost zero; by `nye` every
--     element IS the unit.  So a NONTRIVIAL group carries no cost at all.
------------------------------------------------------------------------

प्रतिलोमे-सर्वं-नोपः :
  {Op : Type ℓ} (M : MonoidMachine Op) (L : Laghava M)
  → (inv : Op → Op)
  → ((y : Op) → MonoidMachine.seq M y (inv y) ≡ MonoidMachine.noop M)
  → (x : Op) → x ≡ MonoidMachine.noop M
प्रतिलोमे-सर्वं-नोपः M L inv law x =
  शून्ये x (वाम-शून्यम् (मात्रा x) (मात्रा (inv x))
            ( sym (संयोगे x (inv x))
            ∙ cong मात्रा (law x)
            ∙ अनोपस्य-मात्रा-शून्या M मूलम् ))
  where open Laghava L

-- THE MASTER STATEMENT, in the form that gets used: a group with a
-- non-unit element is not graded.
अनेकगणे-मात्रा-नास्ति :
  {Op : Type ℓ} (M : MonoidMachine Op)
  → (inv : Op → Op)
  → ((y : Op) → MonoidMachine.seq M y (inv y) ≡ MonoidMachine.noop M)
  → (x : Op) → ¬ (x ≡ MonoidMachine.noop M)
  → ¬ Laghava M
अनेकगणे-मात्रा-नास्ति M inv law x nontrivial L =
  nontrivial (प्रतिलोमे-सर्वं-नोपः M L inv law x)

------------------------------------------------------------------------
-- §4  TRANSPORT HAS NO PRICE.
--
--     `X ≃ X` under compEquiv is a group.  `Bool ≃ Bool` has a
--     self-equivalence that is not the identity.  Therefore, by §3,
--     THERE IS NO COST FUNCTION ON THE TRANSPORTS OF Bool.
--
--     This is the proof of the standing claim that cost is not a
--     univalent invariant.  A univalent invariant is a function on the
--     groupoid of transports; §3 says that groupoid has no grading.  The
--     cost is not *discarded* by univalence.  It cannot live there.
------------------------------------------------------------------------

-- Bool's flip is a transport and is not the no-op: it moves `true`.
नो-नोपः : ¬ (notEquiv ≡ idEquiv Bool)
नो-नोपः p = false≢true (cong (λ e → equivFun e true) p)

संक्रमणस्य-मूल्यं-नास्ति : ¬ Laghava (एकत्वम् Bool)
संक्रमणस्य-मूल्यं-नास्ति =
  अनेकगणे-मात्रा-नास्ति (एकत्वम् Bool)
    (λ e → invOf e) (λ e → rinvOf e) notEquiv नो-नोपः
  where
  -- the inverse and its right law, named locally so §4 depends on the
  -- SAME monoid record §3 quantifies over and not on a re-spelling.
  open import Cubical.Foundations.Equiv using (invEquiv ; invEquiv-is-rinv)
  invOf  : (Bool ≃ Bool) → (Bool ≃ Bool)
  invOf  = invEquiv
  rinvOf : (e : Bool ≃ Bool) → MonoidMachine.seq (एकत्वम् Bool) e (invOf e)
                             ≡ MonoidMachine.noop (एकत्वम् Bool)
  rinvOf = invEquiv-is-rinv

------------------------------------------------------------------------
-- §5  THE KERNEL HAS ONE.
--
--     `len` adds under `⊕` (that is `len-⊕`, from AvrttiResidue_) and
--     detects `done` (below).  So it is a cost in the sense of §1, and
--     §2 then refuses every inverse — which is `AvrttiResidue_`'s
--     `the-kernel-carries-no-inverse`, now as an INSTANCE rather than
--     as its own argument.
------------------------------------------------------------------------

कर्णस्य-मात्रा : Matra आवृत्तिः
कर्णस्य-मात्रा = record
  { मात्रा = len
  ; संयोगे = len-⊕ }

-- ONLY A `Matra`, AND THE REASON IS NOT LAZINESS.
--
-- The missing field would be `len d ≡ 0 → d ≡ done A`, and its proof is
-- two clauses.  Both are refused, in opposite directions, and the pair of
-- refusals is worth recording because it is the repository's own cubical
-- idiom biting at exactly the place the theorem is about:
--
--   at the CONCRETE endpoint `A = add var zero`, matching `done _`
--   against `Derivation A A` makes Agda unify `add` with itself —
--   constructor injectivity in an INDEX position.  Agda accepts it and
--   emits `UnsupportedIndexedMatch`: the function "will not compute when
--   applied to transports".  In a file whose subject IS transport, that
--   is not a warning to carry.
--
--   at an ABSTRACT endpoint `a`, the unification `a ≟ a` is a reflexive
--   equation, and with K disabled — which `--cubical` disables — it
--   cannot be eliminated.  `SplitError.UnificationStuck`.
--
-- So the kernel's cost is a grading.  §2 takes a `Matra`.  Nothing below
-- is weakened, and
-- the general lesson is the one this corpus already carries — do not
-- match a constructor in an index position; match the datum, or measure
-- it.  `len` measures it.

-- the round trip costs, so the kernel is not a group — by the theorem,
-- not by a fresh argument.
कर्णः-न-गणः :
  (inv : Derivation A A → Derivation A A)
  → ((d : Derivation A A) → MonoidMachine.seq आवृत्तिः d (inv d)
                          ≡ MonoidMachine.noop आवृत्तिः)
  → ⊥
कर्णः-न-गणः =
  मात्रा-प्रतिलोमं-निषेधति आवृत्तिः कर्णस्य-मात्रा आवृत्तम्
    (λ p → snotz (sym आवृत्तस्य-मात्रा ∙ p))

------------------------------------------------------------------------
-- §6  WHAT THE TWO INSTANCES ARE TO EACH OTHER.
--
-- They are the same monoid interface (`MonoidMachine`, one record, one
-- file) carrying opposite answers to one question, and the question is
-- decidable by §2/§3 with no further information:
--
--     does this structure admit a lghava?
--
--   YES → it records its own history, and nothing can undo it.
--   NO  → it can be undone, and it remembers nothing.
--
-- There is no third position, and this is the sense in which the whole
-- corpus has one theorem in it.  `ua` is the passage from the second
-- column to the first read backwards: an equivalence, which has no cost
-- and no memory, becomes a PATH — and every route that produced it is
-- gone, not by omission but because the destination type has no room for
-- it.  `Aresidue_…` measures the loss exactly: soundness lands in a
-- proposition, so the fibre over any meaning is the WHOLE derivation
-- type, and by §5 that fibre is graded while the meaning is not.
--
-- The interface consequence, and it is mechanical: any wire that returns
-- a transport returns something §4 proves is priceless — and therefore
-- historyless.  A wire that intends to carry cost, route, effort, or
-- provenance must carry the DERIVATION, because §3 says those quantities
-- do not exist on the other side of `ua`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7  AND THEREFORE: NO FUNCTION OF THE IMAGE RECOVERS THE COST.
--
--     §3 refuses a cost ON a group.  This refuses something stronger and
--     more useful: given ANY map out of a graded structure onto a group
--     — not `ua`, not soundness, any monoid homomorphism with a section —
--     there is NO function whatsoever of the target that agrees with the
--     cost on the source.
--
--     `Laghava` has this as a two-point witness: it
--     exhibits `short` and `long`, equal in meaning, of sizes 3 and 5,
--     and concludes `laghava-does-not-factor` for THAT `size`.  A witness
--     refutes one candidate.  This refutes the type.
--
--     The proof is §3 run on the image: the section pushes the source's
--     additivity forward, so `f` is a grading on the target; the target
--     is a group, so §3's argument makes `f` identically zero; so the
--     cost it was supposed to reproduce is zero, and one costly element
--     ends it.
------------------------------------------------------------------------

मात्रा-न-प्रतिबिम्बात् :
  {Op : Type ℓ} {G : Type ℓ}
  (M : MonoidMachine Op) (MG : MonoidMachine G) (L : Matra M)
  (φ : Op → G)
  (hom  : (a b : Op) → φ (MonoidMachine.seq M a b)
                     ≡ MonoidMachine.seq MG (φ a) (φ b))
  (unit : φ (MonoidMachine.noop M) ≡ MonoidMachine.noop MG)
  (inv  : G → G)
  (rinv : (g : G) → MonoidMachine.seq MG g (inv g) ≡ MonoidMachine.noop MG)
  (ψ    : G → Op) (sec : (g : G) → φ (ψ g) ≡ g)
  (x    : Op) (costly : ¬ (Matra.मात्रा L x ≡ N.zero))
  → ¬ (Σ[ f ∈ (G → ℕ) ] ((z : Op) → Matra.मात्रा L z ≡ f (φ z)))
मात्रा-न-प्रतिबिम्बात् {G = G} M MG L φ hom unit inv rinv ψ sec x costly (f , eq) =
  costly (eq x ∙ f-शून्यम् (φ x))
  where
  -- the unit of the target is free, because the unit of the source is
  f-नोपः : f (MonoidMachine.noop MG) ≡ N.zero
  f-नोपः = cong f (sym unit)
         ∙ sym (eq (MonoidMachine.noop M))
         ∙ अनोपस्य-मात्रा-शून्या M L

  -- and the target is ADDITIVE, pushed forward along the section
  f-संयोगे : (g h : G) → f (MonoidMachine.seq MG g h) ≡ f g + f h
  f-संयोगे g h =
      cong f (cong₂ (MonoidMachine.seq MG) (sym (sec g)) (sym (sec h)))
    ∙ cong f (sym (hom (ψ g) (ψ h)))
    ∙ sym (eq (MonoidMachine.seq M (ψ g) (ψ h)))
    ∙ Matra.संयोगे L (ψ g) (ψ h)
    ∙ cong₂ _+_ (eq (ψ g)) (eq (ψ h))
    ∙ cong₂ _+_ (cong f (sec g)) (cong f (sec h))

  -- so f is a grading on a group, and §3's argument flattens it
  f-शून्यम् : (g : G) → f g ≡ N.zero
  f-शून्यम् g =
    वाम-शून्यम् (f g) (f (inv g))
      ( sym (f-संयोगे g (inv g)) ∙ cong f (rinv g) ∙ f-नोपः )

------------------------------------------------------------------------
-- §8  THE INSTANCE THE KERNEL IS.
--
--     `sound : Derivation a b → Meaning a b` lands in a PROPOSITION
--     (`Aresidue_…`, `isPropMeaning`), and an inhabited proposition is the
--     trivial group: one element, its own inverse, seq and noop forced.
--     So §7 applies with `G = Unit`, and says exactly this — NOTHING
--     COMPUTED FROM THE MEANING SEES THE ROUTE.  Not "no obvious
--     function": no function.
------------------------------------------------------------------------

एकः : MonoidMachine Unit
एकः = record
  { seq = λ _ _ → tt ; noop = tt
  ; unitL = λ _ → refl ; unitR = λ _ → refl ; assoc = λ _ _ _ → refl }

अर्थात्-न-मात्रा :
  ¬ (Σ[ f ∈ (Unit → ℕ) ] ((d : Derivation A A) → len d ≡ f tt))
अर्थात्-न-मात्रा (f , eq) =
  मात्रा-न-प्रतिबिम्बात् आवृत्तिः एकः कर्णस्य-मात्रा
    (λ _ → tt) (λ _ _ → refl) refl
    (λ _ → tt) (λ _ → refl)
    (λ _ → done A) (λ { tt → refl })
    आवृत्तम् (λ p → snotz (sym आवृत्तस्य-मात्रा ∙ p))
    (f , eq)
