{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- HidingAndHardnessAreOneFibreSoTwoWitnessesForbidExtraction
--
-- TERM.  गुप्ति · gupti -- guarding, concealment; from गुप्, to hide.  In
-- Jaina usage it is one of the means of savara -- the three guptis, the
-- restraint of mind, speech and body.  The word is taken in its plain sense,
-- which is concealment, because that is what §2 proves costs `isProp`.
-- (
-- has a technical vocabulary for secret communication -- Kauilya's
-- *Arthaśāstra* uses गूढ-compounds for it, and the Kāmasūtra's list of arts
-- includes .)
--
------------------------------------------------------------------------
-- WHY THIS FILE EXISTS.
--
-- The corpus proves the structural content of zero-knowledge in at least
-- five places and never once uses the phrase.  The five places:
--
--   `TheWholeDerivationTypeIsOneFibre…`  fibre-is-everything: a map into a
--     proposition has every fibre equal to its whole domain.
--   `TheDerivationCarriesNoMeaning…`     soundness-factors-through-truncation:
--     the verifier's view is a function of ∥ Derivation ∥₁ and not of the
--     derivation.
--   `TritiyaMarga_…`                     getting a witness back out of an
--     existence costs Markov's principle.
--   `fibre/` and abstracts/05             bind the output and the fibre is
--     contractible, free; bind the input and it is the exact loss.  Every
--     cryptographic construction sits at the second binding.
--   abstracts/19, abstracts/11            the same fibre in phonology, and
--     non-interference holding definitionally rather than approximately.
--
-- What no file does is put the two readings of that one fibre side by side.
-- This one does, and they turn out to be a single statement read twice.
--
--   §1  THE SETTING.  A witness type, a view type that is a PROPOSITION,
--       and the honest prover's map between them.  Three lines, no
--       protocol, no rounds, no coins.
--   §2  PERFECT SIMULATION COSTS `isProp` AND NOTHING ELSE.  The simulator
--       holds the statement and outputs the statement; the real transcript
--       and the simulated one are EQUAL -- not indistinguishable, not
--       computationally close.  One line, and it is the whole of hiding.
--   §3  AND THE VIEW SHRINKS NOTHING.  `fiber view v ≃ W`: after the
--       verifier has seen everything it will ever see, the space of
--       witnesses consistent with what it saw is the space it started with,
--       undiminished.  This is a stronger statement than §2 and it is where
--       the word "zero" is earned.
--   §4  EXTRACTION IS EXACTLY UNIQUENESS, in both directions.  The view is
--       invertible iff the witness was unique and the statement entails
--       one.  Both hypotheses are named because both are needed.
--   §5  SO HIDING AND HARDNESS ARE ONE FIBRE READ TWICE.  Two distinct
--       witnesses forbid extraction outright -- not "make it expensive",
--       forbid.  Hiding is that fibre being everything; hardness is that
--       same fibre being non-contractible.  ONE OBJECT, TWO READINGS.
--   §6  THE CANONICAL INSTANCE: `∣_∣₁` IS THE MODALITY.  Propositional
--       truncation is not merely a tool for stating hiding, it is the
--       maximal hiding view, and extraction from it is an equivalence
--       exactly when the witness is unique.
--   §7  THE KERNEL'S OWN INSTANCE, DISCHARGED WITH NO ASSUMPTION.  `sound`
--       is a perfect-hiding view, and at the kernel's own seed extraction
--       is impossible -- because two routes exist there, which is a term.
--   §8  THE ASYMMETRY.  Binding the output is contractible and free; the
--       whole price is at the other binding.  The prover gives away nothing
--       by evaluating.
--
-- THE SENTENCE, for this file.  A verifier is blind exactly to what its own
-- collapse identifies, and here the collapse is `isProp` on the view: the
-- statement type has no room to hold which witness, so it holds none, and
-- the amount it fails to hold is all of it.  Hiding is not achieved.  It is
-- what is left when a codomain has no capacity.
--
-- PRIOR ART IN THIS REPOSITORY, CITED AND NOT RESTATED.  None is imported: the kernel is kept self-contained on purpose,
-- and a citation that is checked elsewhere is not weaker for being cited.
--
--   `Laghava_TheCostAndTheInverseCannotCoexist…`  A COST AND AN INVERSE
--     CANNOT COEXIST, and §2 of it is this file's §5 arrived at from the
--     other side: a structure carrying a grading admits NO inverse -- not
--     no obvious one, no function whatsoever.  `len` is such a grading on
--     `Derivation` (`the-scalar-is-additive`, in `TheEncounterOfTwoPeers…`,
--     is exactly the `Matra` law), so derivation composition is already
--     forbidden an inverse by additivity alone.  §5 below forbids
--     extraction from MULTIPLICITY instead.  Two independent routes to one
--     no-go, and the hypotheses are different -- which is the interesting
--     part, not a redundancy.  Read together they also say why `rev` can
--     exist here at all: it is an inverse up to MEANING and not on the
--     nose, and `the-round-trip-costs-four` is the grading refusing to be
--     zero.
--
-- abstracts/02, `every-operation-that-exists-is-sound`  UNFORGEABILITY BY
-- CONSTRUCTION. A `NativeOperation` cannot be built without a checked
-- derivation, so an operation carrying a falsehood is not rejected -- it
-- cannot be formed. That IS soundness against a dishonest party at the level
-- the kernel accepts things, and it holds against an adversary with full
-- control of the channel.
--
--   abstracts/05, `Bijamula`  A DEPLOYED HARDNESS ASSUMPTION, PROVED NOT
--     ASSUMED at one instance: the modular power map is shown constructively
--     not to be an equivalence, with the inversion function built from the
--     hypothesis and the recovery of the hidden exponent discharged, so the
--     assumption and the non-contractibility are interderivable rather than
--     analogous.  §5 below is the GENERAL form of that shape; that file is
--     the instance.  Neither subsumes the other.
--
--   * "Perfect" here means EQUAL, which is stronger than
--     indistinguishable, and it is bought entirely by the codomain being a
--     proposition.  A protocol whose transcripts do NOT land in a
--     proposition receives none of this for free and must pay with a
--     simulator argument.
--
--   * COMPLETENESS OF THE CALCULUS is the exact
--     hypothesis §4 takes.  `view : W → V` says an
--     honest party's view comes from a witness; it does not say an
--     inhabitant of `V` entails one.  At the kernel, `Meaning a b` can hold
--     with no `Derivation a b` -- two terms may be pointwise equal with no
--     route between them -- so `uniqueness-gives-extraction` demands
--     `V → W` explicitly.  This is COMPLETENESS, not soundness.
------------------------------------------------------------------------

module HidingAndHardnessAreOneFibreSoTwoWitnessesForbidExtraction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; fiber ; isEquiv ; invEquiv)
open import Cubical.Foundations.Isomorphism using (iso ; isoToIsEquiv)
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁ ; rec)
open import Cubical.Data.Empty using (⊥)

open import Kernel.RewriteCertificate
open import Kernel.GenerativeKernel using (seed ; target₀ ; direct-history ; detour-history)
open import Kernel.Residue_TheDerivationCarriesNoMeaningAtAllSoAllOfItIsRemainderAndNoSemanticCriterionSelectsTheShortOne
  using (direct≢detour ; derivations-are-not-a-proposition
        ; soundness-factors-through-truncation)
open import Kernel.Asesa_TheWholeDerivationTypeIsOneFibreSoSoundnessIsNeverAnEquivalence
  using (fibre-is-everything ; Meaning ; isPropMeaning ; sound
        ; the-whole-derivation-type-is-one-fibre
        ; soundness-is-not-an-equivalence-at-the-kernels-own-seed)

private
  variable
    ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------
-- §1.  THE SETTING.
--
-- `W` is what the prover holds.  `V` is what the verifier ends up with.
-- `view` is the honest prover's act.  The one hypothesis is that `V` is a
-- proposition -- that the statement type has no room to hold two positions.
--
-- Everything in §2-§5 is proved from that hypothesis alone.  No structure
-- on W, no decidability, no finiteness, no protocol.
------------------------------------------------------------------------

module _ {W : Type ℓ} {V : Type ℓ'} (isPropV : isProp V) (view : W → V) where

  ------------------------------------------------------------------------
  -- §2.  PERFECT SIMULATION, IN ONE LINE.
  --
  -- The simulator is the identity on the statement: given `v : V` and no
  -- witness at all, output `v`.  Then the honest transcript and the
  -- simulated transcript are EQUAL.  Not indistinguishable by a bounded
  -- adversary -- equal, as terms, for every witness and every statement.
  ------------------------------------------------------------------------

  simulate : V → V
  simulate v = v

  simulation-is-perfect : (w : W) (v : V) → view w ≡ simulate v
  simulation-is-perfect w v = isPropV (view w) v

  -- The same fact from the verifier's side: two provers holding different
  -- witnesses are indistinguishable, because their transcripts are equal.
  no-two-provers-differ : (w w′ : W) → view w ≡ view w′
  no-two-provers-differ w w′ = isPropV (view w) (view w′)

  -- and therefore NO function of the view separates them, at any type and
  -- any level -- the form the statement actually takes.
  no-verifier-strategy-separates :
    {C : Type ℓ''} (φ : V → C) (w w′ : W) → φ (view w) ≡ φ (view w′)
  no-verifier-strategy-separates φ w w′ = cong φ (no-two-provers-differ w w′)

  ------------------------------------------------------------------------
  -- §3.  AND THE VIEW SHRINKS NOTHING.
  --
  -- §2 says the transcripts agree.  This says something strictly stronger
  -- and it is where the word "zero" is earned: the space of witnesses
  -- consistent with what the verifier saw IS the space of witnesses, with
  -- nothing removed.  A verifier that has seen the entire interaction has
  -- not narrowed the field by one element.
  ------------------------------------------------------------------------

  the-view-shrinks-nothing : (v : V) → fiber view v ≃ W
  the-view-shrinks-nothing = fibre-is-everything isPropV view

  ------------------------------------------------------------------------
  -- §4.  EXTRACTION IS EXACTLY UNIQUENESS.  Both directions, both
  -- hypotheses named.
  ------------------------------------------------------------------------

  -- If the view is invertible, the witness was unique.  So an extractor is
  -- not a clever algorithm that was missing: its existence RETROACTIVELY
  -- collapses the witness space to a point.
  extraction-forces-uniqueness : isEquiv view → (w w′ : W) → w ≡ w′
  extraction-forces-uniqueness e =
    isOfHLevelRespectEquiv 1 (invEquiv (view , e)) isPropV

  -- And conversely -- with BOTH hypotheses, because both are needed: the
  -- statement must entail a witness (`extract`, which is soundness and is
  -- not free), and the witness must be unique (`isPropW`).
  uniqueness-gives-extraction : (extract : V → W) → isProp W → isEquiv view
  uniqueness-gives-extraction extract isPropW =
    isoToIsEquiv (iso view extract
                      (λ v → isPropV (view (extract v)) v)
                      (λ w → isPropW (extract (view w)) w))

  ------------------------------------------------------------------------
  -- §5.  HIDING AND HARDNESS ARE ONE FIBRE READ TWICE.
  --
  -- §3: the fibre is everything -- that reading is HIDING.
  -- §4: the fibre is contractible iff the view inverts -- that reading is
  -- HARDNESS.  It is the same fibre.  So:
  --
  --   TWO DISTINCT WITNESSES FORBID EXTRACTION.
  --
  -- Not make it expensive.  Not make it require more samples.  Forbid: the
  -- type of extractors is empty, unconditionally, with no complexity
  -- assumption anywhere in the argument.
  ------------------------------------------------------------------------

  two-witnesses-forbid-extraction :
    (w w′ : W) → (w ≡ w′ → ⊥) → isEquiv view → ⊥
  two-witnesses-forbid-extraction w w′ separated e =
    separated (extraction-forces-uniqueness e w w′)

  -- Read the other way round, which is the sentence this file is for: a
  -- proof system hides exactly as much as its witness space is large, and
  -- a system with a unique witness hides NOTHING -- the view determines it.
  a-unique-witness-hides-nothing :
    (extract : V → W) → isProp W → (v : V) (w : W) → extract v ≡ w
  a-unique-witness-hides-nothing extract isPropW v w = isPropW (extract v) w

------------------------------------------------------------------------
-- §6.  THE CANONICAL INSTANCE.  `∣_∣₁` IS THE HIDING MODALITY.
--
-- Propositional truncation is not just a device for STATING that something
-- is hidden.  It is the maximal hiding view: `squash₁` is the `isProp`
-- hypothesis, so every theorem above applies to it with nothing supplied.
------------------------------------------------------------------------

the-truncation-simulates-perfectly :
  {W : Type ℓ} (w : W) (t : ∥ W ∥₁) → ∣ w ∣₁ ≡ t
the-truncation-simulates-perfectly {W = W} = simulation-is-perfect squash₁ (∣_∣₁ {A = W})

the-truncation-shrinks-nothing :
  {W : Type ℓ} (t : ∥ W ∥₁) → fiber ∣_∣₁ t ≃ W
the-truncation-shrinks-nothing {W = W} = the-view-shrinks-nothing squash₁ (∣_∣₁ {A = W})

-- Extraction from an existence is an equivalence EXACTLY when the witness
-- was unique.  `TritiyaMarga_` prices the constructive escape from this for
-- decidable existences; here is the type-level statement of what is being
-- escaped from.
extraction-from-an-existence-forces-uniqueness :
  {W : Type ℓ} → isEquiv (∣_∣₁ {A = W}) → isProp W
extraction-from-an-existence-forces-uniqueness {W = W} e =
  extraction-forces-uniqueness squash₁ (∣_∣₁ {A = W}) e

a-unique-witness-can-be-extracted :
  {W : Type ℓ} → isProp W → isEquiv (∣_∣₁ {A = W})
a-unique-witness-can-be-extracted {W = W} isPropW =
  uniqueness-gives-extraction squash₁ (∣_∣₁ {A = W}) (rec isPropW (λ w → w)) isPropW

------------------------------------------------------------------------
-- §7.  THE KERNEL'S OWN INSTANCE, AND IT NEEDS NO ASSUMPTION.
--
-- `Meaning a b` is a proposition, so `sound a b` is a perfect-hiding view
-- of the derivation.  The kernel is therefore a perfect zero-knowledge
-- carrier for its own equations -- and unlike a cryptographic one it pays
-- nothing for it, because the payment was already made by ℕ being a set.
------------------------------------------------------------------------

the-kernel-simulates-perfectly :
  (a b : Tm) (d : Derivation a b) (m : Meaning a b) → sound a b d ≡ m
the-kernel-simulates-perfectly a b =
  simulation-is-perfect (isPropMeaning a b) (sound a b)

the-kernel-shrinks-nothing :
  (a b : Tm) (m : Meaning a b) → fiber (sound a b) m ≃ Derivation a b
the-kernel-shrinks-nothing = the-whole-derivation-type-is-one-fibre

-- and the hardness half, discharged at the kernel's own seed by exhibiting
-- the two witnesses rather than by assuming anything.  §5 applied.
the-kernel-forbids-extraction-at-its-own-seed :
  isEquiv (sound seed target₀) → ⊥
the-kernel-forbids-extraction-at-its-own-seed =
  two-witnesses-forbid-extraction
    (isPropMeaning seed target₀) (sound seed target₀)
    direct-history detour-history direct≢detour

-- The same conclusion is already in the corpus by a different route, and
-- the two agree.  Kept as a cross-check, not as a second result.
the-two-routes-to-that-conclusion-agree :
  isEquiv (sound seed target₀) → ⊥
the-two-routes-to-that-conclusion-agree =
  soundness-is-not-an-equivalence-at-the-kernels-own-seed

-- The verifier's view factors through the truncation, so the composite is
-- two hiding stages in series and each is perfect by §2.
the-view-factors-through-the-modality :
  {a b : Tm} (ρ : Env) → ∥ Derivation a b ∥₁ → eval a ρ ≡ eval b ρ
the-view-factors-through-the-modality = soundness-factors-through-truncation

-- and the multiplicity that makes §5 bite is a term, not a hypothesis.
the-witness-space-is-not-a-point :
  isProp (Derivation seed target₀) → ⊥
the-witness-space-is-not-a-point = derivations-are-not-a-proposition

------------------------------------------------------------------------
-- §8.  THE ASYMMETRY.  The prover gives away nothing by evaluating.
--
-- The fibre law's other binding, stated here because it is the half that
-- explains WHY all the price sits on the extraction side.  Fix the output
-- of any map at any argument and the space of "what could have accompanied
-- it" is contractible: the datum and the witness that it is the datum ride
-- together, free.  Fix the input instead and you get the fibre, which is
-- §3-§5.  Two bindings, two prices, and every construction that hides
-- something sits at the second.
------------------------------------------------------------------------

binding-the-output-is-free :
  {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) → isContr (singl (f a))
binding-the-output-is-free f a = isContrSingl (f a)
