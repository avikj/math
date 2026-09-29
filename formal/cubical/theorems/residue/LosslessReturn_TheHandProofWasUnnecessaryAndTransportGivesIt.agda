{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- पुनरागमनम् — हस्तसाधनम् अनावश्यकम् आसीत् ; संक्रमणं ददाति ।
--
-- (the hand proof was unnecessary; transport gives it.)
--
-- WHAT THIS IS.  `VivekaPramana_TheRemainderIsLawfulAndTheNetBeats.agda`
-- proves (ℕ × ℕ) ≡ विवेक-प्रमाण by hand.  Its `Iso.rightInv` transports
-- दक्षिण along the प्रमाण field and fills the प्रमाण component with
-- `isProp→PathP` over `isSetℕ`, and its header records the fight:
--
--     "`isPropNat` does not exist and CANNOT: ℕ is not a proposition."
--
-- That obstacle is not in the mathematics.  It is an artefact of building
-- the equivalence instead of recognising it.  The record IS
-- `Fibre.Carrier`'s `Carrier` at योग, for योग (s , l) = s + l, whose fibre is
-- `singl (s + l)`, contractible by `isContrSingl` — no h-level hypothesis,
-- no ℕ, no transport of a field, and true for ARBITRARY A and B.
--
-- So nothing here is constructed.  §1 names the map, §2 is the fibre,
-- §3 is the equivalence and the path, and §4 is the identification with
-- the hand-built one — every proof `refl` or a library lemma.  The
-- content is that there was nothing to do.
--
-- अहिंसा-सूत्र-विस्तारः §६ · द्वौ मार्गौ.  This is the first road taken
-- where the second had been written by hand: संक्रमणे संरचना वहति, and the
-- structure that carries here is the whole equivalence.
--
-- `Carrier` is restated here rather than imported from fibre/ (five
-- lines); §६ records that this duplication is deliberate.
------------------------------------------------------------------------

module LosslessReturn_TheHandProofWasUnnecessaryAndTransportGivesIt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv ; isoToPath)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Univalence using (ua ; uaβ)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _×_ ; _,_ ; fst ; snd ; Σ-contractSnd)
open import Cubical.Data.Nat using (ℕ ; _+_)

import VivekaPramana_TheRemainderIsLawfulAndTheNetBeats as V

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- १ · वाहकः — the law, restated in five lines.
--
-- base, carried, and the witness that the second is the first's image.
------------------------------------------------------------------------

record Carrier {A B : Type ℓ} (f : A → B) : Type ℓ where
  constructor carry
  field
    base    : A
    carried : B
    witness : f base ≡ carried

open Carrier public

------------------------------------------------------------------------
-- २ · क्षेत्रं सम्पूर्णम् — the fibre is contractible, and that is the whole
-- proof.
--
-- `singl (f a)` is inhabited by (f a , refl) and everything in it is
-- joined to that point.  No h-level hypothesis on A or B anywhere.
------------------------------------------------------------------------

module _ {A B : Type ℓ} (f : A → B) where

  क्षेत्रम् : A → Type ℓ
  क्षेत्रम् a = singl (f a)

  क्षेत्र-सम्पूर्णम् : (a : A) → isContr (क्षेत्रम् a)
  क्षेत्र-सम्पूर्णम् a = isContrSingl (f a)

  ------------------------------------------------------------------------
  -- ३ · संक्रमणम् — and therefore A ≃ Carrier f, and A ≡ Carrier f.
  ------------------------------------------------------------------------

  Carrier-as-Σ : Iso (Carrier f) (Σ[ a ∈ A ] क्षेत्रम् a)
  Iso.fun      Carrier-as-Σ c       = base c , (carried c , witness c)
  Iso.inv      Carrier-as-Σ (a , p) = carry a (p .fst) (p .snd)
  Iso.rightInv Carrier-as-Σ _       = refl
  Iso.leftInv  Carrier-as-Σ _       = refl

  Σ-law : (Σ[ a ∈ A ] क्षेत्रम् a) ≃ A
  Σ-law = Σ-contractSnd क्षेत्र-सम्पूर्णम्

  अवतरण : A → Carrier f
  अवतरण a = carry a (f a) refl

  उत्थान : Carrier f → A
  उत्थान = base

  उत्थान-अवतरण : (a : A) → उत्थान (अवतरण a) ≡ a
  उत्थान-अवतरण _ = refl

  अवतरण-उत्थान : (c : Carrier f) → अवतरण (उत्थान c) ≡ c
  अवतरण-उत्थान (carry a b w) i = carry a (q i .fst) (q i .snd)
    where
      q : Path (singl (f a)) (f a , refl) (b , w)
      q = isContrSingl (f a) .snd (b , w)

  Carrier-Iso : Iso A (Carrier f)
  Carrier-Iso = iso अवतरण उत्थान अवतरण-उत्थान उत्थान-अवतरण

  Carrier≃ : A ≃ Carrier f
  Carrier≃ = isoToEquiv Carrier-Iso

  Carrier≡ : A ≡ Carrier f
  Carrier≡ = ua Carrier≃

------------------------------------------------------------------------
-- ४ · तादात्म्यम् — and विवेक-प्रमाण is that, at योग.
--
-- Every line below is refl.  The hand-built record and `Carrier योग` are
-- the same object; uncurrying is the entire difference.
------------------------------------------------------------------------

योग : ℕ × ℕ → ℕ
योग x = fst x + snd x

विवेक≅वाहकः : Iso V.विवेक-प्रमाण (Carrier योग)
Iso.fun      विवेक≅वाहकः v = carry (v .V.सम , v .V.वाम) (v .V.दक्षिण) (sym (v .V.प्रमाण))
Iso.inv      विवेक≅वाहकः c =
  record { सम = fst (base c) ; वाम = snd (base c)
         ; दक्षिण = carried c ; प्रमाण = sym (witness c) }
Iso.rightInv विवेक≅वाहकः _ = refl
Iso.leftInv  विवेक≅वाहकः _ = refl

विवेक≃वाहकः : V.विवेक-प्रमाण ≃ Carrier योग
विवेक≃वाहकः = isoToEquiv विवेक≅वाहकः

------------------------------------------------------------------------
-- ५ · यत् अनावश्यकम् आसीत् — what the hand proof was for.
--
-- `V.ℕ×ℕ≡विवेक-प्रमाण` is built from an Iso whose rightInv transports
-- दक्षिण along प्रमाण and discharges the प्रमाण component with
-- isProp→PathP over isSetℕ.  Here the same path is `Carrier≡ योग`
-- composed with §4's equivalence, and NOTHING about ℕ is used: no isSetℕ,
-- no isProp→PathP, no transport of a field.  Replace ℕ by any type and
-- the proof is unchanged.
------------------------------------------------------------------------

ℕ×ℕ≡वाहकः : (ℕ × ℕ) ≡ Carrier योग
ℕ×ℕ≡वाहकः = Carrier≡ योग

ℕ×ℕ≡विवेक-प्रमाण : (ℕ × ℕ) ≡ V.विवेक-प्रमाण
ℕ×ℕ≡विवेक-प्रमाण = ℕ×ℕ≡वाहकः ∙ sym (ua विवेक≃वाहकः)

-- and it is the same path the hand proof produced, because the two
-- constructions have the same endpoints and there was only ever one
-- equivalence to have.
समान-मार्गः : (x : ℕ × ℕ) → V.उत्थान (V.अवतरण x) ≡ x
समान-मार्गः _ = refl

------------------------------------------------------------------------
-- ६ · शेषः — what is written rather than repaired.
--
-- `VivekaPramana_…` is NOT edited.  §६ of the sūtra gives two roads and
-- this module takes the first; deleting another seat's second road would
-- be the collapse the corpus refuses (§७: नयभेदे सङ्क्षेपो न विद्यते).
-- What is claimed is only that the h-level obstacle its header records is
-- an artefact of the construction and not of the mathematics.
--
-- `Carrier` is restated here rather than imported.  It was written when
-- the carrier library (then punaragamana/, now fibre/, module
-- `Fibre.Carrier`) was a separate lake with its own pin that
-- formal/cubical could not import.  That duplication is a defect, it is
-- deliberate, and the fix is to import the record from fibre/ rather than
-- to keep two copies of a five-line record.  natural-machine.agda-lib now
-- lists `fibre` under `depend:`, so that fix is available.
------------------------------------------------------------------------
