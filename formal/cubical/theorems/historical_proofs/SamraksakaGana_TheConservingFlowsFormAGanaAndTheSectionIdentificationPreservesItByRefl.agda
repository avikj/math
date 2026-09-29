{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- संरक्षकगणः — संरक्षकाः प्रवाहाः गणं रचयन्ति, स्वतन्तुवासश्च तं गणं
-- यथावत् वहति — refl-मात्रेण ।
--
-- (the gaa of conservers: the conserving flows form a monoid, and the
--  section identification carries the monoid — by refl.)
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS.  `SvaTantuVasa_….agda` closes the
-- loss–symmetry scale's middle with the identification
--
--     प्रवाहः f  =  (Σ[ Φ ] संरक्षणम् f Φ)  ≃  ((a : A) → fiber f (f a))
--
-- and this module carries the flow MONOID across it: the convolution
--
--     (s ⋆ t) a  =  ( s (t a .fst) .fst , s (t a .fst) .snd ∙ t a .snd )
--
-- — move by t, then move by s from where t landed, composing the
-- witnesses — is carried onto flow composition BY refl, in both the
-- operation and the unit (§१, गण-गमनम् / एक-गमनम्).  The identification
-- of the spaces was already an identification of the DYNAMICS, and the
-- cost of seeing it is zero.
--
-- At set level (§२–§३) both sides are genuine `Monoid`s of the library's
-- own algebra and वासः is a `MonoidEquiv`, with both preservation fields
-- refl.  §४ prices the poles: at zero loss the gaṇa is trivial — every
-- conserving flow IS the unit, no h-level needed (ध्रुव-बिन्दुः consumed);
-- at total loss the gaa is the FULL transformation monoid of the
-- domain, as monoids, again by refl on the homomorphism.  So the scale
-- of `Dhruva`/`Khahara` is now a scale of MONOIDS: trivial at the near
-- pole, everything at the far pole, and in between exactly the sections
-- of one's own fibres under ⋆.
--
-- ────────────────────────────────────────────────────────────────────
-- TERM.  गण — the class, the troop; in the grammatical tradition the
-- gaapha is the appended list of items that BEHAVE ALIKE under a rule
-- (Pini, Adhyy, ~500 BCE, whose stras cite gaas by their first
-- member; the gaapha is transmitted beside the strapha).  A
-- conserving flow is exactly an item that behaves alike toward the
-- observable — f cannot tell it acted — so the monoid of all of them is
-- named the gaṇa of conservers.  LIMIT: गण is attested as the
-- tradition's own device for "the class behaving alike under a rule";
-- the compound संरक्षकगण and the application to a monoid of flows are
-- built here, and no text is claimed for them.  "Monoid" itself is
-- modern (the structure is used from the library, not re-derived).
------------------------------------------------------------------------

module SamraksakaGana_TheConservingFlowsFormAGanaAndTheSectionIdentificationPreservesItByRefl where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Foundations.HLevels
  using (isSetΣ ; isSetΠ ; isPropΠ)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Monoid

open import Dhruva_TheSymmetryLivesInTheFibreAndWithoutALossThereIsNoSymmetry
open import Khahara_TheZeroDivisorEdgeIsPricedAtItsWholeDomainAndTotalLossIsExactlyTotalSymmetry
  using (सर्व-नाशः)
open import SvaFiberVasa_TheConservingFlowsOfAnyObservableAreTheSectionsOfItsOwnFibers

private variable ℓ : Level

module _ {A B : Type ℓ} (f : A → B) where

  ------------------------------------------------------------------
  -- §१ · THE OPERATIONS, AND THE refl-TRANSPORT.
  --
  -- Conserving flows are closed under composition — the witness of the
  -- composite is the composite of the witnesses — and the identity flow
  -- conserves everything.  Sections carry the convolution ⋆: act by t,
  -- then act by s from where t landed, and compose the two receipts.
  ------------------------------------------------------------------

  प्रवाहः : Type ℓ
  प्रवाहः = Σ[ Φ ∈ (A → A) ] संरक्षणम् f Φ

  _∘प्र_ : प्रवाहः → प्रवाहः → प्रवाहः
  (Φ , c) ∘प्र (Ψ , d) = (λ a → Φ (Ψ a)) , (λ a → c (Ψ a) ∙ d a)

  एकः : प्रवाहः
  एकः = idfun A , (λ _ → refl)

  छेदः : Type ℓ
  छेदः = (a : A) → fiber f (f a)

  _⋆_ : छेदः → छेदः → छेदः
  (s ⋆ t) a = s (t a .fst) .fst , s (t a .fst) .snd ∙ t a .snd

  छेद-एकः : छेदः
  छेद-एकः a = a , refl

  -- THE JEWEL.  `वासः` does not merely identify the two spaces: it
  -- carries the operation and the unit, definitionally.  The dynamics
  -- was in the identification all along, at no cost.
  गण-गमनम् : (σ τ : प्रवाहः)
           → equivFun (वासः f) (σ ∘प्र τ)
           ≡ (equivFun (वासः f) σ) ⋆ (equivFun (वासः f) τ)
  गण-गमनम् σ τ = refl

  एक-गमनम् : equivFun (वासः f) एकः ≡ छेद-एकः
  एक-गमनम् = refl

------------------------------------------------------------------------
-- §२ · THE GAṆA, AT SET LEVEL.  Over set carriers the witness component
-- is proposition-valued, so every law is a Σ≡Prop away from refl and
-- both sides are `Monoid`s of the library's own algebra.
------------------------------------------------------------------------

module गणे {A B : Type ℓ} (setA : isSet A) (setB : isSet B) (f : A → B) where

  प्रवाह-समता : (σ τ : प्रवाहः f) → σ .fst ≡ τ .fst → σ ≡ τ
  प्रवाह-समता _ _ = Σ≡Prop (λ Φ → isPropΠ (λ a → setB _ _))

  छेद-समता : (s t : छेदः f) → ((a : A) → s a .fst ≡ t a .fst) → s ≡ t
  छेद-समता s t h = funExt (λ a → Σ≡Prop (λ _ → setB _ _) (h a))

  प्रवाहगणः : Monoid ℓ
  प्रवाहगणः = makeMonoid {M = प्रवाहः f} (एकः f) (_∘प्र_ f)
    (isSetΣ (isSetΠ (λ _ → setA))
            (λ Φ → isProp→isSet (isPropΠ (λ a → setB _ _))))
    (λ σ τ υ → प्रवाह-समता _ _ refl)
    (λ σ → प्रवाह-समता _ _ refl)
    (λ σ → प्रवाह-समता _ _ refl)

  छेदगणः : Monoid ℓ
  छेदगणः = makeMonoid {M = छेदः f} (छेद-एकः f) (_⋆_ f)
    (isSetΠ (λ _ → isSetΣ setA (λ _ → isProp→isSet (setB _ _))))
    (λ s t u → छेद-समता _ _ (λ _ → refl))
    (λ s → छेद-समता _ _ (λ _ → refl))
    (λ s → छेद-समता _ _ (λ _ → refl))

  ------------------------------------------------------------------
  -- §३ · वासः IS A MONOID EQUIVALENCE, and both preservation fields
  -- are the refl theorems of §१.
  ------------------------------------------------------------------

  गण-समता : MonoidEquiv प्रवाहगणः छेदगणः
  गण-समता = वासः f , monoidequiv refl (λ _ _ → refl)

------------------------------------------------------------------------
-- §४ · THE POLES, AS MONOIDS.
------------------------------------------------------------------------

module _ {A B : Type ℓ} (f : A → B) where

  -- Near pole: zero loss, trivial gaṇa.  No h-level hypothesis — the
  -- flow space is contractible (SvaTantuVasa's ध्रुव-बिन्दुः), so every
  -- conserving flow already IS the unit.
  तुच्छता : isEquiv f → (σ : प्रवाहः f) → σ ≡ एकः f
  तुच्छता e σ = isContr→isProp (ध्रुव-बिन्दुः f e) σ (एकः f)

module अन्धे {A B : Type ℓ} (setA : isSet A) (setB : isSet B)
             (f : A → B) (blind : सर्व-नाशः f) where

  open गणे setA setB f

  -- Far pole: total loss, and the gaa is the FULL transformation
  -- monoid of the domain.  The forward map is the bare projection —
  -- which is a monoid homomorphism by refl, since the map component of
  -- a flow composite is the composite of the map components.
  समापकगणः : Monoid ℓ
  समापकगणः = makeMonoid {M = A → A} (idfun A) (λ g h a → g (h a))
    (isSetΠ (λ _ → setA))
    (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)

  सर्व-गण-समता : MonoidEquiv प्रवाहगणः समापकगणः
  सर्व-गण-समता = isoToEquiv i , monoidequiv refl (λ _ _ → refl)
    where
    i : Iso (प्रवाहः f) (A → A)
    Iso.fun i = fst
    Iso.inv i Φ = Φ , (λ a → blind (Φ a) a)
    Iso.rightInv i _ = refl
    Iso.leftInv i σ = प्रवाह-समता _ _ refl

