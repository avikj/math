{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- संरक्षकसमूहः — व्युत्क्रमवन्तः संरक्षकाः प्रवाहाः समूहं रचयन्ति ; सर्व-नाशे
-- सः समूहः सर्वः आत्म-समता-समूहः एव ।
--
-- (the sarakaka-samha: the conserving flows that HAVE inverses form
--  a group — the symmetry group of the observable — and at total loss
--  that group is the full automorphism group Aut(A), by a homomorphism
--  whose function part is refl.)
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS.
-- The invertible elements of the gaa — flows with conserving
-- inverses — are the observable's symmetry GROUP, and at the far pole
-- they are the symmetric group of the domain.  This
-- module constructs it.
--
--   §१  inverse data is a PROPOSITION (inverses in the gaṇa are unique,
--       by the usual two-line monoid argument, executed not cited), so
--       the carrier Σ[ σ ] व्युत्क्रम-सत् σ adds no structure to the flow;
--   §२  the carrier is a `Group` of the library's own algebra, with
--       every law a समता away from refl and both inverse laws being
--       LITERALLY the stored inverse evidence;
--   §३  the group rides वासः onto the sections: a unit's image under
--       the section identification is ⋆-invertible, each direction one
--       `cong` — because `गण-गमनम्` was refl, the group structure was
--       in the identification all along;
--   §४  the poles.  Zero loss: every unit IS the identity (ध्रुव-बिन्दुः
--       consumed).  Total loss: `GroupEquiv` between the symmetry group
--       and Aut(A) = (A ≃ A) under composition — the full automorphism
--       group — with the underlying equivalence's function part and the
--       homomorphism law both refl.  So the Dhruva/Khahara scale, made
--       a scale of MONOIDS by SamraksakaGana, is now a scale of GROUPS:
--       trivial at the near pole, all of Aut at the far pole, and in
--       between exactly the self-symmetries the observable cannot see.
--
-- ────────────────────────────────────────────────────────────────────
-- TERMS.  संरक्षक and गण as in `SamraksakaGana` (गण attested as the
-- gaapha's device, Pini, Adhyy ~500 BCE; the application to
-- flows built in this corpus).  समूह for "group" follows this corpus's
-- own precedent (`BhavanaSamuha.agda` (absent from this repository)); it is MODERN mathematical
-- , and no classical text is claimed for it.  व्युत्क्रम for the
-- inverse follows `BhavanaSamuha`'s use for the conjugate inverse
-- (a,−b).  The compound संरक्षकसमूह is built here.
------------------------------------------------------------------------

module SamraksakaSet_TheInvertibleConservingFlowsAreTheSymmetryGroupAndTotalLossMakesItAllOfAut where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Foundations.HLevels
  using (isSetΣ ; isSetΠ ; isPropΠ ; isProp× ; isOfHLevel≃)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)

open import Khahara_TheZeroDivisorEdgeIsPricedAtItsWholeDomainAndTotalLossIsExactlyTotalSymmetry
  using (सर्व-नाशः)
open import SvaFiberVasa_TheConservingFlowsOfAnyObservableAreTheSectionsOfItsOwnFibers
open import SamraksakaGana_TheConservingFlowsFormAGanaAndTheSectionIdentificationPreservesItByRefl

private variable ℓ : Level

------------------------------------------------------------------------
-- §१ · THE UNITS, over set carriers.  Inverse data is a proposition:
-- the gaa is a monoid, and inverses in a monoid are unique.
------------------------------------------------------------------------

module समूहे {A B : Type ℓ} (setA : isSet A) (setB : isSet B) (f : A → B) where

  open गणे setA setB f using (प्रवाह-समता)

  private
    P : Type ℓ
    P = प्रवाहः f

    _∙प_ : P → P → P
    _∙प_ = _∘प्र_ f

    ई : P
    ई = एकः f

    infixl 7 _∙प_

    प्रवाह-सेट् : isSet P
    प्रवाह-सेट् =
      isSetΣ (isSetΠ (λ _ → setA))
             (λ Φ → isProp→isSet (isPropΠ (λ a → setB _ _)))

    -- the gaa's laws, each refl on the map component
    गुण-योगः : (x y z : P) → x ∙प (y ∙प z) ≡ (x ∙प y) ∙प z
    गुण-योगः x y z = प्रवाह-समता _ _ refl

    वाम-एकः : (x : P) → ई ∙प x ≡ x
    वाम-एकः x = प्रवाह-समता _ _ refl

    दक्षिण-एकः : (x : P) → x ∙प ई ≡ x
    दक्षिण-एकः x = प्रवाह-समता _ _ refl

  -- a two-sided conserving inverse for a flow
  व्युत्क्रम-सत् : P → Type ℓ
  व्युत्क्रम-सत् σ = Σ[ τ ∈ P ] ((σ ∙प τ ≡ ई) × (τ ∙प σ ≡ ई))

  -- inverses are UNIQUE, so this is a proposition: the carrier of the
  -- group is a subtype of the flows, not new structure on them.
  व्युत्क्रम-एकत्वम् : (σ : P) → isProp (व्युत्क्रम-सत् σ)
  व्युत्क्रम-एकत्वम् σ (τ , p , q) (τ' , p' , q') =
    Σ≡Prop (λ _ → isProp× (प्रवाह-सेट् _ _) (प्रवाह-सेट् _ _)) τ≡τ'
    where
    τ≡τ' : τ ≡ τ'
    τ≡τ' = sym (दक्षिण-एकः τ)
         ∙ cong (τ ∙प_) (sym p')
         ∙ गुण-योगः τ σ τ'
         ∙ cong (_∙प τ') q
         ∙ वाम-एकः τ'

  -- THE CARRIER: flows together with their (unique) inverse evidence.
  समूह-वाहः : Type ℓ
  समूह-वाहः = Σ[ σ ∈ P ] व्युत्क्रम-सत् σ

  समूह-समता : {u v : समूह-वाहः} → u .fst ≡ v .fst → u ≡ v
  समूह-समता = Σ≡Prop व्युत्क्रम-एकत्वम्

  ------------------------------------------------------------------
  -- §२ · THE GROUP.  Both inverse laws are the stored evidence.
  ------------------------------------------------------------------

  एकम् : समूह-वाहः
  एकम् = ई , ई , वाम-एकः ई , वाम-एकः ई

  _·स_ : समूह-वाहः → समूह-वाहः → समूह-वाहः
  (σ , τ , p , q) ·स (σ' , τ' , p' , q') =
    (σ ∙प σ') , (τ' ∙प τ) , कण्ठ , उदर
    where
    कण्ठ : (σ ∙प σ') ∙प (τ' ∙प τ) ≡ ई
    कण्ठ = प्रवाह-समता _ _ (funExt (λ a →
             cong (σ .fst) (funExt⁻ (cong fst p') (τ .fst a))
           ∙ funExt⁻ (cong fst p) a))

    उदर : (τ' ∙प τ) ∙प (σ ∙प σ') ≡ ई
    उदर = प्रवाह-समता _ _ (funExt (λ a →
             cong (τ' .fst) (funExt⁻ (cong fst q) (σ' .fst a))
           ∙ funExt⁻ (cong fst q') a))

  व्युत् : समूह-वाहः → समूह-वाहः
  व्युत् (σ , τ , p , q) = τ , σ , q , p

  संरक्षक-समूहः : Group ℓ
  संरक्षक-समूहः = makeGroup एकम् _·स_ व्युत्
    (isSetΣ प्रवाह-सेट् (λ σ → isProp→isSet (व्युत्क्रम-एकत्वम् σ)))
    (λ x y z → समूह-समता (गुण-योगः (x .fst) (y .fst) (z .fst)))
    (λ x → समूह-समता (दक्षिण-एकः (x .fst)))
    (λ x → समूह-समता (वाम-एकः (x .fst)))
    (λ x → समूह-समता (x .snd .snd .fst))
    (λ x → समूह-समता (x .snd .snd .snd))

  ------------------------------------------------------------------
  -- §३ · THE GROUP RIDES वासः.  A unit's image among the sections is
  -- ⋆-invertible, each direction one `cong` — गण-गमनम् was refl, so
  -- the inverse evidence transports with no transport.
  ------------------------------------------------------------------

  छेद-व्युत्क्रमः : (u : समूह-वाहः)
    → (_⋆_ f (equivFun (वासः f) (u .fst)) (equivFun (वासः f) (u .snd .fst))
        ≡ छेद-एकः f)
    × (_⋆_ f (equivFun (वासः f) (u .snd .fst)) (equivFun (वासः f) (u .fst))
        ≡ छेद-एकः f)
  छेद-व्युत्क्रमः u =
      cong (equivFun (वासः f)) (u .snd .snd .fst)
    , cong (equivFun (वासः f)) (u .snd .snd .snd)

  ------------------------------------------------------------------
  -- §४a · NEAR POLE.  Zero loss: the symmetry group is trivial.
  ------------------------------------------------------------------

  तुच्छ-समूहः : isEquiv f → (u : समूह-वाहः) → u ≡ एकम्
  तुच्छ-समूहः e u =
    समूह-समता (isContr→isProp (ध्रुव-बिन्दुः f e) (u .fst) ई)

------------------------------------------------------------------------
-- §४b · FAR POLE.  Total loss: the symmetry group is ALL of Aut(A).
------------------------------------------------------------------------

module अन्ध-समूहे {A B : Type ℓ} (setA : isSet A) (setB : isSet B)
                  (f : A → B) (blind : सर्व-नाशः f) where

  open समूहे setA setB f
  open गणे setA setB f using (प्रवाह-समता)

  -- Aut(A): the equivalences A ≃ A, composed in application order
  -- (e µ f' applies f' first), so that the comparison below is refl.
  आत्म-समूहः : Group ℓ
  आत्म-समूहः = makeGroup (idEquiv A) (λ e f' → compEquiv f' e) invEquiv
    (isOfHLevel≃ 2 setA setA)
    (λ e f' g → sym (compEquiv-assoc g f' e))
    (λ e → compEquivIdEquiv e)
    (λ e → compEquivEquivId e)
    (λ e → invEquiv-is-linv e)
    (λ e → invEquiv-is-rinv e)

  -- a unit IS an equivalence: the two flow-inverse laws are exactly the
  -- two homotopies of an isomorphism.
  प्रति : समूह-वाहः → A ≃ A
  प्रति (σ , τ , p , q) =
    isoToEquiv (iso (σ .fst) (τ .fst)
                    (funExt⁻ (cong fst p)) (funExt⁻ (cong fst q)))

  -- and at total loss every equivalence is a unit: blindness supplies
  -- the conserving witness of both the map and its inverse.
  private
    वाहित : (g : A → A) → प्रवाहः f
    वाहित g = g , (λ a → blind (g a) a)

  आगमः : (A ≃ A) → समूह-वाहः
  आगमः e = वाहित (equivFun e)
         , वाहित (invEq e)
         , प्रवाह-समता _ _ (funExt (secEq e))
         , प्रवाह-समता _ _ (funExt (retEq e))

  प्रति-आगमः : (e : A ≃ A) → प्रति (आगमः e) ≡ e
  प्रति-आगमः e = equivEq refl

  आगम-प्रतिः : (u : समूह-वाहः) → आगमः (प्रति u) ≡ u
  आगम-प्रतिः u = समूह-समता (प्रवाह-समता _ _ refl)

  -- THE GROUP EQUIVALENCE.  The function part is refl and the
  -- homomorphism law is refl: at total loss the observable's symmetry
  -- group is the full automorphism group, on the nose.
  सर्व-समूह-समता : GroupEquiv संरक्षक-समूहः आत्म-समूहः
  सर्व-समूह-समता =
      isoToEquiv (iso प्रति आगमः प्रति-आगमः आगम-प्रतिः)
    , makeIsGroupHom (λ u v → equivEq refl)

