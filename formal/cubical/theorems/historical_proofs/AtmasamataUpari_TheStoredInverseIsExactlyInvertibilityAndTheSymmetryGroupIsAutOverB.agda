{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- आत्मसमता उपरि — व्युत्क्रम-सत्त्वं समता-सत्त्वमेव, संरक्षक-समूहश्च
-- उपरि-आत्मसमता-समूहः ।
--
-- (the stored two-sided conserving inverse of a flow is EXACTLY the
--  invertibility of its map component — no extra datum — and therefore
--  the observable's symmetry group is Aut_B(A), the automorphisms of A
--  that commute with f.)
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS.  A SIMPLIFICATION of an existing theorem, not a
-- correction of one.  Everything it leans on is checked and stands:
--
--   · `SamraksakaSamuha_….agda` §१–§४ builds the symmetry group over the
--     carrier `Σ[ σ ∈ प्रवाहः f ] व्युत्क्रम-सत् σ` — a flow bundled with
--     STORED two-sided conserving-inverse evidence — and proves that
--     evidence is a proposition (व्युत्क्रम-एकत्वम्), so the carrier is a
--     subtype.  That is all correct.
--   · `SamanaKaksya_….agda` §५ proves, separately, that when the map is
--     an equivalence its inverse conserves automatically
--     (व्युत्क्रम-संरक्षणम् — one `sym`, one `cong`).
--
-- The two were never joined.  Joining them (§१) collapses the stored
-- datum: व्युत्क्रम-सत् σ ≃ isEquiv (σ .fst).  Left to right is the
-- iso→equiv the group's own `प्रति` already performs; right to left is
-- SamanaKaksya's backward conservation, which supplies the one thing the
-- bare `isEquiv` does not carry — that the INVERSE map is itself a flow.
-- Both sides are propositions, so it is an equivalence and not merely a
-- biimplication.
--
-- Consequently the group's carrier is `Σ[ σ ∈ प्रवाहः f ] isEquiv (σ .fst)`
-- — the conserving flows that HAPPEN to be invertible, with no attached
-- data — and, reassociated (§२), it is
--
--     आत्मसमता-उपरि  =  Σ[ ε ∈ (A ≃ A) ] संरक्षणम् f (equivFun ε),
--
-- Aut_B(A): the automorphisms of A lying OVER B, i.e. commuting with f.
-- §३ makes that a `Group` in its own right and exhibits a `GroupEquiv`
-- from `संरक्षक-समूहः` onto it whose hom law is `उपरि-समता refl`.  So the
-- Dhruva/Khahara scale reads, intrinsically:
--
--     near pole (isEquiv f)   Aut_B(A) is trivial                (§४a)
--     far pole  (सर्व-नाशः f)  Aut_B(A) ≃ Aut(A), the witness free (§४c)
--     in between              Aut_B(A) exactly, nothing else.
--
-- §४b prices `Apratiloma`'s witness intrinsically: चूर्ण is outside the
-- unit subgroup for exactly one reason — it is not an equivalence
-- (चूर्ण 0 ≡ चूर्ण 1 while 0 ≢ 1) — and by §१ that reason is the ONLY one
-- available.  `Apratiloma`'s fence does not move: `प्रवाहः f` is still a
-- monoid and not a group, `crush` is still in it and still has no
-- inverse.  What §१ adds is that non-invertibility of the underlying map
-- is not merely sufficient for falling outside the group, it is
-- necessary and sufficient, so "which flows are the units" has an answer
-- with no reference to the monoid at all.
--
-- ────────────────────────────────────────────────────────────────────
-- TERMS.  आत्म-समता — "self-sameness"; the compound आत्म-समता-समूहः is
-- already this corpus's own name for Aut(A) (`SamraksakaSamuha` §४b),
-- and it is MODERN mathematical : no classical text is claimed
-- for it, there and not here either.  उपरि — "above, over", ordinary
-- , used here for the slice: "over B".  संरक्षक, प्रवाह, गण, समूह,
-- व्युत्क्रम as in `SamraksakaGana`/`SamraksakaSamuha`, with their limits
-- unchanged (गण attested as the gaṇapāṭha's device, Pāṇini,
-- अष्टाध्यायी, ~500 BCE; the application to flows is this corpus's).
-- The compound आत्मसमता-उपरि is BUILT HERE; no source states
-- anything below.
------------------------------------------------------------------------

module AtmasamataUpari_TheStoredInverseIsExactlyInvertibilityAndTheSymmetryGroupIsAutOverB where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Foundations.HLevels
  using (isSetΣ ; isPropΠ ; isOfHLevel≃)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Properties using (isSetℕ ; znots)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)

open import Dhruva_TheSymmetryLivesInTheFibreAndWithoutALossThereIsNoSymmetry
  using (संरक्षणम्)
open import Khahara_TheZeroDivisorEdgeIsPricedAtItsWholeDomainAndTotalLossIsExactlyTotalSymmetry
  using (सर्व-नाशः)
open import SamanaKaksya_TheOrbitRelationIsAlreadyAnEquivalenceWithoutAnInverseAndTheChargeDescendsToTheQuotient
  using (व्युत्क्रम-संरक्षणम्)
open import SvaFiberVasa_TheConservingFlowsOfAnyObservableAreTheSectionsOfItsOwnFibers
  using (ध्रुव-बिन्दुः)
open import SamraksakaGana_TheConservingFlowsFormAGanaAndTheSectionIdentificationPreservesItByRefl
  using (प्रवाहः ; _∘प्र_ ; एकः ; module गणे)
open import SamraksakaSet_TheInvertibleConservingFlowsAreTheSymmetryGroupAndTotalLossMakesItAllOfAut
  using (module समूहे)
open import Apratiloma_TheConservingFlowsAreAMonoidNotAGroupSoNoethersFirstTheoremDoesNotTransfer
  using (अन्ध ; चूर्ण)

private variable ℓ : Level

module उपरि {A B : Type ℓ} (setA : isSet A) (setB : isSet B) (f : A → B) where

  open गणे setA setB f using (प्रवाह-समता)
  open समूहे setA setB f
    using (व्युत्क्रम-सत् ; व्युत्क्रम-एकत्वम् ; समूह-वाहः ; समूह-समता ; संरक्षक-समूहः)

  ------------------------------------------------------------------
  -- §१ · THE STORED INVERSE IS EXACTLY INVERTIBILITY.
  --
  -- Forward: the two flow-inverse laws, read on the map component, are
  -- the two homotopies of an isomorphism.  Backward: the map's inverse
  -- is a flow because conservation propagates backwards (SamanaKaksya
  -- §५), and the two laws are then secEq / retEq under प्रवाह-समता.
  ------------------------------------------------------------------

  सत्-तः-समता : (σ : प्रवाहः f) → व्युत्क्रम-सत् σ → isEquiv (σ .fst)
  सत्-तः-समता σ (τ , p , q) =
    isoToIsEquiv (iso (σ .fst) (τ .fst)
                      (funExt⁻ (cong fst p)) (funExt⁻ (cong fst q)))

  समता-तः-सत् : (σ : प्रवाहः f) → isEquiv (σ .fst) → व्युत्क्रम-सत् σ
  समता-तः-सत् σ e =
      (invEq ε , व्युत्क्रम-संरक्षणम् f (σ .fst) e (σ .snd))
    , प्रवाह-समता _ _ (funExt (secEq ε))
    , प्रवाह-समता _ _ (funExt (retEq ε))
    where
    ε : A ≃ A
    ε = σ .fst , e

  -- both sides are propositions, so this is an equivalence of types and
  -- not merely a two-way implication: NO DATUM IS LOST either way.
  व्युत्क्रम-समता : (σ : प्रवाहः f) → व्युत्क्रम-सत् σ ≃ isEquiv (σ .fst)
  व्युत्क्रम-समता σ =
    isoToEquiv (iso (सत्-तः-समता σ) (समता-तः-सत् σ)
                    (λ e → isPropIsEquiv (σ .fst) _ e)
                    (λ v → व्युत्क्रम-एकत्वम् σ _ v))

  ------------------------------------------------------------------
  -- §२ · THE CARRIER, WITH THE STORED DATUM REMOVED, AND THEN
  -- REASSOCIATED INTO Aut_B(A).
  ------------------------------------------------------------------

  वाह-समता : समूह-वाहः ≃ (Σ[ σ ∈ प्रवाहः f ] isEquiv (σ .fst))
  वाह-समता = Σ-cong-equiv-snd व्युत्क्रम-समता

  -- Aut_B(A): an automorphism of A that f cannot tell acted.
  आत्मसमता-उपरि : Type ℓ
  आत्मसमता-उपरि = Σ[ ε ∈ (A ≃ A) ] संरक्षणम् f (equivFun ε)

  -- equality of such is determined by the underlying FUNCTION alone:
  -- one Σ≡Prop for the conservation witness (setB), one equivEq for the
  -- isEquiv field.
  उपरि-समता : {u v : आत्मसमता-उपरि} → equivFun (u .fst) ≡ equivFun (v .fst) → u ≡ v
  उपरि-समता p = Σ≡Prop (λ _ → isPropΠ (λ a → setB _ _)) (equivEq p)

  उपरि-सेट् : isSet आत्मसमता-उपरि
  उपरि-सेट् = isSetΣ (isOfHLevel≃ 2 setA setA)
                     (λ _ → isProp→isSet (isPropΠ (λ a → setB _ _)))

  ------------------------------------------------------------------
  -- §३ · Aut_B(A) IS THE SYMMETRY GROUP, BY A GroupEquiv WHOSE HOM LAW
  -- IS `उपरि-समता refl`.
  --
  -- Composition is in application order (u ·उ v applies v first), to
  -- match `_·स_`'s order, so that the comparison never has to commute
  -- anything.
  ------------------------------------------------------------------

  एकम्-उ : आत्मसमता-उपरि
  एकम्-उ = idEquiv A , (λ _ → refl)

  _·उ_ : आत्मसमता-उपरि → आत्मसमता-उपरि → आत्मसमता-उपरि
  (ε , c) ·उ (δ , d) = compEquiv δ ε , (λ a → c (equivFun δ a) ∙ d a)

  व्युत्-उ : आत्मसमता-उपरि → आत्मसमता-उपरि
  व्युत्-उ (ε , c) = invEquiv ε , व्युत्क्रम-संरक्षणम् f (equivFun ε) (ε .snd) c

  उपरि-समूहः : Group ℓ
  उपरि-समूहः = makeGroup एकम्-उ _·उ_ व्युत्-उ उपरि-सेट्
    (λ x y z → उपरि-समता refl)
    (λ x → उपरि-समता refl)
    (λ x → उपरि-समता refl)
    (λ x → उपरि-समता (funExt (secEq (x .fst))))
    (λ x → उपरि-समता (funExt (retEq (x .fst))))

  उत्तारः : समूह-वाहः → आत्मसमता-उपरि
  उत्तारः u = (u .fst .fst , सत्-तः-समता (u .fst) (u .snd)) , u .fst .snd

  अवतारः : आत्मसमता-उपरि → समूह-वाहः
  अवतारः (ε , c) = (equivFun ε , c) , समता-तः-सत् (equivFun ε , c) (ε .snd)

  उत्-अव : (u : आत्मसमता-उपरि) → उत्तारः (अवतारः u) ≡ u
  उत्-अव u = उपरि-समता refl

  अव-उत् : (u : समूह-वाहः) → अवतारः (उत्तारः u) ≡ u
  अव-उत् u = समूह-समता (प्रवाह-समता _ _ refl)

  -- THE IDENTIFICATION.  The observable's symmetry group IS the group of
  -- automorphisms of its domain over its codomain.
  उपरि-समूह-समता : GroupEquiv संरक्षक-समूहः उपरि-समूहः
  उपरि-समूह-समता =
      isoToEquiv (iso उत्तारः अवतारः उत्-अव अव-उत्)
    , makeIsGroupHom (λ u v → उपरि-समता refl)

  ------------------------------------------------------------------
  -- §४a · NEAR POLE, intrinsically.  Zero loss ⟹ Aut_B(A) is trivial.
  -- The flow space is already contractible (ध्रुव-बिन्दुः), so no
  -- inverse-side argument is needed at all.
  ------------------------------------------------------------------

  तुच्छम्-उपरि : isEquiv f → (u : आत्मसमता-उपरि) → u ≡ एकम्-उ
  तुच्छम्-उपरि e u =
    उपरि-समता (cong fst (isContr→isProp (ध्रुव-बिन्दुः f e)
                                          (equivFun (u .fst) , u .snd) (एकः f)))

------------------------------------------------------------------------
-- §४b · THE UNIT SUBGROUP, PRICED AT `Apratiloma`'s OWN WITNESS.
--
-- चूर्ण conserves अन्ध and is not a unit.  §१ says the reason can only be
-- one thing, and here it is that thing: चूर्ण is not an equivalence,
-- because a retraction of it would identify 0 with 1.
------------------------------------------------------------------------

चूर्ण-न-समता : ¬ (isEquiv चूर्ण)
चूर्ण-न-समता e = znots (sym (retEq ε zero) ∙ retEq ε (suc zero))
  where
  ε : ℕ ≃ ℕ
  ε = चूर्ण , e

चूर्ण-प्रवाहः : प्रवाहः अन्ध
चूर्ण-प्रवाहः = चूर्ण , (λ _ → refl)

-- and therefore no stored inverse exists — by §१, not by inspection of
-- the monoid.  `Apratiloma`'s fence is unmoved and now has a reason.
चूर्ण-न-व्युत्क्रमः : ¬ (समूहे.व्युत्क्रम-सत् isSetℕ isSetUnit अन्ध चूर्ण-प्रवाहः)
चूर्ण-न-व्युत्क्रमः v = चूर्ण-न-समता (उपरि.सत्-तः-समता isSetℕ isSetUnit अन्ध चूर्ण-प्रवाहः v)

------------------------------------------------------------------------
-- §४c · FAR POLE, intrinsically.  At total loss the conservation
-- witness is free, so Aut_B(A) ≃ Aut(A) by the bare projection —
-- which is `SamraksakaSamuha` §४b's GroupEquiv seen without the stored
-- inverse in the way.
------------------------------------------------------------------------

module अन्धे-उपरि {A B : Type ℓ} (setA : isSet A) (setB : isSet B)
                  (f : A → B) (blind : सर्व-नाशः f) where

  open उपरि setA setB f using (आत्मसमता-उपरि ; उपरि-समता)

  सर्व-उपरि : आत्मसमता-उपरि ≃ (A ≃ A)
  सर्व-उपरि = isoToEquiv
    (iso fst (λ ε → ε , (λ a → blind (equivFun ε a) a))
         (λ _ → refl) (λ u → उपरि-समता refl))

