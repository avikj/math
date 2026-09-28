{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- Punarāgamana · समता-द्विधा
--
-- समता (samatā) — sameness, the state of being an equivalence.  द्विधा
-- (dvidhā) — in two, split.  The compound is CHOSEN here, descriptively;
-- no source is claimed for it (the same standing as `Carrier`'s own name).
--
------------------------------------------------------------------------
-- WHY THIS MODULE EXISTS.
--
-- `Residue_TheResidualIsTheOtherProjectionOfTheSameGraph` states in its
-- header, as prose:
--
--     `isContr (शेष f b)` fails in two OPPOSITE ways —
--       the fibre is EMPTY   — nothing was lost, नास्ति, धनात्मकम्;
--       the fibre is CROWDED — two points not identified, नष्टि, हिंसा.
--     — and this module calls both of them "not an equivalence".
--
-- §4/§5 of that module then handle the CROWDED arm only.  The two arms are
-- named in prose and never separated in a type.  This module separates
-- them, as a checked equivalence, and shows they are ORTHOGONAL: neither
-- implies the other, each exhibited failing while the other holds.
--
-- THE SPLIT.  For any f : A → B, being an equivalence is, fibrewise,
-- `(b : B) → isContr (शेष f b)`.  And for any type X,
--
--     isContr X  ≃  (isProp X × X).
--
-- Distribute that over the b, and the Π over the product:
--
--     ((b : B) → isContr (शेष f b))
--       ≃  ((b : B) → isProp (शेष f b))   ×   ((b : B) → शेष f b).
--        \___________________________/       \__________________/
--          NO TWO POINTS COLLAPSED             NOTHING MISSING
--          = hasPropFibers f = f is an         = a source point over every
--            EMBEDDING (Cubical.Functions.        target = SPLIT SURJECTION
--            Embedding, definitionally)
--
-- So "every genuinely independent distinction must survive" (Carrier's
-- law) is literally a PRODUCT of two independent obligations, and the two
-- ways a residual refuses contractibility are the two factors failing:
--
--   * CROWDED  (नष्टि)      = the LEFT factor fails — some fibre is not a
--                            prop — f is not an embedding.
--   * EMPTY    (नास्ति)     = the RIGHT factor fails — some fibre is
--                            uninhabited — f is not surjective.
--
-- §4 witnesses the orthogonality with two smallest maps:
--   सर्वैकम् : Bool → Unit   collapses (crowded), yet covers    → only LEFT fails
--   बिन्दुः  : Unit → Bool    embeds (all fibres prop), misses false → only RIGHT fails
-- Each is a checked term, so the independence is proved, not asserted.
------------------------------------------------------------------------

-- (Label note: this library's older Residue module names the empty arm
-- अवक्तव्यम्; fibre/src/Fibre/Residue_… corrects it to नास्ति — अवक्तव्यम्
-- is the fourth bhaṅga, earned only by joint assertion.  The empty arm is
-- named नास्ति here to match.)

module Punaragamana.EqualitySplit_TheContractibleFibreSplitsAsEmbeddingTimesSurjectionAndTheEmptyAndCrowdedRefusalsAreTheTwoFactorsFailingApart where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Functions.Embedding using (isEmbedding ; hasPropFibers ; hasPropFibers→isEmbedding ; isEmbedding→hasPropFibers)
open import Cubical.Relation.Nullary using (¬_)

open import Punaragamana.Residue_TheResidualIsTheOtherProjectionOfTheSameGraph
  using (शेष)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 1.  The per-point lemma.  Contractible = a proposition that is
--     inhabited.  Both sides are propositions, so a bi-implication is an
--     equivalence — nothing to cohere.
------------------------------------------------------------------------

isContr≃isProp×inhab : {X : Type ℓ} → isContr X ≃ (isProp X × X)
isContr≃isProp×inhab {X = X} =
  propBiimpl→Equiv isPropIsContr rhs-prop to fro
  where
    to : isContr X → (isProp X × X)
    to c = isContr→isProp c , c .fst

    fro : (isProp X × X) → isContr X
    fro (p , x) = x , p x

    rhs-prop : isProp (isProp X × X)
    rhs-prop = isPropΣ isPropIsProp (λ p → p)

------------------------------------------------------------------------
-- 2.  Π distributes over a pointwise product.  Pure η; both round trips
--     are refl.
------------------------------------------------------------------------

module _ {A : Type ℓ} {P Q : A → Type ℓ} where

  Π×Iso : Iso ((a : A) → (P a × Q a)) (((a : A) → P a) × ((a : A) → Q a))
  Iso.fun      Π×Iso g       = (λ a → fst (g a)) , (λ a → snd (g a))
  Iso.inv      Π×Iso (u , v) = λ a → (u a , v a)
  Iso.rightInv Π×Iso _       = refl
  Iso.leftInv  Π×Iso _       = refl

------------------------------------------------------------------------
-- 3.  THE SPLIT, for an arbitrary f : A → B.
------------------------------------------------------------------------

module _ {A B : Type ℓ} (f : A → B) where

  -- being an equivalence, read fibrewise: a census of contractibilities.
  -- (`isEquiv f` is the record wrapping exactly this, so the two are
  -- equivalent by record-η; the fibrewise form is the one that splits.)
  -- both sides are propositions (`isPropIsEquiv`; a Π of `isPropIsContr`),
  -- so the bi-implication IS the equivalence — no η on `isEquiv` needed.
  समता-census : isEquiv f ≃ ((b : B) → isContr (शेष f b))
  समता-census = propBiimpl→Equiv (isPropIsEquiv f) (isPropΠ (λ _ → isPropIsContr))
                                  equiv-proof (λ c → record { equiv-proof = c })

  -- the two independent obligations, named.
  भेदः    : Type ℓ                       -- "distinction": no two points collapsed
  भेदः    = (b : B) → isProp (शेष f b)

  छादनम्  : Type ℓ                       -- "covering": nothing missing
  छादनम्  = (b : B) → शेष f b

  -- THE THEOREM.  Contractible-fibred (= equivalence) splits, on the nose,
  -- into embedding × split-surjection.
  समता-द्विधा : ((b : B) → isContr (शेष f b)) ≃ (भेदः × छादनम्)
  समता-द्विधा =
    compEquiv (equivΠCod (λ _ → isContr≃isProp×inhab))
              (isoToEquiv Π×Iso)

  -- and the composite, from isEquiv directly.
  समता≃भेद×छादन : isEquiv f ≃ (भेदः × छादनम्)
  समता≃भेद×छादन = compEquiv समता-census समता-द्विधा

  -- the LEFT factor is exactly "f is an embedding".  `भेदः` unfolds to
  -- `hasPropFibers f` definitionally (शेष f = fiber f), so the bridge is
  -- the library's characterisation, no reshaping.
  भेदः→embedding : भेदः → isEmbedding f
  भेदः→embedding = hasPropFibers→isEmbedding

  embedding→भेदः : isEmbedding f → भेदः
  embedding→भेदः = isEmbedding→hasPropFibers

------------------------------------------------------------------------
-- 4.  ORTHOGONALITY.  The two factors are logically independent: each
--     fails at a smallest map while the other holds.  Both witnesses are
--     checked terms, so "two OPPOSITE ways" is now proved, not narrated.
------------------------------------------------------------------------

-- (a)  CROWDED only.  सर्वैकम् : Bool → Unit collapses two points onto tt
--      (LEFT factor fails) but covers its single target (RIGHT holds).

सर्वैकम् : Bool → Unit
सर्वैकम् _ = tt

सर्वैकम्-छादनम् : छादनम् सर्वैकम्
सर्वैकम्-छादनम् _ = (true , refl)

सर्वैकम्-न-भेदः : ¬ (भेदः सर्वैकम्)
सर्वैकम्-न-भेदः pr = false≢true (cong fst (pr tt (false , refl) (true , refl)))

-- (b)  EMPTY only.  बिन्दुः : Unit → Bool picks `true`; every fibre is a
--      prop (RIGHT... LEFT factor holds — it embeds), but the fibre over
--      false is empty, so it misses (RIGHT factor fails).

बिन्दुः : Unit → Bool
बिन्दुः _ = true

बिन्दुः-भेदः : भेदः बिन्दुः
बिन्दुः-भेदः b = isPropΣ isPropUnit (λ _ → isSetBool true b)

बिन्दुः-न-छादनम् : ¬ (छादनम् बिन्दुः)
बिन्दुः-न-छादनम् cov = false≢true (sym (cov false .snd))
