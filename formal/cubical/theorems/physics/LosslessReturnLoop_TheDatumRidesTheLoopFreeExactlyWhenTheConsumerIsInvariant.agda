{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- पुनरागमन-वर्तुलम् — वहनं वर्तुले मुक्तं तदा एव यदा भोक्ता अविकारी ।
--
-- (the carried datum rides the loop free exactly when the consumer is
--  invariant.)
--
-- WHAT THIS IS.  `HolonomyIsInvisibleExactlyToAnInvariant-
-- Semantics` proves `invariantSemanticsIsUnmoved` and
-- `nonTrivialHolonomyMovesTheRawInterface`, and reads them as one theorem
-- at two consumers.  It is right, and the object it is about already has a
-- name in this corpus: पुनरागमन, the coming-back.  Holonomy is the FAILURE
-- of the coming-back to be trivial, and this module says so as terms.
--
--   पुनरागमन   the return exists: the datum is determined, rides free,
--             nothing is lost.  `fibre/` states it for a map.
--   holonomy   go around and return changed.  Stated for a loop.
--
-- Same object, opposite sign, two lanes of this repository.
--
-- WHY IT IS SHORT, AND WHY THAT IS THE POINT.  §६ of अहिंसा-सूत्र-विस्तारः:
-- संक्रमणे संरचना वहति, संक्रमणे न किञ्चिन् नश्यति.  A transport that costs
-- nothing is a geodesic; if joining two things takes work, the joint is
-- wrong.  Every declaration below is `refl`, one library lemma, or one
-- application of a theorem that already existed.  Nothing is constructed.
--
-- THE STATEMENT.  For a consumer `sem : Z → B`, `Carrier sem` carries
-- `sem z` beside `z` at zero degrees of freedom (the fibre `singl (sem z)`
-- is contractible).  A holonomy `h : Z ≃ Z` acts on the base, hence on the
-- Carrier.  §3: the carried datum after one turn is `sem (h z)`, by `refl`.
-- §4: therefore the datum is unmoved for every point exactly when `sem` is
-- invariant — the biconditional, both directions `refl`-cheap.  §5: the
-- identity consumer is the case where the datum IS the interface, so it is
-- unmoved only if `h` is trivial, and `Bool`/`not` exhibits one that is not.
--
-- WHY A BICONDITIONAL IS AVAILABLE HERE AND NOT ON THE OTHER ROAD.  An
-- obstruction (§६'s दोषलेख, road two) is a factorisation failing, and a
-- factorisation does not invert — `DosaLekha_…` records that the univalent
-- holonomy statements are exactly what would NOT instantiate it without an
-- added `isSet`.  That refusal is the boundary between the two roads, and
-- it falls on this side: holonomy is joined to its consumer by a PATH,
-- and a path inverts.  **Holonomy is road one, not road two.**
------------------------------------------------------------------------

module LosslessReturnLoop_TheDatumRidesTheLoopFreeExactlyWhenTheConsumerIsInvariant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun)
open import Cubical.Foundations.Univalence using (ua ; uaβ)
open import Cubical.Data.Bool using (Bool ; true ; false ; notEquiv)
open import Cubical.Relation.Nullary using (¬_)

import HolonomyIsInvisibleExactlyToAnInvariantSemantics as H

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- १ · वाहकः — the law, five lines, as in fibre/.
------------------------------------------------------------------------

record Carrier {A B : Type ℓ} (f : A → B) : Type ℓ where
  constructor carry
  field
    base    : A
    carried : B
    witness : f base ≡ carried

open Carrier public

module _ {A B : Type ℓ} (f : A → B) where

  अवतरण : A → Carrier f
  अवतरण a = carry a (f a) refl

  उत्थान : Carrier f → A
  उत्थान = base

  -- contractible fibre ⇒ equivalence ⇒ path.  The whole proof.
  अवतरण-उत्थान : (c : Carrier f) → अवतरण (उत्थान c) ≡ c
  अवतरण-उत्थान (carry a b w) i = carry a (q i .fst) (q i .snd)
    where
      q : Path (singl (f a)) (f a , refl) (b , w)
      q = isContrSingl (f a) .snd (b , w)

  Carrier≃ : A ≃ Carrier f
  Carrier≃ = isoToEquiv (iso अवतरण उत्थान अवतरण-उत्थान (λ _ → refl))

  Carrier≡ : A ≡ Carrier f
  Carrier≡ = ua Carrier≃

------------------------------------------------------------------------
-- २ · वर्तुलम् — a holonomy acts on the base, hence on the carrier.
--
-- `H.Holonomy Z = Z ≃ Z`, that module's own definition.  Φ is the loop
-- read as a map; the lift is the conjugation अवतरण ∘ Φ ∘ उत्थान, which is
-- the shape `fibre/`'s Φ-carrier already has.
------------------------------------------------------------------------

module _ {B Z : Type₀} (sem : Z → B) (h : H.Holonomy Z) where

  Φ : Z → Z
  Φ = equivFun h

  Φ-वाहके : Carrier sem → Carrier sem
  Φ-वाहके c = अवतरण sem (Φ (उत्थान sem c))

  -- the square closes definitionally, for an opaque variable
  वर्गः : (z : Z) → Φ-वाहके (अवतरण sem z) ≡ अवतरण sem (Φ z)
  वर्गः _ = refl

  ----------------------------------------------------------------------
  -- ३ · यत् वहति — what the datum becomes after one turn.  By refl.
  ----------------------------------------------------------------------

  वहनम्-पदे : (z : Z) → carried (Φ-वाहके (अवतरण sem z)) ≡ sem (Φ z)
  वहनम्-पदे _ = refl

  ----------------------------------------------------------------------
  -- ४ · तदा एव — THE BICONDITIONAL.
  --
  -- The carried datum is unmoved at every point exactly when the consumer
  -- is invariant under the holonomy.  Both directions are the identity on
  -- the underlying family: §3 already made the two sides the same term, so
  -- there is nothing between them.
  --
  -- This is `H.invariantSemanticsIsUnmoved` read as a statement about what
  -- rides free, and it is a BICONDITIONAL because a path inverts.
  ----------------------------------------------------------------------

  अविकारी : Type _
  अविकारी = (z : Z) → sem (Φ z) ≡ sem z

  मुक्तम् : Type _
  मुक्तम् = (z : Z) → carried (Φ-वाहके (अवतरण sem z)) ≡ carried (अवतरण sem z)

  अविकारी→मुक्तम् : अविकारी → मुक्तम्
  अविकारी→मुक्तम् inv = inv

  मुक्तम्→अविकारी : मुक्तम् → अविकारी
  मुक्तम्→अविकारी free = free

------------------------------------------------------------------------
-- ५ · संक्रमणे — and the same along the univalent transport.
--
-- `H.invariantSemanticsIsUnmoved` is stated for `transport (ua h)`, where
-- nothing reduces on a neutral variable — the datum has to be brought back
-- by `uaβ`.  Quoted, not restated: the point is that §४'s biconditional and
-- that theorem are one fact at two presentations of the same loop.
------------------------------------------------------------------------

संक्रमणे-अपि : {B Z : Type₀} (sem : Z → B) (h : H.Holonomy Z)
             → ((z : Z) → sem (equivFun h z) ≡ sem z)
             → (z : Z) → sem (transport (ua h) z) ≡ sem z
संक्रमणे-अपि sem h = H.invariantSemanticsIsUnmoved h sem

------------------------------------------------------------------------
-- ६ · स्वयंभोक्ता — the identity consumer, and a loop that moves it.
--
-- When the carried datum IS the interface, invariance of the consumer is
-- invariance of the holonomy, so the datum rides free only for a trivial
-- loop.  `H.theCacheIsMoved` exhibits one that is not: `not` on `Bool`.
-- That is why caches, provenance and optimizer state are the consumers
-- that see — they are keyed by the raw interface.
------------------------------------------------------------------------

स्वयम् : {Z : Type₀} → Z → Z
स्वयम् z = z

वाहकः-चलितः : ¬ (carried (Φ-वाहके स्वयम् notEquiv (अवतरण स्वयम् true)) ≡ true)
वाहकः-चलितः = H.notIsGenuineHolonomy

कोशः-चलितः : ¬ (transport (ua notEquiv) true ≡ true)
कोशः-चलितः = H.theCacheIsMoved
