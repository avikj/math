{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- कक्ष्या — ध्रुवं कक्ष्यायां स्थिरम् ।
--
-- (the conserved quantity is constant along the orbit.)
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS.  In `Dhruva_TheSymmetryLivesInTheFibreAndWithoutALossThere
-- IsNoSymmetry.agda` (absent from this repository) § the conserved quantity is `f` itself: `���`
-- says exactly that `f` is Φ-invariant, so `f` descends to the orbits 
-- "the charge is a function on the quotient, not on the cover".
--
-- This module states that.  Dhruva's §ध gives one step — `f (Φ a) ≡ f a` — and that
-- alone leaves open whether the charge could drift along a long orbit.  It
-- cannot: §२ below is the induction, and its content is that the charge
-- cannot distinguish ANY two points of an orbit, at ANY distance.  That is
-- what "a function on the quotient rather than on the cover" says without
-- introducing a quotient type: the cover's points are separated by Φ, and
-- the charge is blind to every one of those separations.
--
-- WHY IT IS WORTH A TERM AND NOT A REMARK.  The one-step law is a
-- hypothesis about a generator; the orbit law is a statement about the
-- ORBIT, which is the object `Dhruva` §१ actually identifies with the
-- gauge orbit and the fibre.  Without §२, "the gauge orbit is the fibre"
-- is asserted of a set nothing has been proved constant on.
--
-- ────────────────────────────────────────────────────────────────────
--
-- TERM.  कक्ष्या — in the siddhāntic astronomical tradition, the orbit or
-- orbital circle of a planet (standard from Āryabhaṭa, आर्यभटीयम्, 499,
-- and through the Sryasiddhnta).  Its use here for
-- the forward orbit of an endomorphism is this corpus's.
------------------------------------------------------------------------

module Kaksya_TheChargeIsConstantAlongTheWholeOrbitAndNotOnlyAcrossOneStep where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Dhruva_TheSymmetryLivesInTheFibreAndWithoutALossThereIsNoSymmetry
  using (संरक्षणम्)

private variable ℓ : Level

module _ {A B : Type ℓ} (f : A → B) (Φ : A → A) where

------------------------------------------------------------------------
-- १ · कक्ष्या — the forward orbit, as an iteration of the flow.
--
-- `Φ` is a bare endomorphism, so this is the forward orbit and nothing
-- more: no inverse is available and none is used.
------------------------------------------------------------------------

  कक्ष्या : ℕ → A → A
  कक्ष्या zero    a = a
  कक्ष्या (suc n) a = Φ (कक्ष्या n a)

------------------------------------------------------------------------
-- २ · ध्रुवं कक्ष्यायां स्थिरम् — THE CHARGE IS CONSTANT ALONG THE ORBIT.
--
-- Dhruva §१ gives one step.  This is every step, by induction, and the
-- proof is the one-step law composed with the tail.
--
-- Read at the physics: the observable cannot distinguish any two points
-- of one orbit, however far apart along the flow.  That is the exact
-- content of "the charge is a function on the quotient, not on the
-- cover" — stated on the cover, where it is provable without building a
-- quotient.
------------------------------------------------------------------------

  ध्रुवं-कक्ष्यायाम् : संरक्षणम् f Φ → (n : ℕ) (a : A) → f (कक्ष्या n a) ≡ f a
  ध्रुवं-कक्ष्यायाम् cons zero    a = refl
  ध्रुवं-कक्ष्यायाम् cons (suc n) a = cons (कक्ष्या n a) ∙ ध्रुवं-कक्ष्यायाम् cons n a

------------------------------------------------------------------------
-- ३ · अभेदः — and therefore no two points of an orbit are separated by
--     the charge.  This is §२ read as the blindness it is: for any two
--     stations `m`, `n` on one orbit, the observable agrees.
------------------------------------------------------------------------

  कक्ष्या-अभेदः : संरक्षणम् f Φ → (m n : ℕ) (a : A)
                → f (कक्ष्या m a) ≡ f (कक्ष्या n a)
  कक्ष्या-अभेदः cons m n a =
    ध्रुवं-कक्ष्यायाम् cons m a ∙ sym (ध्रुवं-कक्ष्यायाम् cons n a)

------------------------------------------------------------------------
--    — scope.
--
-- `Φ` is a bare endomorphism.  §नℓ§३ are stated on the cover and need
-- no orbit relation, no quotient, and no inverse.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ५ · नष्टाभावे कक्ष्या एकपदा — WITHOUT LOSS THE ORBIT IS A SINGLE POINT.
--
-- `Dhruva` §२ proves that losslessness plus conservation force `Φ a ≡ a`
-- — one step.  With §१'s iteration that is every step: the whole forward
-- orbit collapses onto its own basepoint.
--
-- This is README movement 30's sentence made literal.  It says there that
-- a lossless world is FROZEN, and what §२ of Dhruva supports on its own is
-- only that the generator is the identity.  The frozen claim is about the
-- ORBIT — that nothing goes anywhere — and that is this.
--
-- Note what it does NOT need: `Φ` is still a bare endomorphism.  No group,
-- no inverse, no continuity.  Losslessness alone kills the whole forward
-- trajectory.
------------------------------------------------------------------------

open import Cubical.Foundations.Equiv using (isEquiv)

module _ {A B : Type ℓ} (f : A → B) (Φ : A → A) where

  open import Dhruva_TheSymmetryLivesInTheFibreAndWithoutALossThereIsNoSymmetry
    using (नष्ट-अभावे-गति-अभावः)

  नष्टाभावे-कक्ष्या-एकपदा : isEquiv f → संरक्षणम् f Φ
                          → (n : ℕ) (a : A) → कक्ष्या f Φ n a ≡ a
  नष्टाभावे-कक्ष्या-एकपदा e cons zero    a = refl
  नष्टाभावे-कक्ष्या-एकपदा e cons (suc n) a =
    cong Φ (नष्टाभावे-कक्ष्या-एकपदा e cons n a) ∙ नष्ट-अभावे-गति-अभावः f Φ e cons a

------------------------------------------------------------------------
-- ६ · कक्ष्या तन्तौ वसति — THE WHOLE ORBIT LIES IN ONE FIBRE.
--
-- `Dhruva` §१ proves that `Φ` carries a fibre into itself — one step —
-- and its prose then reads that as "the gauge orbit IS the fibre".  The
-- orbit is a set §१ never quantifies over.  This is that set: every
-- station of the forward orbit of `a` is a point of the fibre over
-- `f a`, with §२ supplying its membership witness.
--
-- So the sentence "the gauge orbit lies in the fibre" has a term
-- whose subject is the orbit.  The converse -- that the fibre is
-- exhausted by one orbit -- is transitivity of the flow on the fibre,
-- which §ध takes as a hypothesis.
------------------------------------------------------------------------

open import Cubical.Foundations.Equiv using (fiber)

module _ {A B : Type ℓ} (f : A → B) (Φ : A → A) where

  कक्ष्या-तन्तौ : संरक्षणम् f Φ → (n : ℕ) (a : A) → fiber f (f a)
  कक्ष्या-तन्तौ cons n a = कक्ष्या f Φ n a , ध्रुवं-कक्ष्यायाम् f Φ cons n a

------------------------------------------------------------------------
-- ७ · सङ्क्रमणे भारो नास्ति — WHERE THE FLOW IS TRANSITIVE, NO INVARIANT
--     CARRIES A CHARGE.
--
-- § above: the orbit lies IN the fibre, and whether it EXHAUSTS the
-- fibre is transitivity.
--
-- Here transitivity is stated, as a hypothesis, and its consequence
-- proved: if the flow reaches every point of a fibre from every other,
-- then EVERY Φ-invariant observable is constant on that fibre.  Not just
-- `f` — every one.  So there is no further conserved quantity to carry
-- there, and the whole fibre is one state as far as any invariant can
-- tell.
--
-- That is Noether's SECOND theorem's conclusion — a local symmetry gives
-- a constraint rather than a charge — at the level where no Lagrangian is
-- needed.  As in `Dhruva`: no variation, no continuity, no action.
------------------------------------------------------------------------

module _ {A B : Type ℓ} (f : A → B) (Φ : A → A) where

  -- the flow reaches every point of the fibre from every other
  सङ्क्रमणम् : B → Type ℓ
  सङ्क्रमणम् b = (x y : fiber f b) → Σ[ n ∈ ℕ ] कक्ष्या f Φ n (fst x) ≡ fst y

  -- and then NO invariant separates two points of that fibre
  सङ्क्रमणे-भारो-नास्ति :
      {C : Type ℓ} (g : A → C) → संरक्षणम् g Φ
    → (b : B) → सङ्क्रमणम् b
    → (x y : fiber f b) → g (fst x) ≡ g (fst y)
  सङ्क्रमणे-भारो-नास्ति g gcons b tr x y =
    sym (ध्रुवं-कक्ष्यायाम् g Φ gcons (fst (tr x y)) (fst x))
    ∙ cong g (snd (tr x y))
