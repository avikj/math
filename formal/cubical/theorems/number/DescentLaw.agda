{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- DescentLaw
--
-- The one law of the corpus, at its native level.  The Python
-- DescentMachine's `offer` decides, for a FINITE world and one
-- observable, whether the observable is constant on the fibers of the
-- carrier.  This module states what that loop is a shadow of: descent
-- through a carrier is the elimination rule of the set quotient, and
-- the two branches of `offer` are the two universal statements below.
--
--   DESCENDS  is not a checked property but a constructor of the
--             factorization: `descend` (= SetQuotients.rec).
--   COARSEST  the carrier quotient is universal: any factorization
--             agrees with `descend` pointwise (`descend-unique`).
--   FORMS     a splitting witness (x, y related, observable differs)
--             is a proof that NO factorization exists (`forms`) — the
--             machine's split fiber, as an obstruction, over ALL
--             instances at once rather than an enumerated window.
--
-- Companion: machinery/descent_formation_machine.py (absent from this repository) (finite shadow),
-- machinery/core_knowledge.py (absent from this repository) (claims verified by the finite shadow).
------------------------------------------------------------------------

module DescentLaw where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/)

private
  variable
    ℓA ℓR ℓB : Level

module _ {A : Type ℓA} {R : A → A → Type ℓR} {B : Type ℓB}
         (setB : isSet B) where

  -- DESCENDS: an observable constant on carrier fibers factors through
  -- the carrier.
  descend : (f : A → B)
          → (∀ x y → R x y → f x ≡ f y)
          → A / R → B
  descend f resp = SQ.rec setB f resp

  -- The factorization is on the nose (definitional).
  descend-β : (f : A → B) (resp : ∀ x y → R x y → f x ≡ f y) (x : A)
            → descend f resp [ x ] ≡ f x
  descend-β f resp x = refl

  -- COARSEST: any map out of the carrier agreeing with f on points
  -- agrees with `descend` everywhere — the carrier is the universal
  -- (coarsest) object through which f factors.
  descend-unique : (f : A → B) (resp : ∀ x y → R x y → f x ≡ f y)
                 → (g : A / R → B)
                 → (∀ x → g [ x ] ≡ f x)
                 → ∀ q → g q ≡ descend f resp q
  descend-unique f resp g agree =
    SQ.elimProp (λ q → setB _ _) agree

  -- FORMS: an observable that separates one related pair factors
  -- through the carrier in no way at all.  The witness pair IS the
  -- obstruction; `offer`'s split event is the finite trace of this.
  forms : (f : A → B) (g : A / R → B)
        → (∀ x → g [ x ] ≡ f x)
        → ∀ x y → R x y
        → (f x ≡ f y → ⊥)
        → ⊥
  forms f g agree x y r fx≢fy =
    fx≢fy (sym (agree x) ∙ cong g (eq/ x y r) ∙ agree y)
