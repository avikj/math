{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- «त्रयो निर्णयाः,नन द्वौ ।» — three verdicts, never two.
--
-- machinery/crystal/models.py (absent from this repository) gives the engine's three verdict classes
-- their semantic readings:
--
--   SUCCEEDED        every model of T is a model of S
--   IMPOSSIBLE       joint models of T and S are trivial
--   STRICTLY_WEAKER  some model of T fails S, and nontrivial joint
--                    models exist
--
-- and checks them by finite enumeration at domain sizes 2 and 3 —
-- testimony. This module gives each class one KERNEL-CHECKED
-- representative, so the verdict lattice itself — not just one verdict
-- — has a foothold in the corpus:
--
--   SUCCEEDED        the left-zero law proves associativity outright:
--                    left-zero ⟹ semigroup, for every carrier.
--   IMPOSSIBLE       imported: Aikya's collapse (left-zero + right-zero
--                    forces isProp).
--   STRICTLY_WEAKER  semigroup is strictly weaker than commutative
--                    semigroup: the left-zero operation on Bool is
--                    associative and provably not commutative.
--
-- Together with Aikya this converts the engine's three-valued semantic
-- contract from Python prose into terms. What remains testimony is the
-- engine's CLASSIFICATION of any particular theory pair; what is now
-- perception is that the three classes are inhabited, distinct, and
-- correctly specified.
------------------------------------------------------------------------

module TrayoNirnaya_TheEnginesThreeVerdictSemanticsEachCarryOneCheckedRepresentative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Empty as Empty using (⊥)

open import Aikya_TheJointModelOfLeftZeroAndRightZeroIsASingletonSoTheEngineVerdictIsATerm
  using (JointZero; collapse; jointZero→isProp; noJointZeroOnBool) public

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- SUCCEEDED · the left-zero law proves associativity, no carrier
-- hypotheses.  (The engine issued SUCCEEDED for left-zero → semigroup;
-- its completion-based proof is now this term.)

module _ {A : Type ℓ} (_·_ : A → A → A)
         (left-zero : (x y : A) → x · y ≡ x) where

  leftZero→assoc : (x y z : A) → (x · y) · z ≡ x · (y · z)
  leftZero→assoc x y z =
    left-zero (x · y) z ∙ left-zero x y ∙ sym (left-zero x (y · z))

------------------------------------------------------------------------
-- STRICTLY_WEAKER · semigroup does not prove commutativity: the
-- left-zero operation on Bool is associative (by the theorem above)
-- and provably not commutative.  This is the separating model the
-- engine's finite search exhibited at size 2, now as a term.

_◁◁_ : Bool → Bool → Bool
x ◁◁ y = x

◁◁-left-zero : (x y : Bool) → x ◁◁ y ≡ x
◁◁-left-zero x y = refl

◁◁-assoc : (x y z : Bool) → (x ◁◁ y) ◁◁ z ≡ x ◁◁ (y ◁◁ z)
◁◁-assoc = leftZero→assoc _◁◁_ ◁◁-left-zero

◁◁-not-comm : ((x y : Bool) → x ◁◁ y ≡ y ◁◁ x) → ⊥
◁◁-not-comm comm = true≢false (comm true false)

------------------------------------------------------------------------
-- IMPOSSIBLE · re-exported from Aikya above: collapse, jointZero→isProp,
-- noJointZeroOnBool.  Three classes, three inhabitants, no fourth road.
