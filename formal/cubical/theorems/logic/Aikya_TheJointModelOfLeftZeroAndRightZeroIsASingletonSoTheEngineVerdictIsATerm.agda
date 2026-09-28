{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
--  — forced oneness.  (Term used descriptively — aikya, "unity/
-- (aikya: "unity/identity".)
--
-- WHAT THIS IS.  machinery/crystal/'s engine issued IMPOSSIBLE for the
-- identity-map interpretation between the theories `left-zero`
-- (x·y = x) and `right-zero` (x·y = y): completion of the joint theory
-- collapses the carrier, and models.py (absent from this repository) confirmed by finite search that
-- every joint model on domains of size 2 and 3 is trivial.
-- Both of those are testimony — a Python run a
-- reader must trust.  This module is the same verdict as PERCEPTION:
-- a kernel-checked term, for every carrier and every size at once.
--
-- DefectIsNowPriced.md (absent from this repository) (receipt R2): one verdict transported converts
-- the engine from parallel authority to conjecture generator.  This is
-- that transport.  The engine PROPOSED; the kernel now DISPOSES.
--
-- Statement.  If one binary operation on a type satisfies both the
-- left-zero law and the right-zero law, the type is a proposition:
-- any two points are equal.  Consequently no such operation exists on
-- Bool (or any type with two distinguishable points) — the finite
-- searches at sizes 2 and 3 were shadows of this one term.
------------------------------------------------------------------------

module Aikya_TheJointModelOfLeftZeroAndRightZeroIsASingletonSoTheEngineVerdictIsATerm where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Empty as Empty using (⊥)

private
  variable
    ℓ : Level

-- The joint theory, as a structure on a carrier.
record JointZero (A : Type ℓ) : Type ℓ where
  field
    _·_        : A → A → A
    left-zero  : (x y : A) → x · y ≡ x
    right-zero : (x y : A) → x · y ≡ y

-- The collapse: both laws on one operation force any two points equal.
-- This is the whole content of the engine's IMPOSSIBLE verdict.
collapse : {A : Type ℓ} → JointZero A → (x y : A) → x ≡ y
collapse jz x y = sym (JointZero.left-zero jz x y) ∙ JointZero.right-zero jz x y

-- hence the carrier is a proposition …
jointZero→isProp : {A : Type ℓ} → JointZero A → isProp A
jointZero→isProp jz = collapse jz

-- … and the concrete instance the finite search sampled at n = 2:
-- Bool admits no joint model.  (The n = 3 search is the same term.)
noJointZeroOnBool : JointZero Bool → ⊥
noJointZeroOnBool jz = true≢false (collapse jz true false)
