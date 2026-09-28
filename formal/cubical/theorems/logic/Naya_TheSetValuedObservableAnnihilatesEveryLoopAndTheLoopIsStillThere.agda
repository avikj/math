{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- नय · naya — THE STANDPOINT, AND WHAT IT CANNOT REPORT
--
-- THE TERM, ITS TEXT AND ITS DATE.  नय (naya) is the Jaina doctrine of
-- standpoints: every knowing is FROM one, a naya is true but not whole,
-- and a naya that asserts itself by DENYING the others becomes a
-- दुर्नय (durnaya).  Umāsvāti, *Tattvārthasūtra* 1.34-35 (~2nd-5th c.);
-- Siddhasena Divkara, *Sanmatitarka* 1.21-25 (~5th c.); the durnaya
-- sharpening is Siddhasena's and Akalaka's (~8th c.).  Jaina, and the
-- Naiyyikas reject anekntavda outright -- the school is named because
-- the dispute is the content.
--
-- WHAT IS PROVED.  Five things, four of them over the loop `ua notEquiv : Bool ≡ Bool`.
--
--   १  नय-निरोधः  -- every SET-valued observable annihilates every loop:
--      `cong F p ≡ refl` for all `F : A → X` with `X` a set.  No hypothesis
--      on `F`: not continuity, not computability, not naturality.
--   २  लोपाभावः   -- the loop is nevertheless not `refl`.
--   ३  the package: a nonzero charged sector on which every set-valued
--      standpoint has expectation exactly zero.  This is `GAUGE.md` (absent from this repository)
--      Theorem F's MECHANISM at the grain of the identification graph:
--      an invariant observable annihilates what the symmetry moves, and
--      the annihilation is an invariance, not a deficiency of effort.
--   ४  the escape, and there is exactly one shape of it: an observable
--      that is NOT set-valued does see the loop.  Truncating to a set is
--      the whole of the blindness.
--      On a graph whose every edge is an identification, ANTISYMMETRY IS FREE.  A
--      causal order read off such a graph is therefore vacuous -- it
--      constrains nothing, because `R x y → x ≡ y` already holds.
--
-- interactive/Setubandha_….hs (14 automorphisms, "no reachability, real content").
------------------------------------------------------------------------

module Naya_TheSetValuedObservableAnnihilatesEveryLoopAndTheLoopIsStillThere where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool using (Bool; true; false; not; notEquiv; true≢false)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Relation.Nullary using (¬_)

private variable ℓ ℓ' : Level

-- १ ── नय-निरोधः.  A set-valued standpoint annihilates every loop.
नय-निरोधः : {A : Type ℓ} {X : Type ℓ'} → isSet X
          → (F : A → X) {a : A} (p : a ≡ a) → cong F p ≡ refl
नय-निरोधः isSetX F p = isSetX _ _ (cong F p) refl

-- २ ── the loop, and that it is not refl.
आवर्तः : Bool ≡ Bool
आवर्तः = ua notEquiv

लोपाभावः : ¬ (आवर्तः ≡ refl)
लोपाभावः q =
  true≢false ( sym (transportRefl true)
             ∙ cong (λ r → transport r true) (sym q)
             ∙ uaβ notEquiv true )

-- ३ ── the package.  E[charged] = 0, and the charge is not 0.
--      (`X` fixed at Type₀ only so the Σ stays at one level.)
सप्रभावः-शून्यम् :
    (¬ (आवर्तः ≡ refl))
  × ((X : Type₀) → isSet X → (F : Type₀ → X) → cong F आवर्तः ≡ refl)
सप्रभावः-शून्यम् = लोपाभावः , λ X isSetX F → नय-निरोधः isSetX F आवर्तः

-- ४ ── the escape.  Drop the set-truncation and the loop is visible.
--      `cong (λ A → A) आवर्तः` is `आवर्तः` by eta, so §२ applies directly.
स्थान-संयोगः : ¬ (cong (λ (A : Type₀) → A) आवर्तः ≡ refl)
स्थान-संयोगः = लोपाभावः

-- ५ ── antisymmetry is free on a graph of identifications.
--      Setubandha's edges are `A ≃ B` and `A ≡ B`; `ua` turns the first
--      into the second, so every edge is already a path and the causal
--      reading of reachability is vacuous rather than false.
सेतुः-पथः : {A B : Type ℓ} → A ≃ B → A ≡ B
सेतुः-पथः = ua

निर्विषयः : {A : Type ℓ} (R : A → A → Type ℓ')
          → ({x y : A} → R x y → x ≡ y)
          → {x y : A} → R x y → R y x → x ≡ y
निर्विषयः R into r _ = into r
