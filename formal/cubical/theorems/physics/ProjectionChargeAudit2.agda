{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

-- ProjectionChargeAudit2: the general descent criterion, machine-checked.
--
-- Context.  `ProjectionChargeAudit.agda` certifies two *instances*:
--   (+) local coordinate plus total charge is an equivalence on Bool × Bool;
--   (−) a charge separating two quotient-identified points cannot descend
--       (`noChargeDescent`, the eliminator-level form of the sieve witness
--       1 ~ 7 with opposite Liouville charges).
--
-- machine-check, the boxed criterion
--
--     (∃ c̄, c̄ ∘ [_] = c)  ⟺  (∀ x y, R x y → c x = c y)
--
-- for a set-valued charge on a set quotient.  This module closes that gap
-- and sharpens it: not only is descent *equivalent* to relation-respect,
-- the descent datum is a *proposition* — a charge descends in at most one
-- way, so descent is a property of the charge, never extra structure.
-- (The note's §5 warning that "freely adjoining paths does not evade"
-- the criterion is exactly the propositional truncation of this fact.)
--
-- New checked statements:
--   Descent.descends→respects   descent forces relation-respect
--   Descent.respects→descends   relation-respect suffices (via SQ.rec)
--   Descent.isPropDescends      the descended charge is unique
--   Descent.descentCriterion    Descends ≃ Respects  (equivalence of props)
--
-- Instances re-derived from the general theorem (no fresh case analysis):
--   noChargeDescent'            the module-1 negative result, now a
--                               one-line corollary of the criterion
--   totalChargeDescends         the positive counterpart: the gauge-
--                               invariant total charge a ⊕ b descends
--                               through the quotient by charge equality.

module ProjectionChargeAudit2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.SetQuotients as SQ

import ProjectionChargeAudit as PCA

-- ---------------------------------------------------------------------------
-- The general theorem.  X a type, R an arbitrary (proof-relevant) relation,
-- C a set of charge values, c the charge.  Nothing is assumed about R:
-- no reflexivity, no symmetry, no transitivity, no propositionality.
-- ---------------------------------------------------------------------------

module Descent {ℓX ℓR ℓC : Level}
  {X : Type ℓX} (R : X → X → Type ℓR)
  {C : Type ℓC} (setC : isSet C) (c : X → C)
  where

  -- The charge respects the observable relation.
  Respects : Type (ℓ-max ℓX (ℓ-max ℓR ℓC))
  Respects = (x y : X) → R x y → c x ≡ c y

  -- The charge descends: a map on the quotient restricting to c on
  -- representatives.  This is the Σ-type whose negation (at c = id) is
  -- `PCA.NoChargeDescent`.
  Descends : Type (ℓ-max (ℓ-max ℓX ℓR) ℓC)
  Descends = Σ[ cbar ∈ (X / R → C) ] ((x : X) → cbar [ x ] ≡ c x)

  -- Necessity: any descended charge transports along generating paths,
  -- so the charge must agree on related representatives.  This is the
  -- abstract content of module 1's `noChargeDescent` argument.
  descends→respects : Descends → Respects
  descends→respects (cbar , agrees) x y r =
    sym (agrees x) ∙ cong cbar (eq/ x y r) ∙ agrees y

  -- Sufficiency: the set-quotient eliminator produces the descent, and it
  -- restricts *definitionally* to c (the second component is refl).
  respects→descends : Respects → Descends
  respects→descends resp = SQ.rec setC c resp , λ x → refl

  -- Relation-respect is a proposition (C is a set).
  isPropRespects : isProp Respects
  isPropRespects = isPropΠ3 λ x y r → setC (c x) (c y)

  -- Uniqueness: descent is a proposition, not structure.  Two descended
  -- charges agreeing with c on representatives agree everywhere, because
  -- [_] is surjective and equality in a set is a proposition.
  isPropDescends : isProp Descends
  isPropDescends (f , p) (g , q) =
    Σ≡Prop (λ h → isPropΠ λ x → setC (h [ x ]) (c x))
           (funExt (SQ.elimProp (λ z → setC (f z) (g z))
                                (λ x → p x ∙ sym (q x))))

  -- The boxed criterion of CUBICAL_QUOTIENT_AUDIT.md (absent from this repository) §1, as an equivalence
  -- of propositions: descending is exactly respecting.
  descentCriterion : Descends ≃ Respects
  descentCriterion =
    propBiimpl→Equiv isPropDescends isPropRespects
                     descends→respects respects→descends

-- ---------------------------------------------------------------------------
-- Negative instance: module 1's theorem is a corollary of the criterion.
-- The indiscrete relation on Bool with the identity charge fails
-- relation-respect at the pair (false, true), so it cannot descend.
-- No case analysis on the quotient is repeated here.
-- ---------------------------------------------------------------------------

module IdDescent = Descent PCA.R isSetBool (idfun Bool)

identityChargeClash : ¬ IdDescent.Respects
identityChargeClash resp = false≢true (resp false true tt)

noChargeDescent' : PCA.NoChargeDescent
noChargeDescent' d = identityChargeClash (IdDescent.descends→respects d)

-- ---------------------------------------------------------------------------
-- Positive instance: the gauge-invariant observable descends.
-- On the two-bit state of module 1, quotient by equality of *total charge*
-- a ⊕ b.  The total charge tautologically respects this relation, so by
-- the criterion it descends — and `isPropDescends` says the descended
-- observable is the unique one restricting to a ⊕ b.  Together with
-- `noChargeDescent'` this is the full dichotomy of the audit note:
-- invariant charges descend uniquely, non-invariant charges not at all.
-- ---------------------------------------------------------------------------

totalCharge : PCA.State → Bool
totalCharge (a , b) = a ⊕ b

RQ : PCA.State → PCA.State → Type
RQ x y = totalCharge x ≡ totalCharge y

module GaugeDescent = Descent RQ isSetBool totalCharge

totalChargeRespects : GaugeDescent.Respects
totalChargeRespects x y r = r

totalChargeDescends : GaugeDescent.Descends
totalChargeDescends = GaugeDescent.respects→descends totalChargeRespects

-- ---------------------------------------------------------------------------
-- Statements-to-prove toward the remaining open edge
-- (CUBICAL_QUOTIENT_AUDIT.md (absent from this repository) §5: when a genuinely higher object is
-- justified).  Each is a checked-Agda target, not prose:
--
-- 1. Free-action collapse (the §5 kill criterion, positive form): for a
--    group G acting freely on a set X, the action groupoid ∥ X // G ∥₁ is
--    equivalent to the set quotient X / orbit-relation.  Concrete first
--    case: the ℤ-action on ℤ by +6 has quotient equivalent to Fin 6, with
--    no surviving loop — i.e. the HIT adds no content, matching §5's
--    "trivial stabilizers" clause.
--
-- 2. Cocycle descent (the §5 positive edge): for a charge valued in a
--    group C and a *cocycle* φ : ∀ x y → R x y → C twisting the descent
--    equation to  cbar [ y ] ≡ φ x y r · cbar [ x ], descent exists iff φ
--    is a coboundary on each R-component; the obstruction class is the
--    monodromy of φ around loops of the relation graph.  The criterion
--    above is the special case φ ≡ 1.  This is the machinery the C*-side
--    gauge charge (§5 item 2) needs before any HIT encoding is justified.
--
-- 3. Effectivity: for a propositional equivalence relation R, upgrade
--    `descends→respects` to the statement that [ x ] ≡ [ y ] implies
--    ∥ R x y ∥₁ (cubical library: `effective`), making the criterion an
--    equivalence between descent and factoring through the *path* relation
--    of the quotient, not merely the generating relation.
-- ---------------------------------------------------------------------------
