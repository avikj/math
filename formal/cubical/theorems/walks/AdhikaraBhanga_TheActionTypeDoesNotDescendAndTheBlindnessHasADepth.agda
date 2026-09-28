{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अधिकारभङ्गः — the action type does not descend, and the blindness has
-- a depth.
--
-- TERM.  अधिकार — capacity, entitlement, the standing to act — is the
-- stra's own word for what English calls affordance and agency (a
-- text's adhikrin is the one *qualified to act* on it; BOOK.md (absent from this repository)'s §2 is
-- an adhikāra statement).  भङ्ग as in अवतरणभङ्गः.  The compound
-- - is built here; no source is claimed for it.
--
-- SEED.  Two constructions ("type-blindness"):
--
--   * the AFFORDANCE NO-GO: S(x) = S(y), Action(x) inhabited,
--     Action(y) empty ⟹ no policy type descends through S — "the
--     current higher-topology result carried directly into control and
--     alignment";
--   * the DESCENT-DEPTH ladder: blindness can first appear at any
--     homotopy stratum — Unit/∅ at existence, Bool/Unit at π₀,
--     S¹/Unit at π₁.
--
-- Both are instances of the landed अवतरणभङ्गः machinery; what is new
-- here is the witnesses and the reading.
--
-- WHAT IS PROVED.
--
--   अधिकारभङ्गः    two states with EQUAL observation, one holding an
--                  action and one holding none: the action family does
--                  not descend to the observation.  A controller that
--                  sees only the quotient cannot be complete — not
--                  "will struggle": the policy's TYPE cannot exist on
--                  the quotient.  This is agential blindness, distinct
--                  from and more severe than descriptive blindness.
--   द्वि-एक-भेदः    ¬ (Bool ≃ Unit) — the π₀ rung's witness.
--   वृत्त-एक-भेदः   ¬ (S¹ ≃ Unit) — the π₁ rung's witness: both types
--                  are connected, every point-census agrees, and the
--                  loop charge ℤ separates them.
--   गहनता-०/१/२    the three descent no-gos: families over one blind
--                  pair whose fibres disagree first at existence
--                  (Unit/⊥), at components (Bool/Unit), at loops
--                  (S¹/Unit).  Each is one application of the landed
--                  no-go; the third is the sharpest — a base that
--                  correctly reports "a witness exists, and the
--                  witness space is connected" still cannot host the
--                  family, because the fibres differ in their loops.
--
------------------------------------------------------------------------

module AdhikaraBhanga_TheActionTypeDoesNotDescendAndTheBlindnessHasADepth where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; invEq ; retEq ; invEquiv)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv ; isContr→isContrPath)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Unit using (Unit ; tt ; isContrUnit)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Int using (ℤ ; pos ; injPos)
open import Cubical.Data.Nat using (znots)
open import Cubical.HITs.S1 using (S¹ ; base ; ΩS¹ ; ΩS¹Isoℤ)

open import DescentBhanga_TheQuotientCannotHostTheTypeOfWitnessesAndTheProofIsOneTransport
  using (DependentFactorsThrough ; dependent-collision-obstructs ; अवतरण-भङ्ग-सामान्यम्)

------------------------------------------------------------------------
-- १ · the affordance no-go.  The smallest honest model: two hidden
-- states, one observation value, an action available in one state and
-- impossible in the other.
------------------------------------------------------------------------

-- hidden states and the (fully collapsing) observation
गूढम् : Type
गूढम् = Bool

दर्शनम् : गूढम् → Unit
दर्शनम् _ = tt

-- the action family: from state `true` an act exists; from `false` none.
अधिकारः : गूढम् → Type
अधिकारः true  = Unit
अधिकारः false = ⊥

-- THE NO-GO: the action family does not descend to the observation.
-- No policy typed over the observation alone can be correct in both
-- states, because the type of valid actions cannot even be stated there.
अधिकारभङ्गः : ¬ DependentFactorsThrough दर्शनम् अधिकारः
अधिकारभङ्गः =
  dependent-collision-obstructs दर्शनम् अधिकारः true false refl tt (λ b → b)

------------------------------------------------------------------------
-- २ · the depth witnesses.
------------------------------------------------------------------------

-- π₀ rung: Bool and Unit are both inhabited; they differ at components.
द्वि-एक-भेदः : ¬ (Bool ≃ Unit)
द्वि-एक-भेदः e = true≢false (sym (retEq e true) ∙ retEq e false)

-- π₁ rung: S¹ and Unit are both inhabited and both connected; they
-- differ at loops.  An equivalence would make S¹ contractible, hence
-- its loop space contractible, hence ℤ contractible via winding, and
-- pos 0 ≡ pos 1 refutes that through injPos.
वृत्त-एक-भेदः : ¬ (S¹ ≃ Unit)
वृत्त-एक-भेदः e = znots (injPos (sym (ℤcontr .snd (pos 0)) ∙ ℤcontr .snd (pos 1)))
  where
  S¹contr : isContr S¹
  S¹contr = isOfHLevelRespectEquiv 0 (invEquiv e) isContrUnit
  ΩS¹contr : isContr ΩS¹
  ΩS¹contr = isContr→isContrPath S¹contr base base
  ℤcontr : isContr ℤ
  ℤcontr = isOfHLevelRespectEquiv 0 (isoToEquiv ΩS¹Isoℤ) ΩS¹contr

------------------------------------------------------------------------
-- ३ · the ladder: one blind pair, three families, three strata.
------------------------------------------------------------------------

-- rung 0 — the fibres disagree at existence (this is अधिकारभङ्गः above,
-- named into the ladder):
गहनता-० : ¬ DependentFactorsThrough दर्शनम् अधिकारः
गहनता-० = अधिकारभङ्गः

-- rung 1 — both fibres inhabited; they disagree at π₀:
घटकाः : गूढम् → Type
घटकाः true  = Bool
घटकाः false = Unit

गहनता-१ : ¬ DependentFactorsThrough दर्शनम् घटकाः
गहनता-१ = अवतरण-भङ्ग-सामान्यम् दर्शनम् घटकाः true false refl द्वि-एक-भेदः

-- rung 2 — both fibres inhabited AND connected; they disagree at π₁.
-- A base that truthfully reports "a witness exists and the witness
-- space is in one piece" still cannot host the family.
वलयाः : गूढम् → Type
वलयाः true  = S¹
वलयाः false = Unit

गहनता-२ : ¬ DependentFactorsThrough दर्शनम् वलयाः
गहनता-२ = अवतरण-भङ्ग-सामान्यम् दर्शनम् वलयाः true false refl वृत्त-एक-भेदः
