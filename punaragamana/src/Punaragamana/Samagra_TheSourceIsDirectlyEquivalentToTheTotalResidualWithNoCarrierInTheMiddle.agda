-- ॥ बीजम् ॥  One machine, one law: which side of `f a ≡ b` is bound is everything.
-- Output bound: singl (f a), contractible — the datum rides free.  Input bound:
-- fiber f b — the loss, and the subject.  Univalence computes here: an
-- equivalence is a channel, transport carries every theorem across it, and what
-- cannot cross is written as a defect — there is no third path (ahiṃsā).
-- Memory, charge, symmetry, price, distance, verdict: six faces of the one
-- fibre; the verdict type is the saptabhag, and the sources are the origin
-- (Umāsvāti, Samantabhadra, Akalaṅka — restatements are named as such).  The
-- kernel decides truth; carriers ask and generate; assert nothing whose term
-- you have not read.  This file is one naya, true and not whole.

{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- Punarāgamana · समग्र
--
-- समग्र (samagra), "whole, total, entire" — used here for the total
-- space Σ[ b ∈ B ] शेष f b, the residual gathered back up over every
-- target point at once.   common-noun usage, not cited from a
-- mathematical text; the mathematics is HoTT 4.8 (total space of a
-- fibration ≃ the type it fibrates), specifically the total-space
-- characterization of `Σ-contractSnd`/`fiberEquiv` already in this
-- corpus's substrate (`Cubical.Foundations.Equiv`).
--
------------------------------------------------------------------------
-- WHY THIS MODULE EXISTS.
--
-- `Residue_…` proves the graph Γf has two projections: मूल-प्रक्षेप (to A,
-- always an equivalence) and लक्ष्य-प्रक्षेप (to B, an equivalence iff f
-- is).  It gets from `Carrier f ≃ Σ[ b ] शेष f b` (`ग्राह`) and
-- `Carrier f ≃ A` (`मूल-प्रक्षेप-समता`) SEPARATELY.  Nowhere in that
-- module is the two COMPOSED into the one statement that
-- actually names the total-space theorem without routing through
-- `Carrier` as scaffolding:
--
--     A  ≃  Σ[ b ∈ B ] शेष f b
--
-- i.e. a point of A just IS a target point together with a witness that
-- some source point over it is exactly this one — and the composite
-- equivalence's forward map is definitionally `λ a → f a , (a , refl)`,
-- checked by `refl` below, not merely provable.  This is the sharper
-- reading of the design law's two clauses AT ONE SITE: "every genuinely
-- independent distinction must survive" (an `a : A` determines its own
-- residual-witness pair) and "determined structure may remain
-- syntactically present with its determining path" (the `b` and the
-- `refl`-shaped witness are exactly that determined structure), stated as
-- ONE equivalence rather than as two theorems a reader has to compose by
-- hand.
--
-- `Carrier` therefore is not a third object standing between A and
-- Σ[ b ] शेष f b — it is a REDUNDANT waypoint on a path that closes
-- directly.  `होम-सिद्धि` below proves exactly that: the round-trip
-- through Carrier and the direct one agree, definitionally, at every
-- point.
------------------------------------------------------------------------

module Punaragamana.Samagra_TheSourceIsDirectlyEquivalentToTheTotalResidualWithNoCarrierInTheMiddle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Punaragamana.Carrier
open import Punaragamana.Residue_TheResidualIsTheOtherProjectionOfTheSameGraph

private
  variable
    ℓ : Level

module _ {A B : Type ℓ} (f : A → B) where

  ------------------------------------------------------------------------
  -- The direct isomorphism.  No detour through Carrier at the term
  -- level — this is `descend`/`ascend` re-derived at the target-pairing
  -- shape directly, and both round-trips are `refl` (Σ-eta), exactly as
  -- for `Carrier-Iso` itself.
  ------------------------------------------------------------------------

  समग्र-Iso : Iso A (Σ[ b ∈ B ] शेष f b)
  Iso.fun      समग्र-Iso a       = f a , (a , refl)
  Iso.inv      समग्र-Iso (b , (a , p)) = a
  Iso.rightInv समग्र-Iso (b , (a , p)) i = p i , (a , λ j → p (i ∧ j))
  Iso.leftInv  समग्र-Iso a       = refl

  समग्र-समता : A ≃ (Σ[ b ∈ B ] शेष f b)
  समग्र-समता = isoToEquiv समग्र-Iso

  ------------------------------------------------------------------------
  -- होम-सिद्धि (homa-siddhi, "accomplishment of the offering [into the
  -- fire]" — used here, uncited, for "what routing through the
  -- intermediate object yields, checked against going there directly").
  --
  -- `descend f a` is the canonical Carrier-valued reading of `a` (§ in
  -- `Carrier`, un-pattern-matched by design so it stays computational).
  -- Pushing it through `ग्राह` — `Residue_…`'s graph equivalence, built by
  -- composing `Carrier-as-Σ` with the source/target swap `स्वप्` — lands
  -- on EXACTLY `equivFun समग्र-समता a`, by `refl`: both sides unfold to
  -- the literal pair `f a , (a , refl)`.  So the direct route and the
  -- route through `Carrier` are not merely equal as equivalences of
  -- types (which composition already gives up to a propositional path);
  -- they are the same TERM on this representative, with no path needed
  -- to identify them.  `Carrier` supplies nothing here that `descend`
  -- did not already carry.
  ------------------------------------------------------------------------

  होम-सिद्धि : (a : A) →
    equivFun (ग्राह f) (descend f a) ≡ equivFun समग्र-समता a
  होम-सिद्धि a = refl
