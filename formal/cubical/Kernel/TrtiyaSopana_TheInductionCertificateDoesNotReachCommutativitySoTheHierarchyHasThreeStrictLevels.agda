{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Kernel.TrtiyaSopana_TheInductionCertificateDoesNotReach
--            CommutativitySoTheHierarchyHasThreeStrictLevels
--
-- - · the third step of the stair.  The compound is assembled
--
-- WHERE THIS STANDS.  `Naya_…` proved two things:
--
--   §3 there   commutativity of `add` is UNDERIVABLE          (W-model)
--   §4 there   the induction rule is STRICTLY STRONGER than
--              the rewrite closure                            (0 + x = x)
--
-- The question between them: whether the induction apparatus — the strongest
-- thing in the kernel's three files — reaches commutativity.  This
-- module answers: IT DOES NOT.  The same W-standpoint that decided §3
-- decides this, one level up, with no new machinery: an
-- `InductionCertificate (add var yvar) (add yvar var)` carries a `base`
-- field of type `Derivation (add zero yvar) (add yvar zero)`, and the
-- W-values of those endpoints differ at the head —
--
--     ⟦ add zero yvar ⟧ = aM ∷ aY ∷ []        (the marker survives)
--     ⟦ add yvar zero ⟧ = aY ∷ []             (right unit, by refl)
--
-- so `derivation-model` refutes the base, hence the certificate.
--
-- THE CONSEQUENCE, stated as one object below.  Commutativity is TRUE at
-- every environment (`+-comm`), certifiable by nothing the kernel has,
-- installable a fortiori by nothing the kernel has.  With `Naya_…`'s §4
-- this closes a three-level strictness:
--
--     rewrite closure  ⊊  induction closure  ⊊  truth in ℕ
--
-- first strictness witnessed by `0 + x = x` (there), second by
-- `x + y = y + x` (here).  The kernel certifies more than it can
-- install, and there is truth it cannot even certify.
--
-- WHAT THIS MEANS FOR THE APPARATUS, read forward not backward: the
-- certificate form does induction on ONE coordinate (`var`), and
-- commutativity's classical proof needs a nested induction whose base
-- `0 + y = y` is itself only induction-certifiable — but `base` demands
-- a `Derivation`, and by `Naya_…`'s `not-left-unital` argument none
-- exists.  The wall is exactly the type of the `base` field.
------------------------------------------------------------------------

module Kernel.TrtiyaSopana_TheInductionCertificateDoesNotReachCommutativitySoTheHierarchyHasThreeStrictLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; _+_ ; +-comm)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Sigma using (_×_ ; _,_)
import Cubical.Data.Empty as E

open import Kernel.RewriteCertificate
open import Kernel.Naya_EvalIsOneStandpointAndASecondOneProvesTheInductionRuleIsStrictlyStrongerThanTheRewriteClosure
  using (Atom ; aX ; aY ; aM ; W ; ⟦_⟧ ; derivation-model ; hd)

------------------------------------------------------------------------
-- §1.  The discriminator.  §3 there used the head against aX; the base
--      of a commutativity certificate is decided by the head against aY:
--      the left side keeps the dropped marker aM, the right side is the
--      bare aY by right-unitality.
------------------------------------------------------------------------

isY : Atom → Bool
isY aY = true
isY _  = false

------------------------------------------------------------------------
-- §2.  THE REFUTATION.  The base field's endpoints, evaluated at the
--      W-standpoint, differ at the head; a derivation between them would
--      transport that difference into true ≡ false.
------------------------------------------------------------------------

base-refuted : Derivation (add zero yvar) (add yvar zero) → E.⊥
base-refuted d = true≢false (sym (cong isY (cong hd (derivation-model d))))

not-comm-certifiable :
  InductionCertificate (add var yvar) (add yvar var) → E.⊥
not-comm-certifiable cert =
  base-refuted (InductionCertificate.base cert)

------------------------------------------------------------------------
-- §3.  THE THEOREM, one object: true at every environment, and beyond
--      the certificate's reach.  With Naya_…'s §4 this is the third
--      level of the stair.
------------------------------------------------------------------------

comm-holds-everywhere :
  (ρ : Env) → eval (add var yvar) ρ ≡ eval (add yvar var) ρ
comm-holds-everywhere ρ = +-comm (Env.x ρ) (Env.y ρ)

certificate-does-not-reach-truth :
  ((ρ : Env) → eval (add var yvar) ρ ≡ eval (add yvar var) ρ)
  × (InductionCertificate (add var yvar) (add yvar var) → E.⊥)
certificate-does-not-reach-truth =
  comm-holds-everywhere , not-comm-certifiable
