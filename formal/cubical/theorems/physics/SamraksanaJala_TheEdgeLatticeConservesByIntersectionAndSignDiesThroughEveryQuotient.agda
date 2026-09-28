{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- संरक्षण-जालम् — the conservation-net.  The crystal's L1 typed-edge lattice
-- (runtime/CRYSTAL.md (absent from this repository) §1, runtime/kernel/edges.py (absent from this repository)) made a checked term: what
-- each kind of transport CONSERVES, that a composite conserves the
-- INTERSECTION of its parts, and the consequence the whole machine is built
-- to respect — sign (parity, order data) survives only the Order edge and
-- DIES through every path that passes a Quotient.
--
-- WHY THIS FEEDS THE MACHINE.  runtime/STATUS.md states the kernel's trust
-- boundary plainly: only Eq (proof paths), Iso (round-trip) and β are
-- genuinely machine-checked; for Quotient, Embed, Implies, Approx, Refine,
-- Interp, Dual the checker verifies only that a certificate was DECLARED,
-- not that the mathematics holds.  edges.py (absent from this repository)'s PRESERVES dict is that
-- declaration.  This module is the mathematics behind it: the preservation
-- table, the intersection law, and the parity-blindness corollary, as terms
-- the kernel checks — declared certificate ⟶ proved theorem.
--
-- THE FACTS (edges.py (absent from this repository) verbatim):
--   • Eq conserves everything (the identity transport).
--   • Iso conserves everything EXCEPT presentation and sign — Galois
--     conjugation a+b√2 ↦ a−b√2 is a field iso of ℚ(√2) that exchanges its
--     two orderings, so an iso does not carry order data.  (Witnessed at ℤ
--     in RnaDhanaKrama: neg preserves abs, reverses sign.)
--   • Quotient conserves only task-sufficiency; in particular NOT sign.
--   • Order is the only NON-identity kind conserving sign, and only relative
--     to its named ordering (the avacchedaka/limitor).
--
-- CHECKED:
--   §1  the preservation table _⊨_ : Kind → Tag → Bool (edges.py (absent from this repository) PRESERVES).
--   §2  sign's carriers are exactly Eq and Order (onlyEqAndOrderCarrySign).
--   §3  composition conserves the intersection (pathPreserves = fold of &).
--   §4  PARITY BLINDNESS: any path containing a Quotient conserves sign ≡
--       false — "no path through a Quotient delivers sign", structurally.
------------------------------------------------------------------------

module SamraksanaJala_TheEdgeLatticeConservesByIntersectionAndSignDiesThroughEveryQuotient where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- the eleven edge kinds and the ten preservation tags (edges.py (absent from this repository) KINDS,
-- ALL_PROPERTIES).
data Kind : Type where
  eq iso embed quotient implies approx refine interp dual order conjecture : Kind

data Tag : Type where
  presentation truth structure injectivity taskSuff
    boundedError extensional semantics pairing sign : Tag

------------------------------------------------------------------------
-- §1 · THE PRESERVATION TABLE.  k ⊨ t : "kind k conserves tag t."  This is
-- edges.py (absent from this repository)'s PRESERVES dict, transcribed.  Catch-alls default to false; the
-- listed rows are the true entries.
_⊨_ : Kind → Tag → Bool
eq         ⊨ _            = true            -- the identity conserves all
conjecture ⊨ _            = false           -- a conjecture conserves nothing
iso        ⊨ presentation = false           -- ...all but presentation
iso        ⊨ sign         = false           -- ...and sign (Galois swaps orderings)
iso        ⊨ _            = true
embed      ⊨ injectivity  = true
embed      ⊨ truth        = true
embed      ⊨ _            = false
quotient   ⊨ taskSuff     = true
quotient   ⊨ _            = false
implies    ⊨ truth        = true
implies    ⊨ _            = false
approx     ⊨ boundedError = true
approx     ⊨ _            = false
refine     ⊨ extensional  = true
refine     ⊨ _            = false
interp     ⊨ semantics    = true
interp     ⊨ truth        = true
interp     ⊨ _            = false
dual       ⊨ pairing      = true
dual       ⊨ _            = false
order      ⊨ sign         = true            -- the only non-identity sign-carrier
order      ⊨ _            = false

------------------------------------------------------------------------
-- §2 · SIGN'S CARRIERS ARE EXACTLY Eq AND Order.  Every other kind loses it.
onlyEqAndOrderCarrySign : (k : Kind) → (k ⊨ sign) ≡ true → (k ≡ eq) ⊎ (k ≡ order)
onlyEqAndOrderCarrySign eq         _ = inl refl
onlyEqAndOrderCarrySign order      _ = inr refl
onlyEqAndOrderCarrySign iso        p = Empty.rec (true≢false (sym p))
onlyEqAndOrderCarrySign embed      p = Empty.rec (true≢false (sym p))
onlyEqAndOrderCarrySign quotient   p = Empty.rec (true≢false (sym p))
onlyEqAndOrderCarrySign implies    p = Empty.rec (true≢false (sym p))
onlyEqAndOrderCarrySign approx     p = Empty.rec (true≢false (sym p))
onlyEqAndOrderCarrySign refine     p = Empty.rec (true≢false (sym p))
onlyEqAndOrderCarrySign interp     p = Empty.rec (true≢false (sym p))
onlyEqAndOrderCarrySign dual       p = Empty.rec (true≢false (sym p))
onlyEqAndOrderCarrySign conjecture p = Empty.rec (true≢false (sym p))

isoLosesSign      : (iso      ⊨ sign) ≡ false
isoLosesSign      = refl
quotientLosesSign : (quotient ⊨ sign) ≡ false
quotientLosesSign = refl
orderCarriesSign  : (order    ⊨ sign) ≡ true
orderCarriesSign  = refl

------------------------------------------------------------------------
-- §3 · COMPOSITION CONSERVES THE INTERSECTION.  A path of transports
-- conserves a tag iff every step does — the AND-fold, "the only lattice in
-- the kernel" (edges.py (absent from this repository)).  The empty path is the identity (Eq), conserving
-- all.
_&_ : Bool → Bool → Bool
true  & b = b
false & _ = false

&-false : (b : Bool) → b & false ≡ false
&-false true  = refl
&-false false = refl

pathPreserves : List Kind → Tag → Bool
pathPreserves []       _ = true
pathPreserves (k ∷ ks) t = (k ⊨ t) & pathPreserves ks t

------------------------------------------------------------------------
-- §4 · PARITY BLINDNESS, structurally.  Any path that passes through a
-- Quotient conserves sign ≡ false: sign cannot survive the intersection
-- once one factor is a Quotient.  This is the machine's own statement of
-- what it cannot see — "no path through a Quotient delivers sign" — as a
-- checked term, for a Quotient at any position in the path.
quotientKillsSign : (pre post : List Kind)
  → pathPreserves (pre ++ quotient ∷ post) sign ≡ false
quotientKillsSign []         post = refl        -- false & _ ≡ false, definitionally
quotientKillsSign (k ∷ pre)  post =
  cong ((k ⊨ sign) &_) (quotientKillsSign pre post) ∙ &-false (k ⊨ sign)
