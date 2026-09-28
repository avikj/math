{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- MinPlusResiduationIsAGaloisConnectionAtOneCut
--
-- `TheSaturationClosureNeedsOnlyAGaloisConnection` reduced Δ 28
-- §31–32's saturation obligation to exactly two lines, `galFwd` and
-- `galBwd`, for an abstract Galois connection.
--
-- Here they are proved at ONE CUT — a single burden and a single
-- residual — with the real min-plus data, not a stand-in.
--
-- ────────────────────────────────────────────────────────────────────
-- THE ORDER IS REVERSED, AND THAT IS THE WHOLE POINT.  In min-plus,
-- lower cost is better, so the quantale order is `a ⊑ b = b ≤ ℕ-a`.
-- With ℕ's own `≤` the residuation is NOT a Galois connection and the
-- failure is not subtle: `∸` truncates, and `truncationBreaksTheNaiveOrder`
-- below exhibits `K = 0, φ = 0, ψ = 5` where one side holds and the
-- other does not.  Getting the direction right is not bookkeeping; it
-- is the difference between the obligation being dischargeable and
-- being false.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   ∸-adjˡ / ∸-adjʳ     the monus adjunction, K ∸ ψ ≤ φ  ⟺  K ≤ φ + ψ,
--                       which the pinned cubical (v0.9) does not ship in this form
--   galFwd / galBwd     both directions of the contravariant adjunction
--                       for `u = d = (K ∸_)` under the reversed order —
--                       and both are the SAME statement, since the two
--                       sides are `K ≤ φ + ψ` and `K ≤ ψ + φ`
--   MinPlusCut          the instantiation of `module Galois`, from which
--                       antitonicity, unit, counit, the triangles,
--                       idempotence of `c a = K ∸ (K ∸ a)`, and the
--                       fixed-point characterisation all follow with
--                       NOTHING re-proved
--   truncationBreakstheNaiveOrder
--                       the same maps under ℕ's own order fail
--
-- So Δ 28 §31–32's "re-saturate" is, at one cut, a checked closure over
-- genuine min-plus data: saturate once and stop.
--
-- ────────────────────────────────────────────────────────────────────
-- `(_∸ b) ⊣ (_+ b)` is the standard residuation in ℕ and
-- makes it a residuated monoid; that Isbell conjugation over a quantale
-- is a Galois connection is likewise standard (Lawvere's metric-space
-- reading of enriched categories, `Metric spaces, generalized logic,
-- and closed categories`, 1973, is where min-plus becomes the value
-- object).
------------------------------------------------------------------------

module MinPlusResiduationIsAGaloisConnectionAtOneCut where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _∸_ ; +-zero ; +-suc ; +-comm ; snotz)
open import Cubical.Data.Nat.Order
  using (_≤_ ; ≤-refl ; ≤-trans ; zero-≤ ; suc-≤-suc ; pred-≤-pred)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Relation.Nullary using (¬_)

open import TheSaturationClosureNeedsOnlyAGaloisConnection
  using (module Galois)

------------------------------------------------------------------------
-- 1.  The monus adjunction, which the pinned cubical (v0.9) does not ship in this form
------------------------------------------------------------------------

∸-adjˡ : (K ψ φ : ℕ) → K ∸ ψ ≤ φ → K ≤ φ + ψ
∸-adjˡ K       zero     φ h = subst (K ≤_) (sym (+-zero φ)) h
∸-adjˡ zero    (suc ψ)  φ _ = zero-≤
∸-adjˡ (suc K) (suc ψ)  φ h =
  subst (suc K ≤_) (sym (+-suc φ ψ)) (suc-≤-suc (∸-adjˡ K ψ φ h))

∸-adjʳ : (K ψ φ : ℕ) → K ≤ φ + ψ → K ∸ ψ ≤ φ
∸-adjʳ K       zero     φ h = subst (K ≤_) (+-zero φ) h
∸-adjʳ zero    (suc ψ)  φ _ = zero-≤
∸-adjʳ (suc K) (suc ψ)  φ h =
  ∸-adjʳ K ψ φ (pred-≤-pred (subst (suc K ≤_) (+-suc φ ψ) h))

------------------------------------------------------------------------
-- 2.  The min-plus order: lower cost is better, so ℕ's ≤ is reversed
------------------------------------------------------------------------

module _ (K : ℕ) where

  _⊑_ : ℕ → ℕ → Type
  a ⊑ b = b ≤ a

  ⊑-refl : (a : ℕ) → a ⊑ a
  ⊑-refl a = ≤-refl

  ⊑-trans : (a b c : ℕ) → a ⊑ b → b ⊑ c → a ⊑ c
  ⊑-trans a b c ab bc = ≤-trans bc ab

  res : ℕ → ℕ
  res φ = K ∸ φ

  -- both directions are the same statement, once `+` is commuted
  galFwd : (a b : ℕ) → a ⊑ res b → b ⊑ res a
  galFwd a b h =
    ∸-adjʳ K a b (subst (K ≤_) (+-comm a b) (∸-adjˡ K b a h))

  galBwd : (a b : ℕ) → b ⊑ res a → a ⊑ res b
  galBwd a b h =
    ∸-adjʳ K b a (subst (K ≤_) (+-comm b a) (∸-adjˡ K a b h))

  -- and the whole closure theory follows with nothing re-proved
  open Galois _⊑_ _⊑_ ⊑-refl ⊑-trans ⊑-refl ⊑-trans res res galFwd galBwd
    public

------------------------------------------------------------------------
-- 3.  Under ℕ's own order it is false, and truncation is why
--
-- With `K = 0`, `φ = 0`, `ψ = 5`: `φ ≤ K ∸ ψ` holds (both are 0) and
-- `ψ ≤ K ∸ φ` does not.  So the naive reading — costs ordered upward —
-- does not even give one direction of the adjunction.
------------------------------------------------------------------------

naiveHolds : 0 ≤ (0 ∸ 5)
naiveHolds = zero-≤

naiveFails : ¬ (5 ≤ (0 ∸ 0))
naiveFails (k , e) = snotz (sym (+-comm k 5) ∙ e)

truncationBreaksTheNaiveOrder :
  (0 ≤ (0 ∸ 5)) × (¬ (5 ≤ (0 ∸ 0)))
truncationBreaksTheNaiveOrder = naiveHolds , naiveFails

------------------------------------------------------------------------
-- THE MEET, AND THE PROFILE CUT.  Both are in
-- `TheMeetIsMaxAndTheProfileCutIsAGaloisConnection`.
--
-- **The meet is `max`, not `min`.**  §2 here reverses ℕ's order because
-- lower cost is better; a meet in a reversed order is a JOIN in the
-- original, so `` over burdens is `max` in ℕ.  Writing "min-plus, so
-- take a min" names the operation by its role in the semiring rather
-- than by its role in the order — the same error §2's reversal guards
-- against, one level up.
--
--   max / max-≤ˡ / max-≤ʳ / max-least   the meet, with its universal
--                                       property
--   Profile ks                          profiles as a RECURSIVE FAMILY
--                                       over the kernel, so a length
--                                       mismatch is not representable
--   up ks φ = ⋀ᵢ (kᵢ ∸ φᵢ) ,  dn ks ψ = (kᵢ ∸ ψ)ᵢ
--   goFwd / goBwd                       both directions
--   ProfileCut                          `module Galois` instantiated
--
-- Profiles on BOTH sides:
-- `TheTwoSidedProfileCutNeedsTheBurdensAsAProfile` takes the
-- burdens as a profile so `UpP` produces a residual PROFILE;
-- `TheTwoSidedCutExistsOverANonEmptyResidualIndex` gives the
-- adjunction over a non-empty index; and
-- `TheTwoSidedCutNeedsNoInfinityBecauseTheEmptyMeetIsZero` removes the
-- restriction entirely, over an ARBITRARY residual index list with no
-- `∞` — the empty meet is `0` by ℕ's bottom rather than by choice.
------------------------------------------------------------------------
