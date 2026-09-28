{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FailClosedForgetsOnlyTheReasonForDistrust
--
-- `interactive/KernelProbe.hs` (absent from this repository) collapses two distinct situations into one
-- verdict on purpose — "absence and failure share the same grade,
-- fail-closed" — and grades CAPABILITY, not soundness.  The collapse is
-- exactly one-sided, and this says in which direction:
--
--   * the TRUSTING verdict determines the state completely;
--   * the DISTRUSTING verdict determines nothing beyond "not that".
--
-- So a fail-closed summary is free on the side you act on and total loss
-- on the side you do not.  That is what makes it the right shape for a
-- guard and the wrong shape for a diagnosis.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THE SHELF SAYS
--
-- It probes with two modules — a builtin-only `2 + 2 ≡ 4` under
-- `--no-libraries`, and the same under `--cubical` — and prints
-- `KERNEL-PROBE agda=… refl=… cubical=…`, exiting 0 iff refl-capable and
-- 2 otherwise, "absence and failure share the same grade".  Its own
-- limit, in its own words: *"it grades capability, not soundness.  A
-- passing probe says 'this kernel checks this class of module'; it
-- certifies nothing about the axioms of any registered library."*
--
-- ────────────────────────────────────────────────────────────────────
-- HOW THIS DIFFERS FROM `AFigureWithoutItsInputDecidesNothing`
--
-- `AFigureWithoutItsInputDecidesNothing` also ends in a one-sided test:
-- a mismatch refutes, a match establishes nothing.  The two are NOT the
-- same finding.  There the loss was accidental — an INPUT the reader
-- happens not to have.  Here the loss is DELIBERATE and in the OUTPUT —
-- the verdict is coarsened on purpose so that an ungraded kernel cannot
-- be trusted.  Same shape of one-sidedness, different cause, and the
-- design consequences are opposite: the first wants the input published,
-- the second wants the collapse kept.
------------------------------------------------------------------------

module FailClosedForgetsOnlyTheReasonForDistrust where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  The three situations the probe can be in, and the two-valued
--     verdict it emits
------------------------------------------------------------------------

data KernelState : Type where
  absent    : KernelState   -- agda not on PATH
  incapable : KernelState   -- present, refl probe fails
  capable   : KernelState   -- present, refl probe passes

-- fail-closed: only the third is trusted, and the first two are graded
-- alike ON PURPOSE
trusted : KernelState → Bool
trusted absent    = false
trusted incapable = false
trusted capable   = true

------------------------------------------------------------------------
-- 2.  The trusting side loses nothing
------------------------------------------------------------------------

trustDeterminesTheState :
  (s : KernelState) → trusted s ≡ true → s ≡ capable
trustDeterminesTheState absent    p = Cubical.Data.Empty.rec (false≢true p)
trustDeterminesTheState incapable p = Cubical.Data.Empty.rec (false≢true p)
trustDeterminesTheState capable   _ = refl

------------------------------------------------------------------------
-- 3.  The distrusting side loses everything except "not capable"
------------------------------------------------------------------------

private
  isAbsent : KernelState → Type
  isAbsent absent    = Unit
  isAbsent incapable = ⊥
  isAbsent capable   = ⊥

absent≢incapable : ¬ (absent ≡ incapable)
absent≢incapable p = transport (cong isAbsent p) tt

distrustForgetsTheReason :
  Σ[ s ∈ KernelState ] Σ[ t ∈ KernelState ]
    ((¬ (s ≡ t)) × (trusted s ≡ trusted t))
distrustForgetsTheReason = absent , incapable , absent≢incapable , refl

-- and what distrust DOES determine, which is exactly one thing
distrustDeterminesOnlyNotCapable :
  (s : KernelState) → trusted s ≡ false → ¬ (s ≡ capable)
distrustDeterminesOnlyNotCapable s p q =
  false≢true (sym p ∙ cong trusted q)

------------------------------------------------------------------------
-- 4.  The reading
--
-- §2 and §3 together are the precise content of "fail-closed": the map
-- to the verdict is injective over `true` and two-to-one over `false`.
-- A guard consumes only the `true` fibre, so it loses nothing it uses; a
-- reader diagnosing a red probe consumes the `false` fibre, and there
-- the verdict alone cannot distinguish a missing compiler from a broken
-- one.  Which is why the shelf prints `agda=<version|ABSENT>` on the
-- SAME line as the grade: the reason for distrust is carried beside the
-- verdict, not inside it.
--
------------------------------------------------------------------------
