{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- WrongFirstStepNoTactic
--
-- *** THIS FILE MUST FAIL TO TYPE-CHECK. ***
-- *** AND IT MUST FAIL AT ITS OWN LAST LINE, NOT EARLIER. ***
--
-- This is the tactic-free twin of
-- `NaturalMachine/Control/WrongFirstStep.agda`.  It asserts the SAME
-- false statement, over the SAME computation, and exists for one reason:
-- in a container whose cubical library cannot itself be typechecked, the
-- original control cannot reach its own statement, so it stops being a
-- control.
--
-- ---------------------------------------------------------------- --
-- WHY A TWIN EXISTS.
--
-- `WrongFirstStep.agda` imports `GenerativeLoop` (for
-- `generative-step`) and `CompileBridge` (for
-- `ResidualIs`, `tickCap`, `baseVocab`, `taskTm`).  Neither of those
-- names needs a tactic.  But `GenerativeLoop` line 194 carries
--
--     import AcceptanceTest
--
-- for its §C `Compile` module, `AcceptanceTest` line 99 imports
-- `Transport`, and `Transport` line 46 imports
--
--     open import Cubical.Tactics.NatSolver.Reflection using (solveℕ!)
--
-- for two arithmetic lemmas (`ripple-lem1`, `ripple-lem2`).  Under Agda
-- 2.6.3 with cubical v0.7, `Cubical/Tactics/Reflection.agda:92` does not
-- scope-check: it uses `withReduceDefs`, which entered
-- `Agda.Builtin.Reflection` in Agda 2.6.4.  (cubical v0.7 is released
--
-- So in such a container `WrongFirstStep.agda` exits 42 — the correct
-- exit code — having never looked at its own last line.  An exit code
-- cannot tell that apart from a control doing its job.  Every other file
-- in `NaturalMachine/Control/` fails inside itself, at the line that
-- carries its false claim; that one did not, and a control that fails for
-- the wrong reason is not being tested.
--
-- The dependency is genuinely spurious: nothing on the path from
-- `generative-step` or from §G of `CompileBridge` touches `solveℕ!`.  It
-- is dragged in by a sibling section of a module that must be checked as
-- a whole.  This file cuts it by importing only
-- `Obstruction` — which typechecks in both toolchains —
-- and inlining, VERBATIM, the fragment of `GenerativeLoop` and of
-- `CompileBridge` §G that the assertion actually runs through.
--
-- ---------------------------------------------------------------- --
-- WHAT IT ASSERTS, AND WHY IT MUST FAIL.  Unchanged from the twin.
--
-- `CompileBridge.first-step-names-resume` is `refl`: on the concrete task
-- `taskTm` over the concrete `baseVocab`, the loop's own step function
-- reduces to an obstruction whose residual is `resumeCap`.  The last line
-- below asserts the same thing at `tickCap` — a capability that IS
-- installed in `baseVocab`, so the first step cannot name it.
--
-- `ResidualIs s V t (generative-step V t)` unfolds, on this instance, to
-- `resumeCap ≡ s`, i.e. `0 ≡ 1` for `s = tickCap`.  If `refl` inhabited
-- `ResidualIs` for an ARBITRARY capability, then G1's `refl` would be the
-- empty kind of `refl` and would certify nothing about which head the
-- step named.  This control is what rules that reading out: G1 is a
-- computation with a specific answer, not a type that any `refl`
-- satisfies.
--
-- ---------------------------------------------------------------- --
-- HOW THE COPY IS KEPT HONEST.  Two devices, because a copied definition
-- is a definition that can drift.
--
--  (1) THE POSITIVE GUARD, §Z1 below.  Before the false claim, this file
--      states the TRUE one — `first-step-names-resume` itself, verbatim
--      from `CompileBridge:820-822` — and proves it by `refl`.  Agda
--      reports the first type error and stops.  So the pass condition of
--      this file is not "it fails"; it is "it fails AT §Z2 AND NOT AT
--      §Z1".  An error at §Z1 means the inlined copy no longer computes
--      what the original computes, and the control must be repaired
--      rather than believed.  A copy that drifts in any way that changes
--      the residual is therefore caught, and a drift that does not change
--      the residual is not a drift this control cares about.
--
--  (2) Every inlined block below names its source file and line range at
--      the time of copying, so the copy is diffable rather than merely
--      asserted.  Nothing was edited except the removal of comment prose.
--
-- The twin `WrongFirstStep.agda` remains the primary control and is
-- unchanged in substance: under the pinned toolchain it runs against the
-- real `GenerativeLoop` and the real `CompileBridge` with no copy at all.
-- Run BOTH under the pin.  This file is what can be run without it.
--
-- ---------------------------------------------------------------- --
-- OBSERVED, 2026-08-15, Agda 2.6.3 + cubical v0.7 (this container),
-- `agda NaturalMachine/Control/WrongFirstStepNoTactic.agda`,
-- exit code 42, error verbatim and entire:
--
--   /home/user/math/formal/cubical/NaturalMachine/Control/WrongFirstStepNoTactic.agda:314,25-29
--   0 != 1 of type ℕ
--   when checking that the expression refl has type
--   ResidualIs tickCap baseVocab taskTm
--   (generative-step baseVocab taskTm)
--
-- That is the same equation, `0 != 1`, that the twin reported under Agda
-- 2.6.3 + cubical v0.5 at its own line 59.
--
-- It is NOT part of the checked build.  `agda` does not
-- import it, and nothing else may: the directory `NaturalMachine/Control/`
-- is excluded from the root aggregate exactly so that its contents are
-- allowed to fail.  `scripts/check-agda-closure.sh` (absent from this repository) enforces that.
------------------------------------------------------------------------

module WrongFirstStepNoTactic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-suc ; +-assoc ; +-comm)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_ ; dichotomyBool)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)

open import ObstructionSubstrate
open Obstruction

------------------------------------------------------------------------
-- INLINED §1.  NaturalMachine/GenerativeLoop.agda:274-288 — the measure.
-- Verbatim; the section comment is dropped.
------------------------------------------------------------------------

delta : Vocab → Shape → ℕ
delta V c = if memb c V then 0 else 1

deficit : Vocab → Tm → ℕ
deficit V var        = 0
deficit V (node c u) = delta V c + deficit V u

gapAt : Shape → Vocab → Shape → ℕ
gapAt s V c = if eqℕ c s then delta V c else 0

gaps : Shape → Vocab → Tm → ℕ
gaps s V var        = 0
gaps s V (node c u) = gapAt s V c + gaps s V u

------------------------------------------------------------------------
-- INLINED §2.  NaturalMachine/GenerativeLoop.agda:318-368 — B1, the
-- measure splits exactly when one head is installed.  Verbatim.
------------------------------------------------------------------------

private
  if-const : {A : Type₀} (b : Bool) (x : A) → (if b then x else x) ≡ x
  if-const true  x = refl
  if-const false x = refl

  shuffle : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  shuffle a b c d =
      sym (+-assoc a b (c + d))
    ∙ cong (a +_) (+-assoc b c d)
    ∙ cong (λ z → a + (z + d)) (+-comm b c)
    ∙ cong (a +_) (sym (+-assoc c b d))
    ∙ +-assoc a c (b + d)

delta-split : (s : Shape) (V : Vocab) (c : Shape)
            → delta V c ≡ gapAt s V c + delta (s ∷ V) c
delta-split s V c = covered? (dichotomyBool (memb c V))
  where
  -- membership in the extended vocabulary, unfolded by definition
  ext-true  : eqℕ c s ≡ true → memb c (s ∷ V) ≡ true
  ext-true  e = if≡true {x = true} {y = memb c V} e

  ext-false : eqℕ c s ≡ false → memb c (s ∷ V) ≡ memb c V
  ext-false e = if≡false {x = true} {y = memb c V} e

  covered? : (memb c V ≡ true) ⊎ (memb c V ≡ false)
           → delta V c ≡ gapAt s V c + delta (s ∷ V) c
  covered? (inl e) =
      if≡true e
    ∙ sym ( cong₂ _+_
              ( cong (λ z → if eqℕ c s then z else 0) (if≡true e)
              ∙ if-const (eqℕ c s) 0 )
              (if≡true (memb-mono c s V e)) )
  covered? (inr e) = same? (dichotomyBool (eqℕ c s))
    where
    same? : (eqℕ c s ≡ true) ⊎ (eqℕ c s ≡ false)
          → delta V c ≡ gapAt s V c + delta (s ∷ V) c
    same? (inl q) =
        if≡false e
      ∙ sym ( cong₂ _+_
                ( cong (λ z → if z then delta V c else 0) q ∙ if≡false e )
                (if≡true (ext-true q)) )
    same? (inr q) =
        if≡false e
      ∙ sym ( cong₂ _+_
                (cong (λ z → if z then delta V c else 0) q)
                (if≡false (ext-false q ∙ e)) )

deficit-split : (s : Shape) (V : Vocab) (t : Tm)
              → deficit V t ≡ gaps s V t + deficit (s ∷ V) t
deficit-split s V var        = refl
deficit-split s V (node c u) =
    cong₂ _+_ (delta-split s V c) (deficit-split s V u)
  ∙ shuffle (gapAt s V c) (delta (s ∷ V) c) (gaps s V u) (deficit (s ∷ V) u)

------------------------------------------------------------------------
-- INLINED §3.  NaturalMachine/GenerativeLoop.agda:381-390 — B2,
-- occurrence and the strict decrease.  Verbatim.
------------------------------------------------------------------------

Occurs : Shape → Vocab → Tm → Type₀
Occurs s V t = Σ[ j ∈ ℕ ] gaps s V t ≡ suc j

occurs→decreases : (s : Shape) (V : Vocab) (t : Tm) → Occurs s V t
                 → deficit (s ∷ V) t < deficit V t
occurs→decreases s V t (j , p) =
  j , ( +-suc j (deficit (s ∷ V) t)
      ∙ cong (_+ deficit (s ∷ V) t) (sym p)
      ∙ sym (deficit-split s V t) )

------------------------------------------------------------------------
-- INLINED §4.  NaturalMachine/GenerativeLoop.agda:410-444 — the probe
-- and THE STEP FUNCTION.  Verbatim.  This is the computation the whole
-- control is about: `probe` searches innermost-first, and `read` relabels
-- its answer without touching the residual.
------------------------------------------------------------------------

data Probe (V : Vocab) (t : Tm) : Type₀ where
  covered : Over V t → Probe V t
  gap     : (o : Obstruction V) → Occurs (residual o) V t → Probe V t

probe : (V : Vocab) (t : Tm) → Probe V t
probe V var        = covered tt
probe V (node c u) = lift-probe (probe V u)
  where
  lift-probe : Probe V u → Probe V (node c u)
  lift-probe (gap o (j , p)) =
    gap o ( gapAt (residual o) V c + j
          , cong (gapAt (residual o) V c +_) p
            ∙ +-suc (gapAt (residual o) V c) j )
  lift-probe (covered ou) = here? (dichotomyBool (memb c V))
    where
    here? : (memb c V ≡ true) ⊎ (memb c V ≡ false) → Probe V (node c u)
    here? (inl e) = covered (e , ou)
    here? (inr e) =
      gap (record { residual = c    ; arg     = u  ; argBase     = ou
                  ; failed   = e    ; witness = var ; witnessBase = tt })
          ( gaps c V u
          , cong (_+ gaps c V u) (if≡true (eqℕ-refl c) ∙ if≡false e) )

generative-step : (V : Vocab) (t : Tm)
  → Over V t ⊎ (Σ[ o ∈ Obstruction V ] (deficit (extend V o) t < deficit V t))
generative-step V t = read (probe V t)
  where
  read : Probe V t
       → Over V t ⊎ (Σ[ o ∈ Obstruction V ] (deficit (extend V o) t < deficit V t))
  read (covered h)  = inl h
  read (gap o occ)  = inr (o , occurs→decreases (residual o) V t occ)

------------------------------------------------------------------------
-- INLINED §5.  NaturalMachine/CompileBridge.agda:779-816 — §G, the
-- concrete task and the reading of a step result.  Verbatim.
--
--   resumeCap  "resume the odometer from a checkpoint word"  (missing)
--   tickCap    "advance the odometer one tick"               (installed)
--   readCap    "read the digit word"                         (installed)
------------------------------------------------------------------------

resumeCap tickCap readCap : Shape
resumeCap = 0
tickCap   = 1
readCap   = 2

baseVocab : Vocab
baseVocab = tickCap ∷ readCap ∷ []

taskTm : Tm
taskTm = node resumeCap (node tickCap (node readCap var))

StepResult : Vocab → Tm → Type₀
StepResult V t =
  Over V t ⊎ (Σ[ o ∈ Obstruction V ] (deficit (extend V o) t < deficit V t))

ResidualIs : (s : Shape) (V : Vocab) (t : Tm) → StepResult V t → Type₀
ResidualIs s V t (inl _)       = ⊥
ResidualIs s V t (inr (o , _)) = residual o ≡ s

------------------------------------------------------------------------
-- Z1.  THE POSITIVE GUARD.  This is `CompileBridge.first-step-names-resume`
-- (CompileBridge.agda:820-822) verbatim, over the inlined copies.  It is
-- TRUE and MUST typecheck.
--
-- If the checker's first error is at this declaration, the inlined copy
-- above has drifted from the modules it was copied from and this control
-- is testing nothing.  Repair the copy; do not relabel the failure.
------------------------------------------------------------------------

guard-first-step-names-resume :
  ResidualIs resumeCap baseVocab taskTm (generative-step baseVocab taskTm)
guard-first-step-names-resume = refl

------------------------------------------------------------------------
-- Z2.  THE FALSE CLAIM.  Identical to `WrongFirstStep.agda:57-59`.
-- `tickCap` IS installed in `baseVocab`, so the first step cannot name
-- it, and this `refl` must be rejected with `0 != 1`.
--
-- If a future edit makes this line compile, `CompileBridge`'s §G1 is
-- vacuous and its claim that the FIRST step names the missing capability
-- is broken.
------------------------------------------------------------------------

wrong-step-names-tick :
  ResidualIs tickCap baseVocab taskTm (generative-step baseVocab taskTm)
wrong-step-names-tick = refl
