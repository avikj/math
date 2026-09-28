{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- WrongFirstStep
--
-- *** THIS FILE MUST FAIL TO TYPE-CHECK. ***
--
-- Designed annihilation (collab/PROTOCOL.md (absent from this repository) §7), in the pattern of
-- `NaturalMachine/Control/WrongEquivalence.agda`: the statement below is
-- FALSE, and the point of the file is to exhibit that the type-checker
-- catches it rather than waving it through.
--
-- WHAT IT ASSERTS.  `CompileBridge.first-step-names-resume` is `refl`:
-- on the concrete task `taskTm` over the concrete `baseVocab`, the
-- loop's own step function reduces to an obstruction whose residual is
-- `resumeCap`.  This file asserts the same thing at `tickCap` — a
-- capability that IS installed in `baseVocab`, so the first step cannot
-- name it.
--
-- WHY IT MUST FAIL.  `ResidualIs s V t (generative-step V t)` unfolds,
-- on this instance, to the equation `resumeCap ≡ s`, i.e. `0 ≡ 1` for
-- `s = tickCap`.  If `refl` inhabited `ResidualIs` for an ARBITRARY
-- capability, then G1's `refl` would be the empty kind of `refl` and
-- would certify nothing about which head the step named.  This control
-- is what rules that reading out: G1 is a computation with a specific
-- answer, not a type that any `refl` satisfies.
--
-- It is NOT part of the checked build.  `agda` does not
-- import it, and nothing else may: the directory
-- `NaturalMachine/Control/` is excluded from the root aggregate exactly
-- so that its contents are allowed to fail.
--
-- Under Agda 2.6.3 + cubical v0.5,
-- `agda NaturalMachine/Control/WrongFirstStep.agda`,
-- exit code 42, error verbatim:
--
--   /home/user/math/formal/cubical/NaturalMachine/Control/WrongFirstStep.agda:59,25-29
--   0 != 1 of type Agda.Builtin.Nat.Nat
--   when checking that the expression refl has type
--   ResidualIs tickCap baseVocab taskTm
--   (generative-step baseVocab taskTm)
--
-- If a future edit makes this file compile, `CompileBridge`'s §G1 is
-- vacuous and its claim that the FIRST step names the missing capability
-- is broken.
--
-- ---------------------------------------------------------------- --
-- TOOLCHAIN CAVEAT — THIS CONTROL NEEDS THE PIN.
--
-- A control's pass condition is not "agda exits nonzero".  It is "agda
-- rejects THIS file's statement, at THIS file's line, for the stated
-- reason".  Those come apart here, and only here among the controls.
--
-- This file reaches its own statement only under a toolchain in which
-- `GenerativeLoop` and `CompileBridge`
-- typecheck.  Neither `generative-step` nor §G of `CompileBridge` needs
-- a tactic, but `GenerativeLoop:194` carries
-- `import AcceptanceTest` for its §C `Compile` module,
-- `AcceptanceTest:99` imports `Transport`, and
-- `Transport:46` imports `Cubical.Tactics.NatSolver.Reflection` for
-- `solveℕ!`.  Under Agda 2.6.3 + cubical v0.7,
-- `Cubical/Tactics/Reflection.agda:92` does not scope-check at all
-- (`withReduceDefs` is an Agda 2.6.4 builtin), so this file exits 42
-- WITHOUT EVER LOOKING AT §Z.
--
-- THE TWIN.  `NaturalMachine/Control/WrongFirstStepNoTactic.agda` asserts
-- the identical false statement with the tactic path cut: it imports only
-- `Obstruction` and inlines, verbatim and with source line
-- ranges, the fragment of `GenerativeLoop` and `CompileBridge` §G that
-- the assertion runs through.  It carries a positive guard (the TRUE §G1
-- statement, checked first) so that a drifted copy fails at the guard
-- rather than passing itself off as this control.  It fails at its own
-- line, with `0 != 1`.
------------------------------------------------------------------------

module WrongFirstStep where

open import Cubical.Foundations.Prelude

open import GenerativeLoop using (generative-step)
open import CompileBridge
  using (ResidualIs ; tickCap ; baseVocab ; taskTm)

-- §Z.  THE FALSE CLAIM.  Under the pin this is rejected at line 104 with
-- `0 != 1 of type Agda.Builtin.Nat.Nat`.
wrong-step-names-tick :
  ResidualIs tickCap baseVocab taskTm (generative-step baseVocab taskTm)
wrong-step-names-tick = refl
