{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ReachabilityWithoutStart
--
-- *** THIS FILE MUST FAIL TO TYPE-CHECK. ***
--
-- Designed annihilation (collab/PROTOCOL.md (absent from this repository) §7), in the pattern of
-- `Control/QuantifierDrop.agda`, `Control/InflationFlattened.agda` and
-- `Control/MaximizerWithoutNonvanishing.agda`.
--
-- `collab/messages/0533-codex-automata-adaptive-horizon-red-return.md` (absent from this repository)
-- argues "state `0` is fixed by both actions, **so** states `1`, `2`,
-- `3` are unreachable from the DFA start" — without the premise
-- `start = 0`.  Asserted below: the conclusion of
-- `ReachableFromStart.closed-from-start` with its
-- `st ≡ s0` argument deleted, exactly as the sentence deletes it.
--
-- WHY IT MUST FAIL.  Closure of `{0}` is a statement about the
-- transition function; unreachability is a statement about the pair
-- (transition function, start).  Delete the second and the claim is not
-- merely unproved but false: `run s1 (false ∷ []) ≡ s3`
-- (`escape-from-s1`), and `dropped-premise-false` in the companion
-- module derives ⊥ from precisely the type asserted here.
--
-- This instruments a defect with NO LEXICAL SIGNATURE.  The message's
-- sentence contains no wrong word — it contains one fewer clause than
-- its "so" requires — so no grep can find it, and a type can.
--
-- It is NOT part of the checked build.  `agda` does not
-- import it, and nothing else may: `NaturalMachine/Control/` is
-- excluded from the root aggregate exactly so its contents may fail.
--
-- Under the pin (Agda 2.8.0 + cubical v0.9),
-- `LC_ALL=C.UTF-8 agda --library-file=<v0.9>
-- NaturalMachine/Control/ReachabilityWithoutStart.agda`, exit code 42,
-- error verbatim:
--
--   NaturalMachine/Control/ReachabilityWithoutStart.agda:65.50-54:
--   error: [UnequalTerms]
--   st != s0 of type S
--   when checking that the expression refl has type st ≡ s0
--
-- Read it: what the theorem still wants, and what the shortened
-- sentence does not supply, is `st ≡ s0` — the start-state premise,
-- named by the machine, in the position where the message deleted it.
--
-- If a future edit makes this file compile, the unreachability verdict
-- has been silently extended to every start state and the corpus has
-- readmitted exactly the defect FULL_READ_DRAW_6 §B1 catalogued.
------------------------------------------------------------------------

module ReachabilityWithoutStart where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.List using (List)

open import ReachableFromStart
  using (S ; s0 ; run ; closed-from-start)

closed-without-start : (st : S) (w : List Bool) → run st w ≡ s0
closed-without-start st w = closed-from-start st refl w
