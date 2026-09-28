{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ReachableFromStart
--
-- The unreachability verdict of
-- `collab/messages/0533-codex-automata-adaptive-horizon-red-return.md` (absent from this repository)
-- WITH THE PREMISE IT LEANS ON MADE PART OF THE TYPE.
--
--
--   "In the declared four-state control, state `0` is fixed by both
--    actions, **so** states `1`, `2`, and `3` are unreachable from the
--    DFA start."
--
-- The audit's finding: being fixed by both actions makes `{0}` CLOSED;
-- unreachability of the rest follows only if the start state IS `0`.
-- The message never says so.  It is true —
-- `formal/lean/Pairfield/AdaptiveObservableHorizon.lean:80` reads
-- `start := 0`, which I re-read tonight rather than trusting the audit
-- — so the verdict stands on a premise the argument omits.  That is the
-- corpus's dominant genre: a false ground under a true verdict, with NO
-- LEXICAL SIGNATURE.  Nothing in the sentence is a wrong word; a clause
-- is simply not there, and grep cannot see a clause that is not there.
--
-- THE MODEL.  `S` is the Lean module's `Fin 4` with its `step`
-- transcribed by hand from `AdaptiveObservableHorizon.lean:73-75`:
-- `false` sends `1` to the sink `3`, `true` sends `2` to `3`, every
-- other pair is fixed.  This is a transcription, not a port: no claim is
-- made here about the Lean file's build status, and `run` over `List
-- Bool` replaces Mathlib's `DFA.eval`.
--
-- HEADLINE TERMS
--   s0-fixed             the premise the message DOES state
--   closed-from-s0       the conclusion, for runs that start at s0
--   closed-from-start    the theorem with `start ≡ s0` IN THE TYPE
--   escape-from-s1       one action leaves the closed set from s1
--   dropped-premise-false  so the start-free reading implies ⊥
--
-- The companion control is
-- `NaturalMachine/Control/ReachabilityWithoutStart.agda`, which asserts
-- `closed-from-start` with the premise deleted and MUST FAIL.
------------------------------------------------------------------------

module ReachableFromStart where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)

------------------------------------------------------------------------
-- 0.  The four-state control, transcribed.

data S : Type where
  s0 s1 s2 s3 : S

step : S → Bool → S
step s0 _     = s0
step s1 false = s3
step s1 true  = s1
step s2 false = s2
step s2 true  = s3
step s3 _     = s3

run : S → List Bool → S
run st []       = st
run st (a ∷ w)  = run (step st a) w

------------------------------------------------------------------------
-- 1.  The premise the message states, and what it alone gives.

s0-fixed : (a : Bool) → step s0 a ≡ s0
s0-fixed true  = refl
s0-fixed false = refl

closed-from-s0 : (w : List Bool) → run s0 w ≡ s0
closed-from-s0 []       = refl
closed-from-s0 (a ∷ w)  = cong (λ t → run t w) (s0-fixed a) ∙ closed-from-s0 w

------------------------------------------------------------------------
-- 2.  The verdict, with the missing premise carried in the type.

closed-from-start : (st : S) → st ≡ s0 → (w : List Bool) → run st w ≡ s0
closed-from-start st start≡s0 w =
  cong (λ t → run t w) start≡s0 ∙ closed-from-s0 w

------------------------------------------------------------------------
-- 3.  The premise is load-bearing: without it the conclusion is FALSE.

isSink : S → Bool
isSink s3 = true
isSink _  = false

s3≢s0 : s3 ≡ s0 → ⊥
s3≢s0 p = true≢false (cong isSink p)

escape-from-s1 : run s1 (false ∷ []) ≡ s3
escape-from-s1 = refl

dropped-premise-false : ((st : S) (w : List Bool) → run st w ≡ s0) → ⊥
dropped-premise-false claim = s3≢s0 (sym escape-from-s1 ∙ claim s1 (false ∷ []))
