{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- MaximizerWithoutNonvanishing
--
-- *** THIS FILE MUST FAIL TO TYPE-CHECK. ***
--
-- Designed annihilation (collab/PROTOCOL.md (absent from this repository) §7), in the pattern of
-- `Control/WrongEquivalence.agda`, `Control/WrongFirstStep.agda`,
-- `Control/QuantifierDrop.agda` and `Control/InflationFlattened.agda`.
--
-- §2 -- "every finite `E` **with `f != 0` on `E`** has a point that
-- fails to transport: any point maximizing `v_p(f)`" -- WITHOUT the
-- nonvanishing clause, which is how the summary message
-- `workers/20260812T090934.276887Z--claude_ananta--0005.md` (absent from this repository) §3 restates
-- it: "every finite `E` has a point that cannot transport -- any
--
-- WHY IT MUST FAIL.  The dropped clause is what makes "the maximizer"
-- denote.  On the model of `FiniteWorldMaximizer` the
-- degenerate world `f = 0` on `E` has no point at which the observable
-- fails to vanish, hence no maximizer at all
-- (`vanishing-world-has-no-maximizer`), and
-- `dropped-hypothesis-false` derives ⊥ from precisely the type asserted
-- below.
--
-- The two assertions are the two ways the drop happens in prose:
-- (a) state the conclusion for every world, discharging it with the
-- theorem that still wants the clause; (b) claim the clause is free --
-- that even the vanishing world satisfies it.
--
-- This is the instrument for a defect with NO LEXICAL SIGNATURE: the
-- shortened sentence contains no wrong word, only a missing clause, so
-- grep cannot see it and a type can.
--
-- It is NOT part of the checked build.  `agda` does not
-- import it, and nothing else may: the directory
-- `NaturalMachine/Control/` is excluded from the root aggregate exactly
-- so its contents may fail.
--
-- Under Agda 2.6.3 + cubical v0.5,
-- `LC_ALL=C.UTF-8 agda NaturalMachine/Control/MaximizerWithoutNonvanishing.agda`,
-- exit code 42, error verbatim:
--
--   /home/user/math/formal/cubical/NaturalMachine/Control/MaximizerWithoutNonvanishing.agda:84,23-34
--   NonVanishing W → Σ-syntax Pt (MaxAt W) !=< Σ Pt (MaxAt W)
--   when checking that the expression maximizer W has type
--   Σ-syntax Pt (MaxAt W)
--
-- Read it: what `maximizer W` still wants, and what the asserted type
-- does not supply, is `NonVanishing W` — the dropped clause "`f != 0`
-- on `E`", named by the machine, in the position where the summary
-- deleted it.
--
-- If a future edit makes this file compile, the finite no-go has been
-- silently extended past its nonvanishing hypothesis and the corpus has
-- readmitted exactly the defect `FULL_READ_DRAW_5` §C1 catalogued.
------------------------------------------------------------------------

module MaximizerWithoutNonvanishing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Data.Unit using (tt)

open import FiniteWorldMaximizer
  using (World ; Pt ; MaxAt ; NonVanishing ; maximizer ; vanishing-world)

-- (a) The theorem stated for every world, discharged with the theorem
--     that still wants the clause.
maximizer-dropped : (W : World) → Σ[ m ∈ Pt ] MaxAt W m
maximizer-dropped W = maximizer W

-- (b) The clause claimed to be free.
every-world-nonvanishing : NonVanishing vanishing-world
every-world-nonvanishing q = tt
