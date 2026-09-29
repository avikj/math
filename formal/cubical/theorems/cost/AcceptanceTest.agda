{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- The acceptance test, as one checked term.
--
-- North Star (Vajra's proof-relevant compiler): adding ONE theorem makes
-- a task compile to a strictly better program, replayably — or the
-- theorem is an archive.  This module lands one complete instance.
--
-- Task.  Produce the canonical base-(2+k) digit word of m + n, given
-- that the checkpoint word `digitsC n` has already been computed.
--
-- Programs are DATA, not meta-level observations: `Plan` is a two-
-- constructor inductive type of execution plans, `cost` reads off the
-- number of carry-machine ticks a plan schedules, and `exec` runs it on
-- the already-checked positional-numeral machine.
--
--   restart m n : ignore the checkpoint; tick m + n times from the zero
--                 word.  Cost m + n.
--   resume  m n : resume the carry machine from the checkpoint word
--                 digitsC n for m further ticks.  Cost m.
--
-- The theorem `replay` is pinned to is T = `digitsC-resume`
-- (CountedComposition): digitsC (m + n) ≡ run (digitsC n) sucC m.  It is
-- not definitional: for variable m, `run` computes on the count and
-- `m + n` does not reduce past m's variable spine, so the two plans'
-- executions are not the same normal form and something must be proved.
--
-- `digitsC-resume` is itself three lines of
-- renaming over `CountedComposition.run-+`, and `replay-without-T`
-- below re-proves `replay` from `run-+` and `run-is-digitsC` without
-- mentioning T at all.  The
-- load-bearing input is `run-+`, counted time composes additively along
-- sequential execution, a three-line induction on the resumed segment.
-- The chain's structure is the result.
--
-- The closing term packages the acceptance test:
--
--   betterProgram m n :
--       (exec (resume m (suc n)) ≡ exec (restart m (suc n)))
--     × (cost (resume m (suc n)) < cost (restart m (suc n)))
--
-- i.e. on the whole nonempty range { (m , n′) : n′ = suc n } — every
-- input whose checkpoint holds at least one tick of prior work — the
-- resumed plan computes the SAME answer (replay) at STRICTLY smaller
-- counted cost.  Both components are closed proofs; nothing is measured.
-- The restriction to `suc n` is sharp, not an artefact:
-- `no-improvement-at-empty-checkpoint` shows the two costs are EQUAL at
-- n = 0.
--
------------------------------------------------------------------------

open import Cubical.Data.Nat using (ℕ)

module AcceptanceTest (k : ℕ) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero ; suc ; _+_ ; +-suc ; +-comm ; +-zero)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma using (_×_)

open import Digits k using (CanWord ; digitsC ; valueC)
open import Transport k using (sucC)
open import CountedExecution using (run)
open import CountedDigits k using (run-is-digitsC)
import CountedComposition
open CountedComposition using (run-+)
open CountedComposition.Odometer k
  using (digitsC-resume ; observe-resume)

------------------------------------------------------------------------
-- Programs as data.  Cost is intrinsic to the plan, not observed.
------------------------------------------------------------------------

data Plan : Type₀ where
  restart : (m n : ℕ) → Plan   -- naive: recount the full history from zero
  resume  : (m n : ℕ) → Plan   -- improved: resume from checkpoint digitsC n

-- The counted cost of a plan: how many sucC ticks it schedules.
cost : Plan → ℕ
cost (restart m n) = m + n
cost (resume  m n) = m

-- Executing a plan on the checked carry machine.
exec : Plan → CanWord
exec (restart m n) = run (digitsC zero) sucC (m + n)
exec (resume  m n) = run (digitsC n)    sucC m

------------------------------------------------------------------------
-- REPLAY.  The improved plan computes the same digit word.  The proof is
-- pinned to the one theorem T = digitsC-resume: it is the only edge in
-- the corpus from a checkpoint-seeded execution back to the zero-seeded
-- one.  `run-is-digitsC` merely renames the naive side.
------------------------------------------------------------------------

replay : (m n : ℕ) → exec (resume m n) ≡ exec (restart m n)
replay m n = sym (digitsC-resume m n)        -- T, the one added theorem
           ∙ sym (run-is-digitsC (m + n))

-- Sanity of the task itself: the shared answer decodes to m + n.
replay-observed : (m n : ℕ) → valueC (exec (resume m n)) ≡ m + n
replay-observed = observe-resume

-- `replay` re-proved without T: `run-+`
-- (counted time composes along sequential execution — the three-line
-- induction) plus the instantiation theorem, and no `digitsC-resume`.
-- `digitsC-resume` is itself exactly this composite in CountedComposition,
-- so what T contributes to the acceptance test is a name, not a step.
replay-without-T : (m n : ℕ) → exec (resume m n) ≡ exec (restart m n)
replay-without-T m n =
    cong (λ state → run state sucC m) (sym (run-is-digitsC n))
  ∙ sym (run-+ (digitsC zero) sucC m n)

------------------------------------------------------------------------
-- STRICTLY BETTER.  On every input with a nonempty checkpoint (n = suc
-- n′), the resumed plan is strictly cheaper: m < m + suc n′.  The
-- witness is closed-form — the gap is exactly the checkpointed prefix.
------------------------------------------------------------------------

resume-cheaper : (m n : ℕ) → cost (resume m (suc n)) < cost (restart m (suc n))
resume-cheaper m n =
  n , (+-suc n m ∙ cong suc (+-comm n m) ∙ sym (+-suc m n))

------------------------------------------------------------------------
-- WHAT `cost` IS, PINNED.  Three lemmas, all cheap, stated because the
-- prose above would otherwise be doing their work by eye.
--
--   `exec-runs-cost`  every plan executes as `cost p` ticks of `sucC`
--                     from a plan-determined seed.  DEFINITIONAL: this
--                     is `refl` on both constructors, so it certifies
--                     that `cost` was not chosen independently of
--                     `exec`, and nothing more.  It is not a work
--                     measure for `sucC` itself.
--   `cost-accounting` the saving is exactly the uncharged prefix.
--                     Also `refl`.
--   `no-improvement-at-empty-checkpoint`
--                     hence `betterProgram`'s restriction to `suc n` is
--                     SHARP: at n = 0 the two costs are equal, so the
--                     acceptance test is false there.
------------------------------------------------------------------------

seedOf : Plan → CanWord
seedOf (restart m n) = digitsC zero
seedOf (resume  m n) = digitsC n

exec-runs-cost : (p : Plan) → exec p ≡ run (seedOf p) sucC (cost p)
exec-runs-cost (restart m n) = refl
exec-runs-cost (resume  m n) = refl

cost-accounting : (m n : ℕ) → cost (resume m n) + n ≡ cost (restart m n)
cost-accounting m n = refl

no-improvement-at-empty-checkpoint :
  (m : ℕ) → cost (resume m zero) ≡ cost (restart m zero)
no-improvement-at-empty-checkpoint m = sym (+-zero m)

------------------------------------------------------------------------
-- The acceptance test as one term: same answer, strictly smaller cost,
-- for all m and all nonempty checkpoints suc n.
------------------------------------------------------------------------

betterProgram : (m n : ℕ)
  → (exec (resume m (suc n)) ≡ exec (restart m (suc n)))
  × (cost (resume m (suc n)) < cost (restart m (suc n)))
betterProgram m n = replay m (suc n) , resume-cheaper m n
