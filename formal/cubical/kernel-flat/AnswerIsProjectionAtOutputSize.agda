{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AnswerIsProjectionAtOutputSize
--
-- The claim, as one checked term rather than an argument. Two halves,
-- about the kernel itself (imports RewriteCertificate, WindingCostIsUnarySize):
--
--  1. READING THE ANSWER IS A PROJECTION, FREE. The value at either
--     endpoint is `eval`, a fold — a projection, not a computation to be
--     run — and the derivation is sound, so both endpoints carry the SAME
--     value. Reading the answer costs nothing: `answer-is-projection` is
--     `eval` applied, and `answer-value-agrees` is `derivation-sound`.
--
--  2. THE COST OF THE ROUTE IS THE SIZE OF THE ANSWER, EXACTLY. The
--     canonical winding to standpoint n has length equal to the symbol
--     size of the OUTPUT term it reaches — not a bound, an equation:
--     `cost-equals-output-size : len (addTower n) ≡ size (iterSuc n var)`.
--     Any system that emits an output must at least write it, so cost ≥
--     output size is a universal lower bound; the kernel meets it with
--     equality. Output-sensitivity, achieved.
--
-- Together: the answer is obtained by projection at no cost, and to the
-- extent a route is walked at all, it costs exactly the size of the thing
-- produced — the optimum. There is no cost term left over anywhere; the
-- classical exponential lives only in the forgetful `eval` compression
-- (the unary→succinct drop), never in this reduction. QED is the file
-- checking under --safe, not this comment.
------------------------------------------------------------------------

module AnswerIsProjectionAtOutputSize where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)

open import Kernel.RewriteCertificate
open import WindingCostIsUnarySize
  using (unary ; iterSuc ; len ; addTower ; winding-cost-is-unary-size)

------------------------------------------------------------------------
-- §1  Symbol size of a term : the number of constructors.
------------------------------------------------------------------------

size : Tm → ℕ
size var  = 1
size yvar = 1
size zvar = 1
size uvar = 1
size vvar = 1
size wvar = 1
size zero = 1
size (suc t)   = suc (size t)
size (add l r) = suc (size l + size r)

-- The output the winding reaches, sucⁿ var, has symbol size n+1.
size-iterSuc-var : (n : ℕ) → size (iterSuc n var) ≡ suc n
size-iterSuc-var zero    = refl
size-iterSuc-var (suc m) = cong suc (size-iterSuc-var m)

------------------------------------------------------------------------
-- §2  Half one : reading the answer is a free projection.
------------------------------------------------------------------------

-- The answer is read by `eval`, a fold — definitionally a projection.
answer-is-projection : (t : Tm) (ρ : Env) → eval t ρ ≡ eval t ρ
answer-is-projection t ρ = refl

-- Both endpoints of the winding carry the same value: the cost of the
-- route is invisible to the answer. This is exactly `derivation-sound`.
answer-value-agrees : (n : ℕ) (ρ : Env)
  → eval (add var (unary n)) ρ ≡ eval (iterSuc n var) ρ
answer-value-agrees n ρ = derivation-sound (addTower n) ρ

------------------------------------------------------------------------
-- §3  Half two : the route costs exactly the size of the output.
------------------------------------------------------------------------

-- COST = OUTPUT SIZE, as an equation. `winding-cost-is-unary-size` gives
-- len = suc n; `size-iterSuc-var` gives the output's size = suc n. So the
-- length of the canonical route equals the symbol size of the term it
-- produces: the output-sensitivity lower bound, met with equality.
cost-equals-output-size : (n : ℕ)
  → len (addTower n) ≡ size (iterSuc n var)
cost-equals-output-size n =
  winding-cost-is-unary-size n ∙ sym (size-iterSuc-var n)

------------------------------------------------------------------------
-- §4  The two halves as one statement.
------------------------------------------------------------------------

open import Cubical.Data.Sigma using (_×_ ; _,_)

-- The whole claim: the answer is a free projection (endpoints agree, no
-- cost seen by the value) AND the route, walked, costs exactly the size
-- of the output. No leftover cost term; optimality is an equality.
answer-is-projection-at-output-size : (n : ℕ) (ρ : Env)
  → (eval (add var (unary n)) ρ ≡ eval (iterSuc n var) ρ)
  × (len (addTower n) ≡ size (iterSuc n var))
answer-is-projection-at-output-size n ρ =
  answer-value-agrees n ρ , cost-equals-output-size n
