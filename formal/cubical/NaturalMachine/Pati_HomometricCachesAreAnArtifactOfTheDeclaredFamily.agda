{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Pati_HomometricCachesAreAnArtifactOfTheDeclaredFamily
--
-- पाटी (pāṭī) — the working board.
--
--
--   Śrīdhara, *Pāṭīgaṇita* — also *Bṛhat-Pāṭī*, also *Navaśatī* ("having
--   900", for its 900 stanzas, of which 251 are extant).  rdhara is
--   dated 8th–9th century; the dating is disputed and MacTutor gives
--   870–930, so no single year is asserted here.  The same genre runs on
--   through Bhskara II's *Llvat* (1150).
--
--   *P* is the board — and is itself a non- loanword, which
--   is worth saying in a repository whose file-naming rule asks for the
--   source language rather than for  specifically.  Calculation
--   was done on dust or sand spread over that board, the operation
--   called *dhlikarma*, dust-work.  A quantity is SET DOWN, used, and
--   then WIPED so the space can carry the next quantity.  What survives
--   a step is what the operator chose to leave on the board; what is
--   wiped is gone, whatever its mathematical existence.
--
--   That erase-or-retain choice is the stated hypothesis of this
--   repository's addition-chain cache lane, put plainest at
--   notes/ADDITION_CHAIN_PROCESS_MEMORY.md (absent from this repository) §4 ("The persistence
--   boundary": if the runtime discards every intermediate, both
--   histories become (6,{6}) and no probe separates them).
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS CHECKED HERE
--
--   notes/FLEET_BREAKER_PASS_2026_08_14.md (absent from this repository) §6.4 refutes the
--   recommendation of notes/EXACT_PREDICTIVE_QUANTUM_MEMORY_NO_GO.md (absent from this repository) §5
--   ("compile exact cache histories to their profile quotient") by
--   exhibiting a HOMOMETRIC PAIR: two caches, both reachable from {1},
--   with equal distance profiles on the declared family T = {11}, which
--   one exogenous control drives apart.
--
--   Here it is computed rather than asserted.  d_C(t) is the least
--   number of adjoin-a-sum steps until t is in the cache; every bound
--   below is a finite Bool computation closed by refl.
--
--     C = {1,2,4,6}   reached by  1+1, 2+2, 2+4     (legality checked)
--     D = {1,2,3,4}   reached by  1+1, 1+2, 1+3     (legality checked)
--
--     d_C(11) = 2 = d_D(11)                          homometric at {11}
--     u₁₀ C = C ∪ {10},  d(11) = 1                   control fires on C
--     u₁₀ D = D,          d(11) = 2                   control inert on D
--
--   And one thing §6.4 does not say, which is the reason the witness
--   had to look like that:
--
--     d_C(3) = 1  while  d_D(3) = 0
--
--   so the family T = {3,11} separates the pair with NO control at all.
--   The general statement, proved in the companion note:
--
--     if C △ D ⊆ T then Δ_T(C) = Δ_T(D) implies C = D,
--
--   because d_X(t) = 0 exactly when t ∈ X.  So every homometric pair of
--   caches has a separating element OUTSIDE the declared family, and
--   the nontriviality of the profile quotient is a statement about T
--   alone, never about the dynamics.  Both sides are instantiated
--   below: T = {11} where homometry holds, T = {3,11} where it fails.
------------------------------------------------------------------------

module NaturalMachine.Pati_HomometricCachesAreAnArtifactOfTheDeclaredFamily where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_×_ ; _,_)

------------------------------------------------------------------------
-- 1.  Decidable membership on a board

eqN : ℕ → ℕ → Bool
eqN zero    zero    = true
eqN zero    (suc _) = false
eqN (suc _) zero    = false
eqN (suc m) (suc n) = eqN m n

infix 6 _∈?_
_∈?_ : ℕ → List ℕ → Bool
x ∈? []       = false
x ∈? (y ∷ ys) = if eqN x y then true else (x ∈? ys)

------------------------------------------------------------------------
-- 2.  The transition rule: adjoin one sum of two values already on the
--     board.  `oneStep C` lists every value adjoinable in one step.

addAll : ℕ → List ℕ → List ℕ
addAll x []       = []
addAll x (y ∷ ys) = (x + y) ∷ addAll x ys

sumsFrom : List ℕ → List ℕ → List ℕ
sumsFrom []       C = []
sumsFrom (x ∷ xs) C = addAll x C ++ sumsFrom xs C

oneStep : List ℕ → List ℕ
oneStep C = sumsFrom C C

twoStepFrom : List ℕ → List ℕ → List ℕ
twoStepFrom []       C = []
twoStepFrom (z ∷ zs) C = oneStep (z ∷ C) ++ twoStepFrom zs C

twoStep : List ℕ → List ℕ
twoStep C = twoStepFrom (oneStep C) C

------------------------------------------------------------------------
-- 3.  Legality.  A board is a cache only if it was actually formed from
--     {1}: every operand of every step must already be present when the
--     step is taken.  This is the non-vacuity control — an unreachable
--     pair of sets would refute nothing about caches.

Step : Type₀
Step = ℕ × ℕ

legal : List Step → List ℕ → Bool
legal []             C = true
legal ((x , y) ∷ ss) C =
  if x ∈? C
    then (if y ∈? C then legal ss ((x + y) ∷ C) else false)
    else false

run : List Step → List ℕ → List ℕ
run []             C = C
run ((x , y) ∷ ss) C = run ss ((x + y) ∷ C)

seed : List ℕ
seed = 1 ∷ []

------------------------------------------------------------------------
-- 4.  The two boards of FLEET_BREAKER_PASS §6.4

chainC : List Step
chainC = (1 , 1) ∷ (2 , 2) ∷ (2 , 4) ∷ []

chainD : List Step
chainD = (1 , 1) ∷ (1 , 2) ∷ (1 , 3) ∷ []

C : List ℕ
C = 6 ∷ 4 ∷ 2 ∷ 1 ∷ []

D : List ℕ
D = 4 ∷ 3 ∷ 2 ∷ 1 ∷ []

-- 4.1  Both are legally formed from the seed.

C-legal : legal chainC seed ≡ true
C-legal = refl

C-forms : run chainC seed ≡ C
C-forms = refl

D-legal : legal chainD seed ≡ true
D-legal = refl

D-forms : run chainD seed ≡ D
D-forms = refl

-- 4.2  They are distinct boards, and 3 is one separating value.

three-off-C : 3 ∈? C ≡ false
three-off-C = refl

three-on-D : 3 ∈? D ≡ true
three-on-D = refl

------------------------------------------------------------------------
-- 5.  d_C(11) = 2 = d_D(11).  Each distance is pinned from both sides:
--     not 0, not 1, and achieved in 2.

C-11-not-0 : 11 ∈? C ≡ false
C-11-not-0 = refl

C-11-not-1 : 11 ∈? oneStep C ≡ false
C-11-not-1 = refl

C-11-in-2 : 11 ∈? twoStep C ≡ true
C-11-in-2 = refl

D-11-not-0 : 11 ∈? D ≡ false
D-11-not-0 = refl

D-11-not-1 : 11 ∈? oneStep D ≡ false
D-11-not-1 = refl

D-11-in-2 : 11 ∈? twoStep D ≡ true
D-11-in-2 = refl

------------------------------------------------------------------------
-- 6.  The control u₁₀ : X ↦ X ∪ {10} if 10 ∈ X + X.  It fires on C and
--     is inert on D, and it drives the profiles apart.

ten-adjoinable-to-C : 10 ∈? oneStep C ≡ true
ten-adjoinable-to-C = refl

ten-not-adjoinable-to-D : 10 ∈? oneStep D ≡ false
ten-not-adjoinable-to-D = refl

uC : List ℕ
uC = 10 ∷ C

uC-11-not-0 : 11 ∈? uC ≡ false
uC-11-not-0 = refl

uC-11-in-1 : 11 ∈? oneStep uC ≡ true
uC-11-in-1 = refl

-- u₁₀ D = D, so §5's D-facts already give d_{u₁₀D}(11) = 2.
-- Hence 1 = d_{u₁₀C}(11) ≠ d_{u₁₀D}(11) = 2: the profile quotient at
-- T = {11} is not a congruence for this control.

------------------------------------------------------------------------
-- 7.  The other side, which §6.4 does not state.  Enlarging the declared
--     family to contain a member of C △ D separates the pair outright,
--     with no control applied.

C-3-not-0 : 3 ∈? C ≡ false
C-3-not-0 = refl

C-3-in-1 : 3 ∈? oneStep C ≡ true
C-3-in-1 = refl

D-3-in-0 : 3 ∈? D ≡ true
D-3-in-0 = refl

-- So d_C(3) = 1 and d_D(3) = 0: Δ_{3,11}(C) = (1,2) ≠ (0,2) = Δ_{3,11}(D).
-- The homometry of §6.4 exists only because 3 and 6, the whole of
-- C △ D, lie outside T = {11}.

six-off-D : 6 ∈? D ≡ false
six-off-D = refl

six-on-C : 6 ∈? C ≡ true
six-on-C = refl

------------------------------------------------------------------------
-- 8.  CONTROLS.  Everything above is `refl` on a Bool, so every negative
--     result is worth exactly what the enumerator is worth: if `oneStep`
--     returned [] then `11 ∈? oneStep C ≡ false` would hold and mean
--     nothing.  These fix that.

-- 8.1  `oneStep` is not empty and not truncated: it reaches the extremes
--      of C + C from both ends, and reports the two values (9, 11) that
--      genuinely are not sums of two members of C.

oneStep-C-has-2 : 2 ∈? oneStep C ≡ true       -- 1 + 1, the minimum
oneStep-C-has-2 = refl

oneStep-C-has-12 : 12 ∈? oneStep C ≡ true     -- 6 + 6, the maximum
oneStep-C-has-12 = refl

oneStep-C-has-7 : 7 ∈? oneStep C ≡ true       -- 1 + 6, a cross term
oneStep-C-has-7 = refl

oneStep-C-lacks-9 : 9 ∈? oneStep C ≡ false    -- 9 is genuinely not in C + C
oneStep-C-lacks-9 = refl

oneStep-D-has-8 : 8 ∈? oneStep D ≡ true       -- 4 + 4, the maximum
oneStep-D-has-8 = refl

-- 8.2  `twoStep` likewise: it reaches strictly past `oneStep`, and stops
--      where two steps must stop (max 2·max(C + C) = 24).

twoStep-C-has-9 : 9 ∈? twoStep C ≡ true       -- 3 = 1+2, then 3 + 6
twoStep-C-has-9 = refl

twoStep-C-has-24 : 24 ∈? twoStep C ≡ true     -- 12 = 6+6, then 12 + 12
twoStep-C-has-24 = refl

twoStep-C-lacks-25 : 25 ∈? twoStep C ≡ false  -- out of reach in two steps
twoStep-C-lacks-25 = refl

-- 8.3  `legal` actually rejects.  This chain asks for 3 + 3 when the
--      board holds only {1,2}; if `legal` accepted it, the legality
--      claims in §4.1 would be certifying nothing.

illegalChain : List Step
illegalChain = (1 , 1) ∷ (3 , 3) ∷ []

illegal-is-rejected : legal illegalChain seed ≡ false
illegal-is-rejected = refl

-- 8.4  And `legal` rejects on the second operand too, not only the first.

illegalChain₂ : List Step
illegalChain₂ = (1 , 1) ∷ (2 , 5) ∷ []

illegal₂-is-rejected : legal illegalChain₂ seed ≡ false
illegal₂-is-rejected = refl
