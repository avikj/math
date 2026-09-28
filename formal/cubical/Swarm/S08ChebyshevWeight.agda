{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S08ChebyshevWeight
--
-- THE GRADING THAT SATISFACTION CANNOT SEE.
--
-- `runtime/panini/cakravala.py` (absent from this repository) verifies every Pell solution by
-- substitution and says, in its own docstring, that this is the failure
-- such a check *cannot* see: "the answer is true and wrong" -- a pair
-- (x,y) with x^2 - D y^2 = 1 that is not the fundamental solution.  Its
-- shipped screen `is_bhavana_square` catches only the case where the
-- offender is a bhavana SQUARE.
--
-- The reason it can only catch squares is exact, and it is the content
-- of this module.  The solutions form a group under Brahmagupta's
-- bhavana, and the FIRST COORDINATE of the n-th power depends on n and
-- on the first coordinate of the base alone:
--
--     fst (delta ^ n)  =  T n (fst delta)      whenever N(delta) = 1
--
-- with T n the Chebyshev polynomial of the first kind.  D and the second
-- coordinate drop out completely.  So the index n -- the WEIGHT -- is
-- readable off x by inverting a one-variable integer polynomial, and
-- `is_bhavana_square` is exactly the n = 2 member of that family:
--
--     T 2 u = 2u^2 - 1    <=>    u^2 = (x+1)/2      (the shipped test)
--     T 3 u = 4u^3 - 3u                            (missed: see below)
--
-- The certified escape is D = 3, delta = (2,1), delta^3 = (26,15):
-- 26^2 - 3*15^2 = 1, so substitution accepts it, and 26 + 1 = 27 is odd,
-- so the shipped square screen returns False.  It has weight 3, and no
-- test graded by 2 can see it.
--
-- Contents
--   bhavana-norm        Brahmagupta's samasa-bhavana is norm-multiplicative
--   trace-is-Chebyshev  fst (delta ^ n) = T n (fst delta) for N = 1  [object]
--   T2                  the graded piece the shipped screen implements
--   witness-*           the D = 3 weight-3 escape, by computation
--
-- Toolchain note.  The CommRingSolver in this checkout misreads a bare
-- `1r` or `0r` in the RIGHT operand of `_·_` and after `-_` (it parses
-- both as the zero of the algebra expression).  Every solver lemma below
-- therefore keeps literals in the left operand, or generalizes the
-- literal to a variable and instantiates -- the workaround recorded in
-- Rank1DihedralChart's header.
------------------------------------------------------------------------

module Swarm.S08ChebyshevWeight where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

open CommRingStr (ℤCommRing .snd)

R : Type
R = fst ℤCommRing

-- ---------------------------------------------------------------------
-- the quadratic order Z[sqrt D], its norm, Brahmagupta's composition
-- ---------------------------------------------------------------------

-- (a , b) denotes a + b*sqrt(D)
Sol : Type
Sol = R × R

-- samasa-bhavana (Brahmagupta, 628 CE): multiplication in Z[sqrt D]
mulS : R → Sol → Sol → Sol
mulS D (a , b) (c , d) = (a · c + D · (b · d) , a · d + b · c)

N : R → Sol → R
N D (a , b) = a · a - D · (b · b)

-- ---------------------------------------------------------------------
-- Brahmagupta's identity: the composition is norm-multiplicative
-- ---------------------------------------------------------------------

private
  bhavana-raw : (D a b c d : R)
    →   (a · c + D · (b · d)) · (a · c + D · (b · d))
      - D · ((a · d + b · c) · (a · d + b · c))
    ≡ (a · a - D · (b · b)) · (c · c - D · (d · d))
  bhavana-raw _ _ _ _ _ = solve! ℤCommRing

bhavana-norm : (D : R) (p q : Sol) → N D (mulS D p q) ≡ N D p · N D q
bhavana-norm D (a , b) (c , d) = bhavana-raw D a b c d

-- ---------------------------------------------------------------------
-- powers in the solution group, and the Chebyshev polynomials
-- ---------------------------------------------------------------------

pow : R → Sol → ℕ → Sol
pow D δ zero    = (1r , 0r)
pow D δ (suc n) = mulS D (pow D δ n) δ

-- T n, first kind:  T 0 = 1, T 1 = u, T (n+2) = 2u * T (n+1) - T n
T : R → ℕ → R
T u zero          = 1r
T u (suc zero)    = u
T u (suc (suc n)) = ((1r + 1r) · u) · T u (suc n) - T u n

-- ---------------------------------------------------------------------
-- the three ring lemmas the induction needs
-- ---------------------------------------------------------------------

private
  one-step : (D u v : R) → 1r · u + D · (0r · v) ≡ u
  one-step _ _ _ = solve! ℤCommRing

  -- The whole content, with the defect displayed rather than assumed:
  -- the Chebyshev recurrence holds for ANY norm, up to the factor
  -- (u*u - D*v*v) multiplying the previous trace.  Setting that factor
  -- to 1 is exactly the hypothesis N = 1, and nothing else is used.
  step-raw : (D u v x y : R)
    →   (x · u + D · (y · v)) · u + D · ((x · v + y · u) · v)
    ≡   ((1r + 1r) · u) · (x · u + D · (y · v)) - (u · u - D · (v · v)) · x
  step-raw _ _ _ _ _ = solve! ℤCommRing

  sub1 : (a x : R) → a - 1r · x ≡ a - x
  sub1 _ _ = solve! ℤCommRing

  step : (D u v x y : R) → (u · u - D · (v · v) ≡ 1r)
    →   (x · u + D · (y · v)) · u + D · ((x · v + y · u) · v)
    ≡   ((1r + 1r) · u) · (x · u + D · (y · v)) - x
  step D u v x y h =
      step-raw D u v x y
    ∙ cong (λ z → ((1r + 1r) · u) · (x · u + D · (y · v)) - z · x) h
    ∙ sub1 (((1r + 1r) · u) · (x · u + D · (y · v))) x

-- ---------------------------------------------------------------------
-- THE THEOREM
--
--   For a norm-one delta = (u,v), the first coordinate of delta^n is
--   T n (u).  The index n is therefore a function of the first
--   coordinate alone: a WEIGHT, readable without knowing D or v.
--
--   This is what makes fundamentality decidable without search, and it
--   is what a substitution check can never supply: x^2 - D y^2 = 1 is
--   invariant under the whole group, so it is weight-blind by
--   construction.
-- ---------------------------------------------------------------------

private
  both : (D u v : R) → (N D (u , v) ≡ 1r) → (n : ℕ)
       → (fst (pow D (u , v) n) ≡ T u n)
       × (fst (pow D (u , v) (suc n)) ≡ T u (suc n))
  both D u v h zero    = refl , one-step D u v
  both D u v h (suc n) =
    let ih = both D u v h n
        x  = fst (pow D (u , v) n)
        y  = snd (pow D (u , v) n)
    in  snd ih
      , ( step D u v x y h
        ∙ cong₂ (λ a b → ((1r + 1r) · u) · a - b) (snd ih) (fst ih) )

trace-is-Chebyshev : (D u v : R) → (N D (u , v) ≡ 1r) → (n : ℕ)
                   → fst (pow D (u , v) n) ≡ T u n
trace-is-Chebyshev D u v h n = fst (both D u v h n)

-- ---------------------------------------------------------------------
-- the graded piece the shipped Python screen implements
-- ---------------------------------------------------------------------

private
  T2gen : (e u : R) → ((e + e) · u) · u - e ≡ (e + e) · (u · u) - e
  T2gen _ _ = solve! ℤCommRing

-- T 2 u = 2u^2 - 1.  `is_bhavana_square` solves this for u, i.e. tests
-- whether (x+1)/2 is a perfect square: it is the weight-2 test and only
-- the weight-2 test.
T2 : (u : R) → T u 2 ≡ (1r + 1r) · (u · u) - 1r
T2 u = T2gen 1r u

-- ---------------------------------------------------------------------
-- the certified escape:  D = 3, delta = (2,1), delta^3 = (26,15)
--
--   * both are genuine solutions -- substitution accepts both;
--   * (26,15) is the CUBE of (2,1), hence not fundamental;
--   * 26 = T 3 (2), and 26 is not in the image of T 2 over Z
--     (T 2 u = 26 forces 2u^2 = 27, impossible by parity), which is
--     precisely why `is_bhavana_square(3, 26, 15)` returns False:
--     its first guard is `(x + 1) % 2`, and 27 is odd.
-- ---------------------------------------------------------------------

D3 : R
D3 = pos 3

witness-base-norm : N D3 (pos 2 , pos 1) ≡ 1r
witness-base-norm = refl

witness-cube : pow D3 (pos 2 , pos 1) 3 ≡ (pos 26 , pos 15)
witness-cube = refl

witness-cube-norm : N D3 (pos 26 , pos 15) ≡ 1r
witness-cube-norm = refl

-- the weight is visible in the first coordinate alone: no D, no v
witness-weight : T (pos 2) 3 ≡ pos 26
witness-weight = refl

-- and it is exactly an instance of the theorem
witness-is-instance : fst (pow D3 (pos 2 , pos 1) 3) ≡ T (pos 2) 3
witness-is-instance = trace-is-Chebyshev D3 (pos 2) (pos 1) witness-base-norm 3
