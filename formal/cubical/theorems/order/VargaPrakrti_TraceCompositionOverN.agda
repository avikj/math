{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- VargaPrakrti_TraceBhavanaOverN — भावना और चक्रवाल with the middle
-- coefficient carried, over ℕ, subtraction-free.
--
-- वर्ग-प्रकृति ("square-nature") is BRAHMAGUPTA's own name, in the
-- Brhmasphuasiddhnta (628), ch. 18, for the object of his composition
-- rule.  He composes x² − D y² with arbitrary kepa, which is T = 0
-- below.  The parameter T is not his; it is what
-- the composition becomes in ℤ[ω] with ω² = T·ω + C, and it is introduced
-- here because restricting the reactor to T = 0 was restricting Brahmagupta's
-- rule to the one equation that later displaced it. The identities below at T
-- = 0 ARE his, and that specialisation is exhibited at the bottom of this
-- file as a checked term rather than asserted.
--
-- THE FORM.   N(x, y) = x² + T·x·y − C·y²,  Δ = T² + 4C.
--
--   T = 0, C = D  is  x² − D y²  — Brahmagupta's, and `Nalanda.hs` (absent from this repository)'s.
--   T = 1, C = (Δ−1)/4  is the principal form of a discriminant
--                Δ ≡ 1 (mod 4), i.e. the norm form of the MAXIMAL order
--                ℤ[(1+√Δ)/2], which contains ℤ[√Δ] with index 2 and which
--                x² − D y² = 1 cannot see.
--
-- WHY ℕ AND WHY SUBTRACTION-FREE.
-- `BhavanaSemiring.agda` (absent from this repository): bhvan as classically written
-- is FALSE over ℕ because monus truncates, and moving every negative term
-- across makes it true with no hypothesis and makes it a commutative-
-- SEMIRING identity — no induction, no ordering, no case split on a sign.
-- `CakravalaNat.agda`: the same move applied to the cycle, which is what
-- removed the sign of k as an obstacle rather than handling it.  And the
-- hard constraint underneath both: cubical's ℤ multiplication is unary
-- (`pos (suc n) · m = m + pos n · m`), so a `refl` on the nine- and
-- fifteen-digit integers these runs produce asks the kernel for ~10¹⁸
-- unfoldings and never returns, while cubical's ℕ is `Agda.Builtin.Nat`
-- with GMP-backed `_+_` and `_·_` and is instant.
--
-- HOW THE SUBTRACTION IS CLEARED, so the statements can be read.  Write
-- Qᵢ = xᵢ² + T·xᵢyᵢ, so that N(xᵢ, yᵢ) = Qᵢ − C·yᵢ².  Then over ℤ
--
--     N(X, Y) = N(x₁,y₁)·N(x₂,y₂)
--
-- expands to  (X² + T·XY) − C·Y² = (Q₁ − Cy₁²)(Q₂ − Cy₂²), and carrying
-- every negative term across gives the statement below, in which nothing
-- is subtracted anywhere.  Over ℤ it IS bhāvanā, by adding the same two
-- terms to both sides.
--
-- WHAT IS PROVED HERE.  --safe, no postulates, no holes.
--
--   compositionTraceℕ     the composition law with the middle coefficient,
--                     for ALL naturals T C x₁ y₁ x₂ y₂.
--   cakravalaTraceℕ   the cycle's step — composition with the
--                     interpolator (m, 1) — for ALL naturals T C a b m.
--   vpXIsBrahmagupta / vpYIsBrahmagupta
--                     at T = 0 the two composed coordinates ARE
--                     `BhavanaSemiring.cx` and `.cy`, checked, so the
--                     generalisation demonstrably contains the source's
--                     own statement rather than replacing it.
--
------------------------------------------------------------------------

module VargaPrakrti_TraceCompositionOverN where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; _+_ ; _·_)
open import Cubical.Tactics.NatSolver using (solveℕ!)

------------------------------------------------------------------------
-- BRAHMAGUPTA'S TWO COORDINATES, TRANSCRIBED RATHER THAN IMPORTED.
--
-- `BhavanaSemiring.agda` (absent from this repository) defines exactly `cx` and `cy` below and this file
-- would import them.  It cannot: `BhavanaSemiring.agda` (absent from this repository), `CakravalaNat
-- .agda` and `Brahmagupta.agda` DO NOT CHECK under the toolchain
-- `BUILD.md` (absent from this repository) pins (Agda 2.8.0, cubical v0.9).  They call
-- `Cubical.Tactics.NatSolver.Reflection.solve`, the point-free solver of
-- cubical v0.5, which v0.9 replaced with the hole macro `solveℕ!`.  The
-- error is `[NotInScope] solve`, reproducible in one command:
--
--     cd formal/cubical && agda BhavanaSemiring.agda (absent from this repository)
--
-- This file stands alone: the two coordinates below
-- are transcribed verbatim from `BhavanaSemiring.agda` (absent from this repository) so that the
-- containment claim — that the generalisation at T = 0 IS Brahmagupta's
-- statement — is a checked term here.
------------------------------------------------------------------------

cx : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
cx D x₁ y₁ x₂ y₂ = x₁ · x₂ + D · (y₁ · y₂)

cy : ℕ → ℕ → ℕ → ℕ → ℕ
cy x₁ y₁ x₂ y₂ = x₁ · y₂ + x₂ · y₁

------------------------------------------------------------------------
-- The composed coordinates in ℤ[ω], ω² = T·ω + C.
--
--   (x₁ + y₁ω)(x₂ + y₂ω) = (x₁x₂ + C y₁y₂) + (x₁y₂ + x₂y₁ + T y₁y₂) ω
--
-- The T·y₁y₂ term is the entire difference from Brahmagupta's rule, and
-- it is the term a reactor hard-coded to x² − D y² cannot represent.
------------------------------------------------------------------------

vpX : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
vpX C x₁ y₁ x₂ y₂ = x₁ · x₂ + C · (y₁ · y₂)

vpY : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
vpY T x₁ y₁ x₂ y₂ = x₁ · y₂ + (x₂ · y₁ + T · (y₁ · y₂))

-- Qᵢ = xᵢ² + T·xᵢyᵢ, the subtraction-free half of the norm:
-- N(x, y) = Q(x, y) − C·y².
vpQ : ℕ → ℕ → ℕ → ℕ
vpQ T x y = x · x + T · (x · y)

------------------------------------------------------------------------
-- BHĀVANĀ WITH THE MIDDLE COEFFICIENT, over ℕ, subtraction-free.
--
-- Read it as N(X,Y) = N₁·N₂ with every negative term carried across.
-- `solve` discharges it: after expansion both sides are the same
-- monomials, so it holds in ANY commutative semiring and needs no
-- induction, no ordering, and no subtraction.
------------------------------------------------------------------------

compositionTraceℕ
  : (T C x₁ y₁ x₂ y₂ : ℕ)
  → vpX C x₁ y₁ x₂ y₂ · vpX C x₁ y₁ x₂ y₂
      + (T · (vpX C x₁ y₁ x₂ y₂ · vpY T x₁ y₁ x₂ y₂)
         + (C · (vpQ T x₁ y₁ · (y₂ · y₂)) + C · (vpQ T x₂ y₂ · (y₁ · y₁))))
  ≡ vpQ T x₁ y₁ · vpQ T x₂ y₂
      + (C · C · (y₁ · y₁ · (y₂ · y₂))
         + C · (vpY T x₁ y₁ x₂ y₂ · vpY T x₁ y₁ x₂ y₂))
compositionTraceℕ T C x₁ y₁ x₂ y₂ = solveℕ!

------------------------------------------------------------------------
-- THE CYCLE'S STEP, over ℕ, subtraction-free.
--
-- The cakravla composes the current pair (a, b) with the interpolator
-- (m, 1), whose norm is m² + T·m − C.  Specialising the law above at
-- (x₂, y₂) = (m, 1) gives the step's identity, stated in the shape a run
-- can instantiate turn by turn.
--
--   X = a·m + C·b      Y = a + (b·m + T·b)      Q₂ = m² + T·m
--
-- Note what this is NOT: it is not `refl`.  A `refl` per turn would show
-- only that a generator's arithmetic agrees with the kernel's.  This is
-- the law firing.
------------------------------------------------------------------------

vpStepX : ℕ → ℕ → ℕ → ℕ → ℕ
vpStepX C a b m = a · m + C · b

vpStepY : ℕ → ℕ → ℕ → ℕ → ℕ
vpStepY T a b m = a + (b · m + T · b)

cakravalaTraceℕ
  : (T C a b m : ℕ)
  → vpStepX C a b m · vpStepX C a b m
      + (T · (vpStepX C a b m · vpStepY T a b m)
         + (C · vpQ T a b + C · ((m · m + T · m) · (b · b))))
  ≡ vpQ T a b · (m · m + T · m)
      + (C · C · (b · b) + C · (vpStepY T a b m · vpStepY T a b m))
cakravalaTraceℕ T C a b m = solveℕ!

------------------------------------------------------------------------
-- AT T = 0 THE COORDINATES ARE BRAHMAGUPTA'S, CHECKED.
--
-- `BhavanaSemiring.cx` and `.cy` are his two composed coordinates as that
-- file states them.  The point of exhibiting this rather than asserting
-- it: a generalisation that quietly replaced the source's statement with
-- a near neighbour would look identical in prose.
------------------------------------------------------------------------

vpXIsBrahmagupta : (C x₁ y₁ x₂ y₂ : ℕ)
                 → vpX C x₁ y₁ x₂ y₂ ≡ cx C x₁ y₁ x₂ y₂
vpXIsBrahmagupta C x₁ y₁ x₂ y₂ = refl

vpYIsBrahmagupta : (x₁ y₁ x₂ y₂ : ℕ)
                 → vpY 0 x₁ y₁ x₂ y₂ ≡ cy x₁ y₁ x₂ y₂
vpYIsBrahmagupta x₁ y₁ x₂ y₂ = solveℕ!

-- and at T = 0 the subtraction-free half of the norm is just x².
vpQIsSquare : (x y : ℕ) → vpQ 0 x y ≡ x · x
vpQIsSquare x y = solveℕ!

------------------------------------------------------------------------
-- THE CONTAINMENT, AS A CHECKED TERM.
--
-- The statement below is `BhavanaSemiring.bhavanaℕ` verbatim — Brahmagupta's
-- composition law over ℕ as this repository already states it.  It is NOT
-- proved here by calling the solver again, which would show only that both
-- are semiring identities and would leave the generalisation and the source
-- as two unrelated true things.  It is `transport`ed out of
-- `compositionTraceℕ 0 D x₁ y₁ x₂ y₂` along the two coordinate equalities
-- above.  So: the general law AT T = 0 IS his law, and the kernel says so.
--
-- The `0 · (X · Y) +` summand of the general statement disappears
-- definitionally at T = 0, because ℕ's builtin `_·_` reduces `zero · m` to
-- `zero` and `_+_` reduces `zero + w` to `w`.  Only `vpQ 0 x y = x · x + 0`
-- and `vpY 0 = cy` need the transport, since `_+_` recurses on its FIRST
-- argument and `x + 0` is therefore not definitionally `x`.
------------------------------------------------------------------------

brahmaguptaIsTheTraceZeroCase
  : (D x₁ y₁ x₂ y₂ : ℕ)
  → cx D x₁ y₁ x₂ y₂ · cx D x₁ y₁ x₂ y₂
      + (D · (x₁ · x₁ · (y₂ · y₂)) + D · (x₂ · x₂ · (y₁ · y₁)))
  ≡ x₁ · x₁ · (x₂ · x₂)
      + (D · D · (y₁ · y₁ · (y₂ · y₂))
         + D · (cy x₁ y₁ x₂ y₂ · cy x₁ y₁ x₂ y₂))
brahmaguptaIsTheTraceZeroCase D x₁ y₁ x₂ y₂ =
  transport
    (λ i → cx D x₁ y₁ x₂ y₂ · cx D x₁ y₁ x₂ y₂
             + (D · (vpQIsSquare x₁ y₁ i · (y₂ · y₂))
                + D · (vpQIsSquare x₂ y₂ i · (y₁ · y₁)))
         ≡ vpQIsSquare x₁ y₁ i · vpQIsSquare x₂ y₂ i
             + (D · D · (y₁ · y₁ · (y₂ · y₂))
                + D · (vpYIsBrahmagupta x₁ y₁ x₂ y₂ i
                       · vpYIsBrahmagupta x₁ y₁ x₂ y₂ i)))
    (compositionTraceℕ 0 D x₁ y₁ x₂ y₂)

------------------------------------------------------------------------
-- and the same for the CYCLE: `CakravalaNat.ca` and `.cb` are the T = 0
-- interpolator coordinates.
------------------------------------------------------------------------

ca : ℕ → ℕ → ℕ → ℕ → ℕ
ca D a b m = a · m + D · b

cb : ℕ → ℕ → ℕ → ℕ
cb a b m = a + b · m

vpStepXIsCa : (D a b m : ℕ) → vpStepX D a b m ≡ ca D a b m
vpStepXIsCa D a b m = refl

vpStepYIsCb : (a b m : ℕ) → vpStepY 0 a b m ≡ cb a b m
vpStepYIsCb a b m = solveℕ!

-- `CakravalaNat.cakravalaℕ` verbatim, transported out of the general step.
cakravalaIsTheTraceZeroCase
  : (D a b m : ℕ)
  → ca D a b m · ca D a b m + (D · (a · a) + D · (b · b · (m · m)))
  ≡ a · a · (m · m) + (D · D · (b · b) + D · (cb a b m · cb a b m))
cakravalaIsTheTraceZeroCase D a b m =
  transport
    (λ i → ca D a b m · ca D a b m
             + (D · vpQIsSquare a b i + D · (mulFlip i))
         ≡ vpQIsSquare a b i · (sqFlip i)
             + (D · D · (b · b)
                + D · (vpStepYIsCb a b m i · vpStepYIsCb a b m i)))
    (cakravalaTraceℕ 0 D a b m)
  where
    -- (m · m + 0 · m) · (b · b) ≡ b · b · (m · m)  and  m · m + 0 · m ≡ m · m
    mulFlip : (m · m + 0 · m) · (b · b) ≡ b · b · (m · m)
    mulFlip = solveℕ!
    sqFlip : (m · m + 0 · m) ≡ m · m
    sqFlip = solveℕ!
