{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- EGBDetConservation
--
-- The determinant conservation law det(PQ) = det(P) · det(Q) in its
-- cleanest sector: upper-triangular 2×2 matrices over ℕ.
--
-- An upper-triangular 2×2 matrix  [[a,b],[0,d]]  is carried by the
-- triple (a, b, d).  In this sector:
--
--   * multiplication is subtraction-free:
--       [[a,b],[0,d]] · [[a',b'],[0,d']]
--         = [[a·a', a·b' + b·d'], [0, d·d']]
--   * the determinant is subtraction-free:  det = a·d
--   * the conservation law is pure ℕ algebra:
--       detConserve : detUT (mulUT p q) ≡ detUT p · detUT q
--
-- We check more than the bare equation: (UT, mulUT, ut 1 0 1) is a
-- MONOID (associativity + both identity laws, all closed by the
-- NatSolver reflection tactic), (ℕ, ·, 1) is a monoid, and detUT is a
-- MONOID MORPHISM between them (detHom below, in the sense of
-- Cubical.Algebra.Monoid.IsMonoidHom: presε = refl, pres· =
-- detConserve).  Conservation is not an isolated identity; it is
-- functoriality of det on this sector.
--
-- THE FULL 2×2 CONTRAST (why the sector restriction matters).
-- For a full matrix [[a,b],[c,d]] the determinant is a·d − b·c: it
-- NEEDS subtraction, so over the rig ℕ (no additive inverses) "det"
-- of a full matrix is not even defined — a·d − b·c is not an ℕ-term.
-- The upper-triangular witness explains the
-- sector choice: with c = 0 the would-be subtracted term b·c is
-- b · 0 ≡ 0 (crossTermVanishes below), so the ℤ-determinant,
-- restricted to the sector, collapses to the subtraction-free a·d
-- and the whole conservation law lives inside ℕ.  The sector
-- restriction is exactly what makes the law subtraction-free.
------------------------------------------------------------------------

module EGBDetConservation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSetRetract; isSet×)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Algebra.Monoid
-- Cubical.Tactics.NatSolver.Reflection exports neither `solve` nor
-- `natSolve`: its line 34 is `open EqualityToNormalform renaming (solve to
-- natSolve)` WITHOUT `public`, so both names stop at that module's boundary.
-- The public entry point is the macro `solveℕ!`, re-exported by
-- Cubical.Tactics.NatSolver, and the library's own Examples.agda (absent from this repository) gives the
-- idiom: the macro fills the goal, so the variables must be bound on the
-- left-hand side.
open import Cubical.Tactics.NatSolver using (solveℕ!)

------------------------------------------------------------------------
-- The carrier: upper-triangular 2×2 matrices over ℕ

record UT : Type where
  constructor ut
  field
    a b d : ℕ   -- [[ a , b ],
                --  [ 0 , d ]]

open UT

-- Paths in UT from componentwise paths.
utPath : {p q : UT} → a p ≡ a q → b p ≡ b q → d p ≡ d q → p ≡ q
utPath pa pb pd i = ut (pa i) (pb i) (pd i)

-- UT is a set (retract of ℕ × ℕ × ℕ).
isSetUT : isSet UT
isSetUT = isSetRetract
  (λ p → a p , b p , d p) (λ (x , y , z) → ut x y z) (λ _ → refl)
  (isSet× isSetℕ (isSet× isSetℕ isSetℕ))

------------------------------------------------------------------------
-- (a) Multiplication and determinant, both subtraction-free

mulUT : UT → UT → UT
mulUT (ut a₀ b₀ d₀) (ut a₁ b₁ d₁) =
  ut (a₀ · a₁) (a₀ · b₁ + b₀ · d₁) (d₀ · d₁)

detUT : UT → ℕ
detUT (ut a₀ _ d₀) = a₀ · d₀

idUT : UT
idUT = ut 1 0 1

------------------------------------------------------------------------
-- (b) THE CONSERVATION LAW: det(PQ) = det(P) · det(Q)

private
  -- (a·a')·(d·d') ≡ (a·d)·(a'·d'): the middle-four interchange for ·.
  interchange : (x y z w : ℕ) → (x · y) · (z · w) ≡ (x · z) · (y · w)
  interchange x y z w = solveℕ!

detConserve : (p q : UT) → detUT (mulUT p q) ≡ detUT p · detUT q
detConserve (ut a₀ _ d₀) (ut a₁ _ d₁) = interchange a₀ a₁ d₀ d₁

------------------------------------------------------------------------
-- (c) (UT, mulUT, idUT) is a monoid and detUT is a monoid morphism

private
  assocA : (x y z : ℕ) → x · (y · z) ≡ (x · y) · z
  assocA x y z = solveℕ!

  assocB : (a₀ b₀ a₁ b₁ d₁ b₂ d₂ : ℕ)
         → a₀ · (a₁ · b₂ + b₁ · d₂) + b₀ · (d₁ · d₂)
         ≡ (a₀ · a₁) · b₂ + (a₀ · b₁ + b₀ · d₁) · d₂
  assocB a₀ b₀ a₁ b₁ d₁ b₂ d₂ = solveℕ!

  idRa : (x : ℕ) → x · 1 ≡ x
  idRa x = solveℕ!

  idRb : (x y : ℕ) → x · 0 + y · 1 ≡ y
  idRb x y = solveℕ!

  idLa : (x : ℕ) → 1 · x ≡ x
  idLa x = solveℕ!

  idLb : (x y : ℕ) → 1 · x + 0 · y ≡ x
  idLb x y = solveℕ!

mulUT-assoc : (p q r : UT) → mulUT p (mulUT q r) ≡ mulUT (mulUT p q) r
mulUT-assoc (ut a₀ b₀ d₀) (ut a₁ b₁ d₁) (ut a₂ b₂ d₂) =
  utPath (assocA a₀ a₁ a₂) (assocB a₀ b₀ a₁ b₁ d₁ b₂ d₂) (assocA d₀ d₁ d₂)

mulUT-idR : (p : UT) → mulUT p idUT ≡ p
mulUT-idR (ut a₀ b₀ d₀) = utPath (idRa a₀) (idRb a₀ b₀) (idRa d₀)

mulUT-idL : (p : UT) → mulUT idUT p ≡ p
mulUT-idL (ut a₀ b₀ d₀) = utPath (idLa a₀) (idLb b₀ d₀) (idLa d₀)

-- The two monoids.
UTMonoid : Monoid ℓ-zero
UTMonoid = makeMonoid idUT mulUT isSetUT mulUT-assoc mulUT-idR mulUT-idL

ℕ·Monoid : Monoid ℓ-zero
ℕ·Monoid = makeMonoid 1 _·_ isSetℕ ·-assoc ·-identityʳ ·-identityˡ

-- det on the unit: det [[1,0],[0,1]] = 1, definitionally.
detUT-id : detUT idUT ≡ 1
detUT-id = refl

-- THE MORPHISM: detUT : (UT, mulUT, idUT) → (ℕ, ·, 1).
detHom : MonoidHom UTMonoid ℕ·Monoid
detHom = detUT , monoidequiv detUT-id detConserve

------------------------------------------------------------------------
-- (d) The sector witness for the full-matrix contrast
--
-- Over ℤ, det [[a,b],[c,d]] = a·d − b·c.  Over ℕ that subtraction is
-- unavailable, so a full-matrix det is not stated here at all.  The
-- checked fact below is the upper-triangular witness: in this sector
-- c = 0, so the term the subtraction would remove is already zero,
-- and the ℤ-determinant restricted to the sector IS the
-- subtraction-free detUT = a·d.

crossTermVanishes : (p : UT) → b p · 0 ≡ 0
crossTermVanishes p = sym (0≡m·0 (b p))
