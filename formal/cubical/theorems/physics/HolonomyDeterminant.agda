{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- HolonomyDeterminant
--
-- THE CONSERVED QUANTITY OF SMITH PATH HOLONOMY.
--
-- notes/SMITH_PATH_HOLONOMY.md (absent from this repository) §3 lets `G`
-- be the group of automorphisms of coker(D) induced by target holonomies
-- U_p U_{p₀}⁻¹ and asks which cokernel data descend.
-- notes/RANK_R_PAYLOAD_NORMAL_FORM.md (absent from this repository) §3
-- proves the events form a REGULAR torsor: the payload
-- ranges over the whole stabilizer, "invisible to the endpoint".
-- Read together they suggest that on the cokernel nothing at all is
-- conserved.  Something is.
--
-- For D = diag(d₁, q·d₁), a holonomy H ∈ Γ₀(q) is one representative
-- of the automorphism it induces on coker(D), and H + D·E is another.
-- So the determinant of a representative is defined only modulo d₁ --
-- `detShift` is exactly that well-definedness, as a polynomial
-- identity with the multiplier exhibited rather than existentially
-- asserted.  But every H ∈ Γ₀(q) ⊂ GL₂(ℤ) has det H = ε with ε² = 1.
-- Hence
--
--   `detClass` :  the determinant of ANY representative of a
--                 holonomy-induced automorphism is ≡ ε (mod d₁), and
--                 ε is a square root of 1 in ℤ.
--
-- That is a real constraint exactly when (ℤ/d₁)ˣ ≠ {±1}, i.e. exactly
-- when d₁ ∉ {1,2,3,4,6}.  The smallest witness is d₁ = 5:
--
--   `noSurjectivity` : with d₁ = 5 and ANY q, no unimodular H is
--                 congruent to diag(2,1) modulo D = diag(5, 5q).  For
--                 q = 1 the class of diag(2,1) is a genuine
--                 automorphism of coker(D) = (ℤ/5)², of determinant
--                 2 ∉ {±1} mod 5, so the holonomy map
--                 Γ₀(D) → Aut(coker D) is NOT surjective.
--                 The proof forces 5 ∣ 3 and refutes that in ℕ.
--
-- The exact image (it is the full preimage of {±1} under
-- det : Aut(coker D) → (ℤ/d₁)ˣ, for every D and every rank) is proved
-- in collab/swarm/2026-08-14/swarm-0814-11-holonomy-determinant.md
-- (absent from this repository), not here.
--
-- Conventions follow Gamma0Partner / Gamma0Converse: D = diag(d₁,
-- q·d₁); Γ₀(q) = integer matrices whose lower-left entry is q·k.
-- No postulates, no holes; every algebraic step is `solve! ℤCommRing`.
------------------------------------------------------------------------

module HolonomyDeterminant where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz ; injSuc ; +-comm)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Nat.Divisibility using (m∣n→m≤n)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Int.Divisibility using (_∣_ ; ∣→∣ℕ)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

open CommRingStr (ℤCommRing .snd)

R : Type
R = fst ℤCommRing

------------------------------------------------------------------------
-- 1.  det is well defined modulo d₁ on representatives.
--
--     Replacing C by C + D·E, with D = diag(d₁, q·d₁), changes det by
--     d₁ times an exhibited multiplier.
------------------------------------------------------------------------

detShift : (d1 q c11 c12 c21 c22 e11 e12 e21 e22 : R)
  → (c11 + d1 · e11) · (c22 + (q · d1) · e22)
      - (c12 + d1 · e12) · (c21 + (q · d1) · e21)
    ≡ (c11 · c22 - c12 · c21)
      + d1 · ( (e11 · c22 + q · (c11 · e22) + (q · d1) · (e11 · e22))
             - (e12 · c21 + q · (c12 · e21) + (q · d1) · (e12 · e21)) )
detShift _ _ _ _ _ _ _ _ _ _ = solve! ℤCommRing

------------------------------------------------------------------------
-- 2.  Necessity.  If the holonomy H = (a, b, q·k, e) is congruent
--     modulo D to the representative C = (c11, c12, c21, c22), then
--     det H — a square root of 1 in ℤ — is congruent to det C mod d₁.
------------------------------------------------------------------------

detClass :
    (d1 q a b k e ε c11 c12 c21 c22 e11 e12 e21 e22 : R)
  → a ≡ c11 + d1 · e11
  → b ≡ c12 + d1 · e12
  → q · k ≡ c21 + (q · d1) · e21
  → e ≡ c22 + (q · d1) · e22
  → a · e - b · (q · k) ≡ ε
  → Σ[ t ∈ R ] (ε ≡ (c11 · c22 - c12 · c21) + d1 · t)
detClass d1 q a b k e ε c11 c12 c21 c22 e11 e12 e21 e22 pa pb pk pe pdet =
  ( ( (e11 · c22 + q · (c11 · e22) + (q · d1) · (e11 · e22))
    - (e12 · c21 + q · (c12 · e21) + (q · d1) · (e12 · e21)) )
  , sym pdet ∙ congs ∙ detShift d1 q c11 c12 c21 c22 e11 e12 e21 e22 )
  where
    congs : a · e - b · (q · k)
          ≡ (c11 + d1 · e11) · (c22 + (q · d1) · e22)
              - (c12 + d1 · e12) · (c21 + (q · d1) · e21)
    congs =
      cong₂ (λ x y → x · y - b · (q · k)) pa pe
      ∙ cong₂ (λ x y → (c11 + d1 · e11) · (c22 + (q · d1) · e22) - x · y) pb pk

------------------------------------------------------------------------
-- 3.  A determinant class that is not ±1 admits no unimodular lift.
--
--     If ε = δ + d₁·t and ε² = 1 then d₁ divides δ² − 1.
------------------------------------------------------------------------

sqLem : (D T Δ : R)
  → (- (Δ · T + Δ · T + D · (T · T))) · D
    ≡ Δ · Δ - (Δ + D · T) · (Δ + D · T)
sqLem _ _ _ = solve! ℤCommRing

squareObstruction :
    (d1 δ ε t : R)
  → ε ≡ δ + d1 · t
  → ε · ε ≡ 1r
  → Σ[ c ∈ R ] (c · d1 ≡ δ · δ - 1r)
squareObstruction d1 δ ε t peq psq =
  ( - (δ · t + δ · t + d1 · (t · t))
  , sqLem d1 t δ
    ∙ cong (λ z → δ · δ - z · z) (sym peq)
    ∙ cong (λ z → δ · δ - z) psq )

------------------------------------------------------------------------
-- 4.  The ℕ-side refutation: 5 does not divide 3.
------------------------------------------------------------------------

no5≤3 : ¬ (5 ≤ 3)
no5≤3 (k , p) = snotz (injSuc (injSuc (injSuc (+-comm 5 k ∙ p))))

¬5∣3 : ¬ (pos 5 ∣ pos 3)
¬5∣3 h = no5≤3 (m∣n→m≤n snotz (∣→∣ℕ h))

------------------------------------------------------------------------
-- 5.  The witness.  d₁ = 5, any q; the class of diag(2,1).
--
--     δ = 2·1 − 0·0 = 2 and δ² − 1 = 3, so a unimodular lift would
--     make 5 divide 3.
------------------------------------------------------------------------

deltaSq : (pos 2 · pos 1 - pos 0 · pos 0) · (pos 2 · pos 1 - pos 0 · pos 0) - 1r
        ≡ pos 3
deltaSq = refl

noSurjectivity :
    (q a b k e ε e11 e12 e21 e22 : R)
  → a ≡ pos 2 + pos 5 · e11
  → b ≡ pos 0 + pos 5 · e12
  → q · k ≡ pos 0 + (q · pos 5) · e21
  → e ≡ pos 1 + (q · pos 5) · e22
  → a · e - b · (q · k) ≡ ε
  → ε · ε ≡ 1r
  → ⊥
noSurjectivity q a b k e ε e11 e12 e21 e22 pa pb pk pe pdet psq =
  ¬5∣3 ∣ ( obstruction .fst , obstruction .snd ∙ deltaSq ) ∣₁
  where
    tcls : Σ[ t ∈ R ] (ε ≡ (pos 2 · pos 1 - pos 0 · pos 0) + pos 5 · t)
    tcls = detClass (pos 5) q a b k e ε (pos 2) (pos 0) (pos 0) (pos 1)
                    e11 e12 e21 e22 pa pb pk pe pdet

    obstruction : Σ[ c ∈ R ]
      ( c · pos 5
      ≡ (pos 2 · pos 1 - pos 0 · pos 0) · (pos 2 · pos 1 - pos 0 · pos 0) - 1r )
    obstruction = squareObstruction (pos 5) (pos 2 · pos 1 - pos 0 · pos 0)
                                    ε (tcls .fst) (tcls .snd) psq
