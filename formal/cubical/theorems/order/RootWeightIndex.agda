{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- RootWeightIndex
--
-- Delta 17 T17.24, corrected, and the correction turns out to be the
-- corpus's parity obstruction.
--
-- WHAT T17.24 SAYS: "For the diagonal torus action on (G_m)^k, character
-- lattice modulo diagonal character is the A_{k−1} root lattice."
--
-- WHAT IS TRUE: ℤ^k / ℤ·(1,…,1) is the A_{k−1} **weight** lattice P.
-- The **root** lattice Q is the sublattice {x : Σxᵢ = 0} ⊂ ℤ^k, which is
-- a different object: Q injects into P (they meet ℤδ only at 0) with
--
--     P / Q  ≅  ℤ/k.
--
-- Proof, for the record and because it is three lines: the coordinate sum
-- σ : ℤ^k → ℤ is surjective with kernel exactly Q, and σ(δ) = k, so
-- ℤ^k/(Q + ℤδ) ≅ ℤ/kℤ.  Root and weight lattice differ by exactly the
-- centre of SL_k, which is standard; T17.24 states the quotient and names
-- the sublattice.
--
-- WHY THIS IS NOT PEDANTRY.  T17.24 is load-bearing: it is cited by
-- `SINGULAR_SERIES_LOCAL_FACTOR_IS_A_ROOT_SUBSYSTEM_RANK.md` (absent from this repository), whose
-- 108,596-instance exact verification of ν_p(H) = k − rank Φ_p(H) is a
-- statement about the ROOT system.  A note resting on a lattice named
-- wrongly is a note whose ranks might be off by the index.  (They are
-- not — rank is insensitive to the P/Q distinction — but that is a fact
-- to check, not to assume, and it is checked by the fact that the
-- singular-series note uses rank alone.)
--
-- AND THE PAYOFF.  At k = 2 the index is ℤ/2, and that ℤ/2 is not a new
-- object: it is `PairCoordinates.sumIsDouble`, the parity constraint on
-- Delta 17's cone, which `ConeImage.cone-image` proved is exactly the
-- image condition of the pair map.  So the cone's parity constraint IS
-- the root-versus-weight index of A_1.  Three items in the Delta ledger
-- — T17.13's congruence, T17.24's lattice, and T22.5's discriminant —
-- are one index computation.
--
-- Contents (all by the commutative-ring solver, no holes, no postulates):
--
--   diff                       the weight-lattice coordinate: R²/Rδ ≅ R
--                              via (x,y) ↦ y − x
--   diff-kills-diagonal        δ spans the kernel …
--   diagonal-spans-kernel      … and nothing else does
--   root                       the root sublattice of A_1: (x, −x)
--   root→double                image of Q in P lands in 2P …
--   double→root                … and fills it
--   index-is-two               the two together: image of Q = 2P exactly
--
-- Everything is over an ARBITRARY commutative ring, so "the index is 2"
-- is stated in the form that survives base change: the image of the root
-- lattice is the doubles.  Over ℤ the doubles have index 2 and that final
-- step is the ℤ-specific parity fact, already checked elsewhere in this
-- development rather than re-derived here.
--
------------------------------------------------------------------------

module RootWeightIndex where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

private
  variable
    ℓ : Level

module A1 (R : CommRing ℓ) where
  open CommRingStr (snd R)

  ----------------------------------------------------------------------
  -- §1  The weight lattice: R² modulo the diagonal.
  --
  -- Rather than form the quotient, use the difference map, which is a
  -- surjection R² → R whose kernel is exactly the diagonal.  That is the
  -- quotient, presented by a coordinate, and it makes every statement
  -- below a ring identity instead of a quotient argument.
  ----------------------------------------------------------------------

  diff : fst R → fst R → fst R
  diff x y = y - x

  -- δ = (n,n) is in the kernel …
  diff-kills-diagonal : (n : fst R) → diff n n ≡ 0r
  diff-kills-diagonal n = solve! R

  -- … and the kernel is no bigger: two points with the same difference
  -- differ by a diagonal vector, exhibited.
  diagonal-spans-kernel : (x y x' y' : fst R) → diff x y ≡ diff x' y'
                        → Σ[ n ∈ fst R ] ((x - x' ≡ n) × (y - y' ≡ n))
  diagonal-spans-kernel x y x' y' p = (x - x') , refl , lemma
    where
      -- y − y′ = (y − x) − (y′ − x′) + (x − x′), and the bracket is 0.
      step : (x y x' y' : fst R)
           → y - y' ≡ ((y - x) - (y' - x')) + (x - x')
      step x y x' y' = solve! R

      zeroed : (x y x' y' : fst R) → (0r + (x - x')) ≡ x - x'
      zeroed x y x' y' = solve! R

      lemma : y - y' ≡ x - x'
      lemma = step x y x' y'
            ∙ cong (λ z → z + (x - x')) (cong (λ z → z - diff x' y') p)
            ∙ cong (λ z → z + (x - x')) (rearrange (diff x' y'))
            ∙ zeroed x y x' y'
        where
          rearrange : (z : fst R) → z - z ≡ 0r
          rearrange z = solve! R

  -- Surjectivity of the difference coordinate: every weight is hit.
  diff-surjective : (m : fst R) → Σ[ p ∈ fst R × fst R ]
                                    (diff (fst p) (snd p) ≡ m)
  diff-surjective m = (0r , m) , surj m
    where
      surj : (m : fst R) → diff 0r m ≡ m
      surj m = solve! R

  ----------------------------------------------------------------------
  -- §2  The root lattice, and its image in the weight lattice.
  --
  -- Q = {(x,y) : x + y = 0} = {(x, −x)}, the A_1 root lattice.  Its image
  -- under the difference coordinate is exactly the set of doubles — index
  -- two, in the form that does not need ℤ.
  ----------------------------------------------------------------------

  root : fst R → fst R × fst R
  root x = x , - x

  root-sums-to-zero : (x : fst R) → fst (root x) + snd (root x) ≡ 0r
  root-sums-to-zero x = solve! R

  -- The image lands in the doubles: diff(x, −x) = −x − x = 2·(−x).
  root→double : (x : fst R)
              → Σ[ m ∈ fst R ] (diff (fst (root x)) (snd (root x)) ≡ m + m)
  root→double x = (- x) , img x
    where
      img : (x : fst R) → diff x (- x) ≡ (- x) + (- x)
      img x = solve! R

  -- And it fills them: every double is the image of a root vector.
  double→root : (m : fst R)
              → Σ[ x ∈ fst R ] (diff (fst (root x)) (snd (root x)) ≡ m + m)
  double→root m = (- m) , fillD m
    where
      fillD : (m : fst R) → diff (- m) (- (- m)) ≡ m + m
      fillD m = solve! R

  ----------------------------------------------------------------------
  -- §3  The index, both inclusions at once.
  --
  -- image(Q → P) = 2P.  Over ℤ this is the statement that the A_1 root
  -- lattice sits inside the weight lattice with index two, i.e. P/Q ≅
  -- ℤ/2 — and that ℤ/2 is the parity constraint on Delta 17's cone,
  -- already checked as `PairCoordinates.sumIsDouble` and characterised as
  -- the image condition by `ConeImage.cone-image`.
  ----------------------------------------------------------------------

  index-is-two : ((x : fst R) → Σ[ m ∈ fst R ]
                    (diff (fst (root x)) (snd (root x)) ≡ m + m))
               × ((m : fst R) → Σ[ x ∈ fst R ]
                    (diff (fst (root x)) (snd (root x)) ≡ m + m))
  index-is-two = root→double , double→root
