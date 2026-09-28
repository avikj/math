{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SmithSignControl
--
-- Designed annihilation for the Smith capability (collab/PROTOCOL.md (absent from this repository) §7),
-- in the corpus's C1/C2 idiom.
--
--   S1  The native capability EVALUATES.  `normalMatrix` applied to a closed
--       matrix reduces to a closed integer, so every equation below is
--       checked by normalization and not by a supplied certificate.  This is
--       the property the Lean lane's `Int.gcdA`/`Int.gcdB` do *not* have
--       `Nat.xgcdAux` and no instance can pass the gate.  Here it does not.
--
--   S2  The native normal form is NOT sign-normalized.  `diag(2,3)` has Smith
--       invariants `1, -6`.  The refutation is machine-checked, so the claim
--       "the native output already meets the Lean lane's convention" is
--       destroyed rather than doubted.
--
--   S3  Agreement where the conventions do coincide: the rank-one matrix
--       `[[2,4],[4,8]]` normalizes to `diag(2,0)`, the same invariants the
--       Lean producer returns for it (`Pairfield.RankOneWitness`, control
--       `(produce ⟨2,4,4,8⟩ _).h = 2`).  The two lanes compute the same
--       mathematics; only the choice of representative differs.
--
-- The repair is `SmithSignNormal`.
------------------------------------------------------------------------

module SmithSignControl where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc ; rec)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; negsucNotpos)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.IntegerMatrix.Smith

open import SmithCapability
open import SmithSignNormal using (absℤ)

open Coefficient ℤCommRing

-- A 2×2 matrix.  Built with the library eliminator `FinData.rec`, which is
-- parametric in the bound and so never unifies `suc` with an index: this file
-- raises no `UnsupportedIndexedMatch` warning, unlike the `mk3` of
-- the warning is a property of the presentation, not of the mathematics.
mk2 : (a b c d : ℤ) → Mat 2 2
mk2 a b c d i j = rec (rec a b j) (rec c d j) i

------------------------------------------------------------------------
-- S1 / S2.  diag(2,3) evaluates, to diag(1,-6).

d23 : Mat 2 2
d23 = mk2 (pos 2) (pos 0) (pos 0) (pos 3)

-- The first invariant is the gcd, and it is already nonnegative.
d23-first : normalMatrix d23 zero zero ≡ pos 1
d23-first = refl

-- The second is the product, and it is NEGATIVE.  This equation is the whole
-- finding; everything else in this file is bookkeeping around it.
d23-second : normalMatrix d23 (suc zero) (suc zero) ≡ negsuc 5
d23-second = refl

-- Off the diagonal the form is genuinely diagonal, so the only discrepancy
-- with the Lean lane's `SmithCertificate2` is the sign.
d23-off : normalMatrix d23 zero (suc zero) ≡ pos 0
d23-off = refl

-- S2 as a refutation: the native second invariant is not `6`, so the native
-- output does not satisfy `0 ≤ d₂`.
d23-not-nonneg : ¬ (normalMatrix d23 (suc zero) (suc zero) ≡ pos 6)
d23-not-nonneg p = negsucNotpos 5 6 (sym d23-second ∙ p)

-- And the normalized representative is the expected one, so the repair in
-- `SmithSignNormal` returns the conventional answer on this instance.
d23-repaired : absℤ (normalMatrix d23 (suc zero) (suc zero)) ≡ pos 6
d23-repaired = refl

------------------------------------------------------------------------
-- S3.  The rank-one case agrees with the Lean producer.

r24 : Mat 2 2
r24 = mk2 (pos 2) (pos 4) (pos 4) (pos 8)

r24-first : normalMatrix r24 zero zero ≡ pos 2
r24-first = refl

r24-second : normalMatrix r24 (suc zero) (suc zero) ≡ pos 0
r24-second = refl
