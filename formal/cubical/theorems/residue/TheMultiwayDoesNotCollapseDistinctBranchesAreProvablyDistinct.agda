{-# OPTIONS --cubical --safe #-}

-- multiwayBranchesDistinct — the many paths are distinct: Wolfram's MULTIWAY
-- systems keep branching histories and refuse to collapse them.  Put to
-- the kernel: two computational branches with different winding are
-- PROVABLY unequal — the multiway does not collapse, as a theorem.
--
-- This is the checked witness of Wolfram's core multicomputational
-- principle (a branch is not identified with another branch, ever) — and
-- it is exactly why the corpus's proof-relevant e-graph KEEPS distinct
-- paths (CRYSTAL.md L2: "distinct automorphisms survive as distinct
-- paths").  In a set (an h-set) all paths collapse; the circle is NOT a
-- set, and winding is the invariant that tells the branches apart.

module TheMultiwayDoesNotCollapseDistinctBranchesAreProvablyDistinct where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1.Base using (base ; loop ; ΩS¹ ; winding)
open import Cubical.Data.Int using (ℤ ; pos ; injPos)
open import Cubical.Data.Nat using (znots)
open import Cubical.Relation.Nullary using (¬_)

-- once-around and the trivial branch carry different windings,
-- so they are NOT the same path: the multiway keeps them apart.
loop≢refl : ¬ (loop ≡ refl)
loop≢refl p = znots (injPos (cong winding (sym p)))
  -- cong winding p : winding loop ≡ winding refl, i.e. pos 1 ≡ pos 0;
  -- injPos : 1 ≡ 0 in ℕ; znots : ¬ (0 ≡ suc _).  (sym to match znots.)

-- more strongly: two branches wind differently ⇒ they are distinct.
-- distinct winding is a SUFFICIENT witness of branch-distinctness, which
-- is the whole content of "the multiway does not collapse."
different-winding→different-branch :
  (a b : ΩS¹) → ¬ (winding a ≡ winding b) → ¬ (a ≡ b)
different-winding→different-branch a b wa≢wb a≡b =
  wa≢wb (cong winding a≡b)
