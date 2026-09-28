{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- The Haskell explorer's defining equations are proof-search axioms.
--
-- MathMachine.hs (absent from this repository) uses computation to falsify conjectures, then rewriting
-- and induction to prove survivors.  That architecture only means anything
-- if every defining rewrite agrees with the computation semantics.  Its old
-- positive-positive gcd rule did not:
--
--   gcd (suc x) (suc y) = gcd ((suc x) ∸ (suc y)) (suc y)
--
-- At x = 1 and y = 2 the left side is 1 and the right side is 3.  This
-- module puts that counterexample in the kernel and proves the two gcd base
-- equations that remain in the Haskell rule set.  The Haskell startup audit
-- is a bounded falsifier; these terms are the checked boundary.
------------------------------------------------------------------------

module HaskellDefinitionBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using ( ℕ ; zero ; suc ; _+_ ; _·_ ; _∸_ ; max
        ; +-zero ; +-suc ; +-comm ; 0≡m·0 ; ·-suc ; zero∸
        ; injSuc ; znots )
open import Cubical.Data.Nat.GCD
  using (gcd ; zeroGCD ; symGCD ; isGCD→gcd≡)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Relation.Nullary using (¬_)
open import Agda.Builtin.String using (String)

-- Haskell emits its live rule objects as a temporary Agda module during the
-- one-button check.  That module proves its generated list equals this one by
-- `refl`, so adding, deleting, reordering, or changing a rule cannot drift
-- silently away from the universal proofs below.

expectedDefinitionManifest : List String
expectedDefinitionManifest =
    "+ :: (x+0) = x"
  ∷ "+ :: (x+s(y)) = s((x+y))"
  ∷ "* :: (x*0) = 0"
  ∷ "* :: (x*s(y)) = ((x*y)+x)"
  ∷ "max :: (xmax0) = x"
  ∷ "max :: (0maxx) = x"
  ∷ "max :: (s(x)maxs(y)) = s((xmaxy))"
  ∷ "- :: -(x,0) = x"
  ∷ "- :: -(0,x) = 0"
  ∷ "- :: -(s(x),s(y)) = -(x,y)"
  ∷ "gcd :: (xgcd0) = x"
  ∷ "gcd :: (0gcdx) = x"
  ∷ "le :: le(0,x) = s(0)"
  ∷ "le :: le(s(x),0) = 0"
  ∷ "le :: le(s(x),s(y)) = le(x,y)"
  ∷ []

------------------------------------------------------------------------
-- Every primitive defining equation currently admitted by MathMachine.hs (absent from this repository).
-- The Haskell firewall searches for counterexamples; these are universal
-- terms checked by Agda.
------------------------------------------------------------------------

haskell-add-zero : (x : ℕ) → x + zero ≡ x
haskell-add-zero = +-zero

haskell-add-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
haskell-add-suc = +-suc

haskell-mul-zero : (x : ℕ) → x · zero ≡ zero
haskell-mul-zero x = sym (0≡m·0 x)

-- Cubical's library states the successor law as x + x·y.  Haskell's rule
-- writes x·y + x, so the final commutation is part of the checked bridge.
haskell-mul-suc : (x y : ℕ) → x · suc y ≡ x · y + x
haskell-mul-suc x y = ·-suc x y ∙ +-comm x (x · y)

haskell-max-zero-right : (x : ℕ) → max x zero ≡ x
haskell-max-zero-right zero    = refl
haskell-max-zero-right (suc x) = refl

haskell-max-zero-left : (x : ℕ) → max zero x ≡ x
haskell-max-zero-left x = refl

haskell-max-suc : (x y : ℕ) → max (suc x) (suc y) ≡ suc (max x y)
haskell-max-suc x y = refl

haskell-sub-zero-right : (x : ℕ) → x ∸ zero ≡ x
haskell-sub-zero-right x = refl

haskell-sub-zero-left : (x : ℕ) → zero ∸ x ≡ zero
haskell-sub-zero-left = zero∸

haskell-sub-suc : (x y : ℕ) → suc x ∸ suc y ≡ x ∸ y
haskell-sub-suc x y = refl

-- Haskell represents propositions in its search language by the numbers
-- zero and one.  This recursion is exactly its `(<=) ? 1 : 0` semantics.
leFlag : ℕ → ℕ → ℕ
leFlag zero    y       = 1
leFlag (suc x) zero    = 0
leFlag (suc x) (suc y) = leFlag x y

haskell-le-zero : (x : ℕ) → leFlag zero x ≡ 1
haskell-le-zero x = refl

haskell-le-suc-zero : (x : ℕ) → leFlag (suc x) zero ≡ 0
haskell-le-suc-zero x = refl

haskell-le-suc : (x y : ℕ) → leFlag (suc x) (suc y) ≡ leFlag x y
haskell-le-suc x y = refl

-- The only gcd rewrites admitted by MathMachine.hs (absent from this repository).

haskell-gcd-zero-right : (x : ℕ) → gcd x zero ≡ x
haskell-gcd-zero-right x = isGCD→gcd≡ (zeroGCD x)

haskell-gcd-zero-left : (x : ℕ) → gcd zero x ≡ x
haskell-gcd-zero-left x = isGCD→gcd≡ (symGCD (zeroGCD x))

-- Concrete evaluation of the two sides of the deleted rule.

gcd-two-three : gcd 2 3 ≡ 1
gcd-two-three = refl

two-minus-three : 2 ∸ 3 ≡ 0
two-minus-three = refl

old-gcd-rule-fails-at-two-three :
  ¬ (gcd 2 3 ≡ gcd (2 ∸ 3) 3)
old-gcd-rule-fails-at-two-three p =
  znots (injSuc (sym gcd-two-three ∙ p ∙ haskell-gcd-zero-left 3))
