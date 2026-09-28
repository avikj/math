{-# OPTIONS --cubical --safe --no-import-sorts #-}

-- The walk's forcing law, statement (1): a least non-divisor of L is a
-- prime power.
--
-- Paper proof (WALK_FORCING_LAW.md (absent from this repository)): if q is least with q ∤ L and
-- q = a·b, gcd(a,b)=1, 1<a,b<q, then minimality gives a ∣ L and b ∣ L,
-- and coprime divisors multiply, so q = ab ∣ L — contradiction.
--
-- (H1) coprime divisors multiply is proved gcd-side, no Bezout:
-- gcd (aL) (bL) = gcd a b · L = L (gcd-factorʳ), and ab is a common
-- divisor of aL and bL, hence ab ∣ gcd (aL) (bL) = L.
-- (H2) is <-·sk plus ·-identityˡ/·-comm.

module WalkForcing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Relation.Nullary

LeastNonDivisor : ℕ → ℕ → Type
LeastNonDivisor L q =
  (¬ (q ∣ L)) × ((r : ℕ) → 2 ≤ r → r < q → r ∣ L)

ProperCoprimeSplit : ℕ → Type
ProperCoprimeSplit q =
  Σ[ a ∈ ℕ ] Σ[ b ∈ ℕ ]
    (a · b ≡ q) × isGCD a b 1 × (1 < a) × (1 < b)

-- (H1) coprime divisors multiply
coprime-divisors-multiply :
  (a b L : ℕ) → isGCD a b 1 → a ∣ L → b ∣ L → (a · b) ∣ L
coprime-divisors-multiply a b L g a∣L b∣L =
  subst ((a · b) ∣_) gL≡L
    (gcdIsGCD (a · L) (b · L) .snd (a · b) (ab∣aL , ab∣bL))
  where
  -- gcd (aL) (bL) = gcd a b · L = 1 · L = L
  gL≡L : gcd (a · L) (b · L) ≡ L
  gL≡L = gcd-factorʳ a b L ∙ cong (_· L) (isGCD→gcd≡ g) ∙ ·-identityˡ L

  -- ab ∣ aL since b ∣ L; ab ∣ bL since a ∣ L
  ab∣aL : (a · b) ∣ (a · L)
  ab∣aL = subst2 _∣_ (·-comm b a) (·-comm L a) (∣-multʳ a b∣L)

  ab∣bL : (a · b) ∣ (b · L)
  ab∣bL = subst ((a · b) ∣_) (·-comm L b) (∣-multʳ b a∣L)

-- (H2) proper factors are smaller
proper-factor-< : (x y : ℕ) → 1 < x → 1 < y → x < x · y
proper-factor-< zero    y 1<x 1<y = ⊥.rec (¬-<-zero 1<x)
proper-factor-< (suc x) y 1<x 1<y =
  subst2 _<_ (·-identityˡ (suc x)) (·-comm y (suc x)) (<-·sk 1<y)

-- THE THEOREM: a least non-divisor admits no proper coprime splitting
-- (equivalently, is a prime power: any non-prime-power splits properly).
leastNonDivisor-no-coprime-split :
  (L q : ℕ) → LeastNonDivisor L q → ¬ ProperCoprimeSplit q
leastNonDivisor-no-coprime-split L q (q∤L , below)
  (a , b , ab≡q , cop , 1<a , 1<b) =
  q∤L (subst (_∣ L) ab≡q
        (coprime-divisors-multiply a b L cop
          (below a 1<a (subst (a <_) ab≡q (proper-factor-< a b 1<a 1<b)))
          (below b 1<b (subst (b <_) ab≡q
            (subst (b <_) (·-comm b a) (proper-factor-< b a 1<b 1<a))))))
