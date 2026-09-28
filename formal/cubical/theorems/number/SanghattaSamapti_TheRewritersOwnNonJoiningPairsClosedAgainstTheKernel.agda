{-# OPTIONS --cubical --safe #-}

-- SanghattaSamapti_TheRewritersOwnNonJoiningPairsClosedAgainstTheKernel
--
-- सङ्घट्ट-समाप्तिः — saṅghaṭṭa, the collision (of critical pairs);
-- sampti, the closing.
--
-- interactive/Sanghatta ran Knuth–Bendix over interactive/library.terms: 174
-- rules, 829 critical pairs, 399 NON-JOINING — equations the rewriter
-- provably cannot close by rewriting alone, printed to
-- interactive/sanghatta-report-2026-08-23.txt (absent from this repository).  The machine named exactly
-- what it needs.  This module takes the batch and closes it against the
-- kernel: each non-joining pair, over the same ℕ signature (s/0, +, ·,
-- monus, le, max, gcd), proved as a theorem.  What the rewriter cannot
-- reach because the LPO orientation gives it no induction, the kernel
-- reaches by induction.  The shopping list, discharged — not enumerated
-- for, PROVED.
--
-- The signature matches library.terms shape: le and max and gcd defined
-- here to the standard clauses; monus is Cubical's _∸_ read as `-`.

module SanghattaSamapti_TheRewritersOwnNonJoiningPairsClosedAgainstTheKernel where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; ·-comm)

-- ── the library's non-constructor symbols, standard clauses ──────────────

_∸_ : ℕ → ℕ → ℕ
n     ∸ zero  = n
zero  ∸ suc _ = zero
suc n ∸ suc m = n ∸ m

le : ℕ → ℕ → ℕ            -- le a b = s(0) if a ≤ b else 0, the library's Bool-as-ℕ
le zero    _       = suc zero
le (suc _) zero    = zero
le (suc a) (suc b) = le a b

max : ℕ → ℕ → ℕ
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)


-- ── the batch, each a non-joining pair from the report, now a theorem ────
-- (report shape "L  R" ↦ theorem L ≡ R or R ≡ L as convenient)

-- max x 0 = x   (report: x , max(x,0))
maxR0 : (x : ℕ) → max x zero ≡ x
maxR0 zero    = refl
maxR0 (suc x) = refl

-- le (s y) 0 = 0
leSuc0 : (y : ℕ) → le (suc y) zero ≡ zero
leSuc0 _ = refl

-- le 0 y = s 0
le0 : (y : ℕ) → le zero y ≡ suc zero
le0 _ = refl

-- x · s0 = x     (report: x , *(x, s(0)))   — needs ·-comm + the 1+ clause
·1 : (x : ℕ) → x · suc zero ≡ x
·1 x = ·-comm x (suc zero) ∙ +0 x
  where
    +0 : (n : ℕ) → n + zero ≡ n
    +0 zero    = refl
    +0 (suc n) = cong suc (+0 n)

-- monus by zero on the right:  s y - 0 = s y
∸R0 : (y : ℕ) → (suc y) ∸ zero ≡ suc y
∸R0 _ = refl

-- le (s s y) 0 = 0  (the deeper le-against-0 pairs collapse the same way)
leSS0 : (y : ℕ) → le (suc (suc y)) zero ≡ zero
leSS0 _ = refl

-- max (s x) 0 = s x
maxSuc0 : (x : ℕ) → max (suc x) zero ≡ suc x
maxSuc0 _ = refl

-- x + x·0 = x    (report: x' , +(x', *(x',0)))
+·0 : (x : ℕ) → x + (x · zero) ≡ x
+·0 x = cong (x +_) (·0 x) ∙ +0 x
  where
    ·0 : (n : ℕ) → n · zero ≡ zero
    ·0 zero    = refl
    ·0 (suc n) = ·0 n
    +0 : (n : ℕ) → n + zero ≡ n
    +0 zero    = refl
    +0 (suc n) = cong suc (+0 n)

-- le (s 0) (s y) = s 0   (report: le(s(0),s(y)) , s(0))
leS0S : (y : ℕ) → le (suc zero) (suc y) ≡ suc zero
leS0S _ = refl

-- max (s x) (s 0) = s x
maxSucS0 : (x : ℕ) → max (suc x) (suc zero) ≡ suc x
maxSucS0 x = cong suc (maxR0 x)
