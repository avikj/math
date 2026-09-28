{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- RoughSplit
--
-- THE √X HORIZON FACT, X-UNIFORMLY.
--
--   If n ≤ X and every prime factor of n exceeds √X, then n = 1 or n
--   is prime.
--
-- `NaturalMachine/SieveFiber.agda` §4 proves this ONLY at X = 30, by
-- exhaustion over an explicit 30-element domain.  This module is the
-- general statement, X-uniformly.  It
-- imports nothing from `SieveFiber` and `SieveFiber` is untouched.
--
-- WHAT √X MEANS HERE.  Nothing in the corpus fixes it, and the note's
-- own phrasing is looser than what is provable, so it is fixed here in
-- the only way that keeps every statement inside ℕ:
--
--     isqrt X  =  the largest s with s · s ≤ X.
--
-- `isqrtΣ` below CONSTRUCTS that s together with its two-sided
-- specification `s · s ≤ X  ×  X < suc s · suc s`, by induction on X;
-- `isqrt-greatest` then proves it really is the largest, so the name is
-- earned and not asserted.  (This is the Turing lens taken literally:
-- the machine that computes the horizon carries its own defining
-- property as its second component, so there is no separate correctness
-- statement to drift.)
--
--
-- THE SHAPE OF THE PROOF, and why no factorization theory appears.
-- The English argument is "if n had two prime factors p₁, p₂ > √X then
-- n ≥ p₁p₂ > X".  Rendered as an Agda proof that would need a prime
-- factorization of n, which cubical v0.5 does not have.  It is not
-- needed.  The proof below never factors anything:
--
--   given ANY divisor d of n, write n = c · d and compare c with d.
--   One of the two is ≤ the other, and the smaller one w squares into
--   n:  w · w ≤ c · d = n ≤ X < (s+1)²,  so w ≤ s.
--   If d ≤ c the small factor is d itself, which the hypothesis forbids
--   unless d = 1; if c < d the small factor is c, which the hypothesis
--   forbids unless c = 1, i.e. unless d = n.
--
-- So `d ≡ 1 ⊎ d ≡ n` for every divisor d, which IS `IsPrime n`.  The
-- only inputs are order, multiplication monotonicity, and the totality
-- in its cheapest instance: the universal property of being
-- prime is a statement about ALL divisors, so quantifying over divisors
-- directly is shorter than producing one distinguished factorization.
--
--
-- WHAT IS PROVED (all `--safe`, no postulates, no holes, no TERMINATING)
--
--   isqrtΣ, isqrt, isqrt-lower, isqrt-upper, isqrt-greatest
--                        the horizon, with its specification and its
--                        maximality.
--
--   roughSplit           (s X n : ℕ) → 0 < n → n ≤ X → X < suc s · suc s
--                        → NoSmallDivisor s n → (n ≡ 1) ⊎ IsPrime n
--                        The divisor form: `s` is any number whose
--                        successor squares past X.  This is the working
--                        lemma and the strongest form here.
--
--   roughSplitPrimes     the same with the hypothesis in the note's own
--                        words — every PRIME factor of n exceeds s.
--                        Bridged to the divisor form by `primeDivisor`
--                        from `CoprimeSplitting`.
--
--   roughSplitSqrt       the corollary at s = isqrt X, i.e. the theorem
--
--   roughSplitSelf       the X = n specialisation: n > 0 with no
--                        nontrivial divisor ≤ isqrt n is 1 or prime.
--                        (This is the classical trial-division
--                        criterion; see PRIOR ART below.)
--
--   n≤X-necessary        SHARPNESS.  49 has all prime factors > isqrt 30
--                        = 5, is neither 1 nor prime, and the only
--                        hypothesis it violates is 49 ≤ 30.
--
--   isqrt-30, isqrt-49, isqrt-100  the horizon computes.
--
--
--
-- PRIOR ART, credited.
--   * `NaturalMachine/CoprimeSplitting.agda` (this corpus) —
--     `primeDivisor : (n : ℕ) → 1 < n → Σ[ p ] (IsPrime p × p ∣ n)`,
--     built there over `dec∣` and a bounded divisor search.  Used, not
--     rebuilt.  `pos-≢1→1<` likewise.
--   * `NaturalMachine/WalkJumps.agda` (this corpus) — `IsPrime`, in the
--     all-divisors form, which is exactly the form this proof produces.
--   * mathlib4 (Lean),
--     `Mathlib/Data/Nat/Prime/Defs.lean (absent from this repository):124` and `:368`:
--     `Nat.prime_def_le_sqrt : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m ≤ sqrt p
--     → ¬ m ∣ p`, and `Nat.minFac_sq_le_self`.  PROVED-grade prior art,
--     The X = n case (`roughSplitSelf` below) is
--     mathlib's theorem, by the same square-comparison argument, and no
--     novelty is claimed for it.  What is not in mathlib in this form is
--     the X-uniform statement (horizon isqrt X, integers n ≤ X), which
--     is the one `SIEVE_FIBER` needs, and mathlib is a different
--     substrate anyway.
--   * cubical v0.5 has NO integer square root and NO primality
--     (`Cubical/Data/Nat/` contains neither), and agda-unimath has
--     `is-prime-ℕ` and `is-square-ℕ` but no integer square root and no
--     ∈-criterion.
------------------------------------------------------------------------

module RoughSplit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

open import WalkJumps using (IsPrime; prime-∣-·)
open import CoprimeSplitting
  using (primeDivisor; pos-≢1→1<; prime-∣-prime)

------------------------------------------------------------------------
-- §1  Multiplication against the order, both sides at once
--
-- `Cubical.Data.Nat.Order` gives `≤-·k` (right multiplication only) and
-- `<-·sk`.  Everything below needs the two-sided form, so it is derived
-- once here through `·-comm` and never again.
------------------------------------------------------------------------

≤-·-both : {m n k l : ℕ} → m ≤ n → k ≤ l → m · k ≤ n · l
≤-·-both {m} {n} {k} {l} m≤n k≤l =
  ≤-trans (≤-·k m≤n) (subst2 _≤_ (·-comm k n) (·-comm l n) (≤-·k k≤l))

-- squaring is strictly monotone
sq-mono< : (a b : ℕ) → a < b → a · a < b · b
sq-mono< a zero    a<b = Empty.rec (¬-<-zero a<b)
sq-mono< a (suc k) a<b =
  ≤<-trans (≤-·-both (≤-refl {a}) (<-weaken a<b)) (<-·sk a<b)

-- …hence its contrapositive, which is the only way §3 ever uses it:
-- a number whose square fits under X sits at or below the horizon.
sq≤→≤ : (d s X : ℕ) → d · d ≤ X → X < suc s · suc s → d ≤ s
sq≤→≤ d s X dd≤X X<ss with splitℕ-≤ d s
... | inl d≤s = d≤s
... | inr s<d =
  Empty.rec (¬m<m (<≤-trans (<≤-trans X<ss (≤-·-both s<d s<d)) dd≤X))

≢0→0< : (d : ℕ) → ¬ (d ≡ 0) → 0 < d
≢0→0< zero    h = Empty.rec (h refl)
≢0→0< (suc d) h = suc-≤-suc zero-≤

------------------------------------------------------------------------
-- §2  The horizon:  isqrt X = the largest s with s · s ≤ X
--
-- Built as a Σ-type so that the value and its specification are one
-- object.  Induction on X: the horizon rises by one exactly when the
-- next square is reached, and the equality case is forced (X < (s+1)²
-- and (s+1)² ≤ suc X pin suc X to (s+1)²).
------------------------------------------------------------------------

IsSqrt : ℕ → ℕ → Type
IsSqrt X s = (s · s ≤ X) × (X < suc s · suc s)

isqrtΣ : (X : ℕ) → Σ[ s ∈ ℕ ] IsSqrt X s
isqrtΣ zero    = 0 , (≤-refl , suc-≤-suc zero-≤)
isqrtΣ (suc X) with isqrtΣ X
... | s , (ss≤X , X<ss) with splitℕ-≤ (suc s · suc s) (suc X)
...   | inl ss≤sX = suc s , (ss≤sX , ≤<-trans X<ss (sq-mono< (suc s) (suc (suc s)) ≤-refl))
...   | inr sX<ss = s , (≤-suc ss≤X , sX<ss)

isqrt : ℕ → ℕ
isqrt X = isqrtΣ X .fst

isqrt-lower : (X : ℕ) → isqrt X · isqrt X ≤ X
isqrt-lower X = isqrtΣ X .snd .fst

isqrt-upper : (X : ℕ) → X < suc (isqrt X) · suc (isqrt X)
isqrt-upper X = isqrtΣ X .snd .snd

-- …and it really is the LARGEST such s, so the name is earned.
isqrt-greatest : (X t : ℕ) → t · t ≤ X → t ≤ isqrt X
isqrt-greatest X t tt≤X = sq≤→≤ t (isqrt X) X tt≤X (isqrt-upper X)

-- the horizon computes
isqrt-30 : isqrt 30 ≡ 5
isqrt-30 = refl

isqrt-49 : isqrt 49 ≡ 7
isqrt-49 = refl

isqrt-100 : isqrt 100 ≡ 10
isqrt-100 = refl

------------------------------------------------------------------------
-- §3  THE THEOREM, divisor form
--
-- `NoSmallDivisor s n` is `CoprimeSplitting.NoDivBelow n
-- s` spelled out locally (that module keeps it in the other argument
-- order; it is not re-exported here to avoid a name clash for importers
-- of both).
------------------------------------------------------------------------

NoSmallDivisor : ℕ → ℕ → Type
NoSmallDivisor s n = (d : ℕ) → 1 < d → d ≤ s → ¬ (d ∣ n)

-- n ≤ X, the horizon s satisfies X < (s+1)², and n has no nontrivial
-- divisor at or below s.  Then n is 1 or prime.
--
-- The whole content is the two `splitℕ-≤` splits: one decides which of
-- the two cofactors is the small one, the other decides whether the
-- small one is 1.  No factorization, no valuation, no induction.
roughSplit : (s X n : ℕ) → 0 < n → n ≤ X → X < suc s · suc s
           → NoSmallDivisor s n
           → (n ≡ 1) ⊎ IsPrime n
roughSplit s X n 0<n n≤X X<ss none with discreteℕ n 1
... | yes n≡1 = inl n≡1
... | no  n≢1 = inr (pos-≢1→1< n 0<n n≢1 , divs)
  where
  divs : (d : ℕ) → d ∣ n → (d ≡ 1) ⊎ (d ≡ n)
  divs d d∣n with discreteℕ d 1
  ... | yes d≡1 = inl d≡1
  ... | no  d≢1 = go
    where
    c : ℕ
    c = ∣-untrunc d∣n .fst

    cd≡n : c · d ≡ n
    cd≡n = ∣-untrunc d∣n .snd

    d≢0 : ¬ (d ≡ 0)
    d≢0 d≡0 = <→≢ 0<n (sym (sym cd≡n ∙ cong (c ·_) d≡0 ∙ sym (0≡m·0 c)))

    1<d : 1 < d
    1<d = pos-≢1→1< d (≢0→0< d d≢0) d≢1

    c≢0 : ¬ (c ≡ 0)
    c≢0 c≡0 = <→≢ 0<n (sym (sym cd≡n ∙ cong (_· d) c≡0))

    c∣n : c ∣ n
    c∣n = subst (c ∣_) cd≡n (∣-left d)

    go : (d ≡ 1) ⊎ (d ≡ n)
    go with splitℕ-≤ d c
    -- d ≤ c: then d is the small factor, d · d ≤ c · d = n ≤ X,
    -- so d ≤ s — forbidden.
    ... | inl d≤c =
          Empty.rec (none d 1<d
                      (sq≤→≤ d s X
                        (≤-trans (subst (d · d ≤_) cd≡n (≤-·k d≤c)) n≤X)
                        X<ss)
                      d∣n)
    -- c < d: then c is the small factor, c · c ≤ c · d = n ≤ X, so
    -- c ≤ s; c > 1 is forbidden, and c ≠ 0, so c = 1 and d = n.
    ... | inr c<d with splitℕ-≤ 2 c
    ...   | inl 2≤c =
            Empty.rec (none c 2≤c
                        (sq≤→≤ c s X
                          (≤-trans
                            (subst (c · c ≤_) cd≡n
                              (≤-·-both (≤-refl {c}) (<-weaken c<d)))
                            n≤X)
                          X<ss)
                        c∣n)
    ...   | inr c<2 =
            inr (sym (·-identityˡ d) ∙ cong (_· d) (sym c≡1) ∙ cd≡n)
            where
            c≡1 : c ≡ 1
            c≡1 = ≤-antisym (pred-≤-pred c<2) (≢0→0< c c≢0)

------------------------------------------------------------------------
-- §4  THE THEOREM, in the note's own words
--
-- "n ≤ X, every prime factor of n greater than √X ⟹ n = 1 or n is
-- prime."  The prime hypothesis implies the divisor hypothesis because
-- every d > 1 has a prime divisor (`primeDivisor`), which then divides
-- n and is ≤ d ≤ s.  This is the ONE place factorization-flavoured
-- machinery enters, and it enters only as existence of a single prime
-- divisor.
------------------------------------------------------------------------

AllPrimeFactorsAbove : ℕ → ℕ → Type
AllPrimeFactorsAbove s n = (p : ℕ) → IsPrime p → p ∣ n → s < p

primeAbove→noSmallDivisor :
  (s n : ℕ) → AllPrimeFactorsAbove s n → NoSmallDivisor s n
primeAbove→noSmallDivisor s n above d 1<d d≤s d∣n =
  ¬m<m (<≤-trans (above p pp (∣-trans p∣d d∣n))
                 (≤-trans (m∣n→m≤n d≢0 p∣d) d≤s))
  where
  pd = primeDivisor d 1<d
  p  = pd .fst
  pp = pd .snd .fst
  p∣d = pd .snd .snd

  d≢0 : ¬ (d ≡ 0)
  d≢0 d≡0 = ¬-<-zero (subst (1 <_) d≡0 1<d)

roughSplitPrimes :
  (s X n : ℕ) → 0 < n → n ≤ X → X < suc s · suc s
  → AllPrimeFactorsAbove s n
  → (n ≡ 1) ⊎ IsPrime n
roughSplitPrimes s X n 0<n n≤X X<ss above =
  roughSplit s X n 0<n n≤X X<ss (primeAbove→noSmallDivisor s n above)

------------------------------------------------------------------------

-- THE STATEMENT THE NOTE ASKED FOR.
roughSplitSqrt :
  (X n : ℕ) → 0 < n → n ≤ X
  → AllPrimeFactorsAbove (isqrt X) n
  → (n ≡ 1) ⊎ IsPrime n
roughSplitSqrt X n 0<n n≤X above =
  roughSplitPrimes (isqrt X) X n 0<n n≤X (isqrt-upper X) above

roughSplitSqrtDiv :
  (X n : ℕ) → 0 < n → n ≤ X
  → NoSmallDivisor (isqrt X) n
  → (n ≡ 1) ⊎ IsPrime n
roughSplitSqrtDiv X n 0<n n≤X none =
  roughSplit (isqrt X) X n 0<n n≤X (isqrt-upper X) none

-- The X = n specialisation: the classical trial-division criterion.
-- (mathlib4 `Nat.prime_def_le_sqrt`; recorded so
-- that the general statement's specialisation is visible and checked.)
roughSplitSelf :
  (n : ℕ) → 0 < n → NoSmallDivisor (isqrt n) n → (n ≡ 1) ⊎ IsPrime n
roughSplitSelf n 0<n none = roughSplitSqrtDiv n n 0<n ≤-refl none

------------------------------------------------------------------------
-- §6  SHARPNESS:  n ≤ X cannot be dropped
--
-- 49 = 7 · 7 has isqrt 30 = 5 < 7, so every prime factor of
-- 49 clears the X = 30 horizon; 49 is neither 1 nor prime; and the sole
-- hypothesis of `roughSplitSqrt` that it fails is 49 ≤ 30.
------------------------------------------------------------------------

-- 7 is prime — proved BY the theorem, at X = n = 7 (isqrt 7 = 2, so
-- the only small divisor to rule out is 2).  The witness for the
-- sharpness of `roughSplitSqrt` is thus produced by `roughSplitSqrt`
-- itself; nothing about 7 is asserted by hand except that 2 ∤ 7.
private
  ¬2∣7 : ¬ (2 ∣ 7)
  ¬2∣7 h = go (∣-untrunc h)
    where
    go : Σ[ c ∈ ℕ ] c · 2 ≡ 7 → ⊥
    go (zero , e) = znots e
    go (suc zero , e) = znots (injSuc (injSuc e))
    go (suc (suc zero) , e) =
      znots (injSuc (injSuc (injSuc (injSuc e))))
    go (suc (suc (suc zero)) , e) =
      znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc e))))))
    go (suc (suc (suc (suc c))) , e) =
      snotz (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc e)))))))

  noSmall-7 : NoSmallDivisor (isqrt 7) 7
  noSmall-7 d 1<d d≤2 d∣7 with ≤-antisym d≤2 1<d
  ... | d≡2 = ¬2∣7 (subst (_∣ 7) d≡2 d∣7)

isPrime7 : IsPrime 7
isPrime7 with roughSplitSelf 7 (suc-≤-suc zero-≤) noSmall-7
... | inl 7≡1 = Empty.rec (snotz (injSuc 7≡1))
... | inr pp  = pp

7∣49 : 7 ∣ 49
7∣49 = ∣-left {m = 7} 7

49≢1 : ¬ (49 ≡ 1)
49≢1 p = snotz (injSuc p)

¬prime49 : ¬ (IsPrime 49)
¬prime49 pp with pp .snd 7 7∣49
... | inl 7≡1  = snotz (injSuc 7≡1)
... | inr 7≡49 =
  znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc 7≡49)))))))

-- Every prime factor of 49 exceeds the X = 30 horizon.  49 = 7 · 7, so
-- a prime divisor of it divides 7 (Euclid, `prime-∣-·`), hence IS 7.
49-rough-at-30 : AllPrimeFactorsAbove (isqrt 30) 49
49-rough-at-30 p pp p∣49 =
  subst (5 <_) (sym (prime-∣-prime p 7 pp isPrime7 p∣7)) ≤-sucℕ
  where
  p∣7 : p ∣ 7
  p∣7 with prime-∣-· p 7 7 pp p∣49
  ... | inl h = h
  ... | inr h = h

-- and yet:
n≤X-necessary :
  (¬ (49 ≡ 1)) × (¬ (IsPrime 49)) × AllPrimeFactorsAbove (isqrt 30) 49
n≤X-necessary = 49≢1 , ¬prime49 , 49-rough-at-30

------------------------------------------------------------------------
-- §7  SHARPNESS, second control:  the horizon cannot be lowered
--
-- `roughSplit` takes s with X < (s+1)².  That hypothesis is not slack.
-- At X = 30 and s = 4 it fails by exactly one step ((s+1)² = 25 ≤ 30),
-- and so does the conclusion: 25 ≤ 30, every prime factor of 25 exceeds
-- 4, and 25 is neither 1 nor prime.  So `isqrt X` in §5 is the smallest
-- horizon that works, not a convenient choice.
------------------------------------------------------------------------

private
  ¬2∣5 : ¬ (2 ∣ 5)
  ¬2∣5 h = go (∣-untrunc h)
    where
    go : Σ[ c ∈ ℕ ] c · 2 ≡ 5 → ⊥
    go (zero , e) = znots e
    go (suc zero , e) = znots (injSuc (injSuc e))
    go (suc (suc zero) , e) =
      znots (injSuc (injSuc (injSuc (injSuc e))))
    go (suc (suc (suc c)) , e) =
      snotz (injSuc (injSuc (injSuc (injSuc (injSuc e)))))

  noSmall-5 : NoSmallDivisor (isqrt 5) 5
  noSmall-5 d 1<d d≤2 d∣5 with ≤-antisym d≤2 1<d
  ... | d≡2 = ¬2∣5 (subst (_∣ 5) d≡2 d∣5)

isPrime5 : IsPrime 5
isPrime5 with roughSplitSelf 5 (suc-≤-suc zero-≤) noSmall-5
... | inl 5≡1 = Empty.rec (snotz (injSuc 5≡1))
... | inr pp  = pp

5∣25 : 5 ∣ 25
5∣25 = ∣-left {m = 5} 5

25≢1 : ¬ (25 ≡ 1)
25≢1 p = snotz (injSuc p)

¬prime25 : ¬ (IsPrime 25)
¬prime25 pp with pp .snd 5 5∣25
... | inl 5≡1  = snotz (injSuc 5≡1)
... | inr 5≡25 = znots (injSuc (injSuc (injSuc (injSuc (injSuc 5≡25)))))

25-rough-at-4 : AllPrimeFactorsAbove 4 25
25-rough-at-4 p pp p∣25 =
  subst (4 <_) (sym (prime-∣-prime p 5 pp isPrime5 p∣5)) ≤-refl
  where
  p∣5 : p ∣ 5
  p∣5 with prime-∣-· p 5 5 pp p∣25
  ... | inl h = h
  ... | inr h = h

-- 25 ≤ 30, all prime factors of 25 exceed 4, and 25 is neither 1 nor
-- prime.  The sole hypothesis of `roughSplit 4 30 25` that fails is
-- `30 < 5 · 5`.
horizon-necessary :
  (25 ≤ 30) × (¬ (25 ≡ 1)) × (¬ (IsPrime 25)) × AllPrimeFactorsAbove 4 25
horizon-necessary =
  (5 , refl) , 25≢1 , ¬prime25 , 25-rough-at-4
