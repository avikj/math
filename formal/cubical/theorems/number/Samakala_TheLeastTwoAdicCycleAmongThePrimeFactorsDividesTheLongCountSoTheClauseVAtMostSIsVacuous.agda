{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Samakala_TheLeastTwoAdicCycleAmongThePrimeFactorsDividesTheLongCountSoTheClauseVAtMostSIsVacuous
--
-- समकालः, synchrony.  The least 2-adic cycle length 2^ω among the prime
-- factors of an odd n automatically divides the Long Count n − 1, so
-- the clause "v ≤ s" of SEED-10 Theorem N (S) is a consequence of the
-- others and may be struck.
--
-- ────────────────────────────────────────────────────────────────────
-- THE SOURCE, VERBATIM (notes/SEED66_CRT_SYNCHRONISATION.md (absent from this repository), §2 and §8).
--
--   > **Theorem Y.** (a) $2^{\omega}\mid n-1$; hence $\omega\le s$.
--   > (b) For $b\in C$, the values taken by the common $v$ in the
--   > synchronisation clause $v_1=\dots=v_k=v$ are exactly
--   > $v\in\{0,1,\dots,\omega\}$, every value attained.
--   > (c) Consequently the clause "$v\le s$" in `SEED-10` Theorem N (S)
--   > is implied by the other clauses and may be deleted from the
--   > statement.
--
--   *Proof.* (a) For each $j$, $q_j\equiv1\pmod{2^{c_j}}$ and
--   $\omega\le c_j$, so $q_j\equiv1\pmod{2^{\omega}}$, hence
--   $q_j^{a_j}\equiv1\pmod{2^{\omega}}$ and
--   $n=\prod_jq_j^{a_j}\equiv1\pmod{2^{\omega}}$.  Thus
--   $2^{\omega}\mid n-1=2^sm$ with $m$ odd, i.e. $\omega\le s$.
--
--   (c) By (b) any $b$ satisfying the clause has $v\le\omega$, and by
--   (a) $\omega\le s$. $\square$
--
--   **Remark (this is the calendrical statement).** (a) says the cycles
--   are not independent of the ambient count: the *least* 2-adic cycle
--   length $2^{\omega}$ among the primes automatically divides the Long
--   Count $n-1$.  One never has to check the coincidence against $s$;
--   the coincidence, when it happens at all, happens inside the window.
--
--   ## 8. Successor seeds
--   3. **PROVE** — Theorems Y and Z in `formal/cubical/`; Y.a is four
--      lines and is the cheapest formalisation target in this whole
--      family.
--   4. **STRIKE** — the clause "$v\le s$" in `SEED-10` Theorem N (S),
--      per Theorem Y.
--
-- Here n = ∏_j q_j^{a_j} is odd with q_j − 1 = 2^{c_j} m_j (m_j odd),
-- ω = min_j c_j, and n − 1 = 2^s m with m odd.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED (over ℕ, with the library's truncated `_∣_` of
-- Cubical.Data.Nat.Divisibility, the one Prthakkarana_… also uses).
--
--   §1  Congruence-to-one is closed under product and power.
--         cong-1-mul  : M ∣ (x ∸ 1) → 1 ≤ x → M ∣ (y ∸ 1) → 1 ≤ y
--                       → M ∣ (x · y ∸ 1)
--                       (x = 1 + M u, y = 1 + M w ⟹ xy − 1 = M(u + w + M u w);
--                        the ring identity is discharged by `solveℕ!`)
--         cong-1-pow  : M ∣ (q ∸ 1) → 1 ≤ q → ∀ a → M ∣ (q ^ a ∸ 1)
--         cong-1-prod : every factor of a list ≡ 1 (mod M) and ≥ 1
--                       ⟹ the product ≡ 1 (mod M)
--   §2  Powers are monotone under divisibility.
--         pow-+       : b ^ (k + ω) ≡ b ^ k · b ^ ω
--         pow-mono-∣  : ω ≤ c → b ^ ω ∣ b ^ c            (pow2-mono = b := 2)
--   §3  THEOREM Y.a.  `Hyp ω fs` packages, for each (q_j , a_j) in the
--       list fs, a c_j with ω ≤ c_j, 2 ^ c_j ∣ (q_j ∸ 1) and 1 ≤ q_j;
--       `n-of fs` is ∏_j q_j ^ a_j.
--         theorem-Y-a : Hyp ω fs → 2 ^ ω ∣ (n-of fs ∸ 1)
--       ω is a parameter bounded by every c_j — that is all the proof
--       uses; the minimum is the sharpest such parameter.
--   §4  "hence ω ≤ s".  From 2^ω ∣ 2^s · m with m odd: if s < ω then
--       2^{s+1} ∣ 2^s · m, cancel 2^s (library `∣-cancelʳ`), so 2 ∣ m.
--         two-adic-bound          : ¬ (2 ∣ m) → 2 ^ ω ∣ (2 ^ s · m) → ω ≤ s
--         theorem-Y-a-consequence : Hyp ω fs → ¬ (2 ∣ m)
--                                   → n-of fs ∸ 1 ≡ 2 ^ s · m → ω ≤ s
--       and, with s the actual 2-adic valuation मानम् 2 (n ∸ 1) of the
--       corpus (Prthakkarana_…'s splitting पृथक्करणम् at p = 2),
--         ω≤v₂ : Hyp ω fs → (pos : 0 < n-of fs ∸ 1) → ω ≤ मानम् 2 (n-of fs ∸ 1) pos
--   §5  THE CLAUSE (c).  Given v ≤ ω (which is what Y.b supplies), v ≤ s:
--         clause-v≤s-is-implied : Hyp ω fs → ¬ (2 ∣ m) → n-of fs ∸ 1 ≡ 2 ^ s · m
--                                 → v ≤ ω → v ≤ s
--   §6  INSTANCES, by refl on closed terms and through theorem-Y-a:
--         561  = 3 · 11 · 17,  c = (1, 1, 4), ω = 1, 560  = 2^4 · 35,  s = 4
--         1105 = 5 · 13 · 17,  c = (2, 2, 4), ω = 2, 1104 = 2^4 · 69,  s = 4
--         45   = 3^2 · 5,      c = (1, 2),    ω = 1, 44   = 2^2 · 11,  s = 2
--       (the last exercises an exponent a_j > 1).
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS NOT HERE.
--
--   Y.b — that the common v ranges over exactly {0, …, ω}, every value
--   attained — needs element orders in the cyclic groups (ℤ/q_j)^× and
--   the CRT assembly; it is not formalised.  Only the direction Y.b
--   feeds into (c), namely "v ≤ ω", is taken as a hypothesis in §5.
--   Theorem Z (the synchronisation condition as a stabiliser condition)
--   and Theorem X of the same note are not touched.  Nothing here
--   involves strong non-witnesses, orders, or primality of the q_j: the
--   q_j are arbitrary naturals ≥ 1 with 2 ^ c_j ∣ q_j − 1, which is all
--   Y.a's proof consumes.
------------------------------------------------------------------------

module Samakala_TheLeastTwoAdicCycleAmongThePrimeFactorsDividesTheLongCountSoTheClauseVAtMostSIsVacuous where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; Σ-syntax)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁ ; map2)
open import Cubical.Tactics.NatSolver.Reflection using (solveℕ!)

open import Drdha_TheFirmNumbersProductIsEveryPositiveIntegerAndTheirMembershipIsDecidedByDivision
  using (दृढम्)
open import Ekatva_TheFirmFactorisationIsUniqueTwoPrimeListsWithOneProductAreAPermutationSoTheValuationIsWellDefinedAndPermIsExactlySameCount
  using (मानम्)
open import Prthakkarana_EveryPositiveIntegerIsAPrimePowerTimesAPrimeFreeRestTheExponentIsTheValuationAndTheValuationAddsOverProducts
  using (पृथक्करणम् ; मान-एकत्वम् ; गुण-धनः ; घात-धनः)

------------------------------------------------------------------------
-- §0 · bookkeeping
------------------------------------------------------------------------

-- a positive number is a successor
pos→suc : {x : ℕ} → 1 ≤ x → x ≡ suc (predℕ x)
pos→suc {x} h = suc-predℕ x (λ x≡0 → ¬-<-zero (subst (1 ≤_) x≡0 h))

------------------------------------------------------------------------
-- §1 · congruence to one is closed under product and power
------------------------------------------------------------------------

-- the four-line calculation:  (1 + M u)(1 + M w) − 1 = M (w + u + u M w)
private
  ring-mul : (u w M : ℕ) → (w + u + u · M · w) · M ≡ w · M + u · M · (1 + w · M)
  ring-mul u w M = solveℕ!

-- with the successors exposed:  M ∣ x, M ∣ y  ⟹  M ∣ (1 + x)(1 + y) − 1
cong-1-mul-suc : (M x y : ℕ) → M ∣ x → M ∣ y → M ∣ (suc x · suc y ∸ 1)
cong-1-mul-suc M x y =
  map2 λ { (u , p) (w , q) →
    (w + u + u · M · w) , (ring-mul u w M ∙ cong₂ (λ a b → a + b · suc a) q p) }

-- (L1)
cong-1-mul : (M x y : ℕ) → M ∣ (x ∸ 1) → 1 ≤ x → M ∣ (y ∸ 1) → 1 ≤ y
           → M ∣ (x · y ∸ 1)
cong-1-mul M zero    y       _  px _  _  = ⊥-rec (¬-<-zero px)
cong-1-mul M (suc x) zero    _  _  _  py = ⊥-rec (¬-<-zero py)
cong-1-mul M (suc x) (suc y) hx _  hy _  = cong-1-mul-suc M x y hx hy

-- (L2)
cong-1-pow : (M q : ℕ) → M ∣ (q ∸ 1) → 1 ≤ q → (a : ℕ) → M ∣ (q ^ a ∸ 1)
cong-1-pow M q h pq zero    = ∣-zeroʳ M
cong-1-pow M q h pq (suc a) =
  cong-1-mul M q (q ^ a) h pq (cong-1-pow M q h pq a) (घात-धनः q a pq)

-- (L3) lists of factors
prod : List ℕ → ℕ
prod []       = 1
prod (x ∷ xs) = x · prod xs

-- every factor is ≥ 1 and ≡ 1 (mod M)
AllCong1 : ℕ → List ℕ → Type₀
AllCong1 M []       = Unit
AllCong1 M (x ∷ xs) = ((1 ≤ x) × (M ∣ (x ∸ 1))) × AllCong1 M xs

prod-pos : (M : ℕ) (xs : List ℕ) → AllCong1 M xs → 1 ≤ prod xs
prod-pos M []       _                 = ≤-refl
prod-pos M (x ∷ xs) ((px , _) , rest) = गुण-धनः x (prod xs) px (prod-pos M xs rest)

cong-1-prod : (M : ℕ) (xs : List ℕ) → AllCong1 M xs → M ∣ (prod xs ∸ 1)
cong-1-prod M []       _                  = ∣-zeroʳ M
cong-1-prod M (x ∷ xs) ((px , hx) , rest) =
  cong-1-mul M x (prod xs) hx px (cong-1-prod M xs rest) (prod-pos M xs rest)

------------------------------------------------------------------------
-- §2 · powers are monotone under divisibility
------------------------------------------------------------------------

pow-+ : (b k ω : ℕ) → b ^ (k + ω) ≡ b ^ k · b ^ ω
pow-+ b zero    ω = sym (+-zero (b ^ ω))
pow-+ b (suc k) ω = cong (b ·_) (pow-+ b k ω) ∙ ·-assoc b (b ^ k) (b ^ ω)

pow-mono-∣ : (b ω c : ℕ) → ω ≤ c → (b ^ ω) ∣ (b ^ c)
pow-mono-∣ b ω c (k , e) =
  subst ((b ^ ω) ∣_) (sym (pow-+ b k ω) ∙ cong (b ^_) e) (∣-right (b ^ k))

-- (L4)
pow2-mono : (ω c : ℕ) → ω ≤ c → (2 ^ ω) ∣ (2 ^ c)
pow2-mono = pow-mono-∣ 2

------------------------------------------------------------------------
-- §3 · THEOREM Y.a
------------------------------------------------------------------------

-- the data of the theorem: a list of (q_j , a_j), and for each j a c_j
-- with ω ≤ c_j, 2 ^ c_j ∣ q_j − 1, q_j ≥ 1
Hyp : ℕ → List (ℕ × ℕ) → Type₀
Hyp ω []       = Unit
Hyp ω (p ∷ fs) =
  (Σ[ c ∈ ℕ ] ((ω ≤ c) × ((2 ^ c) ∣ (fst p ∸ 1)) × (1 ≤ fst p))) × Hyp ω fs

-- n = ∏_j q_j ^ a_j
n-of : List (ℕ × ℕ) → ℕ
n-of fs = prod (map (λ p → fst p ^ snd p) fs)

-- each q_j ^ a_j ≡ 1 (mod 2^ω):  2^ω ∣ 2^{c_j} ∣ q_j − 1, then the power
Hyp→AllCong1 : (ω : ℕ) (fs : List (ℕ × ℕ)) → Hyp ω fs
             → AllCong1 (2 ^ ω) (map (λ p → fst p ^ snd p) fs)
Hyp→AllCong1 ω []       _                                = tt
Hyp→AllCong1 ω (p ∷ fs) ((c , ω≤c , h , pq) , rest) =
  ( घात-धनः (fst p) (snd p) pq
  , cong-1-pow (2 ^ ω) (fst p) (∣-trans (pow2-mono ω c ω≤c) h) pq (snd p) )
  , Hyp→AllCong1 ω fs rest

-- (T1)  Theorem Y.a:  2^ω ∣ n − 1
theorem-Y-a : (ω : ℕ) (fs : List (ℕ × ℕ)) → Hyp ω fs → (2 ^ ω) ∣ (n-of fs ∸ 1)
theorem-Y-a ω fs H = cong-1-prod (2 ^ ω) _ (Hyp→AllCong1 ω fs H)

------------------------------------------------------------------------
-- §4 · hence ω ≤ s
------------------------------------------------------------------------

-- 2 ∣ c · 2, so a number of that shape is even
private
  even-·2 : (c : ℕ) → isEvenT (c · 2)
  even-·2 zero    = tt
  even-·2 (suc c) = even-·2 c

-- an odd number is not divisible by 2
odd→¬2∣ : (m : ℕ) → isOddT m → ¬ (2 ∣ m)
odd→¬2∣ m odd d =
  ¬evenAndOdd m
    ( subst isEvenT (snd (∣-untrunc d)) (even-·2 (fst (∣-untrunc d)))
    , odd )

-- (T2)  from 2^ω ∣ 2^s · m with m odd, ω ≤ s:
--       if s < ω then 2^{s+1} ∣ 2^s · m, and cancelling 2^s gives 2 ∣ m
two-adic-bound : (ω s m : ℕ) → ¬ (2 ∣ m) → (2 ^ ω) ∣ (2 ^ s · m) → ω ≤ s
two-adic-bound ω s m odd d with splitℕ-≤ ω s
... | inl ω≤s = ω≤s
... | inr s<ω = ⊥-rec (odd (∣-cancelʳ k (subst2 _∣_ e1 e2 d')))
  where
  d' : (2 ^ suc s) ∣ (2 ^ s · m)
  d' = ∣-trans (pow2-mono (suc s) ω s<ω) d

  k : ℕ
  k = predℕ (2 ^ s)

  e : 2 ^ s ≡ suc k
  e = pos→suc (घात-धनः 2 s (suc-≤-suc zero-≤))

  e1 : 2 ^ suc s ≡ 2 · suc k
  e1 = cong (2 ·_) e

  e2 : 2 ^ s · m ≡ m · suc k
  e2 = ·-comm (2 ^ s) m ∙ cong (m ·_) e

-- Theorem Y.a, second half:  with n − 1 = 2^s m, m odd,  ω ≤ s
theorem-Y-a-consequence : (ω : ℕ) (fs : List (ℕ × ℕ)) → Hyp ω fs
                        → (s m : ℕ) → ¬ (2 ∣ m) → n-of fs ∸ 1 ≡ 2 ^ s · m
                        → ω ≤ s
theorem-Y-a-consequence ω fs H s m odd e =
  two-adic-bound ω s m odd (subst ((2 ^ ω) ∣_) e (theorem-Y-a ω fs H))

-- and with s the corpus's own 2-adic valuation of n − 1
private
  दृढम्-2 : दृढम् 2
  दृढम्-2 = suc-≤-suc (suc-≤-suc zero-≤) , divisor
    where
    divisor : (d : ℕ) → d ∣ 2 → (d ≡ 1) ⊎ (d ≡ 2)
    divisor zero                d = ⊥-rec (¬-<-zero (m∣sn→z<m d))
    divisor (suc zero)          _ = inl refl
    divisor (suc (suc zero))    _ = inr refl
    divisor (suc (suc (suc d))) h =
      ⊥-rec (¬-<-zero (pred-≤-pred (pred-≤-pred (m∣sn→m≤sn h))))

ω≤v₂ : (ω : ℕ) (fs : List (ℕ × ℕ)) → Hyp ω fs
     → (pos : 0 < n-of fs ∸ 1) → ω ≤ मानम् 2 (n-of fs ∸ 1) pos
ω≤v₂ ω fs H pos =
  theorem-Y-a-consequence ω fs H _ (fst split) (snd (snd split)) (fst (snd split))
  where
  split = पृथक्करणम् 2 दृढम्-2 (n-of fs ∸ 1) pos

------------------------------------------------------------------------
-- §5 · the clause "v ≤ s" is implied
------------------------------------------------------------------------

-- (c)  any v ≤ ω (which Y.b supplies for the common v) has v ≤ s
clause-v≤s-is-implied : (ω : ℕ) (fs : List (ℕ × ℕ)) → Hyp ω fs
                      → (s m : ℕ) → ¬ (2 ∣ m) → n-of fs ∸ 1 ≡ 2 ^ s · m
                      → (v : ℕ) → v ≤ ω → v ≤ s
clause-v≤s-is-implied ω fs H s m odd e v v≤ω =
  ≤-trans v≤ω (theorem-Y-a-consequence ω fs H s m odd e)

------------------------------------------------------------------------
-- §6 · instances
------------------------------------------------------------------------

-- 561 = 3 · 11 · 17;  c = (1, 1, 4);  ω = 1;  560 = 2^4 · 35;  s = 4
fs-561 : List (ℕ × ℕ)
fs-561 = (3 , 1) ∷ (11 , 1) ∷ (17 , 1) ∷ []

n-561 : n-of fs-561 ≡ 561
n-561 = refl

hyp-561 : Hyp 1 fs-561
hyp-561 =
    (1 , ≤-refl    , ∣ 1 , refl ∣₁ , (2  , refl))
  , (1 , ≤-refl    , ∣ 5 , refl ∣₁ , (10 , refl))
  , (4 , (3 , refl) , ∣ 1 , refl ∣₁ , (16 , refl))
  , tt

Y-a-561 : (2 ^ 1) ∣ (561 ∸ 1)
Y-a-561 = theorem-Y-a 1 fs-561 hyp-561

Y-a-561-refl : (2 ^ 1) ∣ (561 ∸ 1)
Y-a-561-refl = ∣ 280 , refl ∣₁

s-561 : 561 ∸ 1 ≡ 2 ^ 4 · 35
s-561 = refl

ω≤s-561 : 1 ≤ 4
ω≤s-561 = theorem-Y-a-consequence 1 fs-561 hyp-561 4 35 (odd→¬2∣ 35 tt) refl

-- 1105 = 5 · 13 · 17;  c = (2, 2, 4);  ω = 2;  1104 = 2^4 · 69;  s = 4
fs-1105 : List (ℕ × ℕ)
fs-1105 = (5 , 1) ∷ (13 , 1) ∷ (17 , 1) ∷ []

n-1105 : n-of fs-1105 ≡ 1105
n-1105 = refl

hyp-1105 : Hyp 2 fs-1105
hyp-1105 =
    (2 , ≤-refl    , ∣ 1 , refl ∣₁ , (4  , refl))
  , (2 , ≤-refl    , ∣ 3 , refl ∣₁ , (12 , refl))
  , (4 , (2 , refl) , ∣ 1 , refl ∣₁ , (16 , refl))
  , tt

Y-a-1105 : (2 ^ 2) ∣ (1105 ∸ 1)
Y-a-1105 = theorem-Y-a 2 fs-1105 hyp-1105

Y-a-1105-refl : (2 ^ 2) ∣ (1105 ∸ 1)
Y-a-1105-refl = ∣ 276 , refl ∣₁

s-1105 : 1105 ∸ 1 ≡ 2 ^ 4 · 69
s-1105 = refl

ω≤s-1105 : 2 ≤ 4
ω≤s-1105 = theorem-Y-a-consequence 2 fs-1105 hyp-1105 4 69 (odd→¬2∣ 69 tt) refl

-- 45 = 3^2 · 5;  c = (1, 2);  ω = 1;  44 = 2^2 · 11;  s = 2  (an exponent > 1)
fs-45 : List (ℕ × ℕ)
fs-45 = (3 , 2) ∷ (5 , 1) ∷ []

n-45 : n-of fs-45 ≡ 45
n-45 = refl

hyp-45 : Hyp 1 fs-45
hyp-45 =
    (1 , ≤-refl    , ∣ 1 , refl ∣₁ , (2 , refl))
  , (2 , (1 , refl) , ∣ 1 , refl ∣₁ , (4 , refl))
  , tt

Y-a-45 : (2 ^ 1) ∣ (45 ∸ 1)
Y-a-45 = theorem-Y-a 1 fs-45 hyp-45

ω≤s-45 : 1 ≤ 2
ω≤s-45 = theorem-Y-a-consequence 1 fs-45 hyp-45 2 11 (odd→¬2∣ 11 tt) refl
