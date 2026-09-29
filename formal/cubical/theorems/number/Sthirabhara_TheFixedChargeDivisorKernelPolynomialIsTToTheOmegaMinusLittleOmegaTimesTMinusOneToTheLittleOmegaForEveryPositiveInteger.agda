{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Sthirabhara_TheFixedChargeDivisorKernelPolynomialIsTToTheOmegaMinusLittleOmegaTimesTMinusOneToTheLittleOmegaForEveryPositiveInteger
--
-- -, the fixed charge.  D0026 §5.5 displays
--
--     "Φ_n(t) = Σ_{d|n} μ(n/d) t^{Ω(d)} = t^{Ω(n)−ω(n)} (t−1)^{ω(n)}"
--
-- whose coefficients are the fixed-charge divisor kernels κ_r(n).  The
-- package's (1.1)–(1.3) say, with ρ(d) = Ω(d) − ω(d) and j = ω(d), that
-- κ_r(d) = (−1)^{j−k} C(j,k) with k = r − ρ, so that κ₁(d) = (−1)^{j−1} j
-- if ρ = 0, (−1)^j if ρ = 1, 0 if ρ ≥ 2; and D0026 §5.4 says
--
--     "κ₁(d) = Σ_{p|d} μ(d/p) — sparse and Möbius-coherent but not
--      multiplicative".
--
-- `ChargePolynomialFinite.agda` certified the identity at n = 12, 30,
-- 360 only, on factorisation TABLES taken as input.  This module proves the
-- identity for EVERY n ≥ 1, from the corpus's own μ, divisibility and
-- factorisation, with no table.
--
-- DEFINITIONS (§1–2).  ℤ[t] is represented as coefficient sequences,
-- Poly = ℕ → ℤ, so that κ_r(n) is literally the r-th coefficient:
--
--     term n d r     = [d ∣ n] · μ(n/d) · [r = Ω(d)]
--     Φ n r          = Σ_{d=1}^{n} term n d r      -- Φ_n(t) = Σ_{d|n} μ(n/d) t^{Ω(d)}
--     κ r n          = Φ n r                        -- = Σ_{d|n, Ω(d)=r} μ(n/d)
--     closedForm a b = t^a (t−1)^b                  -- tPow a (tm1Pow b)
--
-- with μ = `mu`, [d ∣ n] = `dividesb`, n/d = `_div_` and Ω = `bigOmega`,
-- all of `TransmissionRefutations` (fuel-bounded trial-division
-- programs, specified in `MobiusPhi_…`); ω is defined here by the same
-- least-prime-factor recursion as Ω, counting a prime at its last
-- occurrence.  Both are then IDENTIFIED with the corpus's factorisation
-- (§8, §9, §11):
--
--     Ω-is-length-of-every-firm-factorisation :
--       (n : ℕ) (L : List ℕ) → सर्वे दृढम् L → वधः L ≡ n → Ω n ≡ length L
--     Ω-is-length-of-Drdha-factorisation :
--       (n : ℕ) (0<n : 0 < n) → Ω n ≡ length (fst (विभाजनम् n 0<n))
--     Ω-additive       : (m n : ℕ) → 1 ≤ m → 1 ≤ n → Ω (m · n) ≡ Ω m + Ω n
--     ω-is-smallOmega  : (n : ℕ) → 1 ≤ n → ω n ≡ smallOmega n
--
-- so Ω(n) is the length of Drdha's list — of EVERY list of firm numbers
-- with product n, by Uniqueness's uniqueness (a Perm preserves length) —
-- and ω(n) is TransmissionRefutations' exhaustive count of primes
-- dividing n, whose `isPrimeb` is shown to be Drdha's दृढम् in both
-- directions (`isPrimeb-firm`, `firm-isPrimeb`).
--
-- WHAT IS PROVED.
--
--   Φ-closed-form : (n : ℕ) → 1 ≤ n → Φ n ≡ closedForm (Ω n ∸ ω n) (ω n)
--   κ-closed-form : (r n : ℕ) → 1 ≤ n → κ r n ≡ closedForm (Ω n ∸ ω n) (ω n) r
--
-- i.e. Φ_n(t) = t^{Ω(n)−ω(n)} (t−1)^{ω(n)} as an equality of coefficient
-- sequences (a path in ℕ → ℤ), for every n ≥ 1.  The route is NOT
-- multiplicativity but the peeling recursion along the least prime
-- factor p of m = p·c (§4):
--
--   Φ-peel-repeat : 2 ≤ m → p ∣ c → Φ m ≡ t · Φ c
--   Φ-peel-new    : 2 ≤ m → p ∤ c → Φ m ≡ (t − 1) · Φ c
--
-- The divisors of m split into the p-free ones, which are the p-free
-- divisors of c by Gauss's lemma, and the multiples p·e with e ∣ c;
-- μ(p·(c/d)) is read off MobiusPhi's `mu-mult`, and Euclid's lemma from
-- Drdha (युक्लिड-वाक्यम्) kills the first half when p ∣ c.  With
-- Ω(m) = Ω(c) + 1 and ω(m) = ω(c) + [p ∤ c] — the recursions of Ω and ω
-- with their fuel discharged (§3) — the closed form follows by
-- induction (§5).  Then for κ₁ (§6):
--
--   κ₁-is-prime-cofactor-sum : (n : ℕ) → κ 1 n ≡ primeCofactorSum n
--       -- Σ_{p ≤ n} [p prime][p ∣ n] μ(n/p), i.e. §5.4's Σ_{p|d} μ(d/p)
--   κ₁-three-cases : (n : ℕ) → 1 ≤ n → κ 1 n ≡ threeCase (Ω n ∸ ω n) (ω n)
--       -- threeCase 0 j = (−1)^{j−1}·j,  threeCase 1 j = (−1)^j,
--       -- threeCase (2+_) j = 0;  as κ₁-ρ0, κ₁-ρ1, κ₁-ρ≥2 separately
--   κ₁-not-multiplicative : ¬ (κ 1 6 ≡ κ 1 2 · κ 1 3)      -- −2 ≠ 1
--
-- and the general kernel (1.1)–(1.3) (§10), with `binom` Pascal's
-- triangle and `parity k` = (−1)^k:
--
--   κ-general : 1 ≤ n → ρ ≤ r → κ r n ≡ (−1)^{ω(n) − (r−ρ)} · C(ω(n), r−ρ)
--   κ-below-ρ : 1 ≤ n → r < ρ → κ r n ≡ 0                (ρ := Ω n ∸ ω n)
--
-- CHECKED BY refl (§7), from the RAW divisor sum, not from the closed
-- form:  coeffs (Φ 12) = (0, 1, −2, 1, 0),  coeffs (Φ 30) =
-- (−1, 3, −3, 1, 0),  coeffs (Φ 360) = (0, 0, 0, −1, 3, −3, 1, 0), with
-- (Ω, ω) = (3, 2), (3, 3), (6, 3); and κ₁(6) = −2 while κ₁(2)·κ₁(3) = 1.
--
-- No postulates, no holes, no termination pragmas; every fuel-bounded
-- program is used only on the range where its specification is proved.
------------------------------------------------------------------------

module Sthirabhara_TheFixedChargeDivisorKernelPolynomialIsTToTheOmegaMinusLittleOmegaTimesTMinusOneToTheLittleOmegaForEveryPositiveInteger where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; _∸_ ; snotz ; znots ; injSuc
        ; +-zero ; +-suc ; +-comm ; +-assoc ; ·-comm ; ·-assoc
        ; ·-identityʳ ; ·-identityˡ ; 0≡m·0 ; isSetℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Int
  using (ℤ ; pos ; negsuc ; -_)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Int.Properties
  using (+Comm ; +Assoc ; pos0+ ; -Dist+ ; -DistL· ; ·DistR+ ; ·IdR ; ·AnnihilR
        ; pos+ ; negsucNotpos ; injPos)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; if_then_else_ ; _and_ ; true≢false ; false≢true)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.List.Properties using (length++)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

open import TransmissionRefutations
  using (eqb ; leb ; dividesb ; spf ; isPrimeb ; mu ; negZ ; bigOmegaF ; bigOmega
        ; omegaCount ; smallOmega ; parity ; addN)
  renaming (_div_ to _divN_ ; _mod_ to _modN_)
open import MobiusPhi_TheDivisorSumOfMobiusTimesCofactorIsEulersTotientForEveryPositiveInteger
  using (eqb-dec ; eqb-refl ; eqb-≢ ; leb-dec ; leb-≤ ; if-true ; if-false
        ; modN-unique ; dividesb-dec ; dividesb-∣ ; ∣-dividesb ; ¬∣-dividesb
        ; divN-exact ; divN-< ; dividesb-false→¬∣
        ; Σ≤ ; Σ≤-ext ; Σ≤-const0 ; Σ≤-zero ; Σ≤-add ; Σ≤-above ; Σ≤-multiples
        ; 2≤spf ; 0<spf ; spf∣ ; spf-least ; spf-prime ; mu-mult
        ; bool-split ; A-eq ; prod-pos ; 0<· ; cancel-∣ ; coprime-of-prime ; gauss
        ; if-and ; addN≡+ ; pos-if)
open import Drdha_TheFirmNumbersProductIsEveryPositiveIntegerAndTheirMembershipIsDecidedByDivision
  using (दृढम् ; वधः ; सर्वे ; विभाजनम् ; युक्लिड-वाक्यम् ; वध-++ ; सर्वे-++)
open import Ekatva_TheFirmFactorisationIsUniqueTwoPrimeListsWithOneProductAreAPermutationSoTheValuationIsWellDefinedAndPermIsExactlySameCount
  using (एकत्वम् ; वध-धनः)
open import TheUsualReasonsMadeExplicitTheInductivePermutationRelationEmbedsInAdjacentTranspositions
  using (Insert ; here ; there ; Perm ; pnil ; pcons)

------------------------------------------------------------------------
-- 1.  ℤ[t] as coefficient sequences.  The r-th coefficient of P is P r.
------------------------------------------------------------------------

Poly : Type₀
Poly = ℕ → ℤ

-- the monomial t^k
X^ : ℕ → Poly
X^ k r = if eqb r k then pos 1 else pos 0

infixl 6 _+P_
infixr 7 _·P_

_+P_ : Poly → Poly → Poly
(P +P Q) r = P r +ℤ Q r

_·P_ : ℤ → Poly → Poly
(z ·P P) r = z ·ℤ P r

-P_ : Poly → Poly
(-P P) r = - P r

-- multiplication by t: shift the coefficients up
tP : Poly → Poly
tP P zero = pos 0
tP P (suc r) = P r

-- multiplication by (t − 1)
tm1P : Poly → Poly
tm1P P = tP P +P (-P P)

-- t^a · Q
tPow : ℕ → Poly → Poly
tPow zero Q = Q
tPow (suc a) Q = tP (tPow a Q)

-- (t − 1)^b
tm1Pow : ℕ → Poly
tm1Pow zero = X^ 0
tm1Pow (suc b) = tm1P (tm1Pow b)

-- the closed form t^a (t − 1)^b
closedForm : ℕ → ℕ → Poly
closedForm a b = tPow a (tm1Pow b)

-- the first k coefficients, as a list (for the refl checks)
coeffsFrom : Poly → ℕ → ℕ → List ℤ
coeffsFrom P i zero = []
coeffsFrom P i (suc k) = P i ∷ coeffsFrom P (suc i) k

coeffs : Poly → ℕ → List ℤ
coeffs P = coeffsFrom P 0

------------------------------------------------------------------------
-- 2.  Ω, ω, and the divisor-sum polynomial Φ_n(t) = Σ_{d ∣ n} μ(n/d) t^{Ω(d)}.
--
-- Ω is `bigOmega` of TransmissionRefutations: Ω(1) = 0 and
-- Ω(n) = 1 + Ω(n / spf n), i.e. the number of steps of repeated
-- least-prime-factor division (§8 identifies it with the LENGTH of
-- every firm factorisation of n).  ω runs the same recursion and counts
-- a step exactly when the prime being removed does not divide the
-- quotient, i.e. at its last occurrence (§9 identifies it with the
-- exhaustive count of primes dividing n).
------------------------------------------------------------------------

Ω : ℕ → ℕ
Ω = bigOmega

ωF : ℕ → ℕ → ℕ
ωF zero _ = 0
ωF (suc f) n =
  if eqb n 1 then 0
  else (if dividesb (spf n) (n divN spf n)
          then ωF f (n divN spf n)
          else suc (ωF f (n divN spf n)))

ω : ℕ → ℕ
ω n = ωF n n

-- the summand [d ∣ n] · μ(n/d) · t^{Ω(d)}, coefficient by coefficient
term : ℕ → ℕ → Poly
term n d r = if dividesb d n then mu (n divN d) ·ℤ X^ (Ω d) r else pos 0

-- Φ_n(t): the sum over d = 1..n of the summand
Φ : ℕ → Poly
Φ n r = Σ≤ (λ d → term n d r) n

-- the fixed-charge divisor kernel κ_r(n) IS the r-th coefficient:
-- κ_r(n) = Σ_{d ∣ n, Ω(d) = r} μ(n/d)
κ : ℕ → ℕ → ℤ
κ r n = Φ n r

------------------------------------------------------------------------
-- 3.  The recursion laws of Ω and ω, with the fuel discharged.
------------------------------------------------------------------------

n≢1 : (n : ℕ) → 2 ≤ n → ¬ n ≡ 1
n≢1 n 2≤n n≡1 = ¬m<m (subst (2 ≤_) n≡1 2≤n)

1≤ : (n : ℕ) → 2 ≤ n → 1 ≤ n
1≤ n 2≤n = ≤-trans (suc-≤-suc zero-≤) 2≤n

-- the quotient by the least prime factor: positive, smaller, exact
quot-eq : (n : ℕ) → 2 ≤ n → spf n · (n divN spf n) ≡ n
quot-eq n 2≤n = ·-comm (spf n) _ ∙ divN-exact (spf n) n (0<spf n 2≤n) (spf∣ n 2≤n)

quot-pos : (n : ℕ) → 2 ≤ n → 1 ≤ n divN spf n
quot-pos n 2≤n = prod-pos (spf n) (n divN spf n) n (quot-eq n 2≤n) (1≤ n 2≤n)

quot-< : (n : ℕ) → 2 ≤ n → n divN spf n < n
quot-< n 2≤n = divN-< (spf n) n (2≤spf n 2≤n) (1≤ n 2≤n)

-- Ω

ΩF-unfold : (f n : ℕ) → 2 ≤ n → bigOmegaF (suc f) n ≡ suc (bigOmegaF f (n divN spf n))
ΩF-unfold f n 2≤n =
  if-false (_≡ suc (bigOmegaF f (n divN spf n))) 0 _ (eqb-≢ n 1 (n≢1 n 2≤n)) refl

ΩF-stable : (f g n : ℕ) → 1 ≤ n → n ≤ f → n ≤ g → bigOmegaF f n ≡ bigOmegaF g n
ΩF-stable zero g n 1≤n n≤0 _ = ⊥rec (¬-<-zero (≤-trans 1≤n n≤0))
ΩF-stable (suc f) zero n 1≤n _ n≤0 = ⊥rec (¬-<-zero (≤-trans 1≤n n≤0))
ΩF-stable (suc f) (suc g) zero 1≤n _ _ = ⊥rec (¬-<-zero 1≤n)
ΩF-stable (suc f) (suc g) (suc zero) _ _ _ = refl
ΩF-stable (suc f) (suc g) (suc (suc n')) _ n≤sf n≤sg =
  ΩF-unfold f n 2≤n
  ∙ cong suc (ΩF-stable f g q (quot-pos n 2≤n)
                (pred-≤-pred (≤-trans (quot-< n 2≤n) n≤sf))
                (pred-≤-pred (≤-trans (quot-< n 2≤n) n≤sg)))
  ∙ sym (ΩF-unfold g n 2≤n)
  where
  n = suc (suc n')
  2≤n : 2 ≤ n
  2≤n = suc-≤-suc (suc-≤-suc zero-≤)
  q = n divN spf n

Ω-1 : Ω 1 ≡ 0
Ω-1 = refl

Ω-step : (n : ℕ) → 2 ≤ n → Ω n ≡ suc (Ω (n divN spf n))
Ω-step zero h = ⊥rec (¬-<-zero h)
Ω-step (suc n') h =
  ΩF-unfold n' (suc n') h
  ∙ cong suc (ΩF-stable n' q q (quot-pos (suc n') h) (pred-≤-pred (quot-< (suc n') h)) ≤-refl)
  where
  q = (suc n') divN spf (suc n')

-- the least prime factor of p·e is p when every divisor ≥ 2 is ≥ p
spf-of-mult : (p e : ℕ) → 2 ≤ p → 1 ≤ e
            → ((d : ℕ) → 2 ≤ d → d ∣ (p · e) → p ≤ d)
            → (2 ≤ p · e) × ((spf (p · e) ≡ p) × ((p · e) divN p ≡ e))
spf-of-mult p e 2≤p 1≤e least = 2≤m , spf≡p , q≡e
  where
  m = p · e
  0<p : 0 < p
  0<p = ≤-trans (suc-≤-suc zero-≤) 2≤p
  p≤m : p ≤ m
  p≤m = subst (_≤ m) (·-identityˡ p) (subst (1 · p ≤_) (·-comm e p) (≤-·k {k = p} 1≤e))
  2≤m : 2 ≤ m
  2≤m = ≤-trans 2≤p p≤m
  spf≡p : spf m ≡ p
  spf≡p = ≤-antisym (spf-least m 2≤m p 2≤p (∣-left e))
                    (least (spf m) (2≤spf m 2≤m) (spf∣ m 2≤m))
  q≡e : m divN p ≡ e
  q≡e = fst (modN-unique m p e 0 0<p 0<p (+-zero (e · p) ∙ ·-comm e p))

Ω-mult : (p e : ℕ) → 2 ≤ p → 1 ≤ e
       → ((d : ℕ) → 2 ≤ d → d ∣ (p · e) → p ≤ d)
       → Ω (p · e) ≡ suc (Ω e)
Ω-mult p e 2≤p 1≤e least =
  Ω-step (p · e) (fst s)
  ∙ cong (λ z → suc (Ω z)) (cong ((p · e) divN_) (fst (snd s)) ∙ snd (snd s))
  where
  s = spf-of-mult p e 2≤p 1≤e least

-- ω

ωF-unfold : (f n : ℕ) → 2 ≤ n
          → ωF (suc f) n ≡ (if dividesb (spf n) (n divN spf n)
                              then ωF f (n divN spf n) else suc (ωF f (n divN spf n)))
ωF-unfold f n 2≤n =
  if-false (_≡ (if dividesb (spf n) (n divN spf n)
                  then ωF f (n divN spf n) else suc (ωF f (n divN spf n))))
           0 _ (eqb-≢ n 1 (n≢1 n 2≤n)) refl

ωF-stable : (f g n : ℕ) → 1 ≤ n → n ≤ f → n ≤ g → ωF f n ≡ ωF g n
ωF-stable zero g n 1≤n n≤0 _ = ⊥rec (¬-<-zero (≤-trans 1≤n n≤0))
ωF-stable (suc f) zero n 1≤n _ n≤0 = ⊥rec (¬-<-zero (≤-trans 1≤n n≤0))
ωF-stable (suc f) (suc g) zero 1≤n _ _ = ⊥rec (¬-<-zero 1≤n)
ωF-stable (suc f) (suc g) (suc zero) _ _ _ = refl
ωF-stable (suc f) (suc g) (suc (suc n')) _ n≤sf n≤sg =
  ωF-unfold f n 2≤n
  ∙ cong (λ z → if dividesb (spf n) q then z else suc z)
         (ωF-stable f g q (quot-pos n 2≤n)
                (pred-≤-pred (≤-trans (quot-< n 2≤n) n≤sf))
                (pred-≤-pred (≤-trans (quot-< n 2≤n) n≤sg)))
  ∙ sym (ωF-unfold g n 2≤n)
  where
  n = suc (suc n')
  2≤n : 2 ≤ n
  2≤n = suc-≤-suc (suc-≤-suc zero-≤)
  q = n divN spf n

ω-1 : ω 1 ≡ 0
ω-1 = refl

ω-step : (n : ℕ) → 2 ≤ n
       → ω n ≡ (if dividesb (spf n) (n divN spf n) then ω (n divN spf n) else suc (ω (n divN spf n)))
ω-step zero h = ⊥rec (¬-<-zero h)
ω-step (suc n') h =
  ωF-unfold n' (suc n') h
  ∙ cong (λ z → if dividesb (spf (suc n')) q then z else suc z)
         (ωF-stable n' q q (quot-pos (suc n') h) (pred-≤-pred (quot-< (suc n') h)) ≤-refl)
  where
  q = (suc n') divN spf (suc n')

ω-mult : (p e : ℕ) → 2 ≤ p → 1 ≤ e
       → ((d : ℕ) → 2 ≤ d → d ∣ (p · e) → p ≤ d)
       → ω (p · e) ≡ (if dividesb p e then ω e else suc (ω e))
ω-mult p e 2≤p 1≤e least =
  ω-step (p · e) (fst s)
  ∙ cong₂ (λ p' z → if dividesb p' z then ω z else suc (ω z)) (fst (snd s))
          (cong ((p · e) divN_) (fst (snd s)) ∙ snd (snd s))
  where
  s = spf-of-mult p e 2≤p 1≤e least

-- ω ≤ Ω
if-bound : (b : Bool) (x y z : ℕ) → x ≤ z → y ≤ z → (if b then x else y) ≤ z
if-bound true x y z hx hy = hx
if-bound false x y z hx hy = hy

ω≤Ω-fuel : (f n : ℕ) → n ≤ f → 1 ≤ n → ω n ≤ Ω n
ω≤Ω-fuel zero n n≤0 1≤n = ⊥rec (¬-<-zero (≤-trans 1≤n n≤0))
ω≤Ω-fuel (suc f) zero _ 1≤n = ⊥rec (¬-<-zero 1≤n)
ω≤Ω-fuel (suc f) (suc zero) _ _ = ≤-refl
ω≤Ω-fuel (suc f) (suc (suc n')) n≤sf _ =
  subst2 _≤_ (sym (ω-step n 2≤n)) (sym (Ω-step n 2≤n))
         (if-bound (dividesb (spf n) q) (ω q) (suc (ω q)) (suc (Ω q)) (≤-suc ih) (suc-≤-suc ih))
  where
  n = suc (suc n')
  2≤n : 2 ≤ n
  2≤n = suc-≤-suc (suc-≤-suc zero-≤)
  q = n divN spf n
  ih : ω q ≤ Ω q
  ih = ω≤Ω-fuel f q (pred-≤-pred (≤-trans (quot-< n 2≤n) n≤sf)) (quot-pos n 2≤n)

ω≤Ω : (n : ℕ) → 1 ≤ n → ω n ≤ Ω n
ω≤Ω n 1≤n = ω≤Ω-fuel n n ≤-refl 1≤n

------------------------------------------------------------------------
-- 4.  THE PEELING IDENTITY.  For m ≥ 2 with p = spf m and m = p·c:
--
--     Φ_m(t) = t · Φ_c(t)          if p ∣ c,
--     Φ_m(t) = (t − 1) · Φ_c(t)    if p ∤ c.
--
-- The divisors d of m split into the p-free ones, which are exactly the
-- p-free divisors of c (Gauss), and the multiples p·e with e ∣ c.  On
-- the second half Ω(p·e) = 1 + Ω(e) and m/(p·e) = c/e, so it is t·Φ_c.
-- On the first half μ(m/d) = μ(p · (c/d)) is 0 when p ∣ c/d and
-- −μ(c/d) otherwise; if p ∣ c then, d being p-free, p ∣ c/d (Euclid)
-- and the half vanishes; if p ∤ c the half is −Φ_c.
------------------------------------------------------------------------

Σ≤-neg : (f : ℕ → ℤ) (k : ℕ) → Σ≤ (λ i → - f i) k ≡ - Σ≤ f k
Σ≤-neg f zero = refl
Σ≤-neg f (suc k) = cong (- f (suc k) +ℤ_) (Σ≤-neg f k) ∙ sym (-Dist+ (f (suc k)) (Σ≤ f k))

if-annihil : (b : Bool) (z : ℤ) → (if b then z ·ℤ pos 0 else pos 0) ≡ pos 0
if-annihil true z = ·AnnihilR z
if-annihil false z = refl

-- a sum of shifted monomials is the shift of the sum
shift-sum : (c : ℕ) (g : ℕ → ℤ) (k : ℕ → ℕ) (b : ℕ → Bool) (r : ℕ)
          → Σ≤ (λ e → if b e then g e ·ℤ X^ (suc (k e)) r else pos 0) c
          ≡ tP (λ r' → Σ≤ (λ e → if b e then g e ·ℤ X^ (k e) r' else pos 0) c) r
shift-sum c g k b zero = Σ≤-zero _ c (λ e _ _ → if-annihil (b e) (g e))
shift-sum c g k b (suc r) = refl

Φ-peel : (m : ℕ) → 2 ≤ m → (r : ℕ)
       → Φ m r ≡ (if dividesb (spf m) (m divN spf m) then pos 0 else - Φ (m divN spf m) r)
                 +ℤ tP (Φ (m divN spf m)) r
Φ-peel m 2≤m r =
  Σ≤-ext T (λ d → A d +ℤ B d) m (λ d _ _ → bool-split (dividesb p d) (T d))
  ∙ Σ≤-add A B m
  ∙ cong₂ _+ℤ_ (stepA ∙ stepA') stepB
  where
  p = spf m
  c = m divN p
  1≤m : 1 ≤ m
  1≤m = 1≤ m 2≤m
  m≢0 : ¬ m ≡ 0
  m≢0 m≡0 = ¬-<-zero (subst (1 ≤_) m≡0 1≤m)
  2≤p : 2 ≤ p
  2≤p = 2≤spf m 2≤m
  0<p : 0 < p
  0<p = 0<spf m 2≤m
  m≡pc : p · c ≡ m
  m≡pc = quot-eq m 2≤m
  1≤c : 1 ≤ c
  1≤c = quot-pos m 2≤m
  c≢0 : ¬ c ≡ 0
  c≢0 c≡0 = ¬-<-zero (subst (1 ≤_) c≡0 1≤c)
  c∣m : c ∣ m
  c∣m = subst (c ∣_) m≡pc (∣-right p)
  c≤m : c ≤ m
  c≤m = m∣n→m≤n m≢0 c∣m
  prime : (k : ℕ) → k ∣ p → (k ≡ 1) ⊎ (k ≡ p)
  prime = spf-prime m 2≤m

  x y : ℕ → ℤ
  x d = mu (m divN d) ·ℤ X^ (Ω d) r
  y d = mu (c divN d) ·ℤ X^ (Ω d) r

  T A B A' : ℕ → ℤ
  T d = term m d r
  A d = if dividesb p d then pos 0 else T d
  B d = if dividesb p d then T d else pos 0
  A' d = if dividesb d c then (if dividesb p d then pos 0 else x d) else pos 0

  d∣m→d∣c : (d : ℕ) → ¬ p ∣ d → d ∣ m → d ∣ c
  d∣m→d∣c d ¬p∣d d∣m = gauss p d c (coprime-of-prime p d prime ¬p∣d) (subst (d ∣_) (sym m≡pc) d∣m)
  d∣c→d∣m : (d : ℕ) → d ∣ c → d ∣ m
  d∣c→d∣m d d∣c = ∣-trans d∣c c∣m

  -- for d ∣ c:  m / d = p · (c / d),  c / d ≥ 1,  and μ(m/d) by mu-mult
  quot-split : (d : ℕ) → 1 ≤ d → d ∣ c → m divN d ≡ p · (c divN d)
  quot-split d 1≤d d∣c =
    fst (modN-unique m d (p · (c divN d)) 0 1≤d 1≤d
           (+-zero _ ∙ sym (·-assoc p (c divN d) d) ∙ cong (p ·_) (divN-exact d c 1≤d d∣c) ∙ m≡pc))

  1≤c/d : (d : ℕ) → 1 ≤ d → d ∣ c → 1 ≤ c divN d
  1≤c/d d 1≤d d∣c = prod-pos d (c divN d) c (·-comm d _ ∙ divN-exact d c 1≤d d∣c) 1≤c

  least-m/d : (d : ℕ) → 1 ≤ d → d ∣ c → (k : ℕ) → 2 ≤ k → k ∣ (p · (c divN d)) → p ≤ k
  least-m/d d 1≤d d∣c k 2≤k k∣ =
    spf-least m 2≤m k 2≤k (∣-trans (subst (k ∣_) (sym (quot-split d 1≤d d∣c)) k∣) m/d∣m)
    where
    m/d∣m : (m divN d) ∣ m
    m/d∣m = subst ((m divN d) ∣_) (divN-exact d m 1≤d (d∣c→d∣m d d∣c)) (∣-left d)

  mu-m/d : (d : ℕ) → 1 ≤ d → d ∣ c
         → mu (m divN d) ≡ (if dividesb p (c divN d) then pos 0 else negZ (mu (c divN d)))
  mu-m/d d 1≤d d∣c =
    cong mu (quot-split d 1≤d d∣c)
    ∙ mu-mult p (c divN d) 2≤p (1≤c/d d 1≤d d∣c) (least-m/d d 1≤d d∣c)

  -- the p-free half, cut down to divisors of c
  A-above : (d : ℕ) → c < d → d ≤ m → A d ≡ pos 0
  A-above d c<d _ with dividesb-dec p d 0<p
  ... | inl (_ , e) = cong (λ b → if b then pos 0 else T d) e
  ... | inr (¬p∣d , e) = cong (λ b → if b then pos 0 else T d) e ∙ T≡0
    where
    0<d : 0 < d
    0<d = ≤-trans (suc-≤-suc zero-≤) c<d
    T≡0 : T d ≡ pos 0
    T≡0 with dividesb-dec d m 0<d
    ... | inl (d∣m , _) = ⊥rec (<-asym c<d (m∣n→m≤n c≢0 (d∣m→d∣c d ¬p∣d d∣m)))
    ... | inr (_ , e') = cong (λ b → if b then x d else pos 0) e'

  A-below : (d : ℕ) → 1 ≤ d → d ≤ c → A d ≡ A' d
  A-below d 1≤d _ = A-eq (dividesb p d) (dividesb d m) (dividesb d c) (x d) same
    where
    same : dividesb p d ≡ false → dividesb d m ≡ dividesb d c
    same e with dividesb-dec d m 1≤d
    ... | inl (d∣m , e₁) =
      e₁ ∙ sym (∣-dividesb d c 1≤d (d∣m→d∣c d (dividesb-false→¬∣ p d 0<p e) d∣m))
    ... | inr (¬d∣m , e₁) =
      e₁ ∙ sym (¬∣-dividesb d c 1≤d (λ d∣c → ¬d∣m (d∣c→d∣m d d∣c)))

  stepA : Σ≤ A m ≡ Σ≤ A' c
  stepA = Σ≤-above A c m c≤m A-above ∙ Σ≤-ext A A' c A-below

  -- the p-free half evaluated: 0 if p ∣ c, −Φ_c if p ∤ c
  stepA' : Σ≤ A' c ≡ (if dividesb p c then pos 0 else - Φ c r)
  stepA' with dividesb-dec p c 0<p
  ... | inl (p∣c , e) =
    Σ≤-zero A' c vanish ∙ sym (cong (λ b → if b then pos 0 else - Φ c r) e)
    where
    vanish : (d : ℕ) → 1 ≤ d → d ≤ c → A' d ≡ pos 0
    vanish d 1≤d _ with dividesb-dec d c 1≤d
    ... | inr (_ , e₁) = cong (λ b → if b then (if dividesb p d then pos 0 else x d) else pos 0) e₁
    ... | inl (d∣c , e₁) =
      cong (λ b → if b then (if dividesb p d then pos 0 else x d) else pos 0) e₁ ∙ inner
      where
      inner : (if dividesb p d then pos 0 else x d) ≡ pos 0
      inner with dividesb-dec p d 0<p
      ... | inl (_ , e₂) = cong (λ b → if b then pos 0 else x d) e₂
      ... | inr (¬p∣d , e₂) =
        cong (λ b → if b then pos 0 else x d) e₂ ∙ cong (_·ℤ X^ (Ω d) r) mu≡0
        where
        p∣c/d : p ∣ (c divN d)
        p∣c/d with युक्लिड-वाक्यम् p (c divN d) d (2≤p , prime)
                              (subst (p ∣_) (sym (divN-exact d c 1≤d d∣c)) p∣c)
        ... | inl h = h
        ... | inr h = ⊥rec (¬p∣d h)
        mu≡0 : mu (m divN d) ≡ pos 0
        mu≡0 = mu-m/d d 1≤d d∣c
             ∙ cong (λ b → if b then pos 0 else negZ (mu (c divN d)))
                    (∣-dividesb p (c divN d) 0<p p∣c/d)
  ... | inr (¬p∣c , e) =
    Σ≤-ext A' (λ d → - term c d r) c A'≡-T
    ∙ Σ≤-neg (λ d → term c d r) c
    ∙ sym (cong (λ b → if b then pos 0 else - Φ c r) e)
    where
    A'≡-T : (d : ℕ) → 1 ≤ d → d ≤ c → A' d ≡ - term c d r
    A'≡-T d 1≤d _ with dividesb-dec d c 1≤d
    ... | inr (_ , e₁) =
      cong (λ b → if b then (if dividesb p d then pos 0 else x d) else pos 0) e₁
      ∙ sym (cong (λ b → - (if b then y d else pos 0)) e₁)
    ... | inl (d∣c , e₁) =
      cong (λ b → if b then (if dividesb p d then pos 0 else x d) else pos 0) e₁
      ∙ cong (λ b → if b then pos 0 else x d) (¬∣-dividesb p d 0<p ¬p∣d)
      ∙ cong (_·ℤ X^ (Ω d) r) mu≡neg
      ∙ sym (-DistL· (mu (c divN d)) (X^ (Ω d) r))
      ∙ sym (cong (λ b → - (if b then y d else pos 0)) e₁)
      where
      ¬p∣d : ¬ p ∣ d
      ¬p∣d p∣d = ¬p∣c (∣-trans p∣d d∣c)
      ¬p∣c/d : ¬ p ∣ (c divN d)
      ¬p∣c/d h = ¬p∣c (subst (p ∣_) (divN-exact d c 1≤d d∣c) (∣-trans h (∣-left d)))
      mu≡neg : mu (m divN d) ≡ - mu (c divN d)
      mu≡neg = mu-m/d d 1≤d d∣c
             ∙ cong (λ b → if b then pos 0 else negZ (mu (c divN d)))
                    (¬∣-dividesb p (c divN d) 0<p ¬p∣c/d)
             ∙ sym (pos0+ (- mu (c divN d)))

  -- the multiples of p: t · Φ_c
  stepB : Σ≤ B m ≡ tP (Φ c) r
  stepB =
    cong (Σ≤ B) (sym m≡pc)
    ∙ Σ≤-multiples p 0<p T c
    ∙ Σ≤-ext (λ e → T (p · e))
             (λ e → if dividesb e c then mu (c divN e) ·ℤ X^ (suc (Ω e)) r else pos 0) c Tpe
    ∙ shift-sum c (λ e → mu (c divN e)) Ω (λ e → dividesb e c) r
    where
    Tpe : (e : ℕ) → 1 ≤ e → e ≤ c
        → T (p · e) ≡ (if dividesb e c then mu (c divN e) ·ℤ X^ (suc (Ω e)) r else pos 0)
    Tpe e 1≤e _ with dividesb-dec e c 1≤e
    ... | inl (e∣c , e₁) =
      cong (λ b → if b then x (p · e) else pos 0) (∣-dividesb (p · e) m 0<pe pe∣m)
      ∙ cong₂ (λ z k → mu z ·ℤ X^ k r) q≡ (Ω-mult p e 2≤p 1≤e least)
      ∙ sym (cong (λ b → if b then mu (c divN e) ·ℤ X^ (suc (Ω e)) r else pos 0) e₁)
      where
      0<pe : 0 < p · e
      0<pe = 0<· p e 0<p 1≤e
      pe∣m : (p · e) ∣ m
      pe∣m = subst2 _∣_ (·-comm e p) m≡pc (subst ((e · p) ∣_) (·-comm c p) (∣-multʳ p e∣c))
      prodEq : (c divN e) · (p · e) ≡ m
      prodEq = ·-assoc (c divN e) p e
         ∙ cong (_· e) (·-comm (c divN e) p)
         ∙ sym (·-assoc p (c divN e) e)
         ∙ cong (p ·_) (divN-exact e c 1≤e e∣c)
         ∙ m≡pc
      q≡ : m divN (p · e) ≡ c divN e
      q≡ = fst (modN-unique m (p · e) (c divN e) 0 0<pe 0<pe (+-zero _ ∙ prodEq))
      least : (k : ℕ) → 2 ≤ k → k ∣ (p · e) → p ≤ k
      least k 2≤k k∣pe = spf-least m 2≤m k 2≤k (∣-trans k∣pe pe∣m)
    ... | inr (¬e∣c , e₁) =
      cong (λ b → if b then x (p · e) else pos 0)
           (¬∣-dividesb (p · e) m (0<· p e 0<p 1≤e)
                        (λ pe∣m → ¬e∣c (cancel-∣ p e c 0<p (subst ((p · e) ∣_) (sym m≡pc) pe∣m))))
      ∙ sym (cong (λ b → if b then mu (c divN e) ·ℤ X^ (suc (Ω e)) r else pos 0) e₁)

-- the two faces of the peeling identity, as polynomial equations
Φ-peel-repeat : (m : ℕ) → 2 ≤ m → dividesb (spf m) (m divN spf m) ≡ true
              → Φ m ≡ tP (Φ (m divN spf m))
Φ-peel-repeat m 2≤m e = funExt λ r →
  Φ-peel m 2≤m r
  ∙ cong (_+ℤ tP (Φ (m divN spf m)) r) (cong (λ b → if b then pos 0 else - Φ (m divN spf m) r) e)
  ∙ sym (pos0+ _)

Φ-peel-new : (m : ℕ) → 2 ≤ m → dividesb (spf m) (m divN spf m) ≡ false
           → Φ m ≡ tm1P (Φ (m divN spf m))
Φ-peel-new m 2≤m e = funExt λ r →
  Φ-peel m 2≤m r
  ∙ cong (_+ℤ tP (Φ (m divN spf m)) r) (cong (λ b → if b then pos 0 else - Φ (m divN spf m) r) e)
  ∙ +Comm (- Φ (m divN spf m) r) (tP (Φ (m divN spf m)) r)

------------------------------------------------------------------------
-- 5.  THE THEOREM:  Φ_n(t) = t^{Ω(n) − ω(n)} (t − 1)^{ω(n)}  for n ≥ 1.
------------------------------------------------------------------------

-- t and (t − 1) commute
tP-tm1P : (P : Poly) → tP (tm1P P) ≡ tm1P (tP P)
tP-tm1P P = funExt λ { zero → refl ; (suc r) → refl }

tPow-tm1P : (a : ℕ) (Q : Poly) → tm1P (tPow a Q) ≡ tPow a (tm1P Q)
tPow-tm1P zero Q = refl
tPow-tm1P (suc a) Q = sym (tP-tm1P (tPow a Q)) ∙ cong tP (tPow-tm1P a Q)

Φ-1 : Φ 1 ≡ closedForm 0 0
Φ-1 = refl

closed-fuel : (f n : ℕ) → n ≤ f → 1 ≤ n → Φ n ≡ closedForm (Ω n ∸ ω n) (ω n)
closed-fuel zero n n≤0 1≤n = ⊥rec (¬-<-zero (≤-trans 1≤n n≤0))
closed-fuel (suc f) zero _ 1≤n = ⊥rec (¬-<-zero 1≤n)
closed-fuel (suc f) (suc zero) _ _ = refl
closed-fuel (suc f) (suc (suc n')) n≤sf _ = split (dividesb-dec p q 0<p)
  where
  n = suc (suc n')
  2≤n : 2 ≤ n
  2≤n = suc-≤-suc (suc-≤-suc zero-≤)
  p = spf n
  q = n divN p
  0<p : 0 < p
  0<p = 0<spf n 2≤n
  1≤q : 1 ≤ q
  1≤q = quot-pos n 2≤n
  ih : Φ q ≡ closedForm (Ω q ∸ ω q) (ω q)
  ih = closed-fuel f q (pred-≤-pred (≤-trans (quot-< n 2≤n) n≤sf)) 1≤q

  split : ((p ∣ q) × (dividesb p q ≡ true)) ⊎ ((¬ p ∣ q) × (dividesb p q ≡ false))
        → Φ n ≡ closedForm (Ω n ∸ ω n) (ω n)
  split (inl (_ , e)) =
    Φ-peel-repeat n 2≤n e
    ∙ cong tP ih
    ∙ cong₂ closedForm (sym exp) (sym ωeq)
    where
    ωeq : ω n ≡ ω q
    ωeq = ω-step n 2≤n ∙ cong (λ b → if b then ω q else suc (ω q)) e
    exp : Ω n ∸ ω n ≡ suc (Ω q ∸ ω q)
    exp = cong₂ _∸_ (Ω-step n 2≤n) ωeq ∙ sym (≤-∸-suc (ω≤Ω q 1≤q))
  split (inr (_ , e)) =
    Φ-peel-new n 2≤n e
    ∙ cong tm1P ih
    ∙ tPow-tm1P (Ω q ∸ ω q) (tm1Pow (ω q))
    ∙ cong₂ closedForm (sym exp) (sym ωeq)
    where
    ωeq : ω n ≡ suc (ω q)
    ωeq = ω-step n 2≤n ∙ cong (λ b → if b then ω q else suc (ω q)) e
    exp : Ω n ∸ ω n ≡ Ω q ∸ ω q
    exp = cong₂ _∸_ (Ω-step n 2≤n) ωeq

-- THE THEOREM
Φ-closed-form : (n : ℕ) → 1 ≤ n → Φ n ≡ closedForm (Ω n ∸ ω n) (ω n)
Φ-closed-form n 1≤n = closed-fuel n n ≤-refl 1≤n

-- coefficient by coefficient: κ_r(n) is the r-th coefficient of t^{Ω−ω}(t−1)^{ω}
κ-closed-form : (r n : ℕ) → 1 ≤ n → κ r n ≡ closedForm (Ω n ∸ ω n) (ω n) r
κ-closed-form r n 1≤n = cong (λ P → P r) (Φ-closed-form n 1≤n)

------------------------------------------------------------------------
-- 6.  κ₁.  First κ₁(n) = Σ_{p ∣ n} μ(n/p) with p ranging over the
--     corpus's primes (`isPrimeb`, shown to be Drdha's firmness), then
--     the three-case formula read off the closed form at t^1.
------------------------------------------------------------------------

bool-dec : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
bool-dec true = inl refl
bool-dec false = inr refl

and-true : (a b : Bool) → (a and b) ≡ true → (a ≡ true) × (b ≡ true)
and-true true true _ = refl , refl
and-true true false e = ⊥rec (false≢true e)
and-true false b e = ⊥rec (false≢true e)

if-same : (b : Bool) → (if b then pos 0 else pos 0) ≡ pos 0
if-same true = refl
if-same false = refl

-- the Boolean primality test of TransmissionRefutations IS Drdha's
-- firmness, in both directions
isPrimeb-firm : (p : ℕ) → isPrimeb p ≡ true → दृढम् p
isPrimeb-firm p e = 2≤p , only
  where
  parts = and-true (leb 2 p) (eqb (spf p) p) e
  2≤p : 2 ≤ p
  2≤p with leb-dec 2 p
  ... | inl (h , _) = h
  ... | inr (_ , q) = ⊥rec (true≢false (sym (fst parts) ∙ q))
  spf≡p : spf p ≡ p
  spf≡p with eqb-dec (spf p) p
  ... | inl (h , _) = h
  ... | inr (_ , q) = ⊥rec (true≢false (sym (snd parts) ∙ q))
  only : (d : ℕ) → d ∣ p → (d ≡ 1) ⊎ (d ≡ p)
  only d d∣p with spf-prime p 2≤p d (subst (d ∣_) (sym spf≡p) d∣p)
  ... | inl h = inl h
  ... | inr h = inr (h ∙ spf≡p)

firm-isPrimeb : (p : ℕ) → दृढम् p → isPrimeb p ≡ true
firm-isPrimeb p (1<p , only) = cong₂ _and_ (leb-≤ 2 p 1<p) spfb
  where
  spfb : eqb (spf p) p ≡ true
  spfb with only (spf p) (spf∣ p 1<p)
  ... | inl h = ⊥rec (¬m<m (subst (2 ≤_) h (2≤spf p 1<p)))
  ... | inr h = subst (λ z → eqb z p ≡ true) (sym h) (eqb-refl p)

-- Ω(q) = 0 exactly at q = 1
eqb0-Ω : (q : ℕ) → 1 ≤ q → eqb 0 (Ω q) ≡ eqb q 1
eqb0-Ω zero h = ⊥rec (¬-<-zero h)
eqb0-Ω (suc zero) _ = refl
eqb0-Ω (suc (suc q')) _ = cong (eqb 0) (Ω-step (suc (suc q')) (suc-≤-suc (suc-≤-suc zero-≤)))

-- n / spf n = 1 exactly when spf n = n
quot-one : (n : ℕ) → 2 ≤ n → eqb (n divN spf n) 1 ≡ eqb (spf n) n
quot-one n 2≤n with eqb-dec (n divN spf n) 1
... | inl (q≡1 , e) = e ∙ sym (subst (λ z → eqb z n ≡ true) (sym p≡n) (eqb-refl n))
  where
  p≡n : spf n ≡ n
  p≡n = sym (·-identityʳ (spf n)) ∙ cong (spf n ·_) (sym q≡1) ∙ quot-eq n 2≤n
... | inr (q≢1 , e) = e ∙ sym (eqb-≢ (spf n) n (λ p≡n → q≢1 (q≡1 p≡n)))
  where
  q≡1 : spf n ≡ n → n divN spf n ≡ 1
  q≡1 p≡n = cong (n divN_) p≡n
          ∙ fst (modN-unique n n 1 0 (1≤ n 2≤n) (1≤ n 2≤n) (+-zero _ ∙ ·-identityˡ n))

-- Ω(d) = 1 exactly at the primes
Ω-one-iff-prime : (d : ℕ) → 1 ≤ d → eqb 1 (Ω d) ≡ isPrimeb d
Ω-one-iff-prime zero h = ⊥rec (¬-<-zero h)
Ω-one-iff-prime (suc zero) _ = refl
Ω-one-iff-prime (suc (suc d')) _ =
  cong (eqb 1) (Ω-step d 2≤d)
  ∙ eqb0-Ω (d divN spf d) (quot-pos d 2≤d)
  ∙ quot-one d 2≤d
  ∙ sym (cong (_and eqb (spf d) d) (leb-≤ 2 d 2≤d))
  where
  d = suc (suc d')
  2≤d : 2 ≤ d
  2≤d = suc-≤-suc (suc-≤-suc zero-≤)

-- Σ_{p ∣ n, p prime} μ(n/p), as a sum over p = 1..n
primeCofactorSum : ℕ → ℤ
primeCofactorSum n =
  Σ≤ (λ p → if isPrimeb p and dividesb p n then mu (n divN p) else pos 0) n

if-prime-fold : (b₁ b₂ : Bool) (z : ℤ)
  → (if b₁ then z ·ℤ (if b₂ then pos 1 else pos 0) else pos 0) ≡ (if b₂ and b₁ then z else pos 0)
if-prime-fold true true z = ·IdR z
if-prime-fold true false z = ·AnnihilR z
if-prime-fold false true z = refl
if-prime-fold false false z = refl

-- κ₁(n) = Σ_{p ∣ n} μ(n/p)   (D0026 §5.4), for every n
κ₁-is-prime-cofactor-sum : (n : ℕ) → κ 1 n ≡ primeCofactorSum n
κ₁-is-prime-cofactor-sum n = Σ≤-ext _ _ n per
  where
  per : (d : ℕ) → 1 ≤ d → d ≤ n
      → term n d 1 ≡ (if isPrimeb d and dividesb d n then mu (n divN d) else pos 0)
  per d 1≤d _ =
    cong (λ b → if dividesb d n then mu (n divN d) ·ℤ (if b then pos 1 else pos 0) else pos 0)
         (Ω-one-iff-prime d 1≤d)
    ∙ if-prime-fold (dividesb d n) (isPrimeb d) (mu (n divN d))

-- the coefficient of t^1 in t^a (t − 1)^b
parity-suc : (b : ℕ) → parity (suc b) ≡ - parity b
parity-suc zero = refl
parity-suc (suc zero) = refl
parity-suc (suc (suc b)) = parity-suc b

tm1Pow-at0 : (b : ℕ) → tm1Pow b 0 ≡ parity b
tm1Pow-at0 zero = refl
tm1Pow-at0 (suc b) = sym (pos0+ (- tm1Pow b 0)) ∙ cong -_ (tm1Pow-at0 b) ∙ sym (parity-suc b)

tm1Pow-at1 : (b : ℕ) → tm1Pow b 1 ≡ parity (b ∸ 1) ·ℤ pos b
tm1Pow-at1 zero = refl
tm1Pow-at1 (suc zero) = refl
tm1Pow-at1 (suc (suc b)) =
  cong₂ _+ℤ_ (tm1Pow-at0 (suc b) ∙ sym (·IdR (parity (suc b))))
             (cong -_ (tm1Pow-at1 (suc b))
              ∙ -DistL· (parity b) (pos (suc b))
              ∙ cong (_·ℤ pos (suc b)) (sym (parity-suc b)))
  ∙ sym (·DistR+ (parity (suc b)) (pos 1) (pos (suc b)))
  ∙ cong (parity (suc b) ·ℤ_) (sym (pos+ 1 (suc b)))

-- the package's three cases, with ρ = Ω − ω and j = ω:
--   ρ = 0 : (−1)^{j−1} j,   ρ = 1 : (−1)^j,   ρ ≥ 2 : 0
threeCase : ℕ → ℕ → ℤ
threeCase zero j = parity (j ∸ 1) ·ℤ pos j
threeCase (suc zero) j = parity j
threeCase (suc (suc _)) j = pos 0

coef1-closedForm : (a b : ℕ) → closedForm a b 1 ≡ threeCase a b
coef1-closedForm zero b = tm1Pow-at1 b
coef1-closedForm (suc zero) b = tm1Pow-at0 b
coef1-closedForm (suc (suc a)) b = refl

κ₁-three-cases : (n : ℕ) → 1 ≤ n → κ 1 n ≡ threeCase (Ω n ∸ ω n) (ω n)
κ₁-three-cases n 1≤n = κ-closed-form 1 n 1≤n ∙ coef1-closedForm (Ω n ∸ ω n) (ω n)

κ₁-ρ0 : (n : ℕ) → 1 ≤ n → Ω n ∸ ω n ≡ 0 → κ 1 n ≡ parity (ω n ∸ 1) ·ℤ pos (ω n)
κ₁-ρ0 n 1≤n ρ = κ₁-three-cases n 1≤n ∙ cong (λ a → threeCase a (ω n)) ρ

κ₁-ρ1 : (n : ℕ) → 1 ≤ n → Ω n ∸ ω n ≡ 1 → κ 1 n ≡ parity (ω n)
κ₁-ρ1 n 1≤n ρ = κ₁-three-cases n 1≤n ∙ cong (λ a → threeCase a (ω n)) ρ

κ₁-ρ≥2 : (n k : ℕ) → 1 ≤ n → Ω n ∸ ω n ≡ suc (suc k) → κ 1 n ≡ pos 0
κ₁-ρ≥2 n k 1≤n ρ = κ₁-three-cases n 1≤n ∙ cong (λ a → threeCase a (ω n)) ρ

-- "not multiplicative": κ₁(6) = μ(3) + μ(2) = −2, but κ₁(2)·κ₁(3) = 1
κ₁-at-6 : κ 1 6 ≡ negsuc 1
κ₁-at-6 = refl

κ₁-at-2·3 : κ 1 2 ·ℤ κ 1 3 ≡ pos 1
κ₁-at-2·3 = refl

κ₁-not-multiplicative : ¬ (κ 1 6 ≡ κ 1 2 ·ℤ κ 1 3)
κ₁-not-multiplicative e = negsucNotpos 1 1 (sym κ₁-at-6 ∙ e ∙ κ₁-at-2·3)

------------------------------------------------------------------------
-- 7.  The values at 12 = 2²·3, 30 = 2·3·5, 360 = 2³·3²·5, by refl,
--     from the raw divisor sum (no closed form is used here).
------------------------------------------------------------------------

Ω-12 : Ω 12 ≡ 3
Ω-12 = refl
ω-12 : ω 12 ≡ 2
ω-12 = refl
Ω-30 : Ω 30 ≡ 3
Ω-30 = refl
ω-30 : ω 30 ≡ 3
ω-30 = refl
Ω-360 : Ω 360 ≡ 6
Ω-360 = refl
ω-360 : ω 360 ≡ 3
ω-360 = refl

-- Φ₁₂(t) = t (t−1)² = t³ − 2t² + t
Φ-12 : coeffs (Φ 12) 5 ≡ pos 0 ∷ pos 1 ∷ negsuc 1 ∷ pos 1 ∷ pos 0 ∷ []
Φ-12 = refl

-- Φ₃₀(t) = (t−1)³ = t³ − 3t² + 3t − 1
Φ-30 : coeffs (Φ 30) 5 ≡ negsuc 0 ∷ pos 3 ∷ negsuc 2 ∷ pos 1 ∷ pos 0 ∷ []
Φ-30 = refl

-- Φ₃₆₀(t) = t³ (t−1)³ = t⁶ − 3t⁵ + 3t⁴ − t³
Φ-360 : coeffs (Φ 360) 8 ≡ pos 0 ∷ pos 0 ∷ pos 0 ∷ negsuc 0 ∷ pos 3 ∷ negsuc 2 ∷ pos 1 ∷ pos 0 ∷ []
Φ-360 = refl

-- and the closed forms print the same lists
closed-12 : coeffs (closedForm 1 2) 5 ≡ pos 0 ∷ pos 1 ∷ negsuc 1 ∷ pos 1 ∷ pos 0 ∷ []
closed-12 = refl
closed-30 : coeffs (closedForm 0 3) 5 ≡ negsuc 0 ∷ pos 3 ∷ negsuc 2 ∷ pos 1 ∷ pos 0 ∷ []
closed-30 = refl
closed-360 : coeffs (closedForm 3 3) 8 ≡ pos 0 ∷ pos 0 ∷ pos 0 ∷ negsuc 0 ∷ pos 3 ∷ negsuc 2 ∷ pos 1 ∷ pos 0 ∷ []
closed-360 = refl

------------------------------------------------------------------------
-- 8.  Ω IS THE LENGTH OF EVERY FIRM FACTORISATION.  The spf-recursion
--     produces a list of firm numbers with product n whose length is
--     Ω(n) by construction; Uniqueness's uniqueness makes it a permutation
--     of any other firm factorisation, and permutations preserve length.
------------------------------------------------------------------------

spfListF : ℕ → ℕ → List ℕ
spfListF zero _ = []
spfListF (suc f) n = if eqb n 1 then [] else spf n ∷ spfListF f (n divN spf n)

spfList : ℕ → List ℕ
spfList n = spfListF n n

length-if : (b : Bool) (x : ℕ) (xs : List ℕ)
          → length (if b then [] else x ∷ xs) ≡ (if b then 0 else suc (length xs))
length-if true _ _ = refl
length-if false _ _ = refl

spfListF-length : (f n : ℕ) → length (spfListF f n) ≡ bigOmegaF f n
spfListF-length zero n = refl
spfListF-length (suc f) n =
  length-if (eqb n 1) (spf n) (spfListF f (n divN spf n))
  ∙ cong (λ k → if eqb n 1 then 0 else suc k) (spfListF-length f (n divN spf n))

Ω-is-length-spfList : (n : ℕ) → Ω n ≡ length (spfList n)
Ω-is-length-spfList n = sym (spfListF-length n n)

spfListF-firm : (f n : ℕ) → 1 ≤ n → n ≤ f → सर्वे दृढम् (spfListF f n)
spfListF-firm zero n 1≤n n≤0 = ⊥rec (¬-<-zero (≤-trans 1≤n n≤0))
spfListF-firm (suc f) zero 1≤n _ = ⊥rec (¬-<-zero 1≤n)
spfListF-firm (suc f) (suc zero) _ _ = tt
spfListF-firm (suc f) (suc (suc n')) _ n≤sf =
  (2≤spf n 2≤n , spf-prime n 2≤n)
  , spfListF-firm f (n divN spf n) (quot-pos n 2≤n) (pred-≤-pred (≤-trans (quot-< n 2≤n) n≤sf))
  where
  n = suc (suc n')
  2≤n : 2 ≤ n
  2≤n = suc-≤-suc (suc-≤-suc zero-≤)

spfListF-prod : (f n : ℕ) → 1 ≤ n → n ≤ f → वधः (spfListF f n) ≡ n
spfListF-prod zero n 1≤n n≤0 = ⊥rec (¬-<-zero (≤-trans 1≤n n≤0))
spfListF-prod (suc f) zero 1≤n _ = ⊥rec (¬-<-zero 1≤n)
spfListF-prod (suc f) (suc zero) _ _ = refl
spfListF-prod (suc f) (suc (suc n')) _ n≤sf =
  cong (spf n ·_) (spfListF-prod f (n divN spf n) (quot-pos n 2≤n) (pred-≤-pred (≤-trans (quot-< n 2≤n) n≤sf)))
  ∙ quot-eq n 2≤n
  where
  n = suc (suc n')
  2≤n : 2 ≤ n
  2≤n = suc-≤-suc (suc-≤-suc zero-≤)

Insert-length : {x : ℕ} {xs ys : List ℕ} → Insert x xs ys → length ys ≡ suc (length xs)
Insert-length here = refl
Insert-length (there ins) = cong suc (Insert-length ins)

Perm-length : {xs ys : List ℕ} → Perm xs ys → length xs ≡ length ys
Perm-length pnil = refl
Perm-length (pcons p ins) = cong suc (Perm-length p) ∙ sym (Insert-length ins)

-- Ω(n) is the number of prime factors of n counted with multiplicity:
-- the length of ANY list of firm numbers whose product is n
Ω-is-length-of-every-firm-factorisation :
  (n : ℕ) (L : List ℕ) → सर्वे दृढम् L → वधः L ≡ n → Ω n ≡ length L
Ω-is-length-of-every-firm-factorisation n L firmL prodL =
  Ω-is-length-spfList n
  ∙ Perm-length (एकत्वम् (spfList n) L (spfListF-firm n n 1≤n ≤-refl) firmL
                         (spfListF-prod n n 1≤n ≤-refl ∙ sym prodL))
  where
  1≤n : 1 ≤ n
  1≤n = subst (1 ≤_) prodL (वध-धनः L firmL)

-- in particular of Drdha's own factorisation
Ω-is-length-of-Drdha-factorisation : (n : ℕ) (0<n : 0 < n) → Ω n ≡ length (fst (विभाजनम् n 0<n))
Ω-is-length-of-Drdha-factorisation n 0<n =
  Ω-is-length-of-every-firm-factorisation n (fst (विभाजनम् n 0<n))
    (fst (snd (विभाजनम् n 0<n))) (snd (snd (विभाजनम् n 0<n)))

------------------------------------------------------------------------
-- 9.  ω IS THE NUMBER OF DISTINCT PRIMES DIVIDING n: it agrees with the
--     exhaustive scan `smallOmega` of TransmissionRefutations.  With
--     m = p·c, p = spf m, a prime divides m iff it is p or divides c
--     (Euclid); when p ∤ c the two alternatives are exclusive and the
--     count rises by one, when p ∣ c the second absorbs the first.
------------------------------------------------------------------------

primeInd : ℕ → ℕ → ℤ       -- [j ∣ n] · [j prime]
primeInd n j = if dividesb j n then (if isPrimeb j then pos 1 else pos 0) else pos 0

omegaCount-Σ : (k n : ℕ) → pos (omegaCount k n) ≡ Σ≤ (primeInd n) k
omegaCount-Σ zero n = refl
omegaCount-Σ (suc k) n =
  cong pos (addN≡+ (if isPrimeb (suc k) and dividesb (suc k) n then 1 else 0) (omegaCount k n))
  ∙ pos+ (if isPrimeb (suc k) and dividesb (suc k) n then 1 else 0) (omegaCount k n)
  ∙ cong₂ _+ℤ_ (pos-if (isPrimeb (suc k) and dividesb (suc k) n)
                ∙ if-and (isPrimeb (suc k)) (dividesb (suc k) n) (pos 1))
               (omegaCount-Σ k n)

-- Σ_{j ≤ k} [j = p] = 1 for 1 ≤ p ≤ k
Σ≤-delta : (p k : ℕ) → 1 ≤ p → p ≤ k → Σ≤ (λ j → if eqb j p then pos 1 else pos 0) k ≡ pos 1
Σ≤-delta p zero 1≤p p≤0 = ⊥rec (¬-<-zero (≤-trans 1≤p p≤0))
Σ≤-delta p (suc k) 1≤p p≤sk with ≤-split p≤sk
... | inr p≡sk =
  cong₂ _+ℤ_ (cong (λ b → if b then pos 1 else pos 0)
                   (subst (λ z → eqb (suc k) z ≡ true) (sym p≡sk) (eqb-refl (suc k))))
             (Σ≤-zero _ k (λ j _ j≤k → cong (λ b → if b then pos 1 else pos 0)
                                             (eqb-≢ j p (λ j≡p → ¬m<m (subst (_≤ k) (j≡p ∙ p≡sk) j≤k)))))
... | inl p<sk =
  cong₂ _+ℤ_ (cong (λ b → if b then pos 1 else pos 0)
                   (eqb-≢ (suc k) p (λ e → ¬m<m (subst (p <_) e p<sk))))
             (Σ≤-delta p k 1≤p (pred-≤-pred p<sk))

-- the recursion of the scan count along the least prime factor
S-step : (m : ℕ) → 2 ≤ m
       → Σ≤ (primeInd m) m
       ≡ (if dividesb (spf m) (m divN spf m) then pos 0 else pos 1)
         +ℤ Σ≤ (primeInd (m divN spf m)) (m divN spf m)
S-step m 2≤m = go (dividesb-dec p c 0<p)
  where
  p = spf m
  c = m divN p
  1≤m : 1 ≤ m
  1≤m = 1≤ m 2≤m
  m≢0 : ¬ m ≡ 0
  m≢0 m≡0 = ¬-<-zero (subst (1 ≤_) m≡0 1≤m)
  2≤p : 2 ≤ p
  2≤p = 2≤spf m 2≤m
  0<p : 0 < p
  0<p = 0<spf m 2≤m
  m≡pc : p · c ≡ m
  m≡pc = quot-eq m 2≤m
  1≤c : 1 ≤ c
  1≤c = quot-pos m 2≤m
  c≢0 : ¬ c ≡ 0
  c≢0 c≡0 = ¬-<-zero (subst (1 ≤_) c≡0 1≤c)
  c∣m : c ∣ m
  c∣m = subst (c ∣_) m≡pc (∣-right p)
  c≤m : c ≤ m
  c≤m = m∣n→m≤n m≢0 c∣m
  p≤m : p ≤ m
  p≤m = m∣n→m≤n m≢0 (spf∣ m 2≤m)
  prime : (k : ℕ) → k ∣ p → (k ≡ 1) ⊎ (k ≡ p)
  prime = spf-prime m 2≤m
  isPrimeb-p : isPrimeb p ≡ true
  isPrimeb-p = firm-isPrimeb p (2≤p , prime)

  -- above c nothing divides c
  cut : Σ≤ (primeInd c) m ≡ Σ≤ (primeInd c) c
  cut = Σ≤-above (primeInd c) c m c≤m
          (λ j c<j _ → cong (λ b → if b then (if isPrimeb j then pos 1 else pos 0) else pos 0)
                            (¬∣-dividesb j c (≤-trans (suc-≤-suc zero-≤) c<j)
                                         (λ j∣c → <-asym c<j (m∣n→m≤n c≢0 j∣c))))

  -- a prime dividing m is p or divides c
  prime-div : (j : ℕ) → isPrimeb j ≡ true → j ∣ m → (j ≡ p) ⊎ (j ∣ c)
  prime-div j pj j∣m with युक्लिड-वाक्यम् j p c (isPrimeb-firm j pj) (subst (j ∣_) (sym m≡pc) j∣m)
  ... | inr h = inr h
  ... | inl j∣p with prime j j∣p
  ...   | inl j≡1 = ⊥rec (¬m<m (subst (2 ≤_) j≡1 (fst (isPrimeb-firm j pj))))
  ...   | inr j≡p = inl j≡p

  -- per j, when p ∣ c
  same : p ∣ c → (j : ℕ) → 1 ≤ j → j ≤ m → primeInd m j ≡ primeInd c j
  same p∣c j 1≤j _ with bool-dec (isPrimeb j)
  ... | inr e =
    cong (λ b → if dividesb j m then (if b then pos 1 else pos 0) else pos 0) e
    ∙ if-same (dividesb j m)
    ∙ sym (if-same (dividesb j c))
    ∙ sym (cong (λ b → if dividesb j c then (if b then pos 1 else pos 0) else pos 0) e)
  ... | inl e =
    cong (λ b → if dividesb j m then (if b then pos 1 else pos 0) else pos 0) e
    ∙ cong (λ b → if b then pos 1 else pos 0) divEq
    ∙ sym (cong (λ b → if dividesb j c then (if b then pos 1 else pos 0) else pos 0) e)
    where
    divEq : dividesb j m ≡ dividesb j c
    divEq with dividesb-dec j m 1≤j
    ... | inl (j∣m , e₁) = e₁ ∙ sym (∣-dividesb j c 1≤j j∣c)
      where
      j∣c : j ∣ c
      j∣c with prime-div j e j∣m
      ... | inl j≡p = subst (_∣ c) (sym j≡p) p∣c
      ... | inr h = h
    ... | inr (¬j∣m , e₁) = e₁ ∙ sym (¬∣-dividesb j c 1≤j (λ j∣c → ¬j∣m (∣-trans j∣c c∣m)))

  -- per j, when p ∤ c
  δ : ℕ → ℤ
  δ j = if eqb j p then pos 1 else pos 0

  split : ¬ p ∣ c → (j : ℕ) → 1 ≤ j → j ≤ m → primeInd m j ≡ δ j +ℤ primeInd c j
  split ¬p∣c j 1≤j _ with bool-dec (isPrimeb j)
  ... | inr e =
    cong (λ b → if dividesb j m then (if b then pos 1 else pos 0) else pos 0) e
    ∙ if-same (dividesb j m)
    ∙ sym (cong₂ _+ℤ_ (cong (λ b → if b then pos 1 else pos 0) (eqb-≢ j p j≢p))
                      (cong (λ b → if dividesb j c then (if b then pos 1 else pos 0) else pos 0) e
                       ∙ if-same (dividesb j c)))
    where
    j≢p : ¬ j ≡ p
    j≢p j≡p = true≢false (sym isPrimeb-p ∙ cong isPrimeb (sym j≡p) ∙ e)
  ... | inl e with eqb-dec j p
  ...   | inl (j≡p , e₁) =
    cong (λ b → if dividesb j m then (if b then pos 1 else pos 0) else pos 0) e
    ∙ cong (λ b → if b then pos 1 else pos 0)
           (∣-dividesb j m 1≤j (subst (_∣ m) (sym j≡p) (spf∣ m 2≤m)))
    ∙ sym (cong₂ _+ℤ_ (cong (λ b → if b then pos 1 else pos 0) e₁)
                      (cong (λ b → if dividesb j c then (if b then pos 1 else pos 0) else pos 0) e
                       ∙ cong (λ b → if b then pos 1 else pos 0)
                              (¬∣-dividesb j c 1≤j (λ j∣c → ¬p∣c (subst (_∣ c) j≡p j∣c)))))
  ...   | inr (j≢p , e₁) =
    cong (λ b → if dividesb j m then (if b then pos 1 else pos 0) else pos 0) e
    ∙ cong (λ b → if b then pos 1 else pos 0) divEq
    ∙ pos0+ _
    ∙ sym (cong₂ _+ℤ_ (cong (λ b → if b then pos 1 else pos 0) e₁)
                      (cong (λ b → if dividesb j c then (if b then pos 1 else pos 0) else pos 0) e))
    where
    divEq : dividesb j m ≡ dividesb j c
    divEq with dividesb-dec j m 1≤j
    ... | inl (j∣m , e₂) = e₂ ∙ sym (∣-dividesb j c 1≤j j∣c)
      where
      j∣c : j ∣ c
      j∣c with prime-div j e j∣m
      ... | inl j≡p = ⊥rec (j≢p j≡p)
      ... | inr h = h
    ... | inr (¬j∣m , e₂) = e₂ ∙ sym (¬∣-dividesb j c 1≤j (λ j∣c → ¬j∣m (∣-trans j∣c c∣m)))

  go : ((p ∣ c) × (dividesb p c ≡ true)) ⊎ ((¬ p ∣ c) × (dividesb p c ≡ false))
     → Σ≤ (primeInd m) m ≡ (if dividesb p c then pos 0 else pos 1) +ℤ Σ≤ (primeInd c) c
  go (inl (p∣c , e)) =
    Σ≤-ext (primeInd m) (primeInd c) m (same p∣c)
    ∙ cut
    ∙ pos0+ _
    ∙ cong (_+ℤ Σ≤ (primeInd c) c) (sym (cong (λ b → if b then pos 0 else pos 1) e))
  go (inr (¬p∣c , e)) =
    Σ≤-ext (primeInd m) (λ j → δ j +ℤ primeInd c j) m (split ¬p∣c)
    ∙ Σ≤-add δ (primeInd c) m
    ∙ cong₂ _+ℤ_ (Σ≤-delta p m (1≤ p 2≤p) p≤m ∙ sym (cong (λ b → if b then pos 0 else pos 1) e)) cut

pos-if-count : (b : Bool) (k : ℕ) → pos (if b then k else suc k) ≡ (if b then pos 0 else pos 1) +ℤ pos k
pos-if-count true k = pos0+ (pos k)
pos-if-count false k = pos+ 1 k

ω-Σ-fuel : (f n : ℕ) → n ≤ f → 1 ≤ n → pos (ω n) ≡ Σ≤ (primeInd n) n
ω-Σ-fuel zero n n≤0 1≤n = ⊥rec (¬-<-zero (≤-trans 1≤n n≤0))
ω-Σ-fuel (suc f) zero _ 1≤n = ⊥rec (¬-<-zero 1≤n)
ω-Σ-fuel (suc f) (suc zero) _ _ = refl
ω-Σ-fuel (suc f) (suc (suc n')) n≤sf _ =
  cong pos (ω-step n 2≤n)
  ∙ pos-if-count (dividesb (spf n) q) (ω q)
  ∙ cong ((if dividesb (spf n) q then pos 0 else pos 1) +ℤ_) ih
  ∙ sym (S-step n 2≤n)
  where
  n = suc (suc n')
  2≤n : 2 ≤ n
  2≤n = suc-≤-suc (suc-≤-suc zero-≤)
  q = n divN spf n
  ih : pos (ω q) ≡ Σ≤ (primeInd q) q
  ih = ω-Σ-fuel f q (pred-≤-pred (≤-trans (quot-< n 2≤n) n≤sf)) (quot-pos n 2≤n)

-- ω(n) is the number of distinct primes dividing n: the recursion
-- agrees with the exhaustive scan of TransmissionRefutations
ω-is-smallOmega : (n : ℕ) → 1 ≤ n → ω n ≡ smallOmega n
ω-is-smallOmega n 1≤n = injPos (ω-Σ-fuel n n ≤-refl 1≤n ∙ sym (omegaCount-Σ n n))

------------------------------------------------------------------------
-- 10.  THE GENERAL KERNEL, (1.1)–(1.3):  with ρ = Ω(n) − ω(n) and
--      j = ω(n),  κ_r(n) = (−1)^{j−k} C(j,k) for k = r − ρ ≥ 0, and
--      κ_r(n) = 0 for r < ρ.  The three cases of §6 are r = 1.
------------------------------------------------------------------------

binom : ℕ → ℕ → ℕ
binom n zero = 1
binom zero (suc k) = 0
binom (suc n) (suc k) = binom n k + binom n (suc k)

binom-above : (n k : ℕ) → n < k → binom n k ≡ 0
binom-above zero zero h = ⊥rec (¬-<-zero h)
binom-above (suc n) zero h = ⊥rec (¬-<-zero h)
binom-above zero (suc k) _ = refl
binom-above (suc n) (suc k) h =
  cong₂ _+_ (binom-above n k (pred-≤-pred h)) (binom-above n (suc k) (≤-suc (pred-≤-pred h)))

∸-suc-lt : (j k : ℕ) → k < j → j ∸ k ≡ suc (j ∸ suc k)
∸-suc-lt zero k h = ⊥rec (¬-<-zero h)
∸-suc-lt (suc j) zero _ = refl
∸-suc-lt (suc j) (suc k) h = ∸-suc-lt j k (pred-≤-pred h)

-- the coefficients of (t − 1)^j are the signed binomials
tm1Pow-coef : (j k : ℕ) → tm1Pow j k ≡ parity (j ∸ k) ·ℤ pos (binom j k)
tm1Pow-coef zero zero = refl
tm1Pow-coef zero (suc k) = refl
tm1Pow-coef (suc j) zero =
  sym (pos0+ _)
  ∙ cong -_ (tm1Pow-coef j 0 ∙ ·IdR (parity j))
  ∙ sym (parity-suc j)
  ∙ sym (·IdR (parity (suc j)))
tm1Pow-coef (suc j) (suc k) =
  cong₂ _+ℤ_ (tm1Pow-coef j k) (cong -_ (tm1Pow-coef j (suc k)) ∙ second)
  ∙ sym (·DistR+ (parity (j ∸ k)) (pos (binom j k)) (pos (binom j (suc k))))
  ∙ cong (parity (j ∸ k) ·ℤ_) (sym (pos+ (binom j k) (binom j (suc k))))
  where
  second : - (parity (j ∸ suc k) ·ℤ pos (binom j (suc k))) ≡ parity (j ∸ k) ·ℤ pos (binom j (suc k))
  second with splitℕ-< k j
  ... | inl k<j =
    -DistL· (parity (j ∸ suc k)) (pos (binom j (suc k)))
    ∙ cong (_·ℤ pos (binom j (suc k))) (sym (parity-suc (j ∸ suc k)) ∙ cong parity (sym (∸-suc-lt j k k<j)))
  ... | inr j≤k =
    cong (λ z → - (parity (j ∸ suc k) ·ℤ pos z)) (binom-above j (suc k) (suc-≤-suc j≤k))
    ∙ cong -_ (·AnnihilR (parity (j ∸ suc k)))
    ∙ sym (·AnnihilR (parity (j ∸ k)))
    ∙ cong (λ z → parity (j ∸ k) ·ℤ pos z) (sym (binom-above j (suc k) (suc-≤-suc j≤k)))

-- the coefficients of t^a Q: those of Q shifted up by a
tPow-coef-below : (a : ℕ) (Q : Poly) (r : ℕ) → r < a → tPow a Q r ≡ pos 0
tPow-coef-below zero Q r h = ⊥rec (¬-<-zero h)
tPow-coef-below (suc a) Q zero _ = refl
tPow-coef-below (suc a) Q (suc r) h = tPow-coef-below a Q r (pred-≤-pred h)

tPow-coef-above : (a : ℕ) (Q : Poly) (r : ℕ) → a ≤ r → tPow a Q r ≡ Q (r ∸ a)
tPow-coef-above zero Q r _ = refl
tPow-coef-above (suc a) Q zero h = ⊥rec (¬-<-zero h)
tPow-coef-above (suc a) Q (suc r) h = tPow-coef-above a Q r (pred-≤-pred h)

-- (1.1)–(1.3): κ_r(n) = (−1)^{j−k} C(j,k),  k = r − ρ,  when r ≥ ρ
κ-general : (r n : ℕ) → 1 ≤ n → Ω n ∸ ω n ≤ r
          → κ r n ≡ parity (ω n ∸ (r ∸ (Ω n ∸ ω n))) ·ℤ pos (binom (ω n) (r ∸ (Ω n ∸ ω n)))
κ-general r n 1≤n ρ≤r =
  κ-closed-form r n 1≤n
  ∙ tPow-coef-above (Ω n ∸ ω n) (tm1Pow (ω n)) r ρ≤r
  ∙ tm1Pow-coef (ω n) (r ∸ (Ω n ∸ ω n))

-- and κ_r(n) = 0 below the fixed charge ρ
κ-below-ρ : (r n : ℕ) → 1 ≤ n → r < Ω n ∸ ω n → κ r n ≡ pos 0
κ-below-ρ r n 1≤n r<ρ = κ-closed-form r n 1≤n ∙ tPow-coef-below (Ω n ∸ ω n) (tm1Pow (ω n)) r r<ρ

------------------------------------------------------------------------
-- 11.  Ω is additive over ALL products (the concatenation of two firm
--      factorisations is a firm factorisation of the product).
------------------------------------------------------------------------

Ω-additive : (m n : ℕ) → 1 ≤ m → 1 ≤ n → Ω (m · n) ≡ Ω m + Ω n
Ω-additive m n 1≤m 1≤n =
  Ω-is-length-of-every-firm-factorisation (m · n) (spfList m ++ spfList n)
    (सर्वे-++ (spfList m) (spfList n) (spfListF-firm m m 1≤m ≤-refl) (spfListF-firm n n 1≤n ≤-refl))
    (वध-++ (spfList m) (spfList n)
     ∙ cong₂ _·_ (spfListF-prod m m 1≤m ≤-refl) (spfListF-prod n n 1≤n ≤-refl))
  ∙ length++ (spfList m) (spfList n)
  ∙ cong₂ _+_ (sym (Ω-is-length-spfList m)) (sym (Ω-is-length-spfList n))
