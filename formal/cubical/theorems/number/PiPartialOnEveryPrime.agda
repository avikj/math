{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- PiPartialOnEveryPrime
--
-- ONE theorem, and it is the one `TransmissionRefutations`
-- declines to claim: D0020 §8's Π_∂ identity fails on EVERY prime, by
-- exactly 1, as a closed universally quantified Agda theorem.
--
-- WHY THIS MODULE EXISTS.  `TransmissionRefutations.agda` is the second
-- reader on ledger rows 8.5, 1.5 and 0.3; it establishes ledger row 8.5
-- at ν = 2, 3, 5, 7, 11, 13, 17, 19, 23 (A.5), by computation.  Here the
-- universal claim is proved by changing the representation rather than
-- the argument.  Instead
-- of computing μ, ω, Ω, λ, 𝟙_℘ from a numeral by trial division (where
-- the passage from "ν is prime" to their values is a theorem about the
-- algorithms), each ν is represented by its multiset of prime exponents,
-- on which all five functions are *defined* — and then "ν is prime"
-- becomes Ω(ν) = 1, and the shape of every such ν is DERIVED, not
-- assumed (`Ω≡1→shape`).  The result quantifies over all primes.
--
-- THE TWO MODULES ARE COMPLEMENTARY, and neither subsumes the other:
--   * `TransmissionRefutations` computes on ℕ itself, so its witnesses
--     are witnesses about actual numbers and need no model;
--   * this module proves the universal statement, at the price of the
--     model — §6 records what the
--     model assumes (unique factorisation, and nothing else).
--
-- The source displays (lines 390, 393 of
-- `collab/upstream/raw/D0020-owner-fifth-transmission-2026-08-15.md` (absent from this repository)):
--
--     Π_∂(ν) := μ(ν)² − π₁(ν),      π₁(ν) := ω(ν) − 1
--     ⎡ 1 ≤ Ω(ν) ≤ 2 ⇒ Π_∂(ν) = (1 − λ(ν))/2 − 𝟙_℘(ν) ⎤
--
-- Both displays are present verbatim; the ledger's transcription of them
-- is accurate, and ℘ is fixed as primality at archive line 81.
------------------------------------------------------------------------

module PiPartialOnEveryPrime where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz ; znots ; injSuc ; +-suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; -_)
  renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 0.  Two elementary lemmas, and disequality of integers via Bool.
------------------------------------------------------------------------

+≡0 : (m n : ℕ) → m +ℕ n ≡ 0 → (m ≡ 0) × (n ≡ 0)
+≡0 zero    n p = refl , p
+≡0 (suc m) n p = ⊥rec (snotz p)

lengthZero : (l : List ℕ) → length l ≡ 0 → l ≡ []
lengthZero []      _ = refl
lengthZero (_ ∷ _) p = ⊥rec (snotz p)

isPos0 : ℤ → Bool
isPos0 (pos zero) = true
isPos0 _          = false

1≢0 : ¬ (pos 1 ≡ pos zero)
1≢0 p = true≢false (cong (λ z → not (isPos0 z)) p)

------------------------------------------------------------------------
-- 1.  The model: a positive integer as its multiset of prime exponents.
--
-- A `Shape` is a list of naturals; an entry k stands for one distinct
-- prime carrying exponent (k + 1).  So [] is ν = 1, [0] is any prime,
-- [0,0] is any product of two distinct primes, [1] is any prime square.
-- Every function of the display depends on ν only through this datum.
------------------------------------------------------------------------

Shape : Type₀
Shape = List ℕ

sumL : List ℕ → ℕ
sumL []       = 0
sumL (x ∷ xs) = x +ℕ sumL xs

-- ω(ν): the number of distinct primes.
ωS : Shape → ℕ
ωS = length

-- Ω(ν): prime factors with multiplicity, Σ (kᵢ + 1) = length + Σ kᵢ.
ΩS : Shape → ℕ
ΩS e = length e +ℕ sumL e

-- μ(ν)²: 1 iff squarefree, i.e. iff every exponent is 1 (entry 0).
μ²S : Shape → ℤ
μ²S []          = pos 1
μ²S (zero ∷ e)  = μ²S e
μ²S (suc _ ∷ _) = pos 0

-- 𝟙_℘(ν): the indicator of the primes.  ν is prime exactly when its
-- exponent multiset is the single exponent 1, i.e. the list [ 0 ].
𝟙℘ : Shape → ℤ
𝟙℘ (zero ∷ []) = pos 1
𝟙℘ _           = pos 0

-- π₁(ν) := ω(ν) − 1  and  Π_∂(ν) := μ(ν)² − π₁(ν), exactly as displayed.
π₁S : Shape → ℤ
π₁S e = pos (ωS e) -ℤ pos 1

Π∂ : Shape → ℤ
Π∂ e = μ²S e -ℤ π₁S e

-- λ(ν) = (−1)^{Ω(ν)}, the Liouville function.
lam : ℕ → ℤ
lam zero    = pos 1
lam (suc n) = - lam n

-- (1 − λ(ν))/2, written without division: `par` alternates 0,1,0,1,…
par : ℕ → ℤ
par zero    = pos 0
par (suc n) = pos 1 -ℤ par n

-- The name is discharged, not assumed: par takes only the values 0,1,
-- and 2·par n = 1 − lam n on the nose.
parity : (n : ℕ) → ((lam n ≡ pos 1) × (par n ≡ pos 0))
                 ⊎ ((lam n ≡ negsuc 0) × (par n ≡ pos 1))
parity zero = inl (refl , refl)
parity (suc n) with parity n
... | inl (p , q) = inr (cong -_ p , cong (λ z → pos 1 -ℤ z) q)
... | inr (p , q) = inl (cong -_ p , cong (λ z → pos 1 -ℤ z) q)

halfLemma : (n : ℕ) → par n +ℤ par n ≡ pos 1 -ℤ lam n
halfLemma n with parity n
... | inl (p , q) = cong₂ _+ℤ_ q q ∙ sym (cong (λ z → pos 1 -ℤ z) p)
... | inr (p , q) = cong₂ _+ℤ_ q q ∙ sym (cong (λ z → pos 1 -ℤ z) p)

-- the transmission's right-hand side, as displayed
RHSdisplay : Shape → ℤ
RHSdisplay e = par (ΩS e) -ℤ 𝟙℘ e

-- the ledger's repair: the same display with 𝟙_℘ deleted
RHSrepair : Shape → ℤ
RHSrepair e = par (ΩS e)

------------------------------------------------------------------------
-- 2.  Classification.  The ledger's §5.3 table asserts "the three shapes
--     with 1 ≤ Ω ≤ 2".  That there are exactly three is itself a claim,
--     and it is proved here rather than read off.
------------------------------------------------------------------------

Ω≡1→shape : (e : Shape) → ΩS e ≡ 1 → e ≡ (zero ∷ [])
Ω≡1→shape []      p = ⊥rec (znots p)
Ω≡1→shape (x ∷ e) p =
  let r  = +≡0 (length e) (x +ℕ sumL e) (injSuc p)
  in cong₂ _∷_ (fst (+≡0 x (sumL e) (snd r))) (lengthZero e (fst r))

Ω≡2→shape : (e : Shape) → ΩS e ≡ 2
          → (e ≡ (zero ∷ zero ∷ [])) ⊎ (e ≡ (suc zero ∷ []))
Ω≡2→shape []             p = ⊥rec (znots p)
Ω≡2→shape (zero ∷ [])    p = ⊥rec (znots (injSuc p))
Ω≡2→shape (zero ∷ y ∷ e) p =
  let r = +≡0 (length e) (y +ℕ sumL e) (injSuc (injSuc p))
  in inl (cong₂ (λ a l → zero ∷ a ∷ l)
                (fst (+≡0 y (sumL e) (snd r)))
                (lengthZero e (fst r)))
Ω≡2→shape (suc x ∷ e)    p =
  let q' : suc (length e +ℕ (x +ℕ sumL e)) ≡ 1
      q' = sym (+-suc (length e) (x +ℕ sumL e)) ∙ injSuc p
      r  = +≡0 (length e) (x +ℕ sumL e) (injSuc q')
  in inr (cong₂ (λ a l → suc a ∷ l)
                (fst (+≡0 x (sumL e) (snd r)))
                (lengthZero e (fst r)))

------------------------------------------------------------------------
-- 3.  THE THEOREM.  On every prime the two sides of the display are 1
--     and 0: the identity is false there, by exactly 1.
------------------------------------------------------------------------

prime-values : (Π∂ (zero ∷ []) ≡ pos 1) × (RHSdisplay (zero ∷ []) ≡ pos zero)
prime-values = refl , refl

-- for EVERY ν with Ω(ν) = 1, i.e. for every prime whatsoever
values-on-every-prime : (e : Shape) → ΩS e ≡ 1
                      → (Π∂ e ≡ pos 1) × (RHSdisplay e ≡ pos zero)
values-on-every-prime e p =
  subst (λ f → (Π∂ f ≡ pos 1) × (RHSdisplay f ≡ pos zero))
        (sym (Ω≡1→shape e p)) prime-values

fails-on-every-prime : (e : Shape) → ΩS e ≡ 1 → ¬ (Π∂ e ≡ RHSdisplay e)
fails-on-every-prime e p h =
  1≢0 (sym (fst (values-on-every-prime e p)) ∙ h ∙ snd (values-on-every-prime e p))

-- "by exactly 1", exactly
off-by-exactly-one : (e : Shape) → ΩS e ≡ 1 → Π∂ e ≡ RHSdisplay e +ℤ pos 1
off-by-exactly-one e p =
  fst (values-on-every-prime e p)
  ∙ sym (cong (_+ℤ pos 1) (snd (values-on-every-prime e p)))

-- and the display DOES hold on both Ω = 2 shapes, so the refutation is
-- not read wider than it is: the failure is the Ω = 1 row and only that.
holds-on-every-Ω2 : (e : Shape) → ΩS e ≡ 2 → Π∂ e ≡ RHSdisplay e
holds-on-every-Ω2 e p with Ω≡2→shape e p
... | inl q = subst (λ f → Π∂ f ≡ RHSdisplay f) (sym q) refl
... | inr q = subst (λ f → Π∂ f ≡ RHSdisplay f) (sym q) refl

------------------------------------------------------------------------
-- 4.  THE LEDGER'S REPAIR, proved on the whole range 1 ≤ Ω ≤ 2 — not
--     checked on a range of numerals, but proved for every ν in scope.
------------------------------------------------------------------------

repair-on-whole-range : (e : Shape) → (ΩS e ≡ 1) ⊎ (ΩS e ≡ 2)
                      → Π∂ e ≡ RHSrepair e
repair-on-whole-range e (inl p) =
  subst (λ f → Π∂ f ≡ RHSrepair f) (sym (Ω≡1→shape e p)) refl
repair-on-whole-range e (inr p) with Ω≡2→shape e p
... | inl q = subst (λ f → Π∂ f ≡ RHSrepair f) (sym q) refl
... | inr q = subst (λ f → Π∂ f ≡ RHSrepair f) (sym q) refl

-- Equivalently, as the ledger's §5.3 puts it: on Ω ≤ 2, Π_∂ = 𝟙_{Ω=1}.
Π∂-is-Ω1-indicator : (e : Shape) → (ΩS e ≡ 1) ⊎ (ΩS e ≡ 2)
                   → (Π∂ e ≡ 𝟙℘ e) ⊎ (Π∂ e ≡ pos zero)
Π∂-is-Ω1-indicator e (inl p) =
  inl (subst (λ f → Π∂ f ≡ 𝟙℘ f) (sym (Ω≡1→shape e p)) refl)
Π∂-is-Ω1-indicator e (inr p) with Ω≡2→shape e p
... | inl q = inr (subst (λ f → Π∂ f ≡ pos zero) (sym q) refl)
... | inr q = inr (subst (λ f → Π∂ f ≡ pos zero) (sym q) refl)

------------------------------------------------------------------------
-- 5.  The ledger's SECOND reading, also refuted, and now universally.
--
-- §5.3: "Under the alternative reading that 𝟙_℘ indicates *prime powers*
-- the same table refutes it identically (p and p² both indicated:
-- RHS 0,−1 against 1,0)."  Under that reading a shape is indicated iff it
-- has exactly one distinct prime, i.e. iff it is a one-element list.
------------------------------------------------------------------------

𝟙℘pp : Shape → ℤ
𝟙℘pp (_ ∷ []) = pos 1
𝟙℘pp _        = pos zero

RHSdisplay-pp : Shape → ℤ
RHSdisplay-pp e = par (ΩS e) -ℤ 𝟙℘pp e

fails-pp-on-every-prime : (e : Shape) → ΩS e ≡ 1 → ¬ (Π∂ e ≡ RHSdisplay-pp e)
fails-pp-on-every-prime e p h =
  1≢0 (sym (fst vals) ∙ h ∙ snd vals)
  where
  vals : (Π∂ e ≡ pos 1) × (RHSdisplay-pp e ≡ pos zero)
  vals = subst (λ f → (Π∂ f ≡ pos 1) × (RHSdisplay-pp f ≡ pos zero))
               (sym (Ω≡1→shape e p)) (refl , refl)

-- and on every prime SQUARE it fails too, LHS 0 against RHS −1
fails-pp-on-every-prime-square : (e : Shape) → e ≡ (suc zero ∷ [])
                               → (Π∂ e ≡ pos zero) × (RHSdisplay-pp e ≡ negsuc 0)
fails-pp-on-every-prime-square e q =
  subst (λ f → (Π∂ f ≡ pos zero) × (RHSdisplay-pp f ≡ negsuc 0)) (sym q) (refl , refl)

------------------------------------------------------------------------
-- 6.  WHAT IS A THEOREM HERE.
-- `fails-on-every-prime` and
-- `off-by-exactly-one` quantify over every shape with Ω = 1 — that is,
-- over every prime, with no bound and no enumeration — and the
-- classification `Ω≡1→shape` that makes them bite is proved, not
-- assumed.  Likewise `holds-on-every-Ω2` and `repair-on-whole-range`
-- cover the whole hypothesis 1 ≤ Ω ≤ 2 rather than a range of numerals.
--
-- WHAT IS ASSUMED.  The faithfulness of the model:
-- that ν ↦ its multiset of prime exponents is a bijection from the
-- integers ≥ 1 onto finite multisets of positive integers, and that the
-- five functions of the display are, on that datum, exactly ω = length,
-- Ω = Σ exponents, μ² = [all exponents are 1], λ = (−1)^Ω, and
-- 𝟙_℘ = [Ω = 1].  Each of the five is the *definition* of the arithmetic
-- function on factorisation data; the bijection is unique factorisation
-- (Euclid IX.14; Gauss, D.A. art. 16), which is classical.
-- No other input is used: no ordering, no primality
-- algorithm, no arithmetic beyond ℕ and ℤ.
--
-- Ledger rows 1.5 and 0.3 are settled
-- in `TransmissionRefutations.agda` Sections B and C.
------------------------------------------------------------------------
