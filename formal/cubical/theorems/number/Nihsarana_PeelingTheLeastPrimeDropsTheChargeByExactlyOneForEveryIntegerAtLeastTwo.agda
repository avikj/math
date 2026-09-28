{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Nihsarana — PEELING THE LEAST PRIME DROPS THE CHARGE BY EXACTLY ONE,
-- FOR EVERY INTEGER n ≥ 2.
--
-- SOURCE.  notes/CHARGE_TOWER_MONODROMY.md (absent from this repository) (branch main), lines 193–196,
-- verbatim:
--
--   **Stated, not proved:** that $\Omega(n/p^-(n)) = \Omega(n) - 1$ for all
--   $n \ge 2$. Every `refl` in the module is X = 30 arithmetic, exactly as in
--   `SieveFiber`. The general statement is elementary and is **labelled, not
--   smuggled**.
--
-- The module the note refers to is `ChargeGradedPeeling`, whose own
-- header says the same thing in its SYĀT paragraph: "`peelDrops` in
-- particular is X = 30 arithmetic; the general statement (Ω of the
-- quotient by the least prime factor is Ω − 1) is elementary and is NOT
-- proved here."
--
--
-- WHAT IS PROVED HERE, AND IN WHOSE TERMS
--
-- Everything below is about the functions `ChargeGradedPeeling` actually
-- uses, not about any replacement for them:
--
--   Ω        = `SieveFiber.Ω`        (`omegaF (n + n) 2 n`, trial division
--                                     with fuel n + n, counting with
--                                     multiplicity),
--   lpf, peel = `ChargeGradedPeeling.lpf`, `ChargeGradedPeeling.peel`
--                                    (`lpfF n 2 n`, trial division with
--                                     fuel n; `peel n = n div lpf n` for
--                                     n ≥ 2, and `peel n = n` below 2),
--   charge   = `SieveFiber.charge`   (`isOdd ∘ Ω`),
--   _div_, _rem_ = `SieveFiber`'s fuel-bounded quotient and remainder.
--
-- The main theorem is
--
--   peel-drops : (n : ℕ) → 2 ≤ n → suc (Ω (peel n)) ≡ Ω n
--
-- which is `ChargeGradedPeeling.peelDrops` with the hypothesis
-- `n ∈ domain` (i.e. n ≤ 30) REMOVED.  Its `ltᵇ`-form `peelDrops-ltᵇ`
-- has literally the same conclusion and second hypothesis as
-- `peelDrops`.  The ∸-form `Ω-peel-∸ : Ω (peel n) ≡ Ω n ∸ 1` and
-- `Ω-pos : 1 ≤ Ω n` are the note's own wording.
--
-- Route.  Direct, from the definitions (no bridge to any other Ω):
--
--   §1  the four branches of `omegaF` and the three of `lpfF`, read off;
--   §2  fuel arithmetic: `omegaF f d n` is independent of the fuel once
--       `0 < f` and `n + n < d + f` (`omegaF-stable`), and
--       `omegaF h d m ≡ omegaF h (suc d) m` when d ∤ m (`omegaF-shift`);
--   §3  `lpfF g d n` always divides n exactly, whatever the fuel
--       (`lpfF-divides`), so a non-divisor of n is a non-divisor of the
--       cofactor (`cofactor-nodiv`);
--   §4  the scan lemma `peelF`: along the common scan of `omegaF` and
--       `lpfF` from any divisor d ≥ 2, Ω counts one more than Ω of the
--       quotient by the least divisor found;
--   §5  `peel-drops` and its restatements;
--   §6  the consequences `ChargeGradedPeeling` proves only on [1,30],
--       now for every n: `charge-flip` (`peelFlips`), `charge-square`
--       (`peelSquareCloses`), `peelGrade∞` (`peelGrade`, the ℕ-graded
--       map `H (suc k) → H k`), `P¹∞`/`P²∞` (the Bool-graded maps of
--       §5 there), plus `peel-<` (peeling strictly decreases) and
--       `peel-iter` (Ω n is exactly the number of peelings from n to 1).
--
-- All hypotheses are the visible ones; every `refl` here is a
-- definitional unfolding, not a finite table.
--
--
-- WHAT IS NOT PROVED HERE
--
--  * No identification of `SieveFiber.Ω` with `TransmissionRefutations.
--    bigOmega`, nor of `ChargeGradedPeeling.lpf` with `spf`.  Sthirabhara
--    proves `Ω-step` for `bigOmega`/`spf`; this file proves the statement
--    for `ChargeGradedPeeling`'s own functions directly, so no bridge is
--    needed and none is attempted.
--  * Nothing about the inverse limit of the charge tower: the note's
--    "Stated, not proved, and deliberately not attempted: any inverse
--    limit" stands.  This file is about one integer at a time.
--  * Nothing about monodromy.  `SetBaseNoMonodromy` already says there is
--    none to be had on a set-valued index, and nothing here changes the
--    index.
--  * No novelty: "Ω(n / p⁻(n)) = Ω(n) − 1" is the first step of the
--    definition of Ω by repeated least-prime division.  The content is
--    that `SieveFiber`'s trial-division `Ω` and `ChargeGradedPeeling`'s
--    trial-division `lpf`, two fuel-bounded programs written separately,
--    are shown to agree in this sense with their fuel discharged.
------------------------------------------------------------------------

module Nihsarana_PeelingTheLeastPrimeDropsTheChargeByExactlyOneForEveryIntegerAtLeastTwo where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using ( ℕ ; zero ; suc ; _+_ ; _·_ ; _∸_ ; iter
        ; +-suc ; +-zero ; ·-suc ; ·-identityʳ ; 0≡m·0 ; inj-sm·
        ; znots ; snotz ; injSuc )
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility using (_∣_ ; ∣-trans ; ∣-refl)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; notnot ; if_then_else_ ; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import SieveFiber
  using (ltᵇ ; eqᵇ ; eqᵇ→≡ ; _div_ ; _rem_ ; isOdd ; omegaF ; Ω ; charge)
open import ChargeGradedPeeling using (lpfF ; lpf ; peel ; big)
open import SieveRoughBridge
  using ( boolCase ; ltᵇ→< ; ltᵇ-false→≤ ; ≡→eqᵇ ; mult-grows
        ; rem-spec ; rem0→∣ ; ∣→rem0 )

------------------------------------------------------------------------
-- §0  Reading off an `if`, and the two Boolean comparisons.
------------------------------------------------------------------------

private
  ifT : {A : Type} (b : Bool) {x y : A} → b ≡ true → (if b then x else y) ≡ x
  ifT b {x} {y} e = cong (λ z → if z then x else y) e

  ifF : {A : Type} (b : Bool) {x y : A} → b ≡ false → (if b then x else y) ≡ y
  ifF b {x} {y} e = cong (λ z → if z then x else y) e

≤→ltᵇ-false : (m n : ℕ) → n ≤ m → ltᵇ m n ≡ false
≤→ltᵇ-false zero    zero    _ = refl
≤→ltᵇ-false (suc m) zero    _ = refl
≤→ltᵇ-false zero    (suc n) h = ⊥.rec (¬-<-zero h)
≤→ltᵇ-false (suc m) (suc n) h = ≤→ltᵇ-false m n (pred-≤-pred h)

<→ltᵇ : (m n : ℕ) → m < n → ltᵇ m n ≡ true
<→ltᵇ zero    zero    h = ⊥.rec (¬-<-zero h)
<→ltᵇ (suc m) zero    h = ⊥.rec (¬-<-zero h)
<→ltᵇ zero    (suc n) _ = refl
<→ltᵇ (suc m) (suc n) h = <→ltᵇ m n (pred-≤-pred h)

------------------------------------------------------------------------
-- §1  The branches of `omegaF` and `lpfF`, read off.
------------------------------------------------------------------------

omegaF-small : (f d n : ℕ) → ltᵇ n 2 ≡ true → omegaF (suc f) d n ≡ 0
omegaF-small f d n t = ifT (ltᵇ n 2) t

omegaF-prime : (f d n : ℕ) → ltᵇ n 2 ≡ false → ltᵇ n (d · d) ≡ true
             → omegaF (suc f) d n ≡ 1
omegaF-prime f d n e t = ifF (ltᵇ n 2) e ∙ ifT (ltᵇ n (d · d)) t

omegaF-div : (f d n : ℕ) → ltᵇ n 2 ≡ false → ltᵇ n (d · d) ≡ false
           → eqᵇ (n rem d) 0 ≡ true
           → omegaF (suc f) d n ≡ suc (omegaF f d (n div d))
omegaF-div f d n e b t =
  ifF (ltᵇ n 2) e ∙ ifF (ltᵇ n (d · d)) b ∙ ifT (eqᵇ (n rem d) 0) t

omegaF-skip : (f d n : ℕ) → ltᵇ n 2 ≡ false → ltᵇ n (d · d) ≡ false
            → eqᵇ (n rem d) 0 ≡ false
            → omegaF (suc f) d n ≡ omegaF f (suc d) n
omegaF-skip f d n e b t =
  ifF (ltᵇ n 2) e ∙ ifF (ltᵇ n (d · d)) b ∙ ifF (eqᵇ (n rem d) 0) t

-- Ω of the unit is 0 at every fuel and every starting divisor.
omegaF-one : (f d : ℕ) → omegaF f d 1 ≡ 0
omegaF-one zero    d = refl
omegaF-one (suc f) d = refl

lpfF-prime : (g d n : ℕ) → ltᵇ n (d · d) ≡ true → lpfF (suc g) d n ≡ n
lpfF-prime g d n t = ifT (ltᵇ n (d · d)) t

lpfF-div : (g d n : ℕ) → ltᵇ n (d · d) ≡ false → eqᵇ (n rem d) 0 ≡ true
         → lpfF (suc g) d n ≡ d
lpfF-div g d n b t = ifF (ltᵇ n (d · d)) b ∙ ifT (eqᵇ (n rem d) 0) t

lpfF-skip : (g d n : ℕ) → ltᵇ n (d · d) ≡ false → eqᵇ (n rem d) 0 ≡ false
          → lpfF (suc g) d n ≡ lpfF g (suc d) n
lpfF-skip g d n b t = ifF (ltᵇ n (d · d)) b ∙ ifF (eqᵇ (n rem d) 0) t

------------------------------------------------------------------------
-- §2  Fuel arithmetic.
--
-- A scan state is (d, n).  A division step replaces n by n div d ≤ n/2;
-- a skip step replaces d by suc d, and happens only when d·d ≤ n, hence
-- d < n.  So the fuel `f` is enough as soon as `n + n < d + f` (and
-- f > 0, so that the answer for a prime is 1 and not the fuel-out 0).
------------------------------------------------------------------------

private
  1≤2 : 1 ≤ 2
  1≤2 = suc-≤-suc zero-≤

  0<suc : (k : ℕ) → 0 < suc k
  0<suc k = suc-≤-suc zero-≤

  2·≡ : (k : ℕ) → 2 · k ≡ k + k
  2·≡ k = cong (k +_) (+-zero k)

  k<2+k : (k : ℕ) → k < 2 + k
  k<2+k k = ≤-suc ≤-refl

-- the quotient by d ≥ 2 is at most half
half-quot : (d n : ℕ) → 2 ≤ d → n div d + n div d ≤ n
half-quot d n 2≤d =
  ≤-trans (subst (_≤ d · (n div d)) (2·≡ (n div d)) (≤-·k {k = n div d} 2≤d))
          (subst (d · (n div d) ≤_) (rem-spec d n (≤-trans 1≤2 2≤d) .fst) ≤SumLeft)

-- d·d ≤ n and 2 ≤ d force d < n
scan-d<n : (d n : ℕ) → 2 ≤ d → ltᵇ n (d · d) ≡ false → d < n
scan-d<n d n 2≤d b =
  <≤-trans (mult-grows d d 2≤d (≤-trans 1≤2 2≤d)) (ltᵇ-false→≤ n (d · d) b)

fuel-pos : (f d n : ℕ) → d ≤ n → 2 ≤ n → n + n < d + suc f → 0 < f
fuel-pos f d n d≤n 2≤n h = ≤-trans (≤-trans 1≤2 2≤n) n≤f
  where
  nn≤df : n + n ≤ d + f
  nn≤df = pred-≤-pred (subst (suc (n + n) ≤_) (+-suc d f) h)
  n≤f : n ≤ f
  n≤f = ≤-k+-cancel {k = d} (≤-trans (≤-+k d≤n) nn≤df)

fuel-skip : (f d n : ℕ) → n + n < d + suc f → n + n < suc d + f
fuel-skip f d n h = subst (n + n <_) (+-suc d f) h

fuel-div : (f d n q : ℕ) → 2 ≤ n → q + q ≤ n → n + n < d + suc f → q + q < d + f
fuel-div f d n q 2≤n qq≤n h = ≤<-trans qq≤n (<≤-trans n<nn nn≤df)
  where
  n<nn : n < n + n
  n<nn = <-+k {k = n} (≤-trans 1≤2 2≤n)
  nn≤df : n + n ≤ d + f
  nn≤df = pred-≤-pred (subst (suc (n + n) ≤_) (+-suc d f) h)

gfuel-pos : (g d n : ℕ) → d < n → n < d + suc g → 0 < g
gfuel-pos g d n d<n h =
  <-k+-cancel {k = d} (subst (_< d + g) (sym (+-zero d)) (<≤-trans d<n n≤dg))
  where
  n≤dg : n ≤ d + g
  n≤dg = pred-≤-pred (subst (suc n ≤_) (+-suc d g) h)

gfuel-skip : (g d n : ℕ) → n < d + suc g → n < suc d + g
gfuel-skip g d n h = subst (n <_) (+-suc d g) h

-- THE FUEL IS DISCHARGED: two adequate fuels give the same count.
omegaF-stable : (f g d n : ℕ) → 2 ≤ d
              → 0 < f → n + n < d + f
              → 0 < g → n + n < d + g
              → omegaF f d n ≡ omegaF g d n
omegaF-stable zero    g       d n _   0<f _  _   _  = ⊥.rec (¬m<m 0<f)
omegaF-stable (suc f) zero    d n _   _   _  0<g _  = ⊥.rec (¬m<m 0<g)
omegaF-stable (suc f) (suc g) d n 2≤d _   hf _   hg with boolCase (ltᵇ n 2)
... | inl t = omegaF-small f d n t ∙ sym (omegaF-small g d n t)
... | inr e with boolCase (ltᵇ n (d · d))
...   | inl t = omegaF-prime f d n e t ∙ sym (omegaF-prime g d n e t)
...   | inr b with boolCase (eqᵇ (n rem d) 0)
...     | inl t =
          omegaF-div f d n e b t
          ∙ cong suc (omegaF-stable f g d (n div d) 2≤d
                        (fuel-pos f d n d≤n 2≤n hf) (fuel-div f d n (n div d) 2≤n qq hf)
                        (fuel-pos g d n d≤n 2≤n hg) (fuel-div g d n (n div d) 2≤n qq hg))
          ∙ sym (omegaF-div g d n e b t)
          where
          2≤n : 2 ≤ n
          2≤n = ltᵇ-false→≤ n 2 e
          d≤n : d ≤ n
          d≤n = <-weaken (scan-d<n d n 2≤d b)
          qq : n div d + n div d ≤ n
          qq = half-quot d n 2≤d
...     | inr t =
          omegaF-skip f d n e b t
          ∙ omegaF-stable f g (suc d) n (≤-suc 2≤d)
              (fuel-pos f d n d≤n 2≤n hf) (fuel-skip f d n hf)
              (fuel-pos g d n d≤n 2≤n hg) (fuel-skip g d n hg)
          ∙ sym (omegaF-skip g d n e b t)
          where
          2≤n : 2 ≤ n
          2≤n = ltᵇ-false→≤ n 2 e
          d≤n : d ≤ n
          d≤n = <-weaken (scan-d<n d n 2≤d b)

-- A divisor that does not divide m can be skipped without changing Ω.
omegaF-shift : (h d m : ℕ) → 2 ≤ d → 0 < h → m + m < d + h
             → eqᵇ (m rem d) 0 ≡ false
             → omegaF h d m ≡ omegaF h (suc d) m
omegaF-shift zero    d m _   0<h _  _  = ⊥.rec (¬m<m 0<h)
omegaF-shift (suc h) d m 2≤d _   hh nd with boolCase (ltᵇ m 2)
... | inl t = omegaF-small h d m t ∙ sym (omegaF-small h (suc d) m t)
... | inr e with boolCase (ltᵇ m (d · d))
...   | inl t = omegaF-prime h d m e t ∙ sym (omegaF-prime h (suc d) m e t')
          where
          dd≤sdsd : d · d ≤ suc d · suc d
          dd≤sdsd = ≤-trans (subst (d · d ≤_) (sym (·-suc d d)) ≤SumRight) ≤SumRight
          t' : ltᵇ m (suc d · suc d) ≡ true
          t' = <→ltᵇ m (suc d · suc d) (<≤-trans (ltᵇ→< m (d · d) t) dd≤sdsd)
...   | inr b =
          omegaF-skip h d m e b nd
          ∙ omegaF-stable h (suc h) (suc d) m (≤-suc 2≤d)
              (fuel-pos h d m d≤m 2≤m hh) (fuel-skip h d m hh)
              (0<suc h) (≤-suc hh)
          where
          2≤m : 2 ≤ m
          2≤m = ltᵇ-false→≤ m 2 e
          d≤m : d ≤ m
          d≤m = <-weaken (scan-d<n d m 2≤d b)

------------------------------------------------------------------------
-- §3  `lpfF` returns an exact divisor, whatever the fuel.
------------------------------------------------------------------------

div-self : (n : ℕ) → 0 < n → n div n ≡ 1
div-self zero    0<n = ⊥.rec (¬m<m 0<n)
div-self (suc n) _   = inj-sm· {m = n} (spec' ∙ sym (·-identityʳ (suc n)))
  where
  r0 : suc n rem suc n ≡ 0
  r0 = ∣→rem0 (suc n) (suc n) (0<suc n) (∣-refl refl)
  spec' : suc n · (suc n div suc n) ≡ suc n
  spec' = sym (+-zero _)
        ∙ cong (suc n · (suc n div suc n) +_) (sym r0)
        ∙ rem-spec (suc n) (suc n) (0<suc n) .fst

lpfF-divides : (g d n : ℕ) → 0 < d → 0 < n
             → lpfF g d n · (n div lpfF g d n) ≡ n
lpfF-divides zero    d n _   0<n = cong (n ·_) (div-self n 0<n) ∙ ·-identityʳ n
lpfF-divides (suc g) d n 0<d 0<n with boolCase (ltᵇ n (d · d))
... | inl t = cong (λ p → p · (n div p)) (lpfF-prime g d n t)
              ∙ cong (n ·_) (div-self n 0<n) ∙ ·-identityʳ n
... | inr b with boolCase (eqᵇ (n rem d) 0)
...   | inl t = cong (λ p → p · (n div p)) (lpfF-div g d n b t)
                ∙ sym (+-zero _)
                ∙ cong (d · (n div d) +_) (sym (eqᵇ→≡ (n rem d) 0 t))
                ∙ rem-spec d n 0<d .fst
...   | inr t = cong (λ p → p · (n div p)) (lpfF-skip g d n b t)
                ∙ lpfF-divides g (suc d) n (0<suc d) 0<n

-- the least divisor found is ≥ 2 when the scan starts at d ≥ 2 on n ≥ 2
lpfF-≥2 : (g d n : ℕ) → 2 ≤ d → 2 ≤ n → 2 ≤ lpfF g d n
lpfF-≥2 zero    d n _   2≤n = 2≤n
lpfF-≥2 (suc g) d n 2≤d 2≤n with boolCase (ltᵇ n (d · d))
... | inl t = subst (2 ≤_) (sym (lpfF-prime g d n t)) 2≤n
... | inr b with boolCase (eqᵇ (n rem d) 0)
...   | inl t = subst (2 ≤_) (sym (lpfF-div g d n b t)) 2≤d
...   | inr t = subst (2 ≤_) (sym (lpfF-skip g d n b t))
                      (lpfF-≥2 g (suc d) n (≤-suc 2≤d) 2≤n)

-- a cofactor of a positive number is at most it, and positive
factor-≤ : (p m n : ℕ) → 0 < n → p · m ≡ n → m ≤ n
factor-≤ zero    m n 0<n e = ⊥.rec (¬-<-zero (subst (0 <_) (sym e) 0<n))
factor-≤ (suc p) m n _   e = subst (m ≤_) e ≤SumLeft

factor-pos : (p m n : ℕ) → 0 < n → p · m ≡ n → 0 < m
factor-pos p zero    n 0<n e = ⊥.rec (¬-<-zero (subst (0 <_) (sym (0≡m·0 p ∙ e)) 0<n))
factor-pos p (suc m) n _   _ = 0<suc m

-- a non-divisor of n is a non-divisor of any cofactor of n
cofactor-nodiv : (d p m n : ℕ) → 0 < d → p · m ≡ n
               → eqᵇ (n rem d) 0 ≡ false → eqᵇ (m rem d) 0 ≡ false
cofactor-nodiv d p m n 0<d e nd with boolCase (eqᵇ (m rem d) 0)
... | inr f = f
... | inl t = ⊥.rec (true≢false (sym (≡→eqᵇ (n rem d) 0 (∣→rem0 d n 0<d d∣n)) ∙ nd))
  where
  d∣n : d ∣ n
  d∣n = ∣-trans (rem0→∣ d m 0<d (eqᵇ→≡ (m rem d) 0 t)) ∣ p , e ∣₁

------------------------------------------------------------------------
-- §4  THE SCAN LEMMA.
--
-- `omegaF` and `lpfF` run the same trial-division scan from the same
-- divisor d and branch on the same Booleans.  Along it, Ω(n) is one
-- more than Ω of n divided by the least divisor found — with the inner
-- count still started at d, which is legitimate because everything
-- below d has already been ruled out (§2's `omegaF-shift`).
------------------------------------------------------------------------

peelF : (f g h d n : ℕ) → 2 ≤ d → 2 ≤ n
      → 0 < f → n + n < d + f
      → 0 < g → n < d + g
      → 0 < h → n + n < d + h
      → omegaF f d n ≡ suc (omegaF h d (n div lpfF g d n))
peelF zero    g       h d n _   _   0<f _  _   _  _   _  = ⊥.rec (¬m<m 0<f)
peelF (suc f) zero    h d n _   _   _   _  0<g _  _   _  = ⊥.rec (¬m<m 0<g)
peelF (suc f) (suc g) h d n 2≤d 2≤n _   hf _   hg 0<h hh
  with boolCase (ltᵇ n (d · d))
... | inl t =
      omegaF-prime f d n (≤→ltᵇ-false n 2 2≤n) t
      ∙ cong suc (sym (omegaF-one h d))
      ∙ cong (λ q → suc (omegaF h d q)) (sym (div-self n (≤-trans 1≤2 2≤n)))
      ∙ cong (λ p → suc (omegaF h d (n div p))) (sym (lpfF-prime g d n t))
... | inr b with boolCase (eqᵇ (n rem d) 0)
...   | inl t =
        omegaF-div f d n e b t
        ∙ cong suc (omegaF-stable f h d (n div d) 2≤d
                      (fuel-pos f d n d≤n 2≤n hf)
                      (fuel-div f d n (n div d) 2≤n qq hf)
                      0<h
                      (≤<-trans (≤-trans qq ≤SumLeft) hh))
        ∙ cong (λ p → suc (omegaF h d (n div p))) (sym (lpfF-div g d n b t))
        where
        e : ltᵇ n 2 ≡ false
        e = ≤→ltᵇ-false n 2 2≤n
        d≤n : d ≤ n
        d≤n = <-weaken (scan-d<n d n 2≤d b)
        qq : n div d + n div d ≤ n
        qq = half-quot d n 2≤d
...   | inr t =
        omegaF-skip f d n e b t
        ∙ peelF f g h (suc d) n (≤-suc 2≤d) 2≤n
            (fuel-pos f d n d≤n 2≤n hf) (fuel-skip f d n hf)
            (gfuel-pos g d n d<n hg)    (gfuel-skip g d n hg)
            0<h (≤-suc hh)
        ∙ cong suc (sym (omegaF-shift h d m 2≤d 0<h mm<dh
                          (cofactor-nodiv d p m n 0<d p·m≡n t)))
        ∙ cong (λ p → suc (omegaF h d (n div p))) (sym (lpfF-skip g d n b t))
        where
        e : ltᵇ n 2 ≡ false
        e = ≤→ltᵇ-false n 2 2≤n
        0<d : 0 < d
        0<d = ≤-trans 1≤2 2≤d
        0<n : 0 < n
        0<n = ≤-trans 1≤2 2≤n
        d<n : d < n
        d<n = scan-d<n d n 2≤d b
        d≤n : d ≤ n
        d≤n = <-weaken d<n
        p : ℕ
        p = lpfF g (suc d) n
        m : ℕ
        m = n div p
        p·m≡n : p · m ≡ n
        p·m≡n = lpfF-divides g (suc d) n (0<suc d) 0<n
        m≤n : m ≤ n
        m≤n = factor-≤ p m n 0<n p·m≡n
        mm<dh : m + m < d + h
        mm<dh = ≤<-trans (≤-+-≤ m≤n m≤n) hh

------------------------------------------------------------------------
-- §5  THE THEOREM, in `ChargeGradedPeeling`'s terms.
------------------------------------------------------------------------

-- the quotient actually taken by `peel`, and its size
peel≡div : (n : ℕ) → 2 ≤ n → peel n ≡ n div lpf n
peel≡div n 2≤n = ifF (ltᵇ n 2) (≤→ltᵇ-false n 2 2≤n)

lpf-divides : (n : ℕ) → 1 ≤ n → lpf n · (n div lpf n) ≡ n
lpf-divides n 0<n = lpfF-divides n 2 n 1≤2 0<n

lpf-≥2 : (n : ℕ) → 2 ≤ n → 2 ≤ lpf n
lpf-≥2 n 2≤n = lpfF-≥2 n 2 n ≤-refl 2≤n

peel-pos : (n : ℕ) → 1 ≤ n → 1 ≤ peel n
peel-pos zero          h = ⊥.rec (¬-<-zero h)
peel-pos (suc zero)    _ = ≤-refl
peel-pos (suc (suc n)) _ =
  subst (1 ≤_) (sym (peel≡div m 2≤m))
        (factor-pos (lpf m) (m div lpf m) m 0<m (lpf-divides m 0<m))
  where
  m : ℕ
  m = suc (suc n)
  2≤m : 2 ≤ m
  2≤m = suc-≤-suc (suc-≤-suc zero-≤)
  0<m : 0 < m
  0<m = 0<suc (suc n)

peel-≤ : (n : ℕ) → 1 ≤ n → peel n ≤ n
peel-≤ zero          h = ⊥.rec (¬-<-zero h)
peel-≤ (suc zero)    _ = ≤-refl
peel-≤ (suc (suc n)) _ =
  subst (_≤ m) (sym (peel≡div m 2≤m))
        (factor-≤ (lpf m) (m div lpf m) m 0<m (lpf-divides m 0<m))
  where
  m : ℕ
  m = suc (suc n)
  2≤m : 2 ≤ m
  2≤m = suc-≤-suc (suc-≤-suc zero-≤)
  0<m : 0 < m
  0<m = 0<suc (suc n)

-- peeling strictly decreases every n ≥ 2
peel-< : (n : ℕ) → 2 ≤ n → peel n < n
peel-< n 2≤n =
  subst (_< n) (sym (peel≡div n 2≤n))
        (subst (m <_) (lpf-divides n 0<n)
               (mult-grows (lpf n) m (lpf-≥2 n 2≤n) 0<m))
  where
  0<n : 0 < n
  0<n = ≤-trans 1≤2 2≤n
  m : ℕ
  m = n div lpf n
  0<m : 0 < m
  0<m = factor-pos (lpf n) m n 0<n (lpf-divides n 0<n)

-- THE STATEMENT THE NOTE LABELS "Stated, not proved", PROVED.
Ω-peel : (n : ℕ) → 2 ≤ n → Ω n ≡ suc (Ω (peel n))
Ω-peel n 2≤n =
  peelF (n + n) n (n + n) 2 n ≤-refl 2≤n
        0<nn (k<2+k (n + n)) 0<n (k<2+k n) 0<nn (k<2+k (n + n))
  ∙ cong suc (omegaF-stable (n + n) (m + m) 2 m ≤-refl
                0<nn mm<2+nn 0<mm (k<2+k (m + m)))
  ∙ cong (λ x → suc (Ω x)) (sym (peel≡div n 2≤n))
  where
  0<n : 0 < n
  0<n = ≤-trans 1≤2 2≤n
  0<nn : 0 < n + n
  0<nn = ≤-trans 0<n ≤SumLeft
  m : ℕ
  m = n div lpf n
  0<m : 0 < m
  0<m = factor-pos (lpf n) m n 0<n (lpf-divides n 0<n)
  m≤n : m ≤ n
  m≤n = factor-≤ (lpf n) m n 0<n (lpf-divides n 0<n)
  0<mm : 0 < m + m
  0<mm = ≤-trans 0<m ≤SumLeft
  mm<2+nn : m + m < 2 + (n + n)
  mm<2+nn = ≤-suc (suc-≤-suc (≤-+-≤ m≤n m≤n))

-- `ChargeGradedPeeling.peelDrops`, with `n ∈ domain` removed.
peel-drops : (n : ℕ) → 2 ≤ n → suc (Ω (peel n)) ≡ Ω n
peel-drops n 2≤n = sym (Ω-peel n 2≤n)

-- the same, with exactly `peelDrops`'s second hypothesis
peelDrops-ltᵇ : (n : ℕ) → ltᵇ n 2 ≡ false → suc (Ω (peel n)) ≡ Ω n
peelDrops-ltᵇ n e = peel-drops n (ltᵇ-false→≤ n 2 e)

-- the note's wording: Ω(n / p⁻(n)) = Ω(n) − 1, with Ω(n) ≥ 1
Ω-pos : (n : ℕ) → 2 ≤ n → 1 ≤ Ω n
Ω-pos n 2≤n = subst (1 ≤_) (peel-drops n 2≤n) (0<suc (Ω (peel n)))

Ω-peel-∸ : (n : ℕ) → 2 ≤ n → Ω (peel n) ≡ Ω n ∸ 1
Ω-peel-∸ n 2≤n = cong (_∸ 1) (peel-drops n 2≤n)

------------------------------------------------------------------------
-- §6  THE CONSEQUENCES `ChargeGradedPeeling` HAS ONLY ON [1,30], FOR
--     EVERY INTEGER.
------------------------------------------------------------------------

-- where Ω vanishes
Ω<2 : (n : ℕ) → n < 2 → Ω n ≡ 0
Ω<2 zero          _ = refl
Ω<2 (suc zero)    _ = refl
Ω<2 (suc (suc n)) h = ⊥.rec (¬-<-zero (pred-≤-pred (pred-≤-pred h)))

-- `Ω>0→≥2` of `ChargeGradedPeeling`, without the domain
Ω≢0→≥2 : (n : ℕ) → ¬ (Ω n ≡ 0) → 2 ≤ n
Ω≢0→≥2 zero          h = ⊥.rec (h refl)
Ω≢0→≥2 (suc zero)    h = ⊥.rec (h refl)
Ω≢0→≥2 (suc (suc n)) _ = suc-≤-suc (suc-≤-suc zero-≤)

Ω≡0→<2 : (n : ℕ) → Ω n ≡ 0 → n < 2
Ω≡0→<2 n e with splitℕ-≤ 2 n
... | inl h = ⊥.rec (snotz (peel-drops n h ∙ e))
... | inr h = h

-- `peelFlips`: the parity shadow, for every n ≥ 2
charge-flip : (n : ℕ) → 2 ≤ n → charge (peel n) ≡ not (charge n)
charge-flip n 2≤n =
  sym (notnot (charge (peel n))) ∙ cong not (cong isOdd (peel-drops n 2≤n))

-- `big→≥2` and the square, on the sub-object Ω ≥ 2
big→2≤Ω : (n : ℕ) → big n ≡ true → 2 ≤ Ω n
big→2≤Ω n e = ltᵇ→< 1 (Ω n) e

2≤Ω→2≤n : (n : ℕ) → 2 ≤ Ω n → 2 ≤ n
2≤Ω→2≤n n h = Ω≢0→≥2 n (λ e → ¬-<-zero (subst (2 ≤_) e h))

big→≥2 : (n : ℕ) → big n ≡ true → 2 ≤ n
big→≥2 n e = 2≤Ω→2≤n n (big→2≤Ω n e)

-- one peeling leaves at least one prime factor when there were two
peel-Ω : (n : ℕ) → 2 ≤ Ω n → 1 ≤ Ω (peel n)
peel-Ω n h = pred-≤-pred (subst (2 ≤_) (sym (peel-drops n (2≤Ω→2≤n n h))) h)

peel≥2 : (n : ℕ) → 2 ≤ Ω n → 2 ≤ peel n
peel≥2 n h = Ω≢0→≥2 (peel n) (λ e → ¬-<-zero (subst (1 ≤_) e (peel-Ω n h)))

-- `peelSquareCloses`, for every n with Ω n ≥ 2
charge-square : (n : ℕ) → 2 ≤ Ω n → charge (peel (peel n)) ≡ charge n
charge-square n h =
  charge-flip (peel n) (peel≥2 n h)
  ∙ cong not (charge-flip n (2≤Ω→2≤n n h))
  ∙ notnot (charge n)

-- THE ℕ-GRADED FORM (`H`, `peelGrade`), with no domain.
H∞ : ℕ → Type
H∞ k = Σ[ n ∈ ℕ ] (Ω n ≡ k)

peelGrade∞ : (k : ℕ) → H∞ (suc k) → H∞ k
peelGrade∞ k (n , e) =
  peel n , injSuc (peel-drops n (Ω≢0→≥2 n (λ z → znots (sym z ∙ e))) ∙ e)

-- THE BOOL-GRADED FORM (`G`, `G₂`, `P¹`, `P²`), with no domain.
G∞ : Bool → Type
G∞ r = Σ[ n ∈ ℕ ] (charge n ≡ r)

G₂∞ : Bool → Type
G₂∞ r = Σ[ n ∈ ℕ ] ((big n ≡ true) × (charge n ≡ r))

P¹∞ : (r : Bool) → G₂∞ r → G∞ (not r)
P¹∞ r (n , b , c) = peel n , (charge-flip n (big→≥2 n b) ∙ cong not c)

P²∞ : (r : Bool) → G₂∞ r → G∞ r
P²∞ r (n , b , c) = peel (peel n) , (charge-square n (big→2≤Ω n b) ∙ c)

-- Ω n IS THE HEIGHT: exactly Ω n peelings take n ≥ 1 to the unit.
private
  iter-suc : {A : Type} (k : ℕ) (f : A → A) (z : A)
           → iter (suc k) f z ≡ iter k f (f z)
  iter-suc zero    f z = refl
  iter-suc (suc k) f z = cong f (iter-suc k f z)

peel-iter-Ω : (k n : ℕ) → 1 ≤ n → Ω n ≡ k → iter k peel n ≡ 1
peel-iter-Ω zero    zero          h _ = ⊥.rec (¬-<-zero h)
peel-iter-Ω zero    (suc zero)    _ _ = refl
peel-iter-Ω zero    (suc (suc n)) _ e =
  ⊥.rec (snotz (peel-drops (suc (suc n)) (suc-≤-suc (suc-≤-suc zero-≤)) ∙ e))
peel-iter-Ω (suc k) n 1≤n e =
  iter-suc k peel n
  ∙ peel-iter-Ω k (peel n) (peel-pos n 1≤n)
      (injSuc (peel-drops n 2≤n ∙ e))
  where
  2≤n : 2 ≤ n
  2≤n = Ω≢0→≥2 n (λ z → znots (sym z ∙ e))

peel-iter : (n : ℕ) → 1 ≤ n → iter (Ω n) peel n ≡ 1
peel-iter n h = peel-iter-Ω (Ω n) n h refl
