{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TomographyConditioning
--
-- The exact conditioning constants of
--
-- THE SETTING (the note's model).  B a normed space,
-- G(z) = Σ_{j=0}^R a_j z^j with a_j ∈ B; in the arithmetic application
-- a_j = μ_{j+1} = P U_h Π_{j+1} U_k P, so a_0 = P U_h P U_k P is the
-- charge-one intermediate path and G(1) = P U_{h+k} P is the glued one.
-- Three probe families recover a_0 from linear functionals of G, each
-- with a worst-case ℓ∞→B error amplification κ = Σ_m |coefficient_m|
-- under the note's error model: INDEPENDENT ABSOLUTE errors in the
-- probes, and the natural SUPPORT NORMALIZATION of each family.  That
-- the worst-case amplification of a linear inversion a_0 = Σ_m γ_m Q_m
-- equals Σ_m |γ_m| is one line of normed-space duality; it is NOT
-- formalized here (no normed spaces in this module).  What IS
-- formalized is every combinatorial core — the exact value of Σ_m |γ_m|
-- for each of the three families, which is where the note's content and
-- all of its arithmetic risk sit.
--
-- WHAT IS PROVED GENERALLY IN R (no instance, no fitting):
--
--   * κ_pow,raw = R+1.  With q_R(x) = ∏_{j=1}^R (1 − x/j) = Σ_m c_m x^m
--     and a_0 = Σ_m c_m P_m, the raw amplification is Σ_m |c_m|.  Since
--     R!·q_R(x) = ∏_{j=1}^R (j − x), the coefficients alternate exactly:
--     c_m = (−1)^m s(R,m)/R! with s(R,m) ≥ 0 the unsigned Stirling
--     numbers of the first kind.  Hence Σ_m |c_m| x^m = q_R(−x)·(±) is
--     ∏_{j=1}^R (x + j)/R!, and at x = 1 this is (R+1)!/R! = R+1.
--     Kernel form (denominators cleared): `kappaPowRaw`.
--
--   * κ_pow = C(2R,R).  Same identity at x = R:
--     Σ_m |c_m| R^m = ∏_{j=1}^R (R + j)/R! = (2R)!/(R!)² = C(2R,R).
--     Kernel form: `kappaPowExact` : eval (pochRow R) R · R! ≡ (R+R)!,
--     i.e. Σ_m |c_m| R^m = (2R)!/(R!)², which is C(2R,R).  The bridge
--     `rise R R · R! ≡ (R+R)!` (`riseFact`, general in both arguments)
--     is the whole proof; nothing is fitted and nothing is measured.
--
--   * κ_fac = Σ_{m=0}^R C(R,m) = 2^R.  With F_m = G^{(m)}(1) and the
--     support normalization F̂_m = F_m/R_{underline m}, Taylor's
--     a_0 = Σ_m (−1)^m F_m/m! has coefficients of modulus
--     R_{underline m}/m! = C(R,m).  `kappaFac` proves
--     Σ_{m=0}^R C(R,m) ≡ 2^R generally in R by induction on the
--     library's Pascal-recurrence `_choose_` (this is the binomial
--     theorem at 1, done by hand: `pascalSum` + `chooseAbove`).
--
--   * κ_DFT = 1.  Finite Fourier inversion gives
--     a_0 = (1/n) Σ_{ν<n} G(ω^ν), n = R+1: n coefficients, each of
--     modulus exactly 1/n, so Σ|γ_ν| = n·(1/n) = 1.  `kappaDFT`
--     formalizes the abstract statement — the n-fold sum of the
--     fraction 1/n, computed with honest fraction addition
--     (a/b + c/d = (ad+cb)/(bd)), is equal to 1 as a rational — for
--     every n ≥ 1.  No complex analysis is needed for this: |ω^{-jν}|
--     = 1 is the only fact from the circle, and it is what the
--     hypothesis "each modulus is 1/n" records.
--
--   * κ_fac ≤ κ_pow, i.e. 2^R ≤ C(2R,R), GENERALLY in R, in the
--     denominator-cleared form 2^R·(R!·R!) ≤ (2R)!  (`facLEpow`).
--     The proof is the termwise one and is the honest reason the ratio
--     is exponential: C(2R,R) = ∏_{j=1}^R (R+j)/j and 2^R = ∏_{j=1}^R 2,
--     and (R+j)/j ≥ 2 exactly because j ≤ R (`riseDominates`).
--
--   * κ_DFT ≤ κ_fac, i.e. 1 ≤ 2^R, generally in R (`oneLEpow`).
--
-- WHAT IS INSTANCE-CERTIFIED BY refl (finite exact computation is
-- proof, CLAUDE.md (absent from this repository)), and why:
--
--   * `pochRow-1` … `pochRow-6`: the actual coefficient rows
--     |c_m|·R! = s(R,m), so a reader can see the object the general
--     theorems talk about (720 1764 1624 735 175 21 1 for R = 6).
--   * `kpow-choose-1` … `kpow-choose-6`: Σ_m |c_m| R^m = C(2R,R) with
--     C spelled by the library's binomial `_choose_` rather than by the
--     factorial quotient.  The general theorem `kappaPowExact` proves
--     the factorial-quotient form for ALL R; identifying (2R)!/(R!)²
--     with `(R+R) choose R` in general would need the standard
--     factorial identity for `_choose_`, which is not in the library
--     and is not needed for the conditioning claim.  So: general in the
--     quotient form, R ≤ 6 in the `choose` form.  Stated, not hidden.
--   * `strict-2` … `strict-10`: STRICTNESS 2^R < C(2R,R).  General ≤ is
--     proved above; the strict inequality is certified for 2 ≤ R ≤ 10.
--
-- THE STRICTNESS RANGE.  The circulated
-- comparison reads as "2^R < C(2R,R) for R ≥ 1".  That is FALSE at
-- R = 1: C(2,1) = 2 = 2^1, and also at R = 0 (1 = 1).  The true
-- statement is 2^R ≤ C(2R,R) for all R, strict exactly for R ≥ 2 —
-- `eq-0` and `eq-1` certify the two equality cases.  The note's
-- asymptotic ratio √(πR)/2^R is unaffected.
--
------------------------------------------------------------------------

module TomographyConditioning where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_; _^_)
open import Cubical.Data.Nat.Properties
  using ( _!; _choose_
        ; +-zero; +-suc; +-comm; +-assoc
        ; 0≡m·0; ·-comm; ·-assoc; ·-distribˡ; ·-distribʳ
        ; ·-identityˡ; ·-identityʳ; inj-·sm )
open import Cubical.Data.Nat.Order
  using (_≤_; ≤-refl; ≤-trans; ≤-·k; ≤-+k; ≤-sucℕ; suc-≤-suc; zero-≤)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Data.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using () renaming (_<_ to _<ᵇ_)

------------------------------------------------------------------------
-- 0. Two rearrangement lemmas, used everywhere below

+-shuffle : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-shuffle a b c d =
    sym (+-assoc a b (c + d))
  ∙ cong (a +_) (+-assoc b c d)
  ∙ cong (λ z → a + (z + d)) (+-comm b c)
  ∙ cong (a +_) (sym (+-assoc c b d))
  ∙ +-assoc a c (b + d)

·-shuffle : ∀ a b c d → (a · b) · (c · d) ≡ (a · c) · (b · d)
·-shuffle a b c d =
    sym (·-assoc a b (c · d))
  ∙ cong (a ·_) (·-assoc b c d)
  ∙ cong (λ z → a · (z · d)) (·-comm b c)
  ∙ cong (a ·_) (sym (·-assoc c b d))
  ∙ ·-assoc a c (b · d)

double : ∀ m → 2 · m ≡ m + m
double m = cong (m +_) (·-identityˡ m)

------------------------------------------------------------------------
-- 1. Polynomials with nonnegative coefficients
--
-- A Poly is a coefficient list, least significant first.  All three
-- inversion families below have coefficients whose ABSOLUTE VALUES are
-- what the conditioning constant sees, and in each case those absolute
-- values are (integers)/(a single factorial); so ℕ-coefficient
-- polynomials with the denominator carried separately are an exact
-- encoding — no rationals, no floats, no signs to lose.

Poly : Type₀
Poly = List ℕ

eval : Poly → ℕ → ℕ
eval []      x = 0
eval (a ∷ p) x = a + x · eval p x

addP : Poly → Poly → Poly
addP []      q       = q
addP (a ∷ p) []      = a ∷ p
addP (a ∷ p) (b ∷ q) = (a + b) ∷ addP p q

scaleP : ℕ → Poly → Poly
scaleP c []      = []
scaleP c (a ∷ p) = (c · a) ∷ scaleP c p

-- multiplication by the linear factor (x + c)
mulLin : ℕ → Poly → Poly
mulLin c p = addP (0 ∷ p) (scaleP c p)

evalAdd : ∀ p q x → eval (addP p q) x ≡ eval p x + eval q x
evalAdd []      q       x = refl
evalAdd (a ∷ p) []      x = sym (+-zero (a + x · eval p x))
evalAdd (a ∷ p) (b ∷ q) x =
    cong (λ z → (a + b) + x · z) (evalAdd p q x)
  ∙ cong ((a + b) +_) (sym (·-distribˡ x (eval p x) (eval q x)))
  ∙ +-shuffle a b (x · eval p x) (x · eval q x)

evalScale : ∀ c p x → eval (scaleP c p) x ≡ c · eval p x
evalScale c []      x = 0≡m·0 c
evalScale c (a ∷ p) x =
    cong (λ z → (c · a) + x · z) (evalScale c p x)
  ∙ cong ((c · a) +_) (·-assoc x c (eval p x)
                       ∙ cong (_· eval p x) (·-comm x c)
                       ∙ sym (·-assoc c x (eval p x)))
  ∙ ·-distribˡ c a (x · eval p x)

evalMulLin : ∀ c p x → eval (mulLin c p) x ≡ (x + c) · eval p x
evalMulLin c p x =
    evalAdd (0 ∷ p) (scaleP c p) x
  ∙ cong ((x · eval p x) +_) (evalScale c p x)
  ∙ ·-distribʳ x c (eval p x)

------------------------------------------------------------------------
-- 2. POWER MOMENTS.  P_m = Σ_j j^m a_j, a_0 = Σ_m c_m P_m with
--    q_R(x) = ∏_{j=1}^R (1 − x/j) = Σ_m c_m x^m.
--
--    R!·|c_m| = s(R,m) = [x^m] ∏_{j=1}^R (x + j)  (unsigned Stirling,
--    first kind), because R!·q_R(x) = ∏_{j=1}^R (j − x) has exactly
--    alternating signs.  `pochRow R` IS that coefficient list, built
--    by the same one-factor-at-a-time recursion.

pochRow : ℕ → Poly
pochRow zero    = 1 ∷ []
pochRow (suc n) = mulLin (suc n) (pochRow n)

-- ∏_{j=1}^{k} (x + j)
rise : ℕ → ℕ → ℕ
rise x zero    = 1
rise x (suc k) = (x + suc k) · rise x k

-- the row evaluates to the rising factorial, for every argument
evalPoch : ∀ R x → eval (pochRow R) x ≡ rise x R
evalPoch zero    x = cong (1 +_) (sym (0≡m·0 x)) ∙ +-zero 1
evalPoch (suc n) x =
    evalMulLin (suc n) (pochRow n) x
  ∙ cong ((x + suc n) ·_) (evalPoch n x)

-- the bridge to factorials: ∏_{j=1}^{k}(a+j) · a! = (a+k)!
riseFact : ∀ a k → rise a k · (a !) ≡ ((a + k) !)
riseFact a zero    = ·-identityˡ (a !) ∙ cong _! (sym (+-zero a))
riseFact a (suc k) =
    sym (·-assoc (a + suc k) (rise a k) (a !))
  ∙ cong ((a + suc k) ·_) (riseFact a k)
  ∙ cong (λ z → z · ((a + k) !)) (+-suc a k)
  ∙ sym (cong _! (+-suc a k))

-- κ_pow,raw = Σ_m |c_m| = (R+1)!/R! = R+1.
-- Cleared of the denominator R!: Σ_m s(R,m) = (R+1)·R!.
kappaPowRaw : ∀ R → eval (pochRow R) 1 ≡ suc R · (R !)
kappaPowRaw R =
    evalPoch R 1
  ∙ sym (·-identityʳ (rise 1 R))
  ∙ riseFact 1 R

-- κ_pow = Σ_m |c_m| R^m = (2R)!/(R!)² = C(2R,R).
-- Cleared of one factor of R!: (Σ_m s(R,m) R^m) · R! = (2R)!.
kappaPowExact : ∀ R → eval (pochRow R) R · (R !) ≡ ((R + R) !)
kappaPowExact R = cong (_· (R !)) (evalPoch R R) ∙ riseFact R R

-- The Stirling rows themselves, so the reader can see the coefficients
-- the theorems above quantify over: entry m of `pochRow R` is s(R,m),
-- and |c_m| = s(R,m)/R!.
pochRow-1 : pochRow 1 ≡ 1 ∷ 1 ∷ []
pochRow-1 = refl

pochRow-2 : pochRow 2 ≡ 2 ∷ 3 ∷ 1 ∷ []
pochRow-2 = refl

pochRow-3 : pochRow 3 ≡ 6 ∷ 11 ∷ 6 ∷ 1 ∷ []
pochRow-3 = refl

pochRow-4 : pochRow 4 ≡ 24 ∷ 50 ∷ 35 ∷ 10 ∷ 1 ∷ []
pochRow-4 = refl

pochRow-5 : pochRow 5 ≡ 120 ∷ 274 ∷ 225 ∷ 85 ∷ 15 ∷ 1 ∷ []
pochRow-5 = refl

pochRow-6 : pochRow 6 ≡ 720 ∷ 1764 ∷ 1624 ∷ 735 ∷ 175 ∷ 21 ∷ 1 ∷ []
pochRow-6 = refl

-- κ_pow with the central binomial spelled by the library's Pascal
-- recurrence: (Σ_m s(R,m) R^m) = C(2R,R) · R!.  Instance-certified.
kpow-choose-1 : eval (pochRow 1) 1 ≡ (2 choose 1) · (1 !)
kpow-choose-1 = refl

kpow-choose-2 : eval (pochRow 2) 2 ≡ (4 choose 2) · (2 !)
kpow-choose-2 = refl

kpow-choose-3 : eval (pochRow 3) 3 ≡ (6 choose 3) · (3 !)
kpow-choose-3 = refl

kpow-choose-4 : eval (pochRow 4) 4 ≡ (8 choose 4) · (4 !)
kpow-choose-4 = refl

kpow-choose-5 : eval (pochRow 5) 5 ≡ (10 choose 5) · (5 !)
kpow-choose-5 = refl

kpow-choose-6 : eval (pochRow 6) 6 ≡ (12 choose 6) · (6 !)
kpow-choose-6 = refl

-- and the raw constant, read off: Σ_m |c_m| = R+1 at R = 6 is 7.
kpow-raw-6 : eval (pochRow 6) 1 ≡ 7 · (6 !)
kpow-raw-6 = refl

------------------------------------------------------------------------
-- 3. FACTORIAL MOMENTS.  F_m = G^{(m)}(1); support-normalized
--    F̂_m = F_m/R_{underline m} makes the inversion coefficients
--    (−1)^m C(R,m), so κ_fac = Σ_{m=0}^R C(R,m).  Proved = 2^R
--    generally in R.

-- Σ_{m=0}^{k} (n choose m)
sumChoose : ℕ → ℕ → ℕ
sumChoose n zero    = n choose zero
sumChoose n (suc k) = sumChoose n k + (n choose suc k)

-- off-row entries vanish: C(n, m) = 0 for m > n
chooseAbove : ∀ n k → (n choose suc (n + k)) ≡ 0
chooseAbove zero    k = refl
chooseAbove (suc n) k =
    cong (_+ (n choose suc (n + k)))
         (cong (λ z → n choose suc z) (sym (+-suc n k))
          ∙ chooseAbove n (suc k))
  ∙ chooseAbove n k

-- the Pascal step, summed
pascalSum : ∀ n k → sumChoose (suc n) (suc k)
                  ≡ sumChoose n (suc k) + sumChoose n k
-- both sides normalise to suc ((n choose 1) + 1)
pascalSum n zero = refl
pascalSum n (suc k) =
    cong (_+ ((n choose suc (suc k)) + (n choose suc k))) (pascalSum n k)
  ∙ +-shuffle (sumChoose n (suc k)) (sumChoose n k)
              (n choose suc (suc k)) (n choose suc k)

-- κ_fac = Σ_{m=0}^R C(R,m) = 2^R.  General in R.
kappaFac : ∀ R → sumChoose R R ≡ 2 ^ R
kappaFac zero    = refl
kappaFac (suc n) =
    pascalSum n n
  ∙ cong (_+ sumChoose n n)
         (cong (sumChoose n n +_)
               (cong (λ z → n choose suc z) (sym (+-zero n))
                ∙ chooseAbove n 0)
          ∙ +-zero (sumChoose n n))
  ∙ cong (λ z → z + z) (kappaFac n)
  ∙ cong ((2 ^ n) +_) (sym (+-zero (2 ^ n)))

kfac-5 : sumChoose 5 5 ≡ 32
kfac-5 = refl

kfac-10 : sumChoose 10 10 ≡ 1024
kfac-10 = refl

------------------------------------------------------------------------
-- 4. ROOT-OF-UNITY (DFT).  a_j = (1/n) Σ_ν ω^{-jν} V_ν with n = R+1;
--    every inversion coefficient has modulus |ω^{-jν}|/n = 1/n, and
--    there are n of them, so κ_DFT = n·(1/n) = 1 — exactly, with no
--    R-dependence at all.
--
--    Formalized abstractly: sum n copies of the rational 1/n, with
--    honest fraction addition, and get 1.  (The circle enters only as
--    |ω^k| = 1, which is the hypothesis "each modulus is 1/n".)

Frac : Type₀
Frac = ℕ × ℕ                      -- (numerator , denominator)

_≈_ : Frac → Frac → Type₀
f ≈ g = fst f · snd g ≡ fst g · snd f

addF : Frac → Frac → Frac
addF f g = ((fst f · snd g) + (fst g · snd f)) , (snd f · snd g)

zeroF oneF : Frac
zeroF = 0 , 1
oneF  = 1 , 1

-- the modulus of every DFT inversion coefficient: 1/n
invMod : ℕ → Frac
invMod n = 1 , n

-- k-fold sum of one fraction
sumCopies : ℕ → Frac → Frac
sumCopies zero    f = zeroF
sumCopies (suc k) f = addF f (sumCopies k f)

-- k copies of 1/n add up to k/n, exactly, for every k and every n ≥ 1
sumCopiesLemma : ∀ k n → sumCopies k (invMod (suc n)) ≈ (k , suc n)
sumCopiesLemma zero    n = refl
sumCopiesLemma (suc k) n =
  let S = sumCopies k (invMod (suc n))
  in cong (λ z → (z + (fst S · suc n)) · suc n) (·-identityˡ (snd S))
   ∙ cong (λ z → (snd S + z) · suc n) (sumCopiesLemma k n)
   ∙ sym (·-assoc (suc k) (snd S) (suc n))
   ∙ cong (suc k ·_) (·-comm (snd S) (suc n))

-- κ_DFT = 1, for every n = R+1 ≥ 1.  General.
kappaDFT : ∀ n → sumCopies (suc n) (invMod (suc n)) ≈ oneF
kappaDFT n =
  let S = sumCopies (suc n) (invMod (suc n))
      e : fst S ≡ snd S
      e = inj-·sm (sumCopiesLemma (suc n) n ∙ ·-comm (suc n) (snd S))
  in ·-identityʳ (fst S) ∙ e ∙ sym (·-identityˡ (snd S))

------------------------------------------------------------------------
-- 5. THE COMPARISON.
--
--    κ_DFT = 1 ≤ 2^R = κ_fac ≤ C(2R,R) = κ_pow, both generally in R;
--    the second is strict exactly for R ≥ 2 (certified 2 ≤ R ≤ 10).

-- 2^R is never 0
powNonZero : ∀ R → Σ[ k ∈ ℕ ] (2 ^ R ≡ suc k)
powNonZero zero    = 0 , refl
powNonZero (suc n) =
  let k = fst (powNonZero n)
  in (k + (suc k + 0)) , cong (2 ·_) (snd (powNonZero n))

-- κ_DFT ≤ κ_fac : 1 ≤ 2^R
oneLEpow : ∀ R → 1 ≤ 2 ^ R
oneLEpow R =
  subst (1 ≤_) (sym (snd (powNonZero R))) (suc-≤-suc zero-≤)

-- monotonicity of · in both arguments
≤-·-mono : ∀ {a b c d} → a ≤ b → c ≤ d → a · c ≤ b · d
≤-·-mono {a} {b} {c} {d} p q =
  ≤-trans (≤-·k p)
          (subst2 _≤_ (·-comm c b) (·-comm d b) (≤-·k q))

-- the termwise reason κ_pow ≥ κ_fac: ∏_{j=1}^k (R+j) ≥ ∏_{j=1}^k (2j)
-- whenever every j in range satisfies j ≤ R.
riseDominates : ∀ R k → k ≤ R → (2 ^ k) · (k !) ≤ rise R k
riseDominates R zero    h = ≤-refl
riseDominates R (suc k) h =
  let ih : (2 ^ k) · (k !) ≤ rise R k
      ih = riseDominates R k (≤-trans ≤-sucℕ h)
      fac : 2 · suc k ≤ R + suc k
      fac = subst (_≤ (R + suc k)) (sym (double (suc k))) (≤-+k h)
  in subst (_≤ rise R (suc k))
           (sym (·-shuffle 2 (2 ^ k) (suc k) (k !)))
           (≤-·-mono fac ih)

-- κ_fac ≤ κ_pow : 2^R ≤ C(2R,R), cleared of denominators.
facLEpow : ∀ R → (2 ^ R) · ((R !) · (R !)) ≤ ((R + R) !)
facLEpow R =
  subst2 _≤_ (sym (·-assoc (2 ^ R) (R !) (R !))) (riseFact R R)
         (≤-·k (riseDominates R R ≤-refl))

-- The two equality cases — the reason "2^R < C(2R,R) for R ≥ 1" is
-- the wrong statement and "≤ always, < for R ≥ 2" is the right one.
eq-0 : (2 ^ 0) · ((0 !) · (0 !)) ≡ ((0 + 0) !)
eq-0 = refl

eq-1 : (2 ^ 1) · ((1 !) · (1 !)) ≡ ((1 + 1) !)
eq-1 = refl

-- Strictness for 2 ≤ R ≤ 10, by exact evaluation.
strict-2 : ((2 ^ 2) · ((2 !) · (2 !)) <ᵇ ((2 + 2) !)) ≡ true
strict-2 = refl

strict-3 : ((2 ^ 3) · ((3 !) · (3 !)) <ᵇ ((3 + 3) !)) ≡ true
strict-3 = refl

strict-4 : ((2 ^ 4) · ((4 !) · (4 !)) <ᵇ ((4 + 4) !)) ≡ true
strict-4 = refl

strict-5 : ((2 ^ 5) · ((5 !) · (5 !)) <ᵇ ((5 + 5) !)) ≡ true
strict-5 = refl

strict-6 : ((2 ^ 6) · ((6 !) · (6 !)) <ᵇ ((6 + 6) !)) ≡ true
strict-6 = refl

strict-7 : ((2 ^ 7) · ((7 !) · (7 !)) <ᵇ ((7 + 7) !)) ≡ true
strict-7 = refl

strict-8 : ((2 ^ 8) · ((8 !) · (8 !)) <ᵇ ((8 + 8) !)) ≡ true
strict-8 = refl

strict-9 : ((2 ^ 9) · ((9 !) · (9 !)) <ᵇ ((9 + 9) !)) ≡ true
strict-9 = refl

strict-10 : ((2 ^ 10) · ((10 !) · (10 !)) <ᵇ ((10 + 10) !)) ≡ true
strict-10 = refl

-- The three constants side by side at R = 6 (n = 7 probes):
--   κ_DFT = 1,  κ_fac = 2^6 = 64,  κ_pow = C(12,6) = 924.
kappa-table-6-dft : sumChoose 0 0 ≡ 1
kappa-table-6-dft = refl

kappa-table-6-fac : sumChoose 6 6 ≡ 64
kappa-table-6-fac = refl

kappa-table-6-pow : (12 choose 6) ≡ 924
kappa-table-6-pow = refl
