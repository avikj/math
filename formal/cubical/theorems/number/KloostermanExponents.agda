{-# OPTIONS --cubical --safe #-}
------------------------------------------------------------------------------
-- KloostermanExponents : the exact exponent arithmetic of
-- landed as checked terms.
--
-- THE ENCODING.  Every exponent in the audit is a rational with denominator
-- dividing 40 (the bracket in (2.2) uses 8, 20, 4, 10, 5).  So a monomial
-- D^x R^y F^z is stored as the integer triple (40x, 40y, 40z), and an integer
-- is stored as a pair of naturals `up (-) dn` -- "integer numerator over a
-- cleared denominator", never a float, never a division.  Every claim below is
-- therefore a statement about `_+_`, `_*_` and `_<_` on ℕ, and is decided by
-- the kernel.
------------------------------------------------------------------------------

module KloostermanExponents where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)

------------------------------------------------------------------------------
-- 1. Signed integers as pairs of naturals.
------------------------------------------------------------------------------

infix 6 _⊖_

record ℤ± : Type₀ where
  constructor _⊖_
  field
    up dn : ℕ

open ℤ± public

-- Equality of `up (-) dn` values, cleared to an equation in ℕ.
_≐_ : ℤ± → ℤ± → Type₀
x ≐ y = up x + dn y ≡ up y + dn x

-- Order, likewise cleared.
_≼_ : ℤ± → ℤ± → Type₀
x ≼ y = up x + dn y ≤ up y + dn x

_≺_ : ℤ± → ℤ± → Type₀
x ≺ y = up x + dn y < up y + dn x

isNeg isZer isPos : ℤ± → Type₀
isNeg  x = up x < dn x
isZer x = up x ≡ dn x
isPos  x = dn x < up x

_⊞_ : ℤ± → ℤ± → ℤ±
(a ⊖ b) ⊞ (c ⊖ d) = (a + c) ⊖ (b + d)

⊟_ : ℤ± → ℤ±
⊟ (a ⊖ b) = b ⊖ a

-- Multiplication by a natural scalar (used only on literals).
_⊛_ : ℕ → ℤ± → ℤ±
k ⊛ (a ⊖ b) = (k · a) ⊖ (k · b)

------------------------------------------------------------------------------
-- 2. Transfer lemmas: signs respect `≐` and `≼`.
------------------------------------------------------------------------------

≐-isNeg : {x y : ℤ±} → x ≐ y → isNeg x → isNeg y
≐-isNeg {x} {y} e nx =
  <-k+-cancel {k = dn x}
    (subst (_< dn x + dn y) (+-comm (up y) (dn x))
      (subst (_< dn x + dn y) e (<-+k {k = dn y} nx)))

≐-isPos : {x y : ℤ±} → x ≐ y → isPos x → isPos y
≐-isPos {x} {y} e px =
  <-k+-cancel {k = up x}
    (subst ((up x + dn y) <_) (+-comm (up y) (up x))
      (subst (_< up y + up x) (sym e) (<-k+ {k = up y} px)))

≐-isZer : {x y : ℤ±} → x ≐ y → isZer x → isZer y
≐-isZer {x} {y} e zx =
  inj-+m (sym e ∙ cong (_+ dn y) zx ∙ +-comm (dn x) (dn y))

≼-isNeg : {x y : ℤ±} → x ≼ y → isNeg y → isNeg x
≼-isNeg {x} {y} le ny =
  <-k+-cancel {k = dn y}
    (subst (_< dn y + dn x) (+-comm (up x) (dn y))
      (≤<-trans le (<-+k {k = dn x} ny)))

------------------------------------------------------------------------------
-- 3. Cancelling a positive scalar.  Needed exactly once, to pass between the
--    40-cleared exponent vectors and the q-cleared parameter inequalities.
------------------------------------------------------------------------------

·k-< : {m n : ℕ} (k : ℕ) → m < n → (suc k · m) < (suc k · n)
·k-< {m} {n} k p = subst2 _<_ (·-comm m (suc k)) (·-comm n (suc k)) (<-·sk {k = k} p)

·k-≤ : {m n : ℕ} (k : ℕ) → m ≤ n → (k · m) ≤ (k · n)
·k-≤ {m} {n} k p = subst2 _≤_ (·-comm m k) (·-comm n k) (≤-·k {k = k} p)

·k-<-cancel : {m n : ℕ} (k : ℕ) → (suc k · m) < (suc k · n) → m < n
·k-<-cancel {m} {n} k p with splitℕ-< m n
... | inl q = q
... | inr q = ⊥.rec (<-asym p (·k-≤ (suc k) q))

------------------------------------------------------------------------------
-- 4. Monomials D^x R^y F^z, exponents cleared by 40.
------------------------------------------------------------------------------

record Mono : Type₀ where
  constructor mono
  field
    eD eR eF : ℤ±

open Mono public

_≡ᵐ_ : Mono → Mono → Type₀
x ≡ᵐ y = (eD x ≐ eD y) × ((eR x ≐ eR y) × (eF x ≐ eF y))

_⊞ᵐ_ : Mono → Mono → Mono
x ⊞ᵐ y = mono (eD x ⊞ eD y) (eR x ⊞ eR y) (eF x ⊞ eF y)

⊟ᵐ_ : Mono → Mono
⊟ᵐ x = mono (⊟ eD x) (⊟ eR x) (⊟ eF x)

_⊟ᵐ_ : Mono → Mono → Mono
x ⊟ᵐ y = x ⊞ᵐ (⊟ᵐ y)

_⊛ᵐ_ : ℕ → Mono → Mono
k ⊛ᵐ x = mono (k ⊛ eD x) (k ⊛ eR x) (k ⊛ eF x)

-- The three base scales.
mD mR mF : Mono
mD = mono (40 ⊖ 0) (0 ⊖ 0) (0 ⊖ 0)
mR = mono (0 ⊖ 0) (40 ⊖ 0) (0 ⊖ 0)
mF = mono (0 ⊖ 0) (0 ⊖ 0) (40 ⊖ 0)

-- Section 3, display (3.1): the exact scale substitution M = D, N = D/R.
mM mN : Mono
mM = mD
mN = mD ⊟ᵐ mR

------------------------------------------------------------------------------
-- 5. Section 3: the five terms of Wright's bracket (2.2), and the relative
--    factors (3.3)-(3.7).
--
--    Each term T is DEFINED by a vector and CERTIFIED against its defining
--    expression with denominators cleared, e.g. T₁ = N^{-1/8} is certified as
--    the integer identity 8*T₁ = -N.  Multiplication by a nonzero rational is
--    injective, so the identity pins T₁ uniquely; nothing is assumed.
------------------------------------------------------------------------------

T₁ T₂ T₃ T₄ T₅ : Mono
T₁ = mono (0 ⊖ 5) (5 ⊖ 0)  (0 ⊖ 0)   -- N^{-1/8}
T₂ = mono (0 ⊖ 5) (0 ⊖ 0)  (0 ⊖ 0)   -- R^{1/8} N^{1/8} M^{-1/4}
T₃ = mono (0 ⊖ 2) (0 ⊖ 0)  (0 ⊖ 2)   -- M^{1/10} R^{-3/20} F^{-1/20} N^{-3/20}
T₄ = mono (0 ⊖ 2) (0 ⊖ 6)  (0 ⊖ 6)   -- N^{3/20} F^{-3/20} M^{-1/5}
T₅ = mono (0 ⊖ 5) (0 ⊖ 15) (0 ⊖ 0)   -- N^{3/8} M^{-1/2}

-- 8 * T₁ = -N
def-T₁ : (8 ⊛ᵐ T₁) ≡ᵐ (⊟ᵐ mN)
def-T₁ = refl , refl , refl

-- 8 * T₂ = R + N - 2M
def-T₂ : (8 ⊛ᵐ T₂) ≡ᵐ ((mR ⊞ᵐ mN) ⊟ᵐ (2 ⊛ᵐ mM))
def-T₂ = refl , refl , refl

-- 20 * T₃ = 2M - 3R - F - 3N
def-T₃ : (20 ⊛ᵐ T₃) ≡ᵐ ((((2 ⊛ᵐ mM) ⊟ᵐ (3 ⊛ᵐ mR)) ⊟ᵐ mF) ⊟ᵐ (3 ⊛ᵐ mN))
def-T₃ = refl , refl , refl

-- 20 * T₄ = 3N - 3F - 4M
def-T₄ : (20 ⊛ᵐ T₄) ≡ᵐ (((3 ⊛ᵐ mN) ⊟ᵐ (3 ⊛ᵐ mF)) ⊟ᵐ (4 ⊛ᵐ mM))
def-T₄ = refl , refl , refl

-- 8 * T₅ = 3N - 4M
def-T₅ : (8 ⊛ᵐ T₅) ≡ᵐ ((3 ⊛ᵐ mN) ⊟ᵐ (4 ⊛ᵐ mM))
def-T₅ = refl , refl , refl

-- The fixed prefactor R^{1/4} of (2.2).
quarterR : Mono
quarterR = mono (0 ⊖ 0) (10 ⊖ 0) (0 ⊖ 0)

def-quarterR : (4 ⊛ᵐ quarterR) ≡ᵐ mR
def-quarterR = refl , refl , refl

-- The five relative factors: S i = R^{1/4} * T i.
S₁ S₂ S₃ S₄ S₅ : Mono
S₁ = T₁ ⊞ᵐ quarterR
S₂ = T₂ ⊞ᵐ quarterR
S₃ = T₃ ⊞ᵐ quarterR
S₄ = T₄ ⊞ᵐ quarterR
S₅ = T₅ ⊞ᵐ quarterR

-- The right-hand sides claimed by the note in (3.3)-(3.7), each itself
-- certified against its defining monomial rather than transcribed.
C₁ C₂ C₃ C₄ C₅ : Mono
C₁ = mono (0 ⊖ 5) (15 ⊖ 0) (0 ⊖ 0)   -- D^{-1/8} R^{3/8}
C₂ = mono (0 ⊖ 5) (10 ⊖ 0) (0 ⊖ 0)   -- D^{-1/8} R^{1/4}
C₃ = mono (0 ⊖ 2) (10 ⊖ 0) (0 ⊖ 2)   -- D^{-1/20} F^{-1/20} R^{1/4}
C₄ = mono (0 ⊖ 2) (4 ⊖ 0)  (0 ⊖ 6)   -- D^{-1/20} F^{-3/20} R^{1/10}
C₅ = mono (0 ⊖ 5) (0 ⊖ 5)  (0 ⊖ 0)   -- D^{-1/8} R^{-1/8}

def-C₁ : (8 ⊛ᵐ C₁) ≡ᵐ ((⊟ᵐ mD) ⊞ᵐ (3 ⊛ᵐ mR))
def-C₁ = refl , refl , refl

def-C₂ : (8 ⊛ᵐ C₂) ≡ᵐ ((⊟ᵐ mD) ⊞ᵐ (2 ⊛ᵐ mR))
def-C₂ = refl , refl , refl

def-C₃ : (20 ⊛ᵐ C₃) ≡ᵐ (((⊟ᵐ mD) ⊞ᵐ (5 ⊛ᵐ mR)) ⊟ᵐ mF)
def-C₃ = refl , refl , refl

def-C₄ : (20 ⊛ᵐ C₄) ≡ᵐ (((⊟ᵐ mD) ⊞ᵐ (2 ⊛ᵐ mR)) ⊟ᵐ (3 ⊛ᵐ mF))
def-C₄ = refl , refl , refl

def-C₅ : (8 ⊛ᵐ C₅) ≡ᵐ ((⊟ᵐ mD) ⊟ᵐ mR)
def-C₅ = refl , refl , refl

------------------------------------------------------------------------------
-- THEOREM (audit (3.3)-(3.7), hence the boxed display (0.3)).
------------------------------------------------------------------------------

audit-3-3 : S₁ ≡ᵐ C₁
audit-3-3 = refl , refl , refl

audit-3-4 : S₂ ≡ᵐ C₂
audit-3-4 = refl , refl , refl

audit-3-5 : S₃ ≡ᵐ C₃
audit-3-5 = refl , refl , refl

audit-3-6 : S₄ ≡ᵐ C₄
audit-3-6 = refl , refl , refl

audit-3-7 : S₅ ≡ᵐ C₅
audit-3-7 = refl , refl , refl

------------------------------------------------------------------------------
-- 6. Section 4: the exponent forms (0.4).
--
--    With R = D^ρ and F = D^φ, the D-exponent of S i is
--        E i = (eD + eR * ρ + eF * φ) / 40,
--    so the vector S i IS the coefficient list of (0.4).  Reading it off:
--        S₁ = (-5, 15,  0)/40  =  -1/8  + 3ρ/8
--        S₂ = (-5, 10,  0)/40  =  -1/8  + ρ/4
--        S₃ = (-2, 10, -2)/40  =  -1/20 + ρ/4  - φ/20
--        S₄ = (-2,  4, -6)/40  =  -1/20 + ρ/10 - 3φ/20
--        S₅ = (-5, -5,  0)/40  =  -1/8  - ρ/8
--    which is (0.4) verbatim.  No separate proof is needed: (0.4) is the
--    vector that sections 3 and 5 above already certified.
--
--    Writing ρ = r/q and φ = f/q, `evalAt q r f` returns 40*q*E.
------------------------------------------------------------------------------

evalAt : ℕ → ℕ → ℕ → Mono → ℤ±
evalAt q r f (mono (a ⊖ b) (c ⊖ d) (g ⊖ h)) =
  ((a · q) + ((c · r) + (g · f))) ⊖ ((b · q) + ((d · r) + (h · f)))

-- A value claim: the exponent equals (ap - am)/b, cross-multiplied.
value : ℕ → ℤ± → ℕ → ℕ → ℕ → Type₀
value q x ap am b = b · up x + (40 · q) · am ≡ b · dn x + (40 · q) · ap

------------------------------------------------------------------------------
-- 7. Section 3 / (0.2): the structural hypothesis M << N^2 is exactly ρ < 1/2.
--
--    exponent(N^2) - exponent(M) = (2 - 2ρ) - 1 = 1 - 2ρ, whose q-cleared
--    numerator is q - 2r.  So the hypothesis holds iff 2r < q, and it
--    DEGENERATES TO EQUALITY exactly at the quarter-scale endpoint ρ = 1/2.
------------------------------------------------------------------------------

-- The 40-cleared gap, computed from the monomials rather than asserted.
hypGapM : Mono
hypGapM = (2 ⊛ᵐ mN) ⊟ᵐ mM

hypGapM-value : hypGapM ≡ᵐ mono (40 ⊖ 0) (0 ⊖ 80) (0 ⊖ 0)
hypGapM-value = refl , refl , refl

-- Its q-cleared value: q - 2r.
hypGap : ℕ → ℕ → ℤ±
hypGap q r = q ⊖ (2 · r)

hypGap-bridge : (q r : ℕ) → evalAt q r 0 hypGapM ≐ (40 ⊛ hypGap q r)
hypGap-bridge q r =
    cong (_+ (40 · (2 · r))) (+-zero (80 · q))
  ∙ cong ((80 · q) +_) (·-assoc 40 2 r)
  ∙ sym ( cong ((40 · q) +_) (cong ((40 · q) +_) (+-zero (80 · r)))
        ∙ +-assoc (40 · q) (40 · q) (80 · r)
        ∙ cong (_+ (80 · r)) (·-distribʳ 40 40 q) )

-- (3.2): the hypothesis M << N^2 is available exactly on ρ < 1/2.
wright-hypothesis-iff : (q r : ℕ) → isPos (hypGap q r) ≡ (2 · r < q)
wright-hypothesis-iff q r = refl

-- (0.2) and the endpoint: at ρ = 1/2 the hypothesis is an equality, not a
-- strict inequality.  This is the one place where the note's `R << D^{1/2}`
-- (3.2) and its `R <= D^{1/2}` (1.3), (0.7) differ.
endpoint-is-tight : isZer (hypGap 2 1)
endpoint-is-tight = refl

quarter-scale-admissible : isPos (hypGap 5 1)   -- ρ = 1/5 is strictly inside
quarter-scale-admissible = 2 , refl

------------------------------------------------------------------------------
-- 8. Section 4 / 9: the exponent trichotomy at φ = 0.
--
--    E₃ = (-2 + 10ρ)/40 is the LARGEST of the five exponents throughout the
--    whole admissible range 0 <= ρ <= 1/2.  Hence the direct application saves
--    exactly when E₃ < 0, i.e. exactly when ρ < 1/5.  This is stronger than
--    the note, which observes only that E₃ is the binding constraint.
------------------------------------------------------------------------------

-- 2r <= q  ==>  5r <= 3q.
five-r≤three-q : (q r : ℕ) → 2 · r ≤ q → 5 · r ≤ 3 · q
five-r≤three-q q r h = ≤-trans (≤-·k {m = 5} {n = 6} {k = r} (1 , refl)) h6
  where
  h6 : 6 · r ≤ 3 · q
  h6 = subst2 _≤_ (·-comm (2 · r) 3 ∙ ·-assoc 3 2 r) (·-comm q 3) (≤-·k {k = 3} h)

E₃-dominates-E₁ : (q r : ℕ) → 2 · r ≤ q → evalAt q r 0 S₁ ≼ evalAt q r 0 S₃
E₃-dominates-E₁ q r h =
  subst2 _≤_
    (sym (cong₂ _+_ (+-zero (15 · r)) (+-zero (2 · q))))
    (sym (cong₂ _+_ (+-zero (10 · r)) (+-zero (5 · q))))
    core
  where
  core : 15 · r + 2 · q ≤ 10 · r + 5 · q
  core = subst2 _≤_
           (+-assoc (10 · r) (5 · r) (2 · q) ∙ cong (_+ 2 · q) (·-distribʳ 10 5 r))
           (cong ((10 · r) +_) (·-distribʳ 3 2 q))
           (≤-k+ {k = 10 · r} (≤-+k {k = 2 · q} (five-r≤three-q q r h)))

E₃-dominates-E₂ : (q r : ℕ) → evalAt q r 0 S₂ ≼ evalAt q r 0 S₃
E₃-dominates-E₂ q r =
  ≤-k+ {k = (10 · r) + 0}
    (subst2 _≤_ (sym (+-zero (2 · q))) (sym (+-zero (5 · q)))
      (≤-·k {m = 2} {n = 5} {k = q} (3 , refl)))

E₃-dominates-E₄ : (q r : ℕ) → evalAt q r 0 S₄ ≼ evalAt q r 0 S₃
E₃-dominates-E₄ q r =
  ≤-k+ {k = (10 · r) + 0}
    (≤-k+ {k = 2 · q} (zero-≤ {n = (6 · r) + 0}))

E₃-dominates-E₅ : (q r : ℕ) → evalAt q r 0 S₅ ≼ evalAt q r 0 S₃
E₃-dominates-E₅ q r =
  ≤-k+ {k = (10 · r) + 0}
    (subst (_≤ (5 · q) + ((15 · r) + 0)) (sym (+-zero (2 · q)))
      (≤-trans (≤-·k {m = 2} {n = 5} {k = q} (3 , refl)) ≤SumLeft))

------------------------------------------------------------------------------
-- MAIN THEOREM A (audit (0.6), the saving range).
--   ρ < 1/5, φ = 0  ==>  all five exponents are strictly negative.
------------------------------------------------------------------------------

E₃-neg : (q r : ℕ) → 5 · r < q → isNeg (evalAt q r 0 S₃)
E₃-neg q r h =
  subst2 _<_ (·-assoc 2 5 r ∙ sym (+-zero (10 · r))) (sym (+-zero (2 · q)))
    (·k-< 1 h)

direct-saving
  : (q r : ℕ) → 5 · r < q
  → isNeg (evalAt q r 0 S₁) × (isNeg (evalAt q r 0 S₂)
  × (isNeg (evalAt q r 0 S₃) × (isNeg (evalAt q r 0 S₄)
  × isNeg (evalAt q r 0 S₅))))
direct-saving q r h =
    ≼-isNeg (E₃-dominates-E₁ q r adm) e₃neg
  , ≼-isNeg (E₃-dominates-E₂ q r) e₃neg
  , e₃neg
  , ≼-isNeg (E₃-dominates-E₄ q r) e₃neg
  , ≼-isNeg (E₃-dominates-E₅ q r) e₃neg
  where
  e₃neg : isNeg (evalAt q r 0 S₃)
  e₃neg = E₃-neg q r h
  adm : 2 · r ≤ q
  adm = ≤-trans (≤-·k {m = 2} {n = 5} {k = r} (3 , refl)) (<-weaken h)

-- The four dominations bundled: E₃ is the maximum of the five exponents
-- throughout the admissible range 0 <= ρ <= 1/2 at φ = 0.  Consequently the
-- substituted bound's exponent IS E₃ = -1/20 + ρ/4, and the "two terms worse
-- than trivial" of (0.8) are dominated by E₃ = 3/40 (not by E₁ = 1/16).
E₃-is-max
  : (q r : ℕ) → 2 · r ≤ q
  → (evalAt q r 0 S₁ ≼ evalAt q r 0 S₃) × ((evalAt q r 0 S₂ ≼ evalAt q r 0 S₃)
  × ((evalAt q r 0 S₄ ≼ evalAt q r 0 S₃) × (evalAt q r 0 S₅ ≼ evalAt q r 0 S₃)))
E₃-is-max q r h =
    E₃-dominates-E₁ q r h
  , E₃-dominates-E₂ q r
  , E₃-dominates-E₄ q r
  , E₃-dominates-E₅ q r

------------------------------------------------------------------------------
-- MAIN THEOREM B (audit (0.7) and section 9, the no-go).
--   ρ > 1/5  ==>  E₃ > 0: the substituted bound is strictly WORSE than the
--   arbitrary-coefficient trivial bound.  Note no upper constraint on ρ is
--   needed, so this covers the whole frontier D^{1/5} < R <= D^{1/2}.
------------------------------------------------------------------------------

frontier-no-go : (q r : ℕ) → q < 5 · r → isPos (evalAt q r 0 S₃)
frontier-no-go q r h =
  subst2 _<_ (sym (+-zero (2 · q))) (·-assoc 2 5 r ∙ sym (+-zero (10 · r)))
    (·k-< 1 h)

------------------------------------------------------------------------------
-- MAIN THEOREM C (audit section 4, "at ρ = 1/5 the third term is exactly of
--   trivial size").  The threshold is sharp: E₃ = 0 exactly at ρ = 1/5.
------------------------------------------------------------------------------

threshold-sharp : (q r : ℕ) → q ≡ 5 · r → isZer (evalAt q r 0 S₃)
threshold-sharp q r h =
    +-zero (10 · r)
  ∙ sym (·-assoc 2 5 r)
  ∙ cong (2 ·_) (sym h)
  ∙ sym (+-zero (2 · q))

------------------------------------------------------------------------------
-- MAIN THEOREM D (a SHARPENING of section 5, not stated in the note).
--
--   The note's audit rule (5.2) says a factorisation is not progress unless it
--   beats the unsplit balanced bound.  The note then says termwise fixed-R use
--   "does not pass that test on the full quarter-scale range".  In fact it
--   fails on the WHOLE range: since E₃ = -1/20 + ρ/4 is the maximum exponent
--   for every admissible ρ, and the unsplit balanced value (ρ = 0) is -1/20,
--   the split is strictly worse than unsplit for EVERY ρ > 0, not merely for
--   ρ >= 1/5.  Both sides here are cleared by the same 40q, so they compare
--   directly.
------------------------------------------------------------------------------

split-strictly-worse : (q r : ℕ) → 0 < r → evalAt q 0 0 S₃ ≺ evalAt q r 0 S₃
split-strictly-worse q r h =
  <-+k {k = (2 · q) + 0}
    (subst (0 <_) (sym (+-zero (10 · r))) (·k-< 9 h))

------------------------------------------------------------------------------
-- 9. Numeric certificates.  These replay, as kernel facts, every number of the
--    audit report.  Cross-references are to the JSON
--    report data/egb_circulation_0002/
--      PRIME_MOBIUS_KLOOSTERMAN_PARAMETER_AUDIT_REPORT_2026-08-16.json (absent from this repository).
------------------------------------------------------------------------------

-- ---- check UNSPLIT-BALANCED-COMPARISON, audit (5.1): ρ = 0, φ = 0. --------
-- Exponent vector (-1/8, -1/8, -1/20, -1/20, -1/8); maximum -1/20.

balanced-E₁ : value 1 (evalAt 1 0 0 S₁) 0 1 8
balanced-E₁ = refl

balanced-E₂ : value 1 (evalAt 1 0 0 S₂) 0 1 8
balanced-E₂ = refl

balanced-E₃ : value 1 (evalAt 1 0 0 S₃) 0 1 20
balanced-E₃ = refl

balanced-E₄ : value 1 (evalAt 1 0 0 S₄) 0 1 20
balanced-E₄ = refl

balanced-E₅ : value 1 (evalAt 1 0 0 S₅) 0 1 8
balanced-E₅ = refl

-- ---- check THRESHOLD-SHARPNESS-FOR-DIRECT-BOUND: ρ = 1/5, φ = 0. ---------
-- Exponent vector (-1/20, -3/40, 0, -3/100, -3/20).

fifth-E₁ : value 5 (evalAt 5 1 0 S₁) 0 1 20
fifth-E₁ = refl

fifth-E₂ : value 5 (evalAt 5 1 0 S₂) 0 3 40
fifth-E₂ = refl

fifth-E₃ : value 5 (evalAt 5 1 0 S₃) 0 0 1
fifth-E₃ = refl

fifth-E₄ : value 5 (evalAt 5 1 0 S₄) 0 3 100
fifth-E₄ = refl

fifth-E₅ : value 5 (evalAt 5 1 0 S₅) 0 3 20
fifth-E₅ = refl

fifth-E₃-is-zero : isZer (evalAt 5 1 0 S₃)
fifth-E₃-is-zero = refl

-- ---- check QUARTER-SCALE-ENDPOINT, audit (0.8): ρ = 1/2, φ = 0. ----------
-- Exponent vector (1/16, 0, 3/40, 0, -3/16): two positive, two zero, one
-- negative.

endpoint-E₁ : value 2 (evalAt 2 1 0 S₁) 1 0 16
endpoint-E₁ = refl

endpoint-E₂ : value 2 (evalAt 2 1 0 S₂) 0 0 1
endpoint-E₂ = refl

endpoint-E₃ : value 2 (evalAt 2 1 0 S₃) 3 0 40
endpoint-E₃ = refl

endpoint-E₄ : value 2 (evalAt 2 1 0 S₄) 0 0 1
endpoint-E₄ = refl

endpoint-E₅ : value 2 (evalAt 2 1 0 S₅) 0 3 16
endpoint-E₅ = refl

endpoint-signs
  : isPos (evalAt 2 1 0 S₁) × (isZer (evalAt 2 1 0 S₂)
  × (isPos (evalAt 2 1 0 S₃) × (isZer (evalAt 2 1 0 S₄)
  × isNeg (evalAt 2 1 0 S₅))))
endpoint-signs = (4 , refl) , refl , (5 , refl) , refl , (14 , refl)

-- ---- check EXPONENT-SUBSTITUTION: ρ = 7/31, φ = 2/19. -------------------
-- Common denominator q = 589 = 19*31, so r = 133 = 7*19 and f = 62 = 2*31.
-- The report gives (-5/124, -17/248, 7/5890, -509/11780, -19/124).

sample-E₁ : value 589 (evalAt 589 133 62 S₁) 0 5 124
sample-E₁ = refl

sample-E₂ : value 589 (evalAt 589 133 62 S₂) 0 17 248
sample-E₂ = refl

sample-E₃ : value 589 (evalAt 589 133 62 S₃) 7 0 5890
sample-E₃ = refl

sample-E₄ : value 589 (evalAt 589 133 62 S₄) 0 509 11780
sample-E₄ = refl

sample-E₅ : value 589 (evalAt 589 133 62 S₅) 0 19 124
sample-E₅ = refl

-- ---- check FREQUENCY-PHASE-DIAGRAM. -------------------------------------
-- The threshold ρ*(φ) = min{1/3, (1+φ)/5}: the note's (0.5) also lists 1/2
-- and (1+3φ)/2, both of which are redundant for φ >= 0.  The report's samples
-- are ρ*(0) = 1/5, ρ*(1/5) = 6/25, ρ*(1) = 1/3.
--
-- φ = 0, ρ = 1/5: E₃ = 0 (fifth-E₃ above) and E₁ < 0, so E₃ binds.
phase-φ0-E₁ : isNeg (evalAt 5 1 0 S₁)
phase-φ0-E₁ = 9 , refl

-- φ = 1/5, ρ = 6/25: common denominator q = 25, r = 6, f = 5.  E₃ = 0.
phase-φ5-E₃ : isZer (evalAt 25 6 5 S₃)
phase-φ5-E₃ = refl

phase-φ5-E₁ : isNeg (evalAt 25 6 5 S₁)   -- E₁ still strictly negative there
phase-φ5-E₁ = 34 , refl

-- φ = 1, ρ = 1/3: q = 3, r = 1, f = 3.  Now E₁ = 0 and E₃ < 0: the bottleneck
-- has switched from E₃ to E₁.
phase-φ1-E₁ : isZer (evalAt 3 1 3 S₁)
phase-φ1-E₁ = refl

phase-φ1-E₃ : isNeg (evalAt 3 1 3 S₃)
phase-φ1-E₃ = 1 , refl

-- SUPPLEMENT (not in the note): the crossover is exactly φ = 2/3,
-- where (1+φ)/5 = 1/3 and E₁, E₃ vanish simultaneously.  q = 3, r = 1, f = 2.
crossover-E₁ : isZer (evalAt 3 1 2 S₁)
crossover-E₁ = refl

crossover-E₃ : isZer (evalAt 3 1 2 S₃)
crossover-E₃ = refl

------------------------------------------------------------------------------
-- 10. Section 9 in the original prime-pair scale D = X^{1/2}.
--
--    The frontier ρ ∈ [1/5, 1/2] in D becomes, in X, the range of exponents
--    ρ/2 ∈ [1/10, 1/4].  Cleared: 2*(1/10) = 1/5 and 2*(1/4) = 1/2.
------------------------------------------------------------------------------

-- ρ = 1/5 in D is X^{1/10}: 10 * 1 = 2 * 5 * 1, i.e. (1/10)*2 = 1/5.
X-lower : 10 · 1 ≡ (2 · 5) · 1
X-lower = refl

-- ρ = 1/2 in D is X^{1/4}: 4 * 1 = 2 * 2 * 1.
X-upper : 4 · 1 ≡ (2 · 2) · 1
X-upper = refl
