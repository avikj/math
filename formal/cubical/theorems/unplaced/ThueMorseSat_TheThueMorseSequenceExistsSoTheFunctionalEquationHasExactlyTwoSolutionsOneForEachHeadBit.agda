{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ThueMorseSat_TheThueMorseSequenceExistsSoTheFunctionalEquationHasExactlyTwoSolutionsOneForEachHeadBit
--
-- The EXISTENCE half left open by OffDiagonalThueMorseUnique.  That file's
-- header says, verbatim:
--
--     existence of a solution for each ε₀ (the classical Thue–Morse
--     sequence, cf-prouhet's explicit p = ∏ₖ(1 − x^{2ᵏ})): its formal
--     function-definition is a separable WF-recursion landing and is
--     NOT claimed here.
--
-- and notes/OFFDIAGONAL_NO_GO_UNIQUENESS.md (absent from this repository) (branch main) records:
--
--     Existence (the Thue–Morse function itself) left open.
--
-- This module closes that gap, and then combines it with the imported
-- `uniqueGivenHead` to get the full "exactly two solutions" statement.
--
-- WHAT IS PROVED.
--   * `tm : ℕ → Bool`, the Thue–Morse sequence, defined WITHOUT
--     well-founded recursion: `tm n = tmFuel n n`, where `tmFuel k n` is
--     a structural recursion on the fuel `k` computing the parity of the
--     number of 1s in the binary expansion of `n` (folding `isOdd n` into
--     the accumulator and passing to `half n`).  Fuel `n` suffices.
--   * `tmFuel-stable`, `tmFuel-tm`: fuel-independence — for `n ≤ k`,
--     `tmFuel k n ≡ tm n`.
--   * `tm-sat : Sat tm`, i.e. `tm (2·m) ≡ tm m` and
--     `tm (suc (2·m)) ≡ not (tm m)` for every `m`.
--   * `tm' = not ∘ tm` and `tm'-sat : Sat tm'`: the second solution.
--   * `isPropSat`: `Sat ε` is a proposition (Bool is a set).
--   * `solutions≃Bool : solutions ≃ Bool` where
--     `solutions = Σ[ ε ∈ (ℕ → Bool) ] Sat ε`, the map being `ε ↦ ε 0`.
--     Its inverse sends `true ↦ tm`, `false ↦ tm'`; the round-trip on
--     `solutions` is `uniqueGivenHead` packaged with `funExt` and
--     `Σ≡Prop isPropSat`.  So the functional equation has EXACTLY two
--     solutions, one for each head bit ε₀.
--   * `tm-0` … `tm-15` by `refl`: the prefix 0110 1001 1001 0110.
--
-- CONVENTION (matching OffDiagonalThueMorseUnique: +1 ↦ true, −1 ↦ false,
-- negation ↦ not).  Thue–Morse digit t_n = (number of 1s in binary n) mod 2,
-- and ε_n = (−1)^{t_n}.  So t_n = 0 ↦ ε_n = +1 ↦ true, and t_n = 1 ↦ −1 ↦
-- false.  Hence tm 0 = true (ε₀ = +1), tm 1 = false, tm 2 = false,
-- tm 3 = true, …  `tm'` is the ε₀ = −1 solution.
--
-- WHAT IS NOT PROVED.  Nothing about the generating function
-- ∏ₖ(1 − x^{2ᵏ}) or the identity p = (1 − x) p(x²); nothing about the
-- off-diagonal no-go itself (the forget-the-diagonal fibre); only the
-- coefficient-wise recursion `Sat` is addressed.
------------------------------------------------------------------------

module ThueMorseSat_TheThueMorseSequenceExistsSoTheFunctionalEquationHasExactlyTwoSolutionsOneForEachHeadBit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.IsEven
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (¬_)

open import OffDiagonalThueMorseUnique using (Sat; uniqueGivenHead; m≤2m)

------------------------------------------------------------------------
-- Halving, structurally.
------------------------------------------------------------------------

half : ℕ → ℕ
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

half≤ : (n : ℕ) → half n ≤ n
half≤ zero          = ≤-refl
half≤ (suc zero)    = zero-≤
half≤ (suc (suc n)) = suc-≤-suc (≤-suc (half≤ n))

-- half (suc n) ≤ n : the half of a positive number is strictly smaller.
half-suc≤ : (n : ℕ) → half (suc n) ≤ n
half-suc≤ zero    = ≤-refl
half-suc≤ (suc n) = suc-≤-suc (half≤ n)

-- n ≤ suc k → half n ≤ k.
half≤pred : (n k : ℕ) → n ≤ suc k → half n ≤ k
half≤pred zero    k _ = zero-≤
half≤pred (suc n) k p = ≤-trans (half-suc≤ n) (pred-≤-pred p)

-- doubleℕ agrees with 2 · _.
double≡ : (m : ℕ) → doubleℕ m ≡ 2 · m
double≡ zero    = refl
double≡ (suc m) = cong suc (cong suc (double≡ m) ∙ sym (+-suc m (m + 0)))

half-doubleℕ : (m : ℕ) → half (doubleℕ m) ≡ m
half-doubleℕ zero    = refl
half-doubleℕ (suc m) = cong suc (half-doubleℕ m)

half-suc-doubleℕ : (m : ℕ) → half (suc (doubleℕ m)) ≡ m
half-suc-doubleℕ zero    = refl
half-suc-doubleℕ (suc m) = cong suc (half-suc-doubleℕ m)

half-double : (m : ℕ) → half (2 · m) ≡ m
half-double m = cong half (sym (double≡ m)) ∙ half-doubleℕ m

half-suc-double : (m : ℕ) → half (suc (2 · m)) ≡ m
half-suc-double m = cong (half ∘ suc) (sym (double≡ m)) ∙ half-suc-doubleℕ m

isOdd-double : (m : ℕ) → isOdd (2 · m) ≡ false
isOdd-double m = ¬IsEvenTrue (2 · m) (trueIsEven (2 · m) (m , refl))

isOdd-suc-double : (m : ℕ) → isOdd (suc (2 · m)) ≡ true
isOdd-suc-double m = trueIsEven (2 · m) (m , refl)

------------------------------------------------------------------------
-- The Thue–Morse sequence by fuel-bounded structural recursion.
--
--   tmFuel k n = ⊕ of the low k binary digits of n, starting from true.
--   tm n       = tmFuel n n   (n digits is always enough: n < 2ⁿ).
------------------------------------------------------------------------

tmFuel : ℕ → ℕ → Bool
tmFuel zero    n = true
tmFuel (suc k) n = isOdd n ⊕ tmFuel k (half n)

tm : ℕ → Bool
tm n = tmFuel n n

------------------------------------------------------------------------
-- Fuel-independence: once n ≤ k, one more unit of fuel changes nothing.
------------------------------------------------------------------------

tmFuel-stable : (k n : ℕ) → n ≤ k → tmFuel (suc k) n ≡ tmFuel k n
tmFuel-stable zero    zero    _ = refl
tmFuel-stable zero    (suc n) p = ⊥.rec (¬-<-zero p)
tmFuel-stable (suc k) n       p =
  cong (isOdd n ⊕_) (tmFuel-stable k (half n) (half≤pred n k p))

tmFuel-up : (d n : ℕ) → tmFuel (d + n) n ≡ tm n
tmFuel-up zero    n = refl
tmFuel-up (suc d) n = tmFuel-stable (d + n) n (d , refl) ∙ tmFuel-up d n

-- The exported fuel-independence lemma.
tmFuel-tm : (k n : ℕ) → n ≤ k → tmFuel k n ≡ tm n
tmFuel-tm k n (d , p) = cong (λ j → tmFuel j n) (sym p) ∙ tmFuel-up d n

------------------------------------------------------------------------
-- (2) tm satisfies the functional equation.
------------------------------------------------------------------------

tm-even : (m : ℕ) → tm (2 · m) ≡ tm m
tm-even m =
    sym (tmFuel-stable (2 · m) (2 · m) ≤-refl)
      -- tm (2·m) ≡ tmFuel (suc (2·m)) (2·m) = isOdd (2·m) ⊕ tmFuel (2·m) (half (2·m))
  ∙ cong₂ _⊕_ (isOdd-double m) (cong (tmFuel (2 · m)) (half-double m))
      -- ≡ false ⊕ tmFuel (2·m) m = tmFuel (2·m) m
  ∙ tmFuel-tm (2 · m) m (m≤2m m)

tm-odd : (m : ℕ) → tm (suc (2 · m)) ≡ not (tm m)
tm-odd m =
    -- tm (suc (2·m)) = isOdd (suc (2·m)) ⊕ tmFuel (2·m) (half (suc (2·m)))  definitionally
    cong₂ _⊕_ (isOdd-suc-double m) (cong (tmFuel (2 · m)) (half-suc-double m))
      -- ≡ true ⊕ tmFuel (2·m) m = not (tmFuel (2·m) m)
  ∙ cong not (tmFuel-tm (2 · m) m (m≤2m m))

tm-sat : Sat tm
tm-sat = tm-even , tm-odd

------------------------------------------------------------------------
-- (3) The second solution: the negated sequence.
------------------------------------------------------------------------

tm' : ℕ → Bool
tm' = not ∘ tm

tm'-sat : Sat tm'
tm'-sat = (λ m → cong not (tm-even m))
        , (λ m → cong not (tm-odd m))

------------------------------------------------------------------------
-- (4) Exactly two solutions: solutions ≃ Bool via ε ↦ ε 0.
------------------------------------------------------------------------

isPropSat : (ε : ℕ → Bool) → isProp (Sat ε)
isPropSat ε = isProp× (isPropΠ λ _ → isSetBool _ _) (isPropΠ λ _ → isSetBool _ _)

solutions : Type
solutions = Σ[ ε ∈ (ℕ → Bool) ] Sat ε

headBit : solutions → Bool
headBit (ε , _) = ε 0

fromBit : Bool → solutions
fromBit true  = tm  , tm-sat
fromBit false = tm' , tm'-sat

headBit-fromBit : (b : Bool) → headBit (fromBit b) ≡ b
headBit-fromBit true  = refl
headBit-fromBit false = refl

fromBit-headBit : (s : solutions) → fromBit (headBit s) ≡ s
fromBit-headBit (ε , sε) with dichotomyBool (ε 0)
... | inl p = cong fromBit p
            ∙ Σ≡Prop isPropSat (funExt (uniqueGivenHead tm ε tm-sat sε (sym p)))
... | inr p = cong fromBit p
            ∙ Σ≡Prop isPropSat (funExt (uniqueGivenHead tm' ε tm'-sat sε (sym p)))

solutionsIso : Iso solutions Bool
Iso.fun      solutionsIso = headBit
Iso.inv      solutionsIso = fromBit
Iso.rightInv solutionsIso = headBit-fromBit
Iso.leftInv  solutionsIso = fromBit-headBit

solutions≃Bool : solutions ≃ Bool
solutions≃Bool = isoToEquiv solutionsIso

-- Restated: every solution is tm or tm', according to its head bit.
solutionIsTMorTM' : (ε : ℕ → Bool) → Sat ε → (ε ≡ tm) ⊎ (ε ≡ tm')
solutionIsTMorTM' ε sε with dichotomyBool (ε 0)
... | inl p = inl (funExt (uniqueGivenHead ε tm  sε tm-sat  p))
... | inr p = inr (funExt (uniqueGivenHead ε tm' sε tm'-sat p))

tm≢tm' : ¬ (tm ≡ tm')
tm≢tm' q = true≢false (funExt⁻ q 0)

------------------------------------------------------------------------
-- (5) The prefix 0110 1001 1001 0110, with 0 ↦ true (+1), 1 ↦ false (−1).
------------------------------------------------------------------------

tm-0  : tm 0  ≡ true
tm-0  = refl
tm-1  : tm 1  ≡ false
tm-1  = refl
tm-2  : tm 2  ≡ false
tm-2  = refl
tm-3  : tm 3  ≡ true
tm-3  = refl
tm-4  : tm 4  ≡ false
tm-4  = refl
tm-5  : tm 5  ≡ true
tm-5  = refl
tm-6  : tm 6  ≡ true
tm-6  = refl
tm-7  : tm 7  ≡ false
tm-7  = refl
tm-8  : tm 8  ≡ false
tm-8  = refl
tm-9  : tm 9  ≡ true
tm-9  = refl
tm-10 : tm 10 ≡ true
tm-10 = refl
tm-11 : tm 11 ≡ false
tm-11 = refl
tm-12 : tm 12 ≡ true
tm-12 = refl
tm-13 : tm 13 ≡ false
tm-13 = refl
tm-14 : tm 14 ≡ false
tm-14 = refl
tm-15 : tm 15 ≡ true
tm-15 = refl
