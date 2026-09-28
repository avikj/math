{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SubsetSumChartDepth
--
-- The exact chart depth of the labelled subset-sum valuation response.
--
-- `collab/messages/0161-codex-formation-subset-
-- sum-carrier-result.md` (absent from this repository) closes with the hostile question
--
--     "for labeled valuation-only subset responses, is common unit scaling
--      the complete observational equivalence, or do non-proportional
--      residue tuples remain indistinguishable?"
--
-- This module answers it, negatively and with the exact depth.  Write
-- `m` for the largest finite `v_p` of a subset sum of `a`.  Then every `b`
-- congruent to `a` coordinatewise modulo `p^(m+1)` has the *same* response
-- on every subset, and `p^m` is not enough.  So the observational fibre of
-- `a` contains a whole congruence class, which for `n >= 2` contains
-- tuples that are not scalar multiples of `a`.
--
-- Nothing here needs a valuation function.  "`x` has exact depth `k`" is
-- spelled `(p ^ k) ∣ x` together with `¬ (p ^ suc k) ∣ x`, so the whole
-- argument is divisibility in ℤ and the module stays `--safe` with no
-- postulates and no holes.
--
-- Layout:
--   §1  ring-level divisibility helpers (subtraction)
--   §2  `pinDepth`: the abstract engine, no exponentiation
--   §3  powers, and `chartDepth`: the engine at `d = p^k`, `M = p^(m+1)`
--   §4  masked sums: the "every subset" quantifier
--   §5  `subsetChartDepth`: the theorem
--   §6  `depthMIsNotEnough`: `m+1` cannot be lowered to `m`
--   §7  `fibreTransport` / `notProportional`: the fibre is not the
--       scaling orbit — the negative answer to message 0161
------------------------------------------------------------------------

module SubsetSumChartDepth where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; injSuc ; snotz)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-suc ; ≤-antisym ; suc-≤-suc)
open import Cubical.Data.Nat.Divisibility using (m∣n→m≤n)
  renaming (_∣_ to _∣ℕ_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.Int
  using (ℤ ; pos ; negsuc ; abs ; injPos)
open import Cubical.Data.Int.Divisibility
  using (_∣_ ; _∣'_ ; ∣'→∣ ; ∣-+ ; ∣-trans ; ∣-left ; ∣-right ; ∣-refl ; ∣-right· ; ∣-zeroʳ ; ∣→∣ℕ)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

open CommRingStr (ℤCommRing .snd)

private
  R : Type₀
  R = ℤ

------------------------------------------------------------------------
-- §1  Divisibility helpers: negation and difference.
------------------------------------------------------------------------

private
  negIs : (x : R) → (- 1r) · x ≡ - x
  negIs _ = solve! ℤCommRing

∣-neg : {k x : ℤ} → k ∣ x → k ∣ (- x)
∣-neg {k = k} {x = x} h = subst (k ∣_) (negIs x) (∣-right· {n = - 1r} h)

-- the difference of two multiples is a multiple
∣-sub : {k x y : ℤ} → k ∣ x → k ∣ y → k ∣ (x + (- y))
∣-sub hx hy = ∣-+ hx (∣-neg hy)

private
  back : (x y : R) → x + (- (x + (- y))) ≡ y
  back _ _ = solve! ℤCommRing

  forth : (x y : R) → (x + (- y)) + y ≡ x
  forth _ _ = solve! ℤCommRing

------------------------------------------------------------------------
-- §2  The engine.
--
-- `d` marks the depth reached, `D` the depth just past it, `M` the chart
-- modulus.  The two hypotheses `d ∣ M` and `D ∣ M` are exactly "the chart
-- is at least one digit deeper than the depth being measured"; §6 shows
-- that dropping the second one breaks the conclusion.
------------------------------------------------------------------------

pinDepth : (d D M x y : ℤ)
         → d ∣ M
         → D ∣ M
         → M ∣ (x + (- y))
         → d ∣ x
         → ¬ (D ∣ x)
         → (d ∣ y) × (¬ (D ∣ y))
pinDepth d D M x y d∣M D∣M M∣diff d∣x ¬D∣x = d∣y , ¬D∣y
  where
    d∣diff : d ∣ (x + (- y))
    d∣diff = ∣-trans d∣M M∣diff

    d∣y : d ∣ y
    d∣y = subst (d ∣_) (back x y) (∣-sub d∣x d∣diff)

    ¬D∣y : ¬ (D ∣ y)
    ¬D∣y D∣y = ¬D∣x (subst (D ∣_) (forth x y) (∣-+ (∣-trans D∣M M∣diff) D∣y))

------------------------------------------------------------------------
-- §3  Powers of `p`, and the engine at `d = p^k`, `D = p^(k+1)`,
--     `M = p^(m+1)`.
------------------------------------------------------------------------

_^_ : ℤ → ℕ → ℤ
x ^ zero  = 1r
x ^ suc n = x · (x ^ n)

private
  ^-+ : (p : ℤ) (i j : ℕ) → p ^ (i +ℕ j) ≡ (p ^ i) · (p ^ j)
  ^-+ p zero    j = sym (·IdL (p ^ j))
  ^-+ p (suc i) j = cong (p ·_) (^-+ p i j) ∙ ·Assoc p (p ^ i) (p ^ j)

^∣^ : (p : ℤ) {i j : ℕ} → i ≤ j → (p ^ i) ∣ (p ^ j)
^∣^ p {i = i} {j = j} (c , e) =
  subst ((p ^ i) ∣_) (sym (^-+ p c i) ∙ cong (p ^_) e)
        (∣-right {m = p ^ i} {k = p ^ c})

-- `x` and `y` agree modulo `p^(m+1)`; `x` has exact depth `k <= m`.
-- Then `y` has exact depth `k` too.
chartDepth : (p x y : ℤ) (k m : ℕ)
           → k ≤ m
           → (p ^ suc m) ∣ (x + (- y))
           → (p ^ k) ∣ x
           → ¬ ((p ^ suc k) ∣ x)
           → ((p ^ k) ∣ y) × (¬ ((p ^ suc k) ∣ y))
chartDepth p x y k m k≤m =
  pinDepth (p ^ k) (p ^ suc k) (p ^ suc m) x y
           (^∣^ p (≤-suc k≤m))
           (^∣^ p (suc-≤-suc k≤m))

------------------------------------------------------------------------
-- §4  Masked sums.
--
-- A labelled input tuple is compared with a second one coordinatewise, so
-- the data is a `List (ℤ × ℤ)`: one entry per index, carrying `(a_i , b_i)`.
-- A *context* (a subset of the indices) is a `List Bool` mask.
------------------------------------------------------------------------

mask : List Bool → List (ℤ × ℤ) → List (ℤ × ℤ)
mask []           zs             = []
mask (_ ∷ _)      []             = []
mask (true  ∷ bs) (z ∷ zs)       = z ∷ mask bs zs
mask (false ∷ bs) (_ ∷ zs)       = mask bs zs

sumL : List (ℤ × ℤ) → ℤ
sumL []             = 0r
sumL ((x , _) ∷ zs) = x + sumL zs

sumR : List (ℤ × ℤ) → ℤ
sumR []             = 0r
sumR ((_ , y) ∷ zs) = y + sumR zs

-- `M` divides every coordinatewise difference
Cong : ℤ → List (ℤ × ℤ) → Type₀
Cong M []             = Unit
Cong M ((x , y) ∷ zs) = (M ∣ (x + (- y))) × Cong M zs

Cong-mask : (M : ℤ) (bs : List Bool) (zs : List (ℤ × ℤ))
          → Cong M zs → Cong M (mask bs zs)
Cong-mask M []           zs             c = tt
Cong-mask M (_ ∷ _)      []             c = tt
Cong-mask M (true  ∷ bs) ((x , y) ∷ zs) c =
  fst c , Cong-mask M bs zs (snd c)
Cong-mask M (false ∷ bs) (_ ∷ zs)       c = Cong-mask M bs zs (snd c)

private
  regroup : (x y sx sy : R)
          → (x + sx) + (- (y + sy)) ≡ (x + (- y)) + (sx + (- sy))
  regroup _ _ _ _ = solve! ℤCommRing

Cong-sum : (M : ℤ) (zs : List (ℤ × ℤ))
         → Cong M zs → M ∣ (sumL zs + (- sumR zs))
Cong-sum M []             c = subst (M ∣_) (sym (+InvR 0r)) ∣-zeroʳ
Cong-sum M ((x , y) ∷ zs) c =
  subst (M ∣_) (sym (regroup x y (sumL zs) (sumR zs)))
        (∣-+ (fst c) (Cong-sum M zs (snd c)))

------------------------------------------------------------------------
-- §5  The theorem.
------------------------------------------------------------------------

subsetChartDepth :
    (p : ℤ) (m : ℕ) (zs : List (ℤ × ℤ)) (bs : List Bool) (k : ℕ)
  → k ≤ m
  → Cong (p ^ suc m) zs
  → (p ^ k) ∣ sumL (mask bs zs)
  → ¬ ((p ^ suc k) ∣ sumL (mask bs zs))
  → ((p ^ k) ∣ sumR (mask bs zs)) × (¬ ((p ^ suc k) ∣ sumR (mask bs zs)))
subsetChartDepth p m zs bs k k≤m c =
  chartDepth p (sumL (mask bs zs)) (sumR (mask bs zs)) k m k≤m
             (Cong-sum (p ^ suc m) (mask bs zs) (Cong-mask (p ^ suc m) bs zs c))


------------------------------------------------------------------------
-- §6  The chart depth `m+1` cannot be lowered to `m`.
--
-- Take `p = 3`, two inputs, and the full-set context.
--
--     a = (1 , 2)      subset sums 1, 2, 3        max depth m = 1
--     b = (7 , 2)      subset sums 7, 2, 9
--
-- `a` and `b` agree coordinatewise modulo `3^m = 3`, yet the full-set sum
-- has exact depth 1 on the left and depth at least 2 on the right.  So the
-- chart modulus `p^(suc m)` in `subsetChartDepth` is sharp: `p^m` does not
-- suffice, and the "+1" is not slack.
------------------------------------------------------------------------

private
  zsSharp : List (ℤ × ℤ)
  zsSharp = (pos 1 , pos 7) ∷ (pos 2 , pos 2) ∷ []

  bsFull : List Bool
  bsFull = true ∷ true ∷ []

  -- both coordinates agree modulo 3 = 3^m
  congModP^m : Cong (pos 3 ^ 1) zsSharp
  congModP^m = ∣'→∣ (pos 3) (negsuc 5) (negsuc 1 , refl)
             , ∣'→∣ (pos 3) (pos 0) (pos 0 , refl)
             , tt

  9≤3→⊥ : 9 ≤ 3 → ⊥
  9≤3→⊥ h = snotz (injSuc (injSuc (injSuc (≤-antisym h (6 , refl)))))

  ¬9∣3 : ¬ (pos 9 ∣ pos 3)
  ¬9∣3 d = 9≤3→⊥ (m∣n→m≤n snotz (∣→∣ℕ d))

-- the left tuple's full-set sum is 3 (exact depth 1); the right one's is 9
sharpLeft : sumL (mask bsFull zsSharp) ≡ pos 3
sharpLeft = refl

sharpRight : sumR (mask bsFull zsSharp) ≡ pos 9
sharpRight = refl

depthMIsNotEnough :
    ((pos 3 ^ 1) ∣ sumL (mask bsFull zsSharp))
  × (¬ ((pos 3 ^ 2) ∣ sumL (mask bsFull zsSharp)))
  × ((pos 3 ^ 2) ∣ sumR (mask bsFull zsSharp))
depthMIsNotEnough = ∣'→∣ (pos 3) (pos 3) (pos 1 , refl)
                  , ¬9∣3
                  , ∣'→∣ (pos 9) (pos 9) (pos 1 , refl)

------------------------------------------------------------------------
-- §7  The observational fibre is not the scaling orbit.
--
-- `a = (1 , 2)` and `b = (10 , 2)` agree coordinatewise modulo
-- `3^2 = p^(m+1)`, so by §5 they carry the *same* exact depth on every
-- subset context at every depth `k ≤ m = 1`; but `b` is not a scalar
-- multiple of `a`.  This is the negative answer to the hostile question of
-- `collab/messages/0161-codex-formation-subset-sum-carrier-result.md` (absent from this repository).
------------------------------------------------------------------------

private
  zsFibre : List (ℤ × ℤ)
  zsFibre = (pos 1 , pos 10) ∷ (pos 2 , pos 2) ∷ []

congModP^sm : Cong (pos 3 ^ 2) zsFibre
congModP^sm = ∣'→∣ (pos 9) (negsuc 8) (negsuc 0 , refl)
            , ∣'→∣ (pos 9) (pos 0) (pos 0 , refl)
            , tt

fibreTransport :
    (bs : List Bool) (k : ℕ) → k ≤ 1
  → (pos 3 ^ k) ∣ sumL (mask bs zsFibre)
  → ¬ ((pos 3 ^ suc k) ∣ sumL (mask bs zsFibre))
  → ((pos 3 ^ k) ∣ sumR (mask bs zsFibre))
  × (¬ ((pos 3 ^ suc k) ∣ sumR (mask bs zsFibre)))
fibreTransport bs k k≤1 =
  subsetChartDepth (pos 3) 1 zsFibre bs k k≤1 congModP^sm

notProportional : ¬ (Σ[ c ∈ ℤ ] ((c · pos 1 ≡ pos 10) × (c · pos 2 ≡ pos 2)))
notProportional (c , h1 , h2) =
  snotz (injSuc (injSuc (injPos (sym (cong (_· pos 2) (sym (·IdR c) ∙ h1)) ∙ h2))))
