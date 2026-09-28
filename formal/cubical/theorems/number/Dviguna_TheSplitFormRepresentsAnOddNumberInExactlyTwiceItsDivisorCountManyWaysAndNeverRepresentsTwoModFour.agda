{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Dviguna (द्विगुण, "twice over")
--
-- The split form  W² − R²  represents an odd number in exactly twice
-- its divisor-count many ways, and never represents a number that is
-- 2 (mod 4).
--
-- SOURCE.  notes/FLEET_BREAKER_PASS_2026_08_14.md (absent from this repository), §1.3, verbatim:
--
--   - **Representation count:** `r(N) = 2d(N)` for odd `N`, `0` for `N ≡ 2 (mod 4)`,
--     `2d(N/4)` for `4|N`; hence
--     `Σ r(N)N^{-s} = 2ζ(s)²[1 − 2·2^{-s} + 2·4^{-s}]`. **The split form produces
--     `ζ(s)²` — the divisor problem — and no Dirichlet L-function**, where a
--     nonsquare fundamental discriminant would give `ζ(s)L(s,χ_D)`.
--
-- and the successor seed of the same note (§"seeds"), verbatim:
--
--   2. `PROVE`: `r(N) = 2d(N)` in Agda. It is the first statement in the split-form
--      branch with genuine arithmetic content, and it gives `CenterRelative.agda` a
--      control no current theorem there has: one that *distinguishes* `N ≡ 2 (mod 4)`.
--
-- WHAT IS PROVED (all over ℤ = Cubical.Data.Int for the representations
-- and factor pairs, ℕ for the divisors; every equivalence is an explicit
-- Iso with both round trips checked):
--
--   Rep N      = Σ (W , R) ∈ ℤ × ℤ .  W·W − R·R ≡ N
--   Pairs N    = Σ (a , b) ∈ ℤ × ℤ .  (a·b ≡ N) × SameParity a b
--   AllPairs N = Σ (a , b) ∈ ℤ × ℤ .  a·b ≡ N
--   SameParity a b = Σ k ∈ ℤ . a + b ≡ 2·k        (a proposition)
--   Div n      = Σ d ∈ ℕ . (0 < d) × (d ∣ n)       (positive divisors of n)
--
--   T1  rep≃pairs        : Rep N ≃ Pairs N                       (all N : ℤ)
--         (W,R) ↦ (W−R , W+R),  inverse (a,b) ↦ (k , k − a) with a+b = 2k.
--   T2  pairs≃allPairs-odd : Odd N → Pairs N ≃ AllPairs N
--         (for odd N both factors of any factor pair are odd, so the
--          parity side condition is automatic).
--   T3  noRepTwoModFour  : (k : ℤ) → ¬ Rep (2 + 4·k)
--         (a factor pair of the same parity is both-even or both-odd;
--          both-odd makes an odd product, both-even a multiple of 4).
--   T4  allPairs≃boolDiv : AllPairs (pos (suc m)) ≃ Bool × Div (suc m)
--         (the sign of a and |a|; b is forced).
--   T5  oddRepCount      : (k : ℕ) → Rep (pos (suc (2·k))) ≃ Bool × Div (suc (2·k))
--       oddRepCount-isOdd : isOdd n ≡ true → Rep (pos n) ≃ Bool × Div n
--         This IS the statement "r(N) = 2 d(N)": the corpus has no
--         computed cardinality for Div n, so the count is stated as the
--         equivalence with Bool × Div n rather than as a numeral.
--   T6  fourRep≃allPairs : (M : ℤ) → Rep (4·M) ≃ AllPairs M
--         ("2d(N/4) for 4 | N": with T4 the count for 4·pos(suc m) is
--          again Bool × Div (suc m)); the composite fourRepCount is stated.
--
--   Instances: the eight representations of 15 — (±4,±1), (±8,±7) — are
--   exhibited and their images under rep15 : Rep 15 ≃ Bool × Div 15 are
--   computed (sign , divisor) = (true,3),(true,5),(false,5),(false,3),
--   (true,1),(true,15),(false,15),(false,1) by refl; the inverse sends
--   (true,3,·,∣5·3≡15∣) back to (4,1) by refl.  noRep6 : ¬ Rep 6.
--
-- WHAT IS NOT PROVED.  Nothing about the Dirichlet series identity
-- Σ r(N) N^{-s} = 2ζ(s)²[…], nothing about class groups, discriminants,
-- automorphs or Gauss composition; d(N) is not computed as a number
-- (no Div n ≃ Fin (d n) here).  The N = 2 (mod 4) case is a negation,
-- the 4 | N case is the reduction to AllPairs (N/4) only.
--
-- Ring identities are discharged by the CommRingSolver on an abstract
-- commutative ring and instantiated at ℤCommRing; everything else is
-- explicit.  Nothing is assumed, there are no holes, and no termination
-- pragma is used.
------------------------------------------------------------------------

module Dviguna_TheSplitFormRepresentsAnOddNumberInExactlyTwiceItsDivisorCountManyWaysAndNeverRepresentsTwoModFour where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; ≡-× ; Σ≡Prop)
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false ; dichotomyBool)
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc ; znots ; snotz ; ·-comm)
open import Cubical.Data.Nat.Order using (_<_ ; isProp≤ ; suc-≤-suc ; zero-≤ ; ¬-<-zero)
open import Cubical.Data.Nat.Divisibility using (_∣_ ; isProp∣ ; ∣≃∣')
import Cubical.Data.Nat.IsEven as ℕeven
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver.Reflection using (solve!)

------------------------------------------------------------------------
-- 0.  Ring identities, proved once on an abstract commutative ring and
--     instantiated at ℤ.  (The solver cannot read ℤ numerals directly,
--     so 2 and 4 are written 1r + 1r and (1r + 1r)·(1r + 1r); at ℤ these
--     compute to pos 2 and pos 4.)
------------------------------------------------------------------------

private
  module Alg (R : CommRing ℓ-zero) where
    open CommRingStr (snd R)

    two four : ⟨ R ⟩
    two  = 1r + 1r
    four = two · two

    splitProduct : (w r : ⟨ R ⟩) → (w - r) · (w + r) ≡ w · w - r · r
    splitProduct _ _ = solve! R

    splitSum : (w r : ⟨ R ⟩) → (w - r) + (w + r) ≡ two · w
    splitSum _ _ = solve! R

    halfSquare : (a k : ⟨ R ⟩) → k · k - (k - a) · (k - a) ≡ a · (two · k - a)
    halfSquare _ _ = solve! R

    recoverB : (a b : ⟨ R ⟩) → (a + b) - a ≡ b
    recoverB _ _ = solve! R

    recoverA : (k a : ⟨ R ⟩) → k - (k - a) ≡ a
    recoverA _ _ = solve! R

    recoverSum : (k a : ⟨ R ⟩) → k + (k - a) ≡ two · k - a
    recoverSum _ _ = solve! R

    recoverR : (w r : ⟨ R ⟩) → w - (w - r) ≡ r
    recoverR _ _ = solve! R

    evenTimes : (m b : ⟨ R ⟩) → (two · m) · b ≡ two · (m · b)
    evenTimes _ _ = solve! R

    oddTimesOdd : (m n : ⟨ R ⟩)
      → (1r + two · m) · (1r + two · n) ≡ 1r + two · (m + n + two · (m · n))
    oddTimesOdd _ _ = solve! R

    oddPlusOdd : (m n : ⟨ R ⟩) → (1r + two · m) + (1r + two · n) ≡ two · (1r + (m + n))
    oddPlusOdd _ _ = solve! R

    bFromSum : (a b : ⟨ R ⟩) → b ≡ (a + b) - a
    bFromSum _ _ = solve! R

    evenHalf : (k m : ⟨ R ⟩) → two · k - two · m ≡ two · (k - m)
    evenHalf _ _ = solve! R

    oddHalf : (k m : ⟨ R ⟩) → two · k - (1r + two · m) ≡ 1r + two · (k - m - 1r)
    oddHalf _ _ = solve! R

    fourProduct : (m n : ⟨ R ⟩) → (two · m) · (two · n) ≡ two · (two · (m · n))
    fourProduct _ _ = solve! R

    twoModFourEven : (k : ⟨ R ⟩) → two + four · k ≡ two · (1r + two · k)
    twoModFourEven _ = solve! R

    doubleProduct : (a b : ⟨ R ⟩) → (two · a) · (two · b) ≡ four · (a · b)
    doubleProduct _ _ = solve! R

    doubleSum : (a b : ⟨ R ⟩) → two · a + two · b ≡ two · (a + b)
    doubleSum _ _ = solve! R

    fourEven : (M : ⟨ R ⟩) → four · M ≡ two · (two · M)
    fourEven _ = solve! R

  open Alg ℤCommRing public

-- ℤ itself is opened only now, so that the abstract ring block above
-- sees a single _+_ / _·_ / -_.
open import Cubical.Data.Int
open import Cubical.Data.Int.IsEven using (isEvenTrue ; isEvenFalse ; trueIsEven ; falseIsEven ; 1+2kPos)

------------------------------------------------------------------------
-- 1.  The three types.
------------------------------------------------------------------------

Rep : ℤ → Type₀
Rep N = Σ[ p ∈ ℤ × ℤ ] (fst p · fst p - snd p · snd p ≡ N)

SameParity : ℤ → ℤ → Type₀
SameParity a b = Σ[ k ∈ ℤ ] (a + b ≡ 2 · k)

Pairs : ℤ → Type₀
Pairs N = Σ[ p ∈ ℤ × ℤ ] ((fst p · snd p ≡ N) × SameParity (fst p) (snd p))

AllPairs : ℤ → Type₀
AllPairs N = Σ[ p ∈ ℤ × ℤ ] (fst p · snd p ≡ N)

2≢0 : ¬ (2 ≡ pos 0)
2≢0 p = snotz (injPos p)

4≢0 : ¬ (4 ≡ pos 0)
4≢0 p = snotz (injPos p)

isPropSameParity : (a b : ℤ) → isProp (SameParity a b)
isPropSameParity a b (k , hk) (k' , hk') =
  Σ≡Prop (λ _ → isSetℤ _ _) (·lCancel 2 k k' (sym hk ∙ hk') 2≢0)

isPropPairsFiber : (N : ℤ) (p : ℤ × ℤ)
  → isProp ((fst p · snd p ≡ N) × SameParity (fst p) (snd p))
isPropPairsFiber N p = isProp× (isSetℤ _ _) (isPropSameParity (fst p) (snd p))

------------------------------------------------------------------------
-- 2.  T1: Rep N ≃ Pairs N.
------------------------------------------------------------------------

twoK-a : (a b k : ℤ) → a + b ≡ 2 · k → 2 · k - a ≡ b
twoK-a a b k hk = cong (_- a) (sym hk) ∙ recoverB a b

toPairs : (N : ℤ) → Rep N → Pairs N
toPairs N ((w , r) , e) = (w - r , w + r) , (splitProduct w r ∙ e) , (w , splitSum w r)

fromPairs : (N : ℤ) → Pairs N → Rep N
fromPairs N ((a , b) , e , (k , hk)) =
  (k , k - a) , (halfSquare a k ∙ cong (a ·_) (twoK-a a b k hk) ∙ e)

pairsRound : (N : ℤ) (x : Pairs N) → toPairs N (fromPairs N x) ≡ x
pairsRound N ((a , b) , e , (k , hk)) =
  Σ≡Prop (isPropPairsFiber N) (≡-× (recoverA k a) (recoverSum k a ∙ twoK-a a b k hk))

repRound : (N : ℤ) (x : Rep N) → fromPairs N (toPairs N x) ≡ x
repRound N ((w , r) , e) = Σ≡Prop (λ _ → isSetℤ _ _) (≡-× refl (recoverR w r))

Rep≅Pairs : (N : ℤ) → Iso (Rep N) (Pairs N)
Iso.fun      (Rep≅Pairs N) = toPairs N
Iso.inv      (Rep≅Pairs N) = fromPairs N
Iso.rightInv (Rep≅Pairs N) = pairsRound N
Iso.leftInv  (Rep≅Pairs N) = repRound N

rep≃pairs : (N : ℤ) → Rep N ≃ Pairs N
rep≃pairs N = isoToEquiv (Rep≅Pairs N)

------------------------------------------------------------------------
-- 3.  Parity over ℤ, explicit.
------------------------------------------------------------------------

Even Odd : ℤ → Type₀
Even a = Σ[ m ∈ ℤ ] a ≡ 2 · m
Odd  a = Σ[ m ∈ ℤ ] a ≡ 1 + 2 · m

evenOrOdd : (a : ℤ) → Even a ⊎ Odd a
evenOrOdd a = Sum.rec (λ t → inl (isEvenTrue a t)) (λ f → inr (isEvenFalse a f))
                      (dichotomyBool (isEven a))

¬EvenOdd : (a : ℤ) → Even a → Odd a → ⊥
¬EvenOdd a ev od = true≢false (sym (trueIsEven a ev) ∙ falseIsEven a od)

evenFactor : (a b : ℤ) → Even a → Even (a · b)
evenFactor a b (m , hm) = m · b , cong (_· b) hm ∙ evenTimes m b

oddProduct : (a b : ℤ) → Odd a → Odd b → Odd (a · b)
oddProduct a b (m , hm) (n , hn) = m + n + 2 · (m · n) , cong₂ _·_ hm hn ∙ oddTimesOdd m n

oddLeft : (a b : ℤ) → Odd (a · b) → Odd a
oddLeft a b od =
  Sum.rec (λ ev → ⊥.rec (¬EvenOdd (a · b) (evenFactor a b ev) od)) (λ o → o) (evenOrOdd a)

oddRight : (a b : ℤ) → Odd (a · b) → Odd b
oddRight a b od = oddLeft b a (subst Odd (·Comm a b) od)

oddSameParity : (a b : ℤ) → Odd (a · b) → SameParity a b
oddSameParity a b od = 1 + (m + n) , cong₂ _+_ hm hn ∙ oddPlusOdd m n
  where
  m = fst (oddLeft a b od)
  hm = snd (oddLeft a b od)
  n = fst (oddRight a b od)
  hn = snd (oddRight a b od)

-- A same-parity pair is both even or both odd.
bothEvenOrBothOdd : (a b : ℤ) → SameParity a b → (Even a × Even b) ⊎ (Odd a × Odd b)
bothEvenOrBothOdd a b (k , hk) = Sum.rec
  (λ (m , hm) → inl ((m , hm) , (k - m , bFromSum a b ∙ cong₂ _-_ hk hm ∙ evenHalf k m)))
  (λ (m , hm) → inr ((m , hm) , (k - m - 1 , bFromSum a b ∙ cong₂ _-_ hk hm ∙ oddHalf k m)))
  (evenOrOdd a)

------------------------------------------------------------------------
-- 4.  T2: for odd N the parity side condition is automatic.
------------------------------------------------------------------------

Pairs≅AllPairs-odd : (N : ℤ) → Odd N → Iso (Pairs N) (AllPairs N)
Iso.fun      (Pairs≅AllPairs-odd N odN) ((a , b) , e , sp) = (a , b) , e
Iso.inv      (Pairs≅AllPairs-odd N odN) ((a , b) , e) =
  (a , b) , e , oddSameParity a b (subst Odd (sym e) odN)
Iso.rightInv (Pairs≅AllPairs-odd N odN) _ = refl
Iso.leftInv  (Pairs≅AllPairs-odd N odN) x = Σ≡Prop (isPropPairsFiber N) refl

pairs≃allPairs-odd : (N : ℤ) → Odd N → Pairs N ≃ AllPairs N
pairs≃allPairs-odd N odN = isoToEquiv (Pairs≅AllPairs-odd N odN)

------------------------------------------------------------------------
-- 5.  T3: no representation of 2 + 4k.
------------------------------------------------------------------------

noRepTwoModFour : (k : ℤ) → ¬ Rep (2 + 4 · k)
noRepTwoModFour k rep = Sum.rec evenCase oddCase (bothEvenOrBothOdd a b sp)
  where
  a = fst (fst (toPairs (2 + 4 · k) rep))
  b = snd (fst (toPairs (2 + 4 · k) rep))
  e : a · b ≡ 2 + 4 · k
  e = fst (snd (toPairs (2 + 4 · k) rep))
  sp : SameParity a b
  sp = snd (snd (toPairs (2 + 4 · k) rep))

  oddCase : Odd a × Odd b → ⊥
  oddCase (oa , ob) = ¬EvenOdd (a · b) (1 + 2 · k , e ∙ twoModFourEven k) (oddProduct a b oa ob)

  evenCase : Even a × Even b → ⊥
  evenCase ((m , hm) , (n , hn)) = ¬EvenOdd (2 · (m · n)) (m · n , refl) (k , cancelled)
    where
    doubled : 2 · (2 · (m · n)) ≡ 2 · (1 + 2 · k)
    doubled = sym (fourProduct m n) ∙ sym (cong₂ _·_ hm hn) ∙ e ∙ twoModFourEven k
    cancelled : 2 · (m · n) ≡ 1 + 2 · k
    cancelled = ·lCancel 2 (2 · (m · n)) (1 + 2 · k) doubled 2≢0

noRep6 : ¬ Rep 6
noRep6 = noRepTwoModFour 1

------------------------------------------------------------------------
-- 6.  T4: counting the factor pairs of a positive integer.
------------------------------------------------------------------------

Div : ℕ → Type₀
Div n = Σ[ d ∈ ℕ ] ((0 < d) × (d ∣ n))

isPropDivFiber : (n d : ℕ) → isProp ((0 < d) × (d ∣ n))
isPropDivFiber n d = isProp× isProp≤ isProp∣

-- A positive divisor's witness can be extracted from the truncation.
untrunc : (d n : ℕ) → suc d ∣ n → Σ[ c ∈ ℕ ] c ℕ.· suc d ≡ n
untrunc d n = equivFun (∣≃∣' {m = suc d} {n = n})

signed : Bool → ℕ → ℤ           -- the nonzero integer with sign s and |·| = suc d
signed true  d = pos (suc d)
signed false d = negsuc d

cofactor : Bool → ℕ → ℤ
cofactor true  c = pos c
cofactor false c = - pos c

neg≢possuc : (k m : ℕ) → ¬ neg k ≡ pos (suc m)
neg≢possuc zero    m p = znots (injPos p)
neg≢possuc (suc k) m p = negsucNotpos k (suc m) p

posNegsuc≡neg : (d c : ℕ) → pos (suc d) · negsuc c ≡ neg (suc d ℕ.· suc c)
posNegsuc≡neg d c = pos·negsuc (suc d) c ∙ cong -_ (sym (pos·pos (suc d) (suc c))) ∙ -pos _

negsucPos≡neg : (d c : ℕ) → negsuc d · pos c ≡ neg (suc d ℕ.· c)
negsucPos≡neg d c = negsuc·pos d c ∙ cong -_ (sym (pos·pos (suc d) c)) ∙ -pos _

divWitness : (m : ℕ) (a b : ℤ) → a · b ≡ pos (suc m) → abs b ℕ.· abs a ≡ suc m
divWitness m a b e = ·-comm (abs b) (abs a) ∙ sym (abs· a b) ∙ cong abs e

toDiv : (m : ℕ) → AllPairs (pos (suc m)) → Bool × Div (suc m)
toDiv m ((pos zero , b) , e) = ⊥.rec (znots (injPos e))
toDiv m ((pos (suc d) , b) , e) =
  true , suc d , suc-≤-suc zero-≤ , ∣ abs b , divWitness m (pos (suc d)) b e ∣₁
toDiv m ((negsuc d , b) , e) =
  false , suc d , suc-≤-suc zero-≤ , ∣ abs b , divWitness m (negsuc d) b e ∣₁

fromDiv : (m : ℕ) → Bool × Div (suc m) → AllPairs (pos (suc m))
fromDiv m (s , zero , p , q) = ⊥.rec (¬-<-zero p)
fromDiv m (s , suc d , p , q) = (signed s d , cofactor s c) , prodEq s
  where
  c = fst (untrunc d (suc m) q)
  hc : c ℕ.· suc d ≡ suc m
  hc = snd (untrunc d (suc m) q)
  prodEq : (s : Bool) → signed s d · cofactor s c ≡ pos (suc m)
  prodEq true  = sym (pos·pos (suc d) c) ∙ cong pos (·-comm (suc d) c ∙ hc)
  prodEq false = sym (-DistLR· (pos (suc d)) (pos c)) ∙ prodEq true

fromToDiv : (m : ℕ) (x : AllPairs (pos (suc m))) → fromDiv m (toDiv m x) ≡ x
fromToDiv m ((pos zero , b) , e) = ⊥.rec (znots (injPos e))
fromToDiv m ((pos (suc d) , pos c) , e) = Σ≡Prop (λ _ → isSetℤ _ _) refl
fromToDiv m ((pos (suc d) , negsuc c) , e) =
  ⊥.rec (neg≢possuc _ m (sym (posNegsuc≡neg d c) ∙ e))
fromToDiv m ((negsuc d , pos c) , e) =
  ⊥.rec (neg≢possuc _ m (sym (negsucPos≡neg d c) ∙ e))
fromToDiv m ((negsuc d , negsuc c) , e) = Σ≡Prop (λ _ → isSetℤ _ _) refl

toFromDiv : (m : ℕ) (y : Bool × Div (suc m)) → toDiv m (fromDiv m y) ≡ y
toFromDiv m (s , zero , p , q) = ⊥.rec (¬-<-zero p)
toFromDiv m (true , suc d , p , q) = ≡-× refl (Σ≡Prop (isPropDivFiber (suc m)) refl)
toFromDiv m (false , suc d , p , q) = ≡-× refl (Σ≡Prop (isPropDivFiber (suc m)) refl)

AllPairs≅BoolDiv : (m : ℕ) → Iso (AllPairs (pos (suc m))) (Bool × Div (suc m))
Iso.fun      (AllPairs≅BoolDiv m) = toDiv m
Iso.inv      (AllPairs≅BoolDiv m) = fromDiv m
Iso.rightInv (AllPairs≅BoolDiv m) = toFromDiv m
Iso.leftInv  (AllPairs≅BoolDiv m) = fromToDiv m

allPairs≃boolDiv : (m : ℕ) → AllPairs (pos (suc m)) ≃ (Bool × Div (suc m))
allPairs≃boolDiv m = isoToEquiv (AllPairs≅BoolDiv m)

------------------------------------------------------------------------
-- 7.  T5: r(N) = 2 d(N) for odd N ≥ 1.
------------------------------------------------------------------------

OddRep≅BoolDiv : (k : ℕ) → Iso (Rep (pos (suc (2 ℕ.· k)))) (Bool × Div (suc (2 ℕ.· k)))
OddRep≅BoolDiv k =
  compIso (Rep≅Pairs N) (compIso (Pairs≅AllPairs-odd N oddN) (AllPairs≅BoolDiv (2 ℕ.· k)))
  where
  N = pos (suc (2 ℕ.· k))
  oddN : Odd N
  oddN = pos k , 1+2kPos k

oddRepCount : (k : ℕ) → Rep (pos (suc (2 ℕ.· k))) ≃ (Bool × Div (suc (2 ℕ.· k)))
oddRepCount k = isoToEquiv (OddRep≅BoolDiv k)

oddRepCount-isOdd : (n : ℕ) → ℕ.isOdd n ≡ true → Rep (pos n) ≃ (Bool × Div n)
oddRepCount-isOdd n p =
  subst (λ n' → Rep (pos n') ≃ (Bool × Div n')) (sym (snd (ℕeven.isOddTrue n p)))
        (oddRepCount (fst (ℕeven.isOddTrue n p)))

------------------------------------------------------------------------
-- 8.  Instances: N = 15 and N = 6.
------------------------------------------------------------------------

rep15 : Rep 15 ≃ (Bool × Div 15)
rep15 = oddRepCount 7

-- The eight representations 15 = W² − R².
r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ : Rep 15
r₁ = (4 , 1) , refl
r₂ = (4 , - 1) , refl
r₃ = (- 4 , 1) , refl
r₄ = (- 4 , - 1) , refl
r₅ = (8 , 7) , refl
r₆ = (8 , - 7) , refl
r₇ = (- 8 , 7) , refl
r₈ = (- 8 , - 7) , refl

signDivisor : Bool × Div 15 → Bool × ℕ
signDivisor (s , d , _) = s , d

-- Their images: sign of a = W − R, and the divisor |W − R| of 15.
img₁ : signDivisor (equivFun rep15 r₁) ≡ (true , 3)
img₁ = refl
img₂ : signDivisor (equivFun rep15 r₂) ≡ (true , 5)
img₂ = refl
img₃ : signDivisor (equivFun rep15 r₃) ≡ (false , 5)
img₃ = refl
img₄ : signDivisor (equivFun rep15 r₄) ≡ (false , 3)
img₄ = refl
img₅ : signDivisor (equivFun rep15 r₅) ≡ (true , 1)
img₅ = refl
img₆ : signDivisor (equivFun rep15 r₆) ≡ (true , 15)
img₆ = refl
img₇ : signDivisor (equivFun rep15 r₇) ≡ (false , 15)
img₇ = refl
img₈ : signDivisor (equivFun rep15 r₈) ≡ (false , 1)
img₈ = refl

-- And back: the divisor 3 of 15 (cofactor 5), with positive sign, is (4 , 1).
back₁ : fst (invEq rep15 (true , 3 , suc-≤-suc zero-≤ , ∣ 5 , refl ∣₁)) ≡ (4 , 1)
back₁ = refl

------------------------------------------------------------------------
-- 9.  T6: 4 | N reduces to the factor pairs of N/4.
------------------------------------------------------------------------

halvesOfPairs : (M : ℤ) (x : Pairs (4 · M)) → Even (fst (fst x)) × Even (snd (fst x))
halvesOfPairs M ((a , b) , e , sp) = Sum.rec (λ ee → ee)
  (λ (oa , ob) → ⊥.rec (¬EvenOdd (a · b) (2 · M , e ∙ fourEven M) (oddProduct a b oa ob)))
  (bothEvenOrBothOdd a b sp)

fourTo : (M : ℤ) → Pairs (4 · M) → AllPairs M
fourTo M x = (a' , b') , ·lCancel 4 (a' · b') M (sym (doubleProduct a' b') ∙ sym (cong₂ _·_ ha hb) ∙ snd x .fst) 4≢0
  where
  a' = fst (fst (halvesOfPairs M x))
  ha = snd (fst (halvesOfPairs M x))
  b' = fst (snd (halvesOfPairs M x))
  hb = snd (snd (halvesOfPairs M x))

fourFrom : (M : ℤ) → AllPairs M → Pairs (4 · M)
fourFrom M ((a' , b') , e') =
  (2 · a' , 2 · b') , (doubleProduct a' b' ∙ cong (4 ·_) e') , (a' + b' , doubleSum a' b')

fourRoundAll : (M : ℤ) (y : AllPairs M) → fourTo M (fourFrom M y) ≡ y
fourRoundAll M ((a' , b') , e') = Σ≡Prop (λ _ → isSetℤ _ _)
  (≡-× (·lCancel 2 _ _ (sym (snd (fst hv))) 2≢0) (·lCancel 2 _ _ (sym (snd (snd hv))) 2≢0))
  where
  hv = halvesOfPairs M (fourFrom M ((a' , b') , e'))

fourRoundPairs : (M : ℤ) (x : Pairs (4 · M)) → fourFrom M (fourTo M x) ≡ x
fourRoundPairs M x = Σ≡Prop (isPropPairsFiber (4 · M))
  (≡-× (sym (snd (fst (halvesOfPairs M x)))) (sym (snd (snd (halvesOfPairs M x)))))

Pairs≅AllPairs-four : (M : ℤ) → Iso (Pairs (4 · M)) (AllPairs M)
Iso.fun      (Pairs≅AllPairs-four M) = fourTo M
Iso.inv      (Pairs≅AllPairs-four M) = fourFrom M
Iso.rightInv (Pairs≅AllPairs-four M) = fourRoundAll M
Iso.leftInv  (Pairs≅AllPairs-four M) = fourRoundPairs M

fourRep≃allPairs : (M : ℤ) → Rep (4 · M) ≃ AllPairs M
fourRep≃allPairs M = isoToEquiv (compIso (Rep≅Pairs (4 · M)) (Pairs≅AllPairs-four M))

-- "2d(N/4) for 4 | N", for N/4 = suc m positive.
fourRepCount : (m : ℕ) → Rep (4 · pos (suc m)) ≃ (Bool × Div (suc m))
fourRepCount m = isoToEquiv
  (compIso (Rep≅Pairs (4 · pos (suc m)))
           (compIso (Pairs≅AllPairs-four (pos (suc m))) (AllPairs≅BoolDiv m)))
