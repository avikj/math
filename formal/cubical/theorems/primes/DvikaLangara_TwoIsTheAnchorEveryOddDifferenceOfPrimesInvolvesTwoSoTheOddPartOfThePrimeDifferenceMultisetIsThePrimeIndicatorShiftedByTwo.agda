{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- द्विकं लङ्गरम् · two is the anchor
--
-- notes/PARITY_RIGIDITY.md (absent from this repository) (main), "Prime-prefix consequence: 2 is the
-- anchor":
--
--   "It contains the single even point 0; every other exponent is odd.
--    Equivalently, in the original prime set the unique even prime 2 is a
--    2-adic anchor.  Every odd pairwise difference of primes must involve
--    2, so the positive odd part of the difference multiset literally
--    lists {p−2 : 3 ≤ p ≤ X} once each."
--
--   "There is an explicit O(D) reconstruction from a difference-count
--    array (c(h))_{0≤h≤D}: read off every positive odd h for which
--    c(h)=1 ..."
--
-- The 2 odd-prime arithmetic is composed here, in the corpus's own
-- computable primality (primeb of SamastaPrasna, via the smallest-factor
-- search spf of the RH module), with no polynomial ring:
--
--   even-prime-is-two          an even number passing primeb is 2
--   odd-difference-involves-two two primes at an odd distance: the
--                              smaller one is 2
--   odd-part                   for odd h and X ≥ 2, the ordered count
--                              c X h = #{p ≤ X : p, p+h prime, p+h ≤ X}
--                              is exactly a (2 + h) · [2 + h ≤ X]
--   read-off                   for odd h with 2 + h ≤ X, c X h ≡ 1 iff
--                              2 + h is prime, and c X h ≡ 0 otherwise
--
-- So the odd part of the prime difference multiset IS the prime indicator
-- shifted by two, and the note's O(D) reconstruction reads the primes off
-- it exactly.  This is the arithmetic half of the corollary.  The
-- set-rigidity layers (an arbitrary B with c_B = c_{P_X} is a
-- translate or reflection) live in ParityRigidity.lean's `core`
-- and `rigidity_normalized`.
------------------------------------------------------------------------

module DvikaLangara_TwoIsTheAnchorEveryOddDifferenceOfPrimesInvolvesTwoSoTheOddPartOfThePrimeDifferenceMultisetIsThePrimeIndicatorShiftedByTwo where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using ( ℕ ; zero ; suc ; _+_ ; _·_ ; +-suc ; +-comm ; +-zero ; 0≡m·0 ; snotz ; znots ; discreteℕ )
open import Cubical.Data.Nat.Order
  using ( _≤_ ; _<_ ; ≤-refl ; ≤-suc ; pred-≤-pred ; <-weaken ; ≤-split ; ¬-<-zero ; zero-≤ ; suc-≤-suc ; ¬m<m ; ≤-k+ ; ≤-trans )
open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_ ; false≢true ; true≢false ; not)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Relation.Nullary using (¬_ ; yes ; no)
import Cubical.Data.Empty as E

open import RH_TheWholeQuestionEntersTyped_DavisMatiyasevichRobinsonArithmetization
  using (spf ; spfFrom ; eqb ; ltb ; leb ; modF ; monus ; isZero ; dividesb ; _mod_)
open import SamastaPrasna_TheOpenConstellationEntersTypedAndTheOracleAnswersEveryInstance
  using (primeb ; evenb)
open import EkaBija_OnePairKernelTwoReadersGoldbachIsTheCentreMarginalTwinPrimesTheRadiusMarginalAndTheOrderedGoldbachCountIsTheCauchySquareInCentreRadiusCoordinates
  using (ind ; a ; Σ≤ ; eqb-sound ; if-true ; primeb-unfold)

------------------------------------------------------------------------
-- §1 · parity arithmetic on the corpus's evenb
------------------------------------------------------------------------

evenb-suc : (n : ℕ) → evenb (suc n) ≡ not (evenb n)
evenb-suc zero          = refl
evenb-suc (suc zero)    = refl
evenb-suc (suc (suc n)) = evenb-suc n

evenb-+ : (m n : ℕ) → evenb (m + n) ≡ (if evenb m then evenb n else not (evenb n))
evenb-+ zero    n = refl
evenb-+ (suc m) n =
  evenb-suc (m + n) ∙ cong not (evenb-+ m n) ∙ step (evenb m) ∙ cong (λ b → if b then evenb n else not (evenb n)) (sym (evenb-suc m))
  where
  step : (b : Bool) → not (if b then evenb n else not (evenb n))
                    ≡ (if not b then evenb n else not (evenb n))
  step true  = refl
  step false = notnot (evenb n)
    where
    notnot : (c : Bool) → not (not c) ≡ c
    notnot true  = refl
    notnot false = refl

odd+odd : (m n : ℕ) → evenb m ≡ false → evenb n ≡ false → evenb (m + n) ≡ true
odd+odd m n em en =
  evenb-+ m n ∙ cong (λ b → if b then evenb n else not (evenb n)) em ∙ cong not en

odd≢0 : (h : ℕ) → evenb h ≡ false → ¬ (h ≡ 0)
odd≢0 h eh h≡0 = true≢false (sym (cong evenb h≡0) ∙ eh)

------------------------------------------------------------------------
-- §2 · the smallest factor of an even number ≥ 1 is 2
------------------------------------------------------------------------

-- modF fuel k 2 reaches 0 on an even k once the fuel covers k: each step
-- eats 2 and one unit of fuel.
modF-even : (k fuel : ℕ) → evenb k ≡ true → k ≤ fuel → modF fuel k 2 ≡ 0
modF-even zero zero            _  _   = refl
modF-even zero (suc fuel)      _  _   = refl
modF-even (suc zero) fuel      ek _   = E.rec (false≢true ek)
modF-even (suc (suc k)) zero   _  le  = E.rec (¬-<-zero le)
modF-even (suc (suc k)) (suc fuel) ek le =
  modF-even k fuel ek (<-weaken (pred-≤-pred le))

dividesb-2-even : (n : ℕ) → evenb n ≡ true → dividesb 2 n ≡ true
dividesb-2-even n en = cong isZero (modF-even n n en ≤-refl)

spf-even : (m : ℕ) → evenb (suc m) ≡ true → spf (suc m) ≡ 2
spf-even m em = if-true (dividesb 2 (suc m)) (dividesb-2-even (suc m) em) 2 (spfFrom m 3 (suc m))

------------------------------------------------------------------------
-- §3 · an even prime is 2; two primes at an odd distance involve 2
------------------------------------------------------------------------

even-prime-is-two : (p : ℕ) → primeb p ≡ true → evenb p ≡ true → p ≡ 2
even-prime-is-two zero          pr _  = E.rec (false≢true pr)
even-prime-is-two (suc zero)    pr _  = E.rec (false≢true pr)
even-prime-is-two (suc (suc m)) pr ep =
  sym (eqb-sound 2 (suc (suc m))
        (subst (λ s → eqb s (suc (suc m)) ≡ true) (spf-even (suc m) ep)
               (sym (primeb-unfold m) ∙ pr)))

prime-≥2 : (p : ℕ) → primeb p ≡ true → 2 ≤ p
prime-≥2 zero          pr = E.rec (false≢true pr)
prime-≥2 (suc zero)    pr = E.rec (false≢true pr)
prime-≥2 (suc (suc m)) pr = suc-≤-suc (suc-≤-suc zero-≤)

-- If p and p + h are prime and h is odd, then p = 2.
odd-difference-involves-two : (p h : ℕ) → primeb p ≡ true → primeb (p + h) ≡ true
                            → evenb h ≡ false → p ≡ 2
odd-difference-involves-two p h pp pq eh = go (dichotomy (evenb p))
  where
  dichotomy : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
  dichotomy true  = inl refl
  dichotomy false = inr refl
  -- p + h is an even prime, so it is 2; but p ≥ 2 and h ≥ 1 make it ≥ 3.
  h≥1 : 1 ≤ h
  h≥1 = go' h eh
    where
    go' : (k : ℕ) → evenb k ≡ false → 1 ≤ k
    go' zero    ek = E.rec (true≢false ek)
    go' (suc k) _  = suc-≤-suc zero-≤
  three≤q : 3 ≤ p + h
  three≤q = ≤-trans (suc-≤-suc (prime-≥2 p pp))
                    (subst (λ z → z ≤ p + h) (+-suc p 0 ∙ cong suc (+-comm p 0)) (≤-k+ {k = p} h≥1))
  go : (evenb p ≡ true) ⊎ (evenb p ≡ false) → p ≡ 2
  go (inl ep) = even-prime-is-two p pp ep
  go (inr op) = E.rec (¬m<m (subst (λ q → 3 ≤ q) q≡2 three≤q))
    where
    q≡2 : p + h ≡ 2
    q≡2 = even-prime-is-two (p + h) pq (odd+odd p h op eh)

------------------------------------------------------------------------
-- §4 · the ordered difference count and its odd part
------------------------------------------------------------------------

-- c X h : the number of ordered pairs (p, p + h) of primes with p + h ≤ X,
-- i.e. the coefficient c_{P_X}(h) of notes/PARITY_RIGIDITY.md (absent from this repository) for h > 0.
c : ℕ → ℕ → ℕ
c X h = Σ≤ X (λ p → a p · a (p + h) · ind (leb (p + h) X))

-- A sum over 0..k all of whose terms vanish except possibly the one at j.
Σ≤-zero-of-all : (k : ℕ) (f : ℕ → ℕ) → ((i : ℕ) → i ≤ k → f i ≡ 0) → Σ≤ k f ≡ 0
Σ≤-zero-of-all zero    f z = z zero ≤-refl
Σ≤-zero-of-all (suc k) f z =
  cong₂ _+_ (Σ≤-zero-of-all k f (λ i le → z i (≤-suc le))) (z (suc k) ≤-refl)

Σ≤-ekapada : (k j : ℕ) (f : ℕ → ℕ) → j ≤ k
           → ((i : ℕ) → i ≤ k → ¬ (i ≡ j) → f i ≡ 0) → Σ≤ k f ≡ f j
Σ≤-ekapada zero zero    f le z = refl
Σ≤-ekapada zero (suc j) f le z = E.rec (¬-<-zero le)
Σ≤-ekapada (suc k) j f le z with ≤-split le
... | inl j<sk =
  cong₂ _+_ (Σ≤-ekapada k j f (pred-≤-pred j<sk) (λ i le' ne → z i (≤-suc le') ne))
            (z (suc k) ≤-refl (λ e → ¬m<m (subst (λ t → t < suc k) (sym e) j<sk)))
            ∙ +-zero' (f j)
  where
  +-zero' : (n : ℕ) → n + 0 ≡ n
  +-zero' n = +-comm n 0
... | inr j≡sk =
  cong (_+ f (suc k)) (Σ≤-zero-of-all k f (λ i le' → z i (≤-suc le') (λ e → ¬m<m (subst (λ t → t < suc k) (e ∙ j≡sk) (suc-≤-suc le')))))
  ∙ cong f (sym j≡sk)

-- Every term of c X h at p ≠ 2 vanishes when h is odd.
term-zero : (X h p : ℕ) → evenb h ≡ false → ¬ (p ≡ 2)
          → a p · a (p + h) · ind (leb (p + h) X) ≡ 0
term-zero X h p eh p≢2 = go (dichotomy (primeb p)) (dichotomy (primeb (p + h)))
  where
  dichotomy : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
  dichotomy true  = inl refl
  dichotomy false = inr refl
  go : (primeb p ≡ true) ⊎ (primeb p ≡ false) → (primeb (p + h) ≡ true) ⊎ (primeb (p + h) ≡ false)
     → a p · a (p + h) · ind (leb (p + h) X) ≡ 0
  go (inr np) _        = cong (λ b → ind b · a (p + h) · ind (leb (p + h) X)) np
  go (inl pp) (inr nq) = cong (λ b → a p · ind b · ind (leb (p + h) X)) nq
                         ∙ cong (_· ind (leb (p + h) X)) (sym (0≡m·0 (a p)))
  go (inl pp) (inl pq) = E.rec (p≢2 (odd-difference-involves-two p h pp pq eh))

odd-part : (X h : ℕ) → evenb h ≡ false → 2 ≤ X
         → c X h ≡ a (2 + h) · ind (leb (2 + h) X)
odd-part X h eh 2≤X =
  Σ≤-ekapada X 2 (λ p → a p · a (p + h) · ind (leb (p + h) X)) 2≤X
    (λ i _ i≢2 → term-zero X h i eh i≢2)
  ∙ cong (_· ind (leb (2 + h) X)) (+-zero (a (2 + h)))

-- Reading the primes off the odd part: with 2 + h ≤ X, c X h is the
-- prime indicator at 2 + h.
read-off : (X h : ℕ) → evenb h ≡ false → 2 ≤ X → leb (2 + h) X ≡ true
         → c X h ≡ a (2 + h)
read-off X h eh 2≤X le =
  odd-part X h eh 2≤X ∙ cong (λ b → a (2 + h) · ind b) le ∙ ·1 (a (2 + h))
  where
  ·1 : (n : ℕ) → n · 1 ≡ n
  ·1 zero    = refl
  ·1 (suc n) = cong suc (·1 n)

------------------------------------------------------------------------
-- §5 · witnesses
------------------------------------------------------------------------

-- c(1) at X = 20 counts (2,3) only; c(3) counts (2,5); c(9) counts (2,11);
-- c(7) counts nothing (9 is not prime); c(5) counts (2,7).
c-20-1 : c 20 1 ≡ 1
c-20-1 = refl

c-20-7 : c 20 7 ≡ 0
c-20-7 = refl

c-20-9 : c 20 9 ≡ 1
c-20-9 = refl

-- The even part is not of this shape: c(2) at X = 20 counts the twin
-- pairs (3,5), (5,7), (11,13), (17,19).
c-20-2 : c 20 2 ≡ 4
c-20-2 = refl
