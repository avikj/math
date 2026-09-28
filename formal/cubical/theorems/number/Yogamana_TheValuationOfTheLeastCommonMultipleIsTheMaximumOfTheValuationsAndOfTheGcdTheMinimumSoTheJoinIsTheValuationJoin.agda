{-# OPTIONS --cubical --safe --no-import-sorts #-}
------------------------------------------------------------------------
-- योगमानम् — the valuation of the join.
--
-- (the valuation of the least common multiple is the maximum of the
--  valuations, that of the gcd the minimum; so `gcd · lcm = a · b` reads
--  as `min + max = v(a) + v(b)`, and the join is the valuation join.)
--
-- ────────────────────────────────────────────────────────────────────
-- SOURCE, quoted verbatim.
--
-- notes/ARITHMETIC_LIFE_ADVERSARIAL_AUDIT.md (absent from this repository) (branch main), item 2:
--
--   "2. **PROVE** — the join now rests on `gcd·lcm = ab`. State the
--    corresponding valuation form `v(lcm) = max(v(a),v(b))` and connect
--    it to `VALUATION_FORMATION_UNIVERSALITY`'s universal property; that
--    note's §"addition is not coordinate-local" is the obstruction that
--    keeps this from extending to the additive side, and the two notes
--    should cite each other."
--
-- notes/VALUATION_FORMATION_UNIVERSALITY.md (absent from this repository), on its universal property:
--
--   "Let `N+` be the positive integers under multiplication and let
--    `N^(P)` be the finitely supported prime-indexed exponent vectors
--    under coordinate addition. Then
--        v : N_{>0} ⟶ N^(P),  v(n) = (v_p(n))_p                    (1)
--    is an isomorphism of commutative monoids."
--
--   "The universal property is the fundamental theorem of arithmetic in
--    free-commutative-monoid form, not a novelty claim."
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS MODULE PROVES, over Drdha's firm numbers (दृढम् p, i.e.
-- 1 < p and every divisor of p is 1 or p), Ekatva's valuation
-- मानम् p n pos, Prthakkarana's splitting n ≡ p ^ मानम् p n pos · m with
-- p ∤ m, and LCMExists's IsLCM₂ a b L = (a ∣ L) × (b ∣ L) × (∀ m → a ∣ m
-- → b ∣ m → L ∣ m).  Throughout, p is firm and a, b are positive.
--
--   §१  भाजक-मानम् — the valuation is monotone along divisibility:
--         x ∣ y → मानम् p x ≤ मानम् p y   (y = c · x and additivity).
--
--   §२  (T1) घात-भाजक-लक्षणम् — the valuation characterises divisibility
--       by prime powers, in both directions:
--         घात-भाजकः→मानम् : (p ^ k) ∣ n → k ≤ मानम् p n pos
--         मानम्→घात-भाजकः : k ≤ मानम् p n pos → (p ^ k) ∣ n
--       The first is §१ plus मान-घातः (v(p^k) = k); the second is
--       p ^ k ∣ p ^ (d + k) = p ^ v ∣ p ^ v · m = n.
--
--   §३  (T2) लघुतम-मानम् — for ANY L with IsLCM₂ a b L (such an L is
--       positive, भाजक-धनः, since L ∣ a · b):
--         मानम् p L posL ≡ max (मानम् p a posa) (मानम् p b posb).
--       ≥ : a ∣ L and b ∣ L, by §१ and the least-upper-bound law of max.
--       ≤ : the explicit common multiple
--             M := p ^ max(va,vb) · (a' · b'),   a = p^va · a', b = p^vb · b'
--           has a ∣ M and b ∣ M (चतुर्गुणम् rearranges the four factors),
--           so L ∣ M by leastness, so v(L) ≤ v(M) = max + v(a'·b') = max,
--           where p ∤ a' · b' is Euclid VII.30 (Drdha's युक्लिड-वाक्यम्).
--       लघुतम-मानम्' is the same for LCMExists's lcm a b.
--
--   §४  (T3) महत्तम-मानम् — for ANY g with the library's isGCD a b g:
--         मानम् p g posg ≡ min (मानम् p a posa) (मानम् p b posb).
--       ≤ : g ∣ a, g ∣ b, by §१ and the greatest-lower-bound law of min.
--       ≥ : p ^ min ∣ a and p ^ min ∣ b by (T1), hence p ^ min ∣ g.
--       महत्तम-मानम्' is the same for the library's gcd a b.
--
--   §५  (T4) the identity gcd · lcm ≡ a · b read through valuations:
--         न्यून-अधिक-योगः : min m n + max m n ≡ m + n           (arithmetic)
--         गुण-योग-मानम्   : मानम् p (g · L) ≡ मानम् p (a · b)   (both sides
--                           are min + max = va + vb by (T2), (T3), §४)
--       and the note's "join" statement, BOTH directions, for positive L:
--         सन्धिः : IsLCM₂ a b L
--                  ↔ ((p : ℕ) → दृढम् p → मानम् p L posL ≡ max (v_p a) (v_p b))
--       ⇒ is (T2) with p quantified.  ⇐ needs "two positive numbers with
--       the same valuation at every firm p are equal", मान-सर्वत्र-समता,
--       which the corpus makes short: the valuations ARE the counts in
--       Drdha's firm lists, a non-firm p has count 0 in a firm list
--       (अदृढ-गणना, firmness being decidable, दृढ-निर्णयः), so the two
--       lists have the same count of every natural, are a Perm by
--       Ekatva's count-perm, and a Perm preserves the product (Perm-वधः,
--       from Ekatva's Insert-वधः).  Then L ≡ lcm a b and IsLCM₂ transports.
--
--   §६  परीक्षा — instances a = 12, b = 18, obtained from (T2)/(T3) with
--       the right-hand sides computed by refl (the kernel evaluates the
--       valuations of 12 and 18, not the gcd/lcm recursion):
--         v₂ (lcm 12 18) = 2,  v₃ (lcm 12 18) = 2,
--         v₂ (gcd 12 18) = 1,  v₃ (gcd 12 18) = 1.
--
-- CONNECTION TO THE UNIVERSAL PROPERTY.  The note's (1) says v is a
-- monoid isomorphism N+ ≅ N^(P).  This module holds, over दृढम्, the
-- pieces of that statement the join needs: homomorphism (Prthakkarana's
-- मान-गुणनम्, used at every step), injectivity (मान-सर्वत्र-समता, §५),
-- and — the new content — that under v the divisibility lattice's join
-- and meet become the coordinatewise max and min.  So `gcd · lcm = a · b`
-- is, coordinate by coordinate, `min + max = va + vb`, which is §४.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS **NOT** CLAIMED.
--
--   · Surjectivity of v onto finitely supported vectors (the "iso" half
--     that reconstructs n from its exponents) is not stated; the join
--     does not need it.
--   · Nothing about the additive side: the note's §"addition is not
--     coordinate-local" is an obstruction, and this module does not
--     touch v(a + b).
--   · दृढम् is not identified with theorems/number's IsPrime here (as in
--     Prthakkarana, that bridge is a separate module); the Euclid lemma
--     used is Drdha's युक्लिड-वाक्यम्, not WalkJumps.prime-∣-·.
--   · Valuations at 0 are undefined (मानम् takes 0 < n), so the join
--     statement carries the hypothesis 0 < L; for positive a, b every
--     IsLCM₂-witness is positive anyway (भाजक-धनः).
--
-- CHECKED: Agda 2.8.0 + agda/cubical v0.9, --cubical --safe, no
-- postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module Yogamana_TheValuationOfTheLeastCommonMultipleIsTheMaximumOfTheValuationsAndOfTheGcdTheMinimumSoTheJoinIsTheValuationJoin where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
  using (_∣_ ; ∣-trans ; ∣-left ; ∣-right ; ∣-untrunc ; m∣sn→z<m)
open import Cubical.Data.Nat.GCD using (isGCD ; gcd ; gcdIsGCD)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; Σ-syntax)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr) renaming (rec to ⊎-rec)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import LCMExists using (IsLCM₂ ; lcm ; lcm-isLCM₂)
open import Drdha_TheFirmNumbersProductIsEveryPositiveIntegerAndTheirMembershipIsDecidedByDivision
  using (दृढम् ; वधः ; सर्वे ; विभाजनम् ; युक्लिड-वाक्यम्)
open import Ekatva_TheFirmFactorisationIsUniqueTwoPrimeListsWithOneProductAreAPermutationSoTheValuationIsWellDefinedAndPermIsExactlySameCount
  using (module Bahulya ; मानम् ; मान-निश्चयः ; Insert-वधः)
open import Prthakkarana_EveryPositiveIntegerIsAPrimePowerTimesAPrimeFreeRestTheExponentIsTheValuationAndTheValuationAddsOverProducts
  using (पृथक्करणम् ; मान-अभाज्यः ; मान-घातः ; मान-गुणनम् ; गुण-धनः ; घात-धनः ; शेष-धनः ; दृढ?)
open import TheUsualReasonsMadeExplicitTheInductivePermutationRelationEmbedsInAdjacentTranspositions
  using (Perm ; pnil ; pcons)

open Bahulya discreteℕ using (दश ; गणना ; count-perm)

------------------------------------------------------------------------
-- ० · bookkeeping: positivity, powers, four factors
------------------------------------------------------------------------

-- a firm number is positive
दृढ-धनः : (p : ℕ) → दृढम् p → 0 < p
दृढ-धनः p दृ = <-trans ≤-refl (fst दृ)

-- a divisor of a positive number is positive
भाजक-धनः : (x y : ℕ) → x ∣ y → 0 < y → 0 < x
भाजक-धनः x zero    _ pos = ⊥-rec (¬-<-zero pos)
भाजक-धनः x (suc n) d _   = m∣sn→z<m d

-- the cofactor in c · x ≡ y > 0 is positive
गुणक-धनः : (c x y : ℕ) → c · x ≡ y → 0 < y → 0 < c
गुणक-धनः zero    x y e pos = ⊥-rec (¬-<-zero (subst (0 <_) (sym e) pos))
गुणक-धनः (suc c) _ _ _ _   = suc-≤-suc zero-≤

-- p ^ (a + b) ≡ p ^ a · p ^ b
घात-योगः : (p a b : ℕ) → p ^ (a + b) ≡ p ^ a · p ^ b
घात-योगः p zero    b = sym (·-identityˡ (p ^ b))
घात-योगः p (suc a) b = cong (p ·_) (घात-योगः p a b) ∙ ·-assoc p (p ^ a) (p ^ b)

-- (x · y) · (u · w) ≡ (y · u) · (x · w)
चतुर्गुणम् : (x y u w : ℕ) → (x · y) · (u · w) ≡ (y · u) · (x · w)
चतुर्गुणम् x y u w =
    ·-assoc (x · y) u w
  ∙ cong (_· w) (sym (·-assoc x y u) ∙ ·-comm x (y · u))
  ∙ sym (·-assoc (y · u) x w)

-- the valuation depends only on the number (मानम् is a count in
-- Drdha's list, and मान-निश्चयः says every firm list of n has that count)
मान-समता : (p x y : ℕ) (posx : 0 < x) (posy : 0 < y) → x ≡ y
         → मानम् p x posx ≡ मानम् p y posy
मान-समता p x y posx posy e =
  मान-निश्चयः p y posy (fst (विभाजनम् x posx)) (fst (snd (विभाजनम् x posx)))
              (snd (snd (विभाजनम् x posx)) ∙ e)

------------------------------------------------------------------------
-- १ · भाजक-मानम् — the valuation is monotone along divisibility
------------------------------------------------------------------------

भाजक-मानम् : (p : ℕ) → दृढम् p → (x y : ℕ) (posx : 0 < x) (posy : 0 < y)
          → x ∣ y → मानम् p x posx ≤ मानम् p y posy
भाजक-मानम् p दृ x y posx posy x∣y =
  मानम् p c posc , sym (मान-गुणनम् p c x posc posx poscx) ∙ मान-समता p (c · x) y poscx posy cx≡y
  where
  c     = fst (∣-untrunc x∣y)
  cx≡y  = snd (∣-untrunc x∣y)
  posc  = गुणक-धनः c x y cx≡y posy
  poscx = गुण-धनः c x posc posx

------------------------------------------------------------------------
-- २ · (T1) the valuation characterises divisibility by prime powers
------------------------------------------------------------------------

घात-भाजकः→मानम् : (p : ℕ) (दृ : दृढम् p) (n : ℕ) (pos : 0 < n) (k : ℕ)
               → (p ^ k) ∣ n → k ≤ मानम् p n pos
घात-भाजकः→मानम् p दृ n pos k pᵏ∣n =
  subst (_≤ मानम् p n pos) (मान-घातः p दृ k posₖ) (भाजक-मानम् p दृ (p ^ k) n posₖ pos pᵏ∣n)
  where
  posₖ = घात-धनः p k (दृढ-धनः p दृ)

मानम्→घात-भाजकः : (p : ℕ) (दृ : दृढम् p) (n : ℕ) (pos : 0 < n) (k : ℕ)
               → k ≤ मानम् p n pos → (p ^ k) ∣ n
मानम्→घात-भाजकः p दृ n pos k (d , d+k≡v) = ∣-trans pᵏ∣pᵛ pᵛ∣n
  where
  v  = मानम् p n pos
  m  = fst (पृथक्करणम् p दृ n pos)
  n≡ = fst (snd (पृथक्करणम् p दृ n pos))

  pᵏ∣pᵛ : (p ^ k) ∣ (p ^ v)
  pᵏ∣pᵛ = subst ((p ^ k) ∣_) (sym (घात-योगः p d k) ∙ cong (p ^_) d+k≡v) (∣-right (p ^ d))

  pᵛ∣n : (p ^ v) ∣ n
  pᵛ∣n = subst ((p ^ v) ∣_) (sym n≡) (∣-left m)

-- both directions at once
घात-भाजक-लक्षणम् : (p : ℕ) (दृ : दृढम् p) (n : ℕ) (pos : 0 < n) (k : ℕ)
                → ((p ^ k) ∣ n → k ≤ मानम् p n pos) × (k ≤ मानम् p n pos → (p ^ k) ∣ n)
घात-भाजक-लक्षणम् p दृ n pos k = घात-भाजकः→मानम् p दृ n pos k , मानम्→घात-भाजकः p दृ n pos k

------------------------------------------------------------------------
-- lattice laws of max and min on ℕ
------------------------------------------------------------------------

max-उपरि : (m n k : ℕ) → m ≤ k → n ≤ k → max m n ≤ k
max-उपरि zero    n       k       _  h2 = h2
max-उपरि (suc m) zero    k       h1 _  = h1
max-उपरि (suc m) (suc n) zero    h1 _  = ⊥-rec (¬-<-zero h1)
max-उपरि (suc m) (suc n) (suc k) h1 h2 =
  suc-≤-suc (max-उपरि m n k (pred-≤-pred h1) (pred-≤-pred h2))

min-अधः : (m n k : ℕ) → k ≤ m → k ≤ n → k ≤ min m n
min-अधः zero    n       k       h1 _  = h1
min-अधः (suc m) zero    k       _  h2 = h2
min-अधः (suc m) (suc n) zero    _  _  = zero-≤
min-अधः (suc m) (suc n) (suc k) h1 h2 =
  suc-≤-suc (min-अधः m n k (pred-≤-pred h1) (pred-≤-pred h2))

न्यून-अधिक-योगः : (m n : ℕ) → min m n + max m n ≡ m + n
न्यून-अधिक-योगः zero    n       = refl
न्यून-अधिक-योगः (suc m) zero    = sym (+-zero (suc m))
न्यून-अधिक-योगः (suc m) (suc n) =
  cong suc (+-suc (min m n) (max m n) ∙ cong suc (न्यून-अधिक-योगः m n) ∙ sym (+-suc m n))

------------------------------------------------------------------------
-- ३ · (T2) लघुतम-मानम् — the valuation of the lcm is the max
------------------------------------------------------------------------

-- any IsLCM₂-witness of positive a, b is positive (it divides a · b)
लघुतम-धनः : (a b : ℕ) → 0 < a → 0 < b → (L : ℕ) → IsLCM₂ a b L → 0 < L
लघुतम-धनः a b posa posb L h =
  भाजक-धनः L (a · b) (snd (snd h) (a · b) (∣-left b) (∣-right a)) (गुण-धनः a b posa posb)

लघुतम-मानम् : (p : ℕ) (दृ : दृढम् p) (a b : ℕ) (posa : 0 < a) (posb : 0 < b)
           (L : ℕ) → IsLCM₂ a b L → (posL : 0 < L)
           → मानम् p L posL ≡ max (मानम् p a posa) (मानम् p b posb)
लघुतम-मानम् p दृ a b posa posb L (a∣L , b∣L , least) posL = ≤-antisym vL≤max max≤vL
  where
  va = मानम् p a posa
  vb = मानम् p b posb
  vL = मानम् p L posL
  mx = max va vb

  -- ≥ : L is a common multiple
  max≤vL : mx ≤ vL
  max≤vL = max-उपरि va vb vL (भाजक-मानम् p दृ a L posa posL a∣L)
                              (भाजक-मानम् p दृ b L posb posL b∣L)

  -- ≤ : the explicit common multiple M = p ^ mx · (a' · b')
  a' = fst (पृथक्करणम् p दृ a posa)
  a≡ = fst (snd (पृथक्करणम् p दृ a posa))
  p∤a' = snd (snd (पृथक्करणम् p दृ a posa))
  b' = fst (पृथक्करणम् p दृ b posb)
  b≡ = fst (snd (पृथक्करणम् p दृ b posb))
  p∤b' = snd (snd (पृथक्करणम् p दृ b posb))

  M = p ^ mx · (a' · b')

  posa' = शेष-धनः a (p ^ va) posa a' a≡
  posb' = शेष-धनः b (p ^ vb) posb b' b≡
  posP  = घात-धनः p mx (दृढ-धनः p दृ)
  posR  = गुण-धनः a' b' posa' posb'
  posM  = गुण-धनः (p ^ mx) (a' · b') posP posR

  -- a ∣ M : with d + va ≡ mx, M = (p^d · p^va) · (a' · b') = (p^va · a') · (p^d · b')
  a∣M : a ∣ M
  a∣M = subst (a ∣_) (sym M≡) (∣-left (p ^ d · b'))
    where
    d     = fst (left-≤-max {va} {vb})
    d+va≡ = snd (left-≤-max {va} {vb})
    M≡ : M ≡ a · (p ^ d · b')
    M≡ = cong (_· (a' · b')) (cong (p ^_) (sym d+va≡) ∙ घात-योगः p d va)
       ∙ चतुर्गुणम् (p ^ d) (p ^ va) a' b'
       ∙ cong (_· (p ^ d · b')) (sym a≡)

  b∣M : b ∣ M
  b∣M = subst (b ∣_) (sym M≡) (∣-left (p ^ d · a'))
    where
    d     = fst (right-≤-max {vb} {va})
    d+vb≡ = snd (right-≤-max {vb} {va})
    M≡ : M ≡ b · (p ^ d · a')
    M≡ = cong₂ _·_ (cong (p ^_) (sym d+vb≡) ∙ घात-योगः p d vb) (·-comm a' b')
       ∙ चतुर्गुणम् (p ^ d) (p ^ vb) b' a'
       ∙ cong (_· (p ^ d · a')) (sym b≡)

  L∣M : L ∣ M
  L∣M = least M a∣M b∣M

  -- v(M) = mx + v(a' · b') = mx + 0, by Euclid VII.30
  p∤a'b' : ¬ (p ∣ (a' · b'))
  p∤a'b' dv = ⊎-rec p∤a' p∤b' (युक्लिड-वाक्यम् p a' b' दृ dv)

  vM≡mx : मानम् p M posM ≡ mx
  vM≡mx = मान-गुणनम् p (p ^ mx) (a' · b') posP posR posM
        ∙ cong₂ _+_ (मान-घातः p दृ mx posP) (मान-अभाज्यः p दृ (a' · b') posR p∤a'b')
        ∙ +-zero mx

  vL≤max : vL ≤ mx
  vL≤max = subst (vL ≤_) vM≡mx (भाजक-मानम् p दृ L M posL posM L∣M)

-- the same for LCMExists's lcm, positivity supplied
लघुतम-मानम्' : (p : ℕ) (दृ : दृढम् p) (a b : ℕ) (posa : 0 < a) (posb : 0 < b)
            → मानम् p (lcm a b) (लघुतम-धनः a b posa posb (lcm a b) (lcm-isLCM₂ a b))
              ≡ max (मानम् p a posa) (मानम् p b posb)
लघुतम-मानम्' p दृ a b posa posb =
  लघुतम-मानम् p दृ a b posa posb (lcm a b) (lcm-isLCM₂ a b)
              (लघुतम-धनः a b posa posb (lcm a b) (lcm-isLCM₂ a b))

------------------------------------------------------------------------
-- ४ · (T3) महत्तम-मानम् — the valuation of the gcd is the min
------------------------------------------------------------------------

महत्तम-धनः : (a b : ℕ) → 0 < a → (g : ℕ) → isGCD a b g → 0 < g
महत्तम-धनः a b posa g hg = भाजक-धनः g a (fst (fst hg)) posa

महत्तम-मानम् : (p : ℕ) (दृ : दृढम् p) (a b : ℕ) (posa : 0 < a) (posb : 0 < b)
           (g : ℕ) → isGCD a b g → (posg : 0 < g)
           → मानम् p g posg ≡ min (मानम् p a posa) (मानम् p b posb)
महत्तम-मानम् p दृ a b posa posb g ((g∣a , g∣b) , greatest) posg = ≤-antisym vg≤min min≤vg
  where
  va = मानम् p a posa
  vb = मानम् p b posb
  vg = मानम् p g posg
  mn = min va vb

  -- ≤ : g is a common divisor
  vg≤min : vg ≤ mn
  vg≤min = min-अधः va vb vg (भाजक-मानम् p दृ g a posg posa g∣a)
                            (भाजक-मानम् p दृ g b posg posb g∣b)

  -- ≥ : p ^ mn is a common divisor, hence divides g
  D = p ^ mn
  posD = घात-धनः p mn (दृढ-धनः p दृ)

  D∣g : D ∣ g
  D∣g = greatest D (मानम्→घात-भाजकः p दृ a posa mn (min-≤-left {va} {vb})
                  , मानम्→घात-भाजकः p दृ b posb mn (min-≤-right {va} {vb}))

  min≤vg : mn ≤ vg
  min≤vg = subst (_≤ vg) (मान-घातः p दृ mn posD) (भाजक-मानम् p दृ D g posD posg D∣g)

-- the same for the library's gcd, positivity supplied
महत्तम-मानम्' : (p : ℕ) (दृ : दृढम् p) (a b : ℕ) (posa : 0 < a) (posb : 0 < b)
            → मानम् p (gcd a b) (महत्तम-धनः a b posa (gcd a b) (gcdIsGCD a b))
              ≡ min (मानम् p a posa) (मानम् p b posb)
महत्तम-मानम्' p दृ a b posa posb =
  महत्तम-मानम् p दृ a b posa posb (gcd a b) (gcdIsGCD a b)
              (महत्तम-धनः a b posa (gcd a b) (gcdIsGCD a b))

------------------------------------------------------------------------
-- ५ · (T4) gcd · lcm ≡ a · b through valuations, and the join
------------------------------------------------------------------------

-- min + max ≡ va + vb, at the valuations
योग-समता : (p : ℕ) (a b : ℕ) (posa : 0 < a) (posb : 0 < b)
         → min (मानम् p a posa) (मानम् p b posb) + max (मानम् p a posa) (मानम् p b posb)
           ≡ मानम् p a posa + मानम् p b posb
योग-समता p a b posa posb = न्यून-अधिक-योगः (मानम् p a posa) (मानम् p b posb)

-- v_p (g · L) ≡ v_p (a · b) for any gcd g and any lcm L of a, b
गुण-योग-मानम् : (p : ℕ) (दृ : दृढम् p) (a b : ℕ) (posa : 0 < a) (posb : 0 < b)
             (g : ℕ) (hg : isGCD a b g) (posg : 0 < g)
             (L : ℕ) (hL : IsLCM₂ a b L) (posL : 0 < L)
           → मानम् p (g · L) (गुण-धनः g L posg posL) ≡ मानम् p (a · b) (गुण-धनः a b posa posb)
गुण-योग-मानम् p दृ a b posa posb g hg posg L hL posL =
    मान-गुणनम् p g L posg posL (गुण-धनः g L posg posL)
  ∙ cong₂ _+_ (महत्तम-मानम् p दृ a b posa posb g hg posg)
              (लघुतम-मानम् p दृ a b posa posb L hL posL)
  ∙ योग-समता p a b posa posb
  ∙ sym (मान-गुणनम् p a b posa posb (गुण-धनः a b posa posb))

-- ── the ⇐ direction needs: same valuation at every firm p ⇒ equal ──

-- firmness is decidable for every natural (Prthakkarana's दृढ? for n > 1)
दृढ-निर्णयः : (z : ℕ) → Dec (दृढम् z)
दृढ-निर्णयः z with splitℕ-< 1 z
... | inl 1<z = दृढ? z 1<z
... | inr z≤1 = no λ दृ → <-asym (fst दृ) z≤1

-- a non-firm number has count 0 in a firm list
अदृढ-गणना : (z : ℕ) (L : List ℕ) → सर्वे दृढम् L → ¬ दृढम् z → गणना z L ≡ 0
अदृढ-गणना z []       _          _   = refl
अदृढ-गणना z (x ∷ xs) (दृx , hs) ¬दृ = पदम् (discreteℕ z x)
  where
  पदम् : (d : Dec (z ≡ x)) → दश d + गणना z xs ≡ 0
  पदम् (yes e) = ⊥-rec (¬दृ (subst दृढम् (sym e) दृx))
  पदम् (no  _) = अदृढ-गणना z xs hs ¬दृ

-- a Perm preserves the product (Ekatva's Insert-वधः, folded)
Perm-वधः : {L M : List ℕ} → Perm L M → वधः L ≡ वधः M
Perm-वधः pnil                = refl
Perm-वधः (pcons {x = x} pm ins) = cong (x ·_) (Perm-वधः pm) ∙ sym (Insert-वधः ins)

-- THE INJECTIVITY: two positive numbers with the same valuation at
-- every firm p are equal
मान-सर्वत्र-समता : (x y : ℕ) (posx : 0 < x) (posy : 0 < y)
               → ((p : ℕ) → दृढम् p → मानम् p x posx ≡ मानम् p y posy)
               → x ≡ y
मान-सर्वत्र-समता x y posx posy h =
  sym prodX ∙ Perm-वधः (count-perm Lx Ly sameCount) ∙ prodY
  where
  Lx    = fst (विभाजनम् x posx)
  allX  = fst (snd (विभाजनम् x posx))
  prodX = snd (snd (विभाजनम् x posx))
  Ly    = fst (विभाजनम् y posy)
  allY  = fst (snd (विभाजनम् y posy))
  prodY = snd (snd (विभाजनम् y posy))

  sameCount : (z : ℕ) → गणना z Lx ≡ गणना z Ly
  sameCount z with दृढ-निर्णयः z
  ... | yes दृ = h z दृ
  ... | no ¬दृ = अदृढ-गणना z Lx allX ¬दृ ∙ sym (अदृढ-गणना z Ly allY ¬दृ)

-- ⇐ : a positive L whose valuation at every firm p is the max is an lcm
सन्धि-प्रत्यागमः : (a b : ℕ) (posa : 0 < a) (posb : 0 < b) (L : ℕ) (posL : 0 < L)
               → ((p : ℕ) → दृढम् p → मानम् p L posL ≡ max (मानम् p a posa) (मानम् p b posb))
               → IsLCM₂ a b L
सन्धि-प्रत्यागमः a b posa posb L posL h =
  subst (IsLCM₂ a b) (sym L≡lcm) (lcm-isLCM₂ a b)
  where
  ℓ    = lcm a b
  posℓ = लघुतम-धनः a b posa posb ℓ (lcm-isLCM₂ a b)

  L≡lcm : L ≡ ℓ
  L≡lcm = मान-सर्वत्र-समता L ℓ posL posℓ
            (λ p दृ → h p दृ ∙ sym (लघुतम-मानम् p दृ a b posa posb ℓ (lcm-isLCM₂ a b) posℓ))

-- THE JOIN, both directions: for positive L,
--   IsLCM₂ a b L  ↔  (∀ firm p) v_p L ≡ max (v_p a) (v_p b)
सन्धिः : (a b : ℕ) (posa : 0 < a) (posb : 0 < b) (L : ℕ) (posL : 0 < L)
       → (IsLCM₂ a b L
            → (p : ℕ) → दृढम् p → मानम् p L posL ≡ max (मानम् p a posa) (मानम् p b posb))
       × (((p : ℕ) → दृढम् p → मानम् p L posL ≡ max (मानम् p a posa) (मानम् p b posb))
            → IsLCM₂ a b L)
सन्धिः a b posa posb L posL =
    (λ h p दृ → लघुतम-मानम् p दृ a b posa posb L h posL)
  , सन्धि-प्रत्यागमः a b posa posb L posL

-- and the meet, ⇒ direction with p quantified (the isGCD counterpart)
मेलनम् : (a b : ℕ) (posa : 0 < a) (posb : 0 < b) (g : ℕ) (posg : 0 < g)
       → isGCD a b g
       → (p : ℕ) → दृढम् p → मानम् p g posg ≡ min (मानम् p a posa) (मानम् p b posb)
मेलनम् a b posa posb g posg hg p दृ = महत्तम-मानम् p दृ a b posa posb g hg posg

------------------------------------------------------------------------
-- ६ · परीक्षा — a = 12, b = 18
------------------------------------------------------------------------

private
  सत्यम् : {A : Type₀} → Dec A → Type₀
  सत्यम् (yes _) = Unit
  सत्यम् (no  _) = ⊥

  सिद्धम् : {A : Type₀} (d : Dec A) → सत्यम् d → A
  सिद्धम् (yes a) _ = a

  दृ-२ : दृढम् 2
  दृ-२ = सिद्धम् (दृढ? 2 (suc-≤-suc (suc-≤-suc zero-≤))) tt

  दृ-३ : दृढम् 3
  दृ-३ = सिद्धम् (दृढ? 3 (suc-≤-suc (suc-≤-suc zero-≤))) tt

  ०<१२ : 0 < 12
  ०<१२ = suc-≤-suc zero-≤

  ०<१८ : 0 < 18
  ०<१८ = suc-≤-suc zero-≤

  pos-lcm : 0 < lcm 12 18
  pos-lcm = लघुतम-धनः 12 18 ०<१२ ०<१८ (lcm 12 18) (lcm-isLCM₂ 12 18)

  pos-gcd : 0 < gcd 12 18
  pos-gcd = महत्तम-धनः 12 18 ०<१२ (gcd 12 18) (gcdIsGCD 12 18)

  -- the right-hand sides max (v 12) (v 18), min (v 12) (v 18) are refl
  -- (12 = 2² · 3, 18 = 2 · 3²)
  लघु-२ : मानम् 2 (lcm 12 18) pos-lcm ≡ 2
  लघु-२ = लघुतम-मानम्' 2 दृ-२ 12 18 ०<१२ ०<१८ ∙ refl

  लघु-३ : मानम् 3 (lcm 12 18) pos-lcm ≡ 2
  लघु-३ = लघुतम-मानम्' 3 दृ-३ 12 18 ०<१२ ०<१८ ∙ refl

  महत्-२ : मानम् 2 (gcd 12 18) pos-gcd ≡ 1
  महत्-२ = महत्तम-मानम्' 2 दृ-२ 12 18 ०<१२ ०<१८ ∙ refl

  महत्-३ : मानम् 3 (gcd 12 18) pos-gcd ≡ 1
  महत्-३ = महत्तम-मानम्' 3 दृ-३ 12 18 ०<१२ ०<१८ ∙ refl

  -- min + max = va + vb at 12, 18: 1 + 2 = 2 + 1 (at p = 2), 1 + 2 = 1 + 2 (at p = 3)
  योगः-२ : min (मानम् 2 12 ०<१२) (मानम् 2 18 ०<१८) + max (मानम् 2 12 ०<१२) (मानम् 2 18 ०<१८) ≡ 3
  योगः-२ = refl

  योगः-३ : min (मानम् 3 12 ०<१२) (मानम् 3 18 ०<१८) + max (मानम् 3 12 ०<१२) (मानम् 3 18 ०<१८) ≡ 3
  योगः-३ = refl
