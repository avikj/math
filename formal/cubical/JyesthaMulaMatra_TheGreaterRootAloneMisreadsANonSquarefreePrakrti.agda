{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- JyesthaMulaMatra_TheGreaterRootAloneMisreadsANonSquarefreePrakrti
--
-- वर्गप्रकृति (varga-prakṛti), `x² − N y² = 1`.  Brahmagupta,
-- *Brhmasphuasiddhnta*, ch. 18 (Kuakdhyya), 628 CE, states the
-- भावना (bhāvanā) composition law and names the parts:
--
--   प्रकृति    prakṛti       the multiplier N
--   ज्येष्ठमूल  jyeṣṭha-mūla  the GREATER root, x
--   कनिष्ठमूल  kaniṣṭha-mūla the LESSER root, y
--   क्षेप      kṣepa         the interpolator (here 1)
--
-- The cyclic method चक्रवाल (cakravāla), which produces a least solution
-- for every non-square prakti: Jayadeva (~950, surviving only in
-- Udayadivkara's commentary *Sundar*), in full with worked praktis
-- 61, 67, 103 in Bhskara II, *Bjagaita*, 1150.  "Pell's equation" is
-- Euler's misattribution, ~1730; see notes/NOT_PELL_IT_IS_VARGAPRAKRITI.md (absent from this repository).
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS MODULE IS FOR
--
-- `collab/swarm/2026-08-14/swarm-0814-08-chebyshev-weight-pell.md` (absent from this repository) §3
-- gives a search-free test for whether a solution is the least one:
--
--   (x,y) is least  ⟺  for no prime p < B is there an integer u ≥ 2
--                       with T_p(u) = x AND (u²−1)/N a perfect square,
--   where B = log(2x)/log(2+√N).
--
-- Its §8 asks:
--
--   "is the side condition `(u²−1)/N a perfect square` redundant? …
--    the missing step is integrality.  If N | u²−1 always follows, the
--    criterion becomes a pure one-variable root extraction with no
--    arithmetic side condition."
--
-- IT DOES NOT FOLLOW, and the counterexample lies INSIDE the criterion's
-- own bound, so it is not repaired by tightening B.
--
--   prakṛti N = 28 = 2²·7,  jyeṣṭha 127, kaniṣṭha 24,  p = 2,  u = 8.
--
--   127² = 28·24² + 1;  T₂(8) = 127;  28 ∤ 63 = 8²−1;  and (127,24) is
--   the LEAST solution.  B = log(254)/log(2+√28) = 2.7872…, so p = 2 is
--   admissible.  The criterion with the side condition deleted answers
--   NOT LEAST on a solution that IS least.
--
-- Two further instances are carried so the phenomenon is not read off
-- one number, and so that it cannot be dismissed as a p = 2 artifact:
--
--   N = 45 = 3²·5,  jyeṣṭha 161,  kaniṣṭha 24,  p = 2, u = 9, B = 2.6681…
--   N = 175 = 5²·7, jyeṣṭha 2024, kaniṣṭha 153, p = 3, u = 8, B = 3.0500…
--
-- WHY, exhibited: the p-th root is not missing, it is in a LARGER order.
-- √28 = 2√7, so ℤ[√28] = ℤ + 2ℤ[√7] has conductor 2 in ℤ[√7]; and
-- √45 = 3√5, conductor 3 in ℤ[√5].
--
--   8² = 7·3² + 1                     (8+3√7 has norm 1 in ℤ[√7])
--   8·8 + 7·(3·3) = 127               bhāvanā, greater root
--   8·3 + 3·8    = 48 = 2·24          bhāvanā, lesser root
--
-- so (8+3√7)² = 127 + 48√7 = 127 + 24√28.  The root 8+3√7 lies in ℤ[√7]
-- and NOT in ℤ[√28].  Its trace 16 is an integer either way — which is
-- the mechanism: `T_p(u) = x` constrains the TRACE alone, and a trace
-- cannot see which order its element inhabits.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED HERE
--
--   ==refl, ≢from, and-fst/snd, All≤, All≤-sound
--                        a bounded universal quantifier WITH its
--                        soundness lemma, so a `refl` on the fold is a
--                        proof over the whole range and not a sample
--   sq-mono              m ≤ n → m·m ≤ n·n
--   target-mono          y ≤ Y → N y² + 1 ≤ N Y² + 1
--   root-bound           a square equal to a target with y ≤ Y has root
--                        ≤ xmax, given (xmax+1)² > target N Y
--   least-solution       the generic statement: grid true + range bound
--                        ⇒ no solution with 1 ≤ y ≤ Y
--   ∤-scan, ∤-from       non-divisibility, certified once and reused:
--                        N·n ≡ M with N ≥ 1 forces n ≤ M, so the
--                        cofactor search is finite and exhaustive
--   least-28/45/175      the three instances
--   vargaprakrti-*       the solutions themselves
--   chebyshev-*          T over ℤ by its own recurrence, at the
--                        witnesses: T₂(8)=127, T₂(9)=161, T₃(8)=2024
--   prakrti-∤-*          28 ∤ 63, 45 ∤ 80, 175 ∤ 63, so the side
--                        condition fails non-integrally, not merely
--                        non-squarely
--   lesser-1/2-not-in    at N = 175 the CUBE is the first power to enter
--                        the small order: 5 divides neither 3 nor 48
--   grid-is-live-*       KNOWN-FALSE CONTROL: widened to reach the real
--                        solution the same search returns `false`, so
--                        the `true` above is not vacuous
------------------------------------------------------------------------

module JyesthaMulaMatra_TheGreaterRootAloneMisreadsANonSquarefreePrakrti where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; ·-comm ; +-comm ; ·-identityˡ)
open import Cubical.Data.Nat.Order
  using (_≤_ ; _<_ ; ≤-·k ; ≤-+k ; ≤-antisym ; ≤-trans ; <≤-trans ; ≤-split
        ; pred-≤-pred ; ≤0→≡0 ; splitℕ-≤ ; ¬m<m)
open import Cubical.Data.Int using (ℤ ; pos) renaming (_-_ to _-ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; true≢false)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Agda.Builtin.Nat using (_==_)

------------------------------------------------------------------------
-- 0.  Boolean scaffolding: decisions turned into propositions
------------------------------------------------------------------------

==refl : (n : ℕ) → (n == n) ≡ true
==refl zero    = refl
==refl (suc n) = ==refl n

≢from : (m n : ℕ) → (m == n) ≡ false → ¬ (m ≡ n)
≢from m n q p = true≢false (sym (==refl m) ∙ cong (m ==_) p ∙ q)

and-fst : (a b : Bool) → (a and b) ≡ true → a ≡ true
and-fst true  b p = refl
and-fst false b p = ⊥.rec (true≢false (sym p))

and-snd : (a b : Bool) → (a and b) ≡ true → b ≡ true
and-snd true  b p = p
and-snd false b p = ⊥.rec (true≢false (sym p))

-- A bounded universal quantifier, and the fact that its `true` really
-- means "at every point of the range".  Without All≤-sound a `refl` on
-- the fold would be a sample; with it, the fold is a finite exhaustive
-- verification, which CLAUDE.md (absent from this repository) counts as proof.
All≤ : (ℕ → Bool) → ℕ → Bool
All≤ f zero    = f zero
All≤ f (suc n) = f (suc n) and All≤ f n

All≤-sound : (f : ℕ → Bool) (n : ℕ) → All≤ f n ≡ true
           → (k : ℕ) → k ≤ n → f k ≡ true
All≤-sound f zero    h k k≤n  = subst (λ z → f z ≡ true) (sym (≤0→≡0 k≤n)) h
All≤-sound f (suc n) h k k≤sn with ≤-split k≤sn
... | inr k≡sn = subst (λ z → f z ≡ true) (sym k≡sn) (and-fst _ _ h)
... | inl k<sn = All≤-sound f n (and-snd _ _ h) k (pred-≤-pred k<sn)

------------------------------------------------------------------------
-- 1.  Order scaffolding
------------------------------------------------------------------------

-- `a ≤ b` for literals, from a witness the caller supplies
lit≤ : (a b k : ℕ) → k + a ≡ b → a ≤ b
lit≤ a b k p = k , p

clash : (a b : ℕ) → a ≤ b → b ≤ a → (a == b) ≡ false → ⊥
clash a b p q d = ≢from a b d (≤-antisym p q)

sq-mono : (m n : ℕ) → m ≤ n → (m · m) ≤ (n · n)
sq-mono m n h =
  ≤-trans (subst ((m · m) ≤_) (·-comm n m) (≤-·k {k = m} h))
          (≤-·k {k = n} h)

------------------------------------------------------------------------
-- 1½.  Non-divisibility, certified once and reused
------------------------------------------------------------------------

-- If N ≥ 1 and N·n ≡ M then n ≤ M, so the cofactor search is finite.
∤-scan : ℕ → ℕ → Bool
∤-scan N M = All≤ (λ n → not ((N · n) == M)) M

∤-from : (N M : ℕ) → 1 ≤ N → ∤-scan N M ≡ true
       → ¬ (Σ[ n ∈ ℕ ] N · n ≡ M)
∤-from N M hN g (n , p) = true≢false (sym q ∙ cong not r)
  where
    nbound : n ≤ M
    nbound = subst (n ≤_) p (subst (_≤ (N · n)) (·-identityˡ n) (≤-·k {k = n} hN))
    q : not ((N · n) == M) ≡ true
    q = All≤-sound (λ z → not ((N · z) == M)) M g n nbound
    r : ((N · n) == M) ≡ true
    r = cong ((N · n) ==_) (sym p) ∙ ==refl (N · n)

------------------------------------------------------------------------
-- 2.  The generic least-solution certificate
------------------------------------------------------------------------

-- the quantity under test: N y² + 1, which a greater root must square to
target : ℕ → ℕ → ℕ
target N y = N · (y · y) + 1

row : ℕ → ℕ → ℕ → Bool
row N xmax y = All≤ (λ x → not ((x · x) == target N y)) xmax

-- y runs over 1 … suc m
grid : ℕ → ℕ → ℕ → Bool
grid N xmax m = All≤ (λ y → row N xmax (suc y)) m

target-mono : (N Y y : ℕ) → y ≤ Y → target N y ≤ target N Y
target-mono N Y y h =
  ≤-+k (subst2 _≤_ (·-comm (y · y) N) (·-comm (Y · Y) N)
                   (≤-·k {k = N} (sq-mono y Y h)))

root-bound : (N xmax Y x y : ℕ)
           → target N Y < (suc xmax) · (suc xmax)
           → y ≤ Y → x · x ≡ target N y → x ≤ xmax
root-bound N xmax Y x y wide hy p with splitℕ-≤ x xmax
... | inl x≤xmax = x≤xmax
... | inr xmax<x =
  ⊥.rec (¬m<m (<≤-trans wide
                 (≤-trans (subst ((suc xmax · suc xmax) ≤_) p
                                 (sq-mono (suc xmax) x xmax<x))
                          (target-mono N Y y hy))))

-- THE STATEMENT: a true grid plus a range bound is a proof that no
-- lesser root in 1 … suc m solves the equation.
least-solution : (N xmax m : ℕ)
               → grid N xmax m ≡ true
               → target N (suc m) < (suc xmax) · (suc xmax)
               → (x y : ℕ) → 1 ≤ y → y ≤ suc m → ¬ (x · x ≡ target N y)
least-solution N xmax m g wide x zero h1 h2 p =
  ⊥.rec (≢from 1 0 refl (≤-antisym h1 (lit≤ 0 1 1 refl)))
least-solution N xmax m g wide x (suc y) h1 h2 p = true≢false (sym q ∙ cong not r)
  where
    q : not ((x · x) == target N (suc y)) ≡ true
    q = All≤-sound (λ z → not ((z · z) == target N (suc y))) xmax
          (All≤-sound (λ z → row N xmax (suc z)) m g y (pred-≤-pred h2))
          x (root-bound N xmax (suc m) x (suc y) wide h2 p)
    r : ((x · x) == target N (suc y)) ≡ true
    r = cong ((x · x) ==_) (sym p) ∙ ==refl (x · x)

------------------------------------------------------------------------
-- 3.  Chebyshev of the first kind, over ℤ, by its own recurrence
------------------------------------------------------------------------

-- T₀ = 1, T₁ = u, T_{n+2} = 2u·T_{n+1} − T_n.  No norm-one hypothesis
-- enters the definition; the recurrence is a fact about ℤ[X].
cheb : ℤ → ℕ → ℤ
cheb u zero          = pos 1
cheb u (suc zero)    = u
cheb u (suc (suc n)) = ((pos 2 ·ℤ u) ·ℤ cheb u (suc n)) -ℤ cheb u n

------------------------------------------------------------------------
-- 4.  प्रकृति 28 = 2²·7 — the witness
------------------------------------------------------------------------

vargaprakrti-28 : 127 · 127 ≡ target 28 24
vargaprakrti-28 = refl

chebyshev-two-at-eight : cheb (pos 8) 2 ≡ pos 127
chebyshev-two-at-eight = refl

grid-28 : grid 28 121 22 ≡ true
grid-28 = refl

-- 14813 = target 28 23 < 14884 = 122²
wide-28 : target 28 23 < (suc 121) · (suc 121)
wide-28 = lit≤ 14814 14884 70 refl

least-28 : (x y : ℕ) → 1 ≤ y → y ≤ 23 → ¬ (x · x ≡ target 28 y)
least-28 = least-solution 28 121 22 grid-28 wide-28

-- the side condition: (u²−1)/N is not even an integer, since 28 ∤ 63
prakrti-∤-28 : ¬ (Σ[ n ∈ ℕ ] 28 · n ≡ 63)
prakrti-∤-28 = ∤-from 28 63 (lit≤ 1 28 27 refl) refl

------------------------------------------------------------------------
-- 5.  प्रकृति 45 = 3²·5 — the second instance
------------------------------------------------------------------------

vargaprakrti-45 : 161 · 161 ≡ target 45 24
vargaprakrti-45 = refl

chebyshev-two-at-nine : cheb (pos 9) 2 ≡ pos 161
chebyshev-two-at-nine = refl

grid-45 : grid 45 155 22 ≡ true
grid-45 = refl

-- 23806 = target 45 23 < 24336 = 156²
wide-45 : target 45 23 < (suc 155) · (suc 155)
wide-45 = lit≤ 23807 24336 529 refl

least-45 : (x y : ℕ) → 1 ≤ y → y ≤ 23 → ¬ (x · x ≡ target 45 y)
least-45 = least-solution 45 155 22 grid-45 wide-45

prakrti-∤-45 : ¬ (Σ[ n ∈ ℕ ] 45 · n ≡ 80)
prakrti-∤-45 = ∤-from 45 80 (lit≤ 1 45 44 refl) refl

------------------------------------------------------------------------
-- 5½.  प्रकृति 175 = 5²·7 at p = 3 — the failure is not a p = 2 artifact
------------------------------------------------------------------------

-- 8 + 3√7 again, but now it is the CUBE that lands in the small order:
-- the lesser roots of its powers are 3, 48, 765, and 5 divides only the
-- third.  So ε₁(175) = (8+3√7)³ = 2024 + 765√7 = 2024 + 153√175.
-- B = log(4048)/log(2+√175) = 3.0500…, so p = 3 is admissible.

vargaprakrti-175 : 2024 · 2024 ≡ target 175 153
vargaprakrti-175 = refl

chebyshev-three-at-eight : cheb (pos 8) 3 ≡ pos 2024
chebyshev-three-at-eight = refl

grid-175 : grid 175 2010 151 ≡ true
grid-175 = refl

-- 4043201 = target 175 152 < 4044121 = 2011²
wide-175 : target 175 152 < (suc 2010) · (suc 2010)
wide-175 = lit≤ 4043202 4044121 919 refl

least-175 : (x y : ℕ) → 1 ≤ y → y ≤ 152 → ¬ (x · x ≡ target 175 y)
least-175 = least-solution 175 2010 151 grid-175 wide-175

-- 175 ∤ 63 for the trivial reason that 175 > 63 > 0
prakrti-∤-175 : ¬ (Σ[ n ∈ ℕ ] 175 · n ≡ 63)
prakrti-∤-175 = ∤-from 175 63 (lit≤ 1 175 174 refl) refl

-- the lesser root of the cube: b₃ = b·U₂(a), with U₂(8) = 4·8²−1 = 255
U2-at-8 : 4 · (8 · 8) ≡ 255 + 1
U2-at-8 = refl

cube-lesser-7 : 3 · 255 ≡ 5 · 153
cube-lesser-7 = refl

-- and 5 divides neither of the two earlier lesser roots, which is why
-- the cube and not the square is the first to enter ℤ[√175]
lesser-1-not-in : ¬ (Σ[ n ∈ ℕ ] 5 · n ≡ 3)
lesser-1-not-in = ∤-from 5 3 (lit≤ 1 5 4 refl) refl

lesser-2-not-in : ¬ (Σ[ n ∈ ℕ ] 5 · n ≡ 48)
lesser-2-not-in = ∤-from 5 48 (lit≤ 1 5 4 refl) refl

------------------------------------------------------------------------
-- 6.  KNOWN-FALSE CONTROL — the search is not vacuous
------------------------------------------------------------------------

-- Widen the row until it can reach the real greater root and the same
-- fold returns `false`.  A search that could only ever say `true` would
-- prove nothing; these two lines are what make §4–§5 informative.
grid-is-live-28 : All≤ (λ x → not ((x · x) == target 28 24)) 127 ≡ false
grid-is-live-28 = refl

grid-is-live-28′ : All≤ (λ x → not ((x · x) == target 28 24)) 126 ≡ true
grid-is-live-28′ = refl

grid-is-live-45 : All≤ (λ x → not ((x · x) == target 45 24)) 161 ≡ false
grid-is-live-45 = refl

grid-is-live-45′ : All≤ (λ x → not ((x · x) == target 45 24)) 160 ≡ true
grid-is-live-45′ = refl

------------------------------------------------------------------------
-- 7.  The p-th root, exhibited in the larger order
------------------------------------------------------------------------

-- 8 + 3√7 has norm one in ℤ[√7]; 9 + 4√5 has norm one in ℤ[√5].
root-order-7 : 8 · 8 ≡ 7 · (3 · 3) + 1
root-order-7 = refl

root-order-5 : 9 · 9 ≡ 5 · (4 · 4) + 1
root-order-5 = refl

-- Brahmagupta's भावना of a root with itself:
--   greater ↦ ac + N bd,   lesser ↦ ad + bc
-- and the lesser root comes out divisible by the conductor.
bhavana-square-7-greater : 8 · 8 + 7 · (3 · 3) ≡ 127
bhavana-square-7-greater = refl

bhavana-square-7-lesser : 8 · 3 + 3 · 8 ≡ 2 · 24
bhavana-square-7-lesser = refl

bhavana-square-5-greater : 9 · 9 + 5 · (4 · 4) ≡ 161
bhavana-square-5-greater = refl

bhavana-square-5-lesser : 9 · 4 + 4 · 9 ≡ 3 · 24
bhavana-square-5-lesser = refl

-- The traces are integers on both sides of the conductor, which is why
-- a trace-only criterion cannot separate the two orders.
trace-7 : 8 + 8 ≡ 16
trace-7 = refl

trace-5 : 9 + 9 ≡ 18
trace-5 = refl
