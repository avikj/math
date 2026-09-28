{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CakravalaBound — why the wheel does not run away: |k| stays below 2√D.
--
-- SOURCE AND PRIORITY.  The cakravla ("cycle", "wheel") is stated by
-- JAYADEVA (~950 CE, surviving only through Udayadivkara's Sundar,
-- 1073) and given in full by BHSKARA II, Bjagaita, 1150 CE.  Its
-- choice rule — among the m satisfying k | (a + bm), take one minimising
-- |m² − D| — is not a heuristic for speed.  It is what keeps the interim
-- k's inside a fixed window, and a window is what turns an unbounded
-- search into a wheel that must come round.  Lagrange proves an analogous
-- termination for continued fractions in 1768, six hundred years later
-- and for a different algorithm.
--
-- Toward termination of the cycle, this file proves the bite the
-- classical argument takes: the BOUND.  Everything below is exact — no measurement, no fitting, no
-- floating point, no appeal to a run.
--
-- THE CLASSICAL STATEMENT, and the one proved here.  Write K = |k|,
-- K' = |k'|, so that the descent's k' = (m² − D)/k has K·K' = |m² − D|.
-- Then Bhskara's choice preserves
--
--                          k² ≤ 4D,          i.e.  |k| ≤ 2√D,
--
-- and preserves it STRICTLY: from k² ≤ 4D one gets k'² < 4D.  The
-- quantitative form actually proved is sharper,
--
--                        16·k'²  ≤  36·D          (i.e. |k'| ≤ (3/2)√D),
--
-- which is the classical |k'| ≤ √D + |k|/4 evaluated at |k| ≤ 2√D.
--
-- NO SQUARE ROOTS ANYWHERE.  "√D" never appears.  Every inequality is
-- between naturals, and the two halves of "m is within |k|/2 of √D" are
-- written as the pair of integer inequalities
--
--        (2m − K)² ≤ 4D          4D ≤ (2m + K)²
--
-- with the first stated subtraction-free as A·A ≤ 4D together with
-- A + K ≡ 2m  or  A + 2m ≡ K  (i.e. A = |2m − K|), which is the same
-- clearing of monus that `BhavanaSemiring` and `CakravalaNat` perform for
-- the composition law.  Nothing here needs ℤ, and cubical's ℤ product is
-- unary, so ℕ is also the only substrate on which this computes.
--
-- WHAT IS PROVED.
--
--   amgm            2xy ≤ x² + y², the one analytic fact used.
--   straddleBound   THE INEQUALITY.  If A = |2m − K| with A² ≤ 4D and
--                   4D ≤ (2m + K)², and K² ≤ 4D, and E = |m² − D|, then
--                        16·E²  ≤  36·D·K².
--                   Four cases (sign of m² − D, orientation of 2m − K);
--                   each produces  4E ≤ K·S  with  S² ≤ 36D, and the
--                   squaring is then one lemma.
--   straddleExists  THE CANDIDATE EXISTS, in the congruence class Bhskara
--                   is handed.  For 1 ≤ r ≤ K there is j with
--                   m = r + jK straddling: this is a least-witness search,
--                   `firstHit`, and is constructive — it computes the j.
--   kBoundSharp     THE SHARP FORM, K² cancelled off:  16·K'² ≤ 36·D.
--   cakravalaKBound THE INVARIANT.  Assuming only Bhskara's rule as
--                   stated (E_s = |m*² − D| is minimal over the class) and
--                   K·K' = E_s, one gets K'² < 4D from K² ≤ 4D.
--   seedBound       THE SEED IS INSIDE THE WINDOW.  For n = ⌊√D⌋ and
--                   E = D − n², E² ≤ 4D.  So the invariant holds at turn 0
--                   and `cakravalaKBound` carries it forever.
--   ZBridge.stepAbs THE BRIDGE to `CakravalaDescent`'s ℤ statement.  The
--                   hypothesis `Es ≡ K·K'` is not an assumption about the
--                   world: it is m² − D = k·k' read through | · |, i.e.
--                   `abs·`, and it is discharged here rather than asserted
--                   in a comment.  `ZBridge.cakravalaKBoundℤ` then states
--                   the invariant in the descent's own variables.
--   seed61          D = 61, Bhskara's own example, instantiated.
--
-- AND ONE REFUTATION, §7.  The bound is sharp enough to catch a false
-- claim already in this repository.  `CakravalaWitness.agda` and
-- `machine/NalandaEmit.hs` (absent from this repository) both state that every m in the D = 61 run is
-- the one Bhskara's rule selects.  At turn 7 (|k| = 1, m = 7) it is not:
-- |8² − 61| = 3 beats |7² − 61| = 12, and `machine/Nalanda.hs` (absent from this repository) line 167
-- special-cases |k| = 1 to return ⌊√D⌋ instead of minimising.  §7 checks
-- both candidates in the kernel and proves 16·12² > 36·61, so no
-- rule-obeying m could have produced that turn's |k'|.  The run is still
-- sound — any m satisfying the congruence descends — but the attribution
-- is wrong.
--
--   * MINIMALITY OF BHSKARA'S CHOICE is a HYPOTHESIS of
--     `cakravalaKBound`, discharged by whoever runs the algorithm.  What is
--     proved is that minimality suffices.
--   * The choice rule is used only through the inequality E_s ≤ E for the
--     one straddling candidate `straddleExists` builds.  So the theorem is
--     really about ANY rule that beats that candidate, and Bhskara's is
--     the simplest such.
--   * The constant 36 is 4·(1 + 1/2)², the value of the classical
--     |k'| ≤ √D + K/4 at K = 2√D; iterating the same estimate drives it
--     toward 4·(4/3)² = 64/9.  All §4 needs is 36 < 64.
--   * `1 ≤ r ≤ K` is a normalisation of the congruence class, not a
--     restriction: every class mod K has such a representative.
------------------------------------------------------------------------

module CakravalaBound where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-comm ; +-assoc ; ·-comm ; inj-m+)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Cubical.Tactics.NatSolver.Reflection using (solveℕ!)

------------------------------------------------------------------------
-- 0.  Polynomial identities.  Each is a commutative-semiring identity in
-- its own variables, so `solve` discharges it and no induction, ordering
-- or subtraction appears.  They are collected here so that the
-- inequalities below read as inequalities and not as algebra.
------------------------------------------------------------------------

private
  idAmGmL : (x d : ℕ) → x · x + (d + x) · (d + x) ≡ 2 · (x · (d + x)) + d · d
  idAmGmL x d = solveℕ!

  idAmGmR : (y d : ℕ) → (d + y) · (d + y) + y · y ≡ 2 · ((d + y) · y) + d · d
  idAmGmR y d = solveℕ!

  idMulSq : (K S : ℕ) → (K · S) · (K · S) ≡ (K · K) · (S · S)
  idMulSq K S = solveℕ!

  idFourSq : (E : ℕ) → (4 · E) · (4 · E) ≡ 16 · (E · E)
  idFourSq E = solveℕ!

  idFinal : (K D : ℕ) → (K · K) · (36 · D) ≡ 36 · (D · (K · K))
  idFinal K D = solveℕ!

  -- (2m + K)² + 4E ≡ (4m² + 4E) + K·(4m + K)
  idHi : (m K E : ℕ) → (2 · m + K) · (2 · m + K) + 4 · E
                     ≡ (4 · (m · m) + 4 · E) + K · (4 · m + K)
  idHi m K E = solveℕ!

  -- (A + K)² ≡ A² + K·(2A + K)
  idLo : (A K : ℕ) → (A + K) · (A + K) ≡ A · A + K · (2 · A + K)
  idLo A K = solveℕ!

  -- (A + 2m)² ≡ (A² + 4Am) + 4m²
  idAlt : (A m : ℕ) → (A + 2 · m) · (A + 2 · m) ≡ (A · A + 4 · (A · m)) + 4 · (m · m)
  idAlt A m = solveℕ!

  idSsqA : (A K : ℕ) → (2 · A + K) · (2 · A + K)
                     ≡ 4 · (A · A) + (4 · (A · K) + K · K)
  idSsqA A K = solveℕ!

  idSsqB : (m K : ℕ) → (4 · m + K) · (4 · m + K)
                     ≡ 16 · (m · m) + (8 · (m · K) + K · K)
  idSsqB m K = solveℕ!

  id36 : (D : ℕ) → 16 · D + (16 · D + 4 · D) ≡ 36 · D
  id36 D = solveℕ!

  id4·4 : (D : ℕ) → 4 · (4 · D) ≡ 16 · D
  id4·4 D = solveℕ!

  idFourDist : (D E : ℕ) → 4 · (D + E) ≡ 4 · D + 4 · E
  idFourDist D E = solveℕ!

  idTwoM : (m : ℕ) → (2 · m) · (2 · m) ≡ 4 · (m · m)
  idTwoM m = solveℕ!

  id2·8 : (x : ℕ) → 2 · (2 · x) ≡ 4 · x
  id2·8 x = solveℕ!

  id2·4 : (x : ℕ) → 2 · (4 · x) ≡ 8 · x
  id2·4 x = solveℕ!

  id2·2m : (m K : ℕ) → 2 · ((2 · m) · K) ≡ 4 · (m · K)
  id2·2m m K = solveℕ!

  id2·8D : (D : ℕ) → 2 · (8 · D) ≡ 16 · D
  id2·8D D = solveℕ!

  id4+4 : (D : ℕ) → 4 · D + 4 · D ≡ 8 · D
  id4+4 D = solveℕ!

  id64 : (D : ℕ) → 16 · (4 · D) ≡ 64 · D
  id64 D = solveℕ!

  id4to36 : (D : ℕ) → 32 · D + 4 · D ≡ 36 · D
  id4to36 D = solveℕ!

  idSuc· : (r K x : ℕ) → r + (K + x) ≡ (r + x) + K
  idSuc· r K x = solveℕ!

  idStrad : (m K : ℕ) → (2 · (m + K) ) ≡ (2 · m + K) + K
  idStrad m K = solveℕ!

  idSeed : (n : ℕ) → (n + 1) · (n + 1) ≡ n · n + (2 · n + 1)
  idSeed n = solveℕ!

  idPull16 : (K x : ℕ) → 16 · ((K · K) · x) ≡ (K · K) · (16 · x)
  idPull16 K x = solveℕ!

  idTwoN : (n : ℕ) → (2 · n) · (2 · n) ≡ 4 · (n · n)
  idTwoN n = solveℕ!

------------------------------------------------------------------------
-- 1.  Order toolkit.  Cubical ships ≤-·k but not its mirror, the square
-- monotonicity, or cancellation, so they are built here.
------------------------------------------------------------------------

private
  ≤-k·' : {m n : ℕ} (k : ℕ) → m ≤ n → k · m ≤ k · n
  ≤-k·' {m} {n} k h = subst2 _≤_ (·-comm m k) (·-comm n k) (≤-·k {k = k} h)

  sq≤ : {m n : ℕ} → m ≤ n → m · m ≤ n · n
  sq≤ {m} {n} h = ≤-trans (≤-·k {k = m} h) (≤-k·' n h)

  -- 2xy ≤ x² + y².  The single inequality with any content in this file;
  -- everything else is bookkeeping around it.
  amgm : (x y : ℕ) → 2 · (x · y) ≤ x · x + y · y
  amgm x y with splitℕ-≤ x y
  ... | inl (d , hd) =
        subst (λ w → 2 · (x · w) ≤ x · x + w · w) hd
              (subst (2 · (x · (d + x)) ≤_) (sym (idAmGmL x d)) ≤SumLeft)
  ... | inr y<x =
        let (d , hd) = <-weaken y<x
        in subst (λ w → 2 · (w · y) ≤ w · w + y · y) hd
                 (subst (2 · ((d + y) · y) ≤_) (sym (idAmGmR y d)) ≤SumLeft)

  -- from  P ≤ Q  and  Q + X ≡ P + Y  conclude  X ≤ Y
  shiftLe : (P Q X Y : ℕ) → P ≤ Q → Q + X ≡ P + Y → X ≤ Y
  shiftLe P Q X Y (c , hc) e = c , inj-m+ {m = P} step
    where
    assoc1 : P + (c + X) ≡ Q + X
    assoc1 = +-assoc P c X ∙ cong (_+ X) (+-comm P c) ∙ cong (_+ X) hc

    step : P + (c + X) ≡ P + Y
    step = assoc1 ∙ e

  -- 1 ≤ c gives a predecessor, which is what the strict-monotone lemmas want
  posPred : (c : ℕ) → 1 ≤ c → Σ[ c' ∈ ℕ ] c ≡ suc c'
  posPred c (k , hk) = k , sym hk ∙ +-comm k 1

  ·-cancel-≤ : (c x y : ℕ) → 1 ≤ c → c · x ≤ c · y → x ≤ y
  ·-cancel-≤ c x y hc h with splitℕ-≤ x y
  ... | inl p = p
  ... | inr y<x =
        let (c' , hc') = posPred c hc
            stepA : y · suc c' < x · suc c'
            stepA = <-·sk y<x
            stepB : c · y < c · x
            stepB = subst2 _<_ (·-comm y (suc c') ∙ cong (_· y) (sym hc'))
                               (·-comm x (suc c') ∙ cong (_· x) (sym hc'))
                               stepA
        in ⊥rec (¬m<m (<≤-trans stepB h))

  ·-cancel-< : (c x y : ℕ) → 1 ≤ c → c · x < c · y → x < y
  ·-cancel-< c x y hc h with splitℕ-< x y
  ... | inl p = p
  ... | inr y≤x =
        ⊥rec (¬m<m (<≤-trans h (≤-k·' c y≤x)))

------------------------------------------------------------------------
-- 2.  THE INEQUALITY.
--
-- Given a candidate m that STRADDLES √D at scale K — meaning
-- (2m − K)² ≤ 4D ≤ (2m + K)², the integer form of |m − √D| ≤ K/2 — and
-- given that the previous k already satisfies K² ≤ 4D, the discriminant
-- E = |m² − D| obeys  16E² ≤ 36·D·K².  Dividing by K² (done in §4) this
-- is |m² − D| / K ≤ (3/2)√D, the classical bound.
--
-- Four cases, and they are the four cells of a genuinely two-dimensional
-- split: the sign of m² − D, and the orientation of 2m − K.  Each cell
-- produces the SAME shape, 4E ≤ K·S with S² ≤ 36D, and `coreBound`
-- squares it once for all four.
------------------------------------------------------------------------

coreBound : (D K S E : ℕ) → 4 · E ≤ K · S → S · S ≤ 36 · D
          → 16 · (E · E) ≤ 36 · (D · (K · K))
coreBound D K S E h1 h2 =
  subst (_≤ 36 · (D · (K · K))) (idFourSq E)
        (≤-trans (sq≤ h1)
                 (subst2 _≤_ (sym (idMulSq K S)) (idFinal K D)
                             (≤-k·' (K · K) h2)))

straddleBound : (D K m A E : ℕ)
  → K · K ≤ 4 · D                                    -- |k| ≤ 2√D coming in
  → A · A ≤ 4 · D                                    -- (2m − K)² ≤ 4D
  → (A + K ≡ 2 · m) ⊎ (A + 2 · m ≡ K)                -- A = |2m − K|
  → 4 · D ≤ (2 · m + K) · (2 · m + K)                -- 4D ≤ (2m + K)²
  → (m · m ≡ D + E) ⊎ (D ≡ m · m + E)                -- E = |m² − D|
  → 16 · (E · E) ≤ 36 · (D · (K · K))

-- CASE m² ≤ D.  Only the upper straddle is used; A plays no part.
straddleBound D K m A E hK hA hAK hHi (inr hD) =
  coreBound D K (4 · m + K) E h4E hS
  where
  mmD : m · m ≤ D
  mmD = E , (+-comm E (m · m) ∙ sym hD)

  h4E : 4 · E ≤ K · (4 · m + K)
  h4E = shiftLe (4 · D) ((2 · m + K) · (2 · m + K)) (4 · E) (K · (4 · m + K))
                hHi
                ( idHi m K E
                ∙ cong (_+ K · (4 · m + K))
                       (sym (idFourDist (m · m) E) ∙ cong (4 ·_) (sym hD)) )

  b1 : 16 · (m · m) ≤ 16 · D
  b1 = ≤-k·' 16 mmD

  -- 2·(2m)·K ≤ (2m)² + K², rewritten with the squares expanded
  b0 : 4 · (m · K) ≤ 4 · (m · m) + K · K
  b0 = subst2 _≤_ (id2·2m m K) (cong (_+ K · K) (idTwoM m)) (amgm (2 · m) K)

  b4mK : 4 · (m · K) ≤ 8 · D
  b4mK = subst (4 · (m · K) ≤_) (id4+4 D)
               (≤-trans b0 (≤-+-≤ (≤-k·' 4 mmD) hK))

  b2 : 8 · (m · K) ≤ 16 · D
  b2 = subst2 _≤_ (id2·4 (m · K)) (id2·8D D) (≤-k·' 2 b4mK)

  hS : (4 · m + K) · (4 · m + K) ≤ 36 · D
  hS = subst2 _≤_ (sym (idSsqB m K)) (id36 D)
                  (≤-+-≤ b1 (≤-+-≤ b2 hK))

-- CASE m² ≥ D, with 2m ≥ K.  This is the cell where the sharp bound
-- |k'| ≤ √D + K/4 lives, and A = 2m − K is exactly the quantity the
-- straddle hypothesis controls.
straddleBound D K m A E hK hA (inl hAK) hHi (inl hD) =
  coreBound D K (2 · A + K) E h4E hS
  where
  h4E : 4 · E ≤ K · (2 · A + K)
  h4E = shiftLe (A · A) (4 · D) (4 · E) (K · (2 · A + K)) hA
                ( sym (idFourDist D E)
                ∙ cong (4 ·_) (sym hD)
                ∙ sym (idTwoM m)
                ∙ cong (λ w → w · w) (sym hAK)
                ∙ idLo A K )

  b2AK : 2 · (A · K) ≤ 8 · D
  b2AK = subst (2 · (A · K) ≤_) (id4+4 D) (≤-trans (amgm A K) (≤-+-≤ hA hK))

  b2 : 4 · (A · K) ≤ 16 · D
  b2 = subst2 _≤_ (id2·8 (A · K)) (id2·8D D) (≤-k·' 2 b2AK)

  b1 : 4 · (A · A) ≤ 16 · D
  b1 = subst (4 · (A · A) ≤_) (id4·4 D) (≤-k·' 4 hA)

  hS : (2 · A + K) · (2 · A + K) ≤ 36 · D
  hS = subst2 _≤_ (sym (idSsqA A K)) (id36 D)
                  (≤-+-≤ b1 (≤-+-≤ b2 hK))

-- CASE m² ≥ D, with 2m ≤ K.  Here the straddle collapses: the candidate
-- is so close to the origin that 4E ≤ K² outright, and S = K.
straddleBound D K m A E hK hA (inr hAK) hHi (inl hD) =
  coreBound D K K E h4E hS
  where
  h4E : 4 · E ≤ K · K
  h4E = ((A · A + 4 · (A · m)) + 4 · D)
      , ( sym (+-assoc (A · A + 4 · (A · m)) (4 · D) (4 · E))
        ∙ cong ((A · A + 4 · (A · m)) +_) (sym (idFourDist D E))
        ∙ cong ((A · A + 4 · (A · m)) +_) (cong (4 ·_) (sym hD))
        ∙ sym (idAlt A m)
        ∙ cong (λ w → w · w) hAK )

  hS : K · K ≤ 36 · D
  hS = ≤-trans hK (32 · D , id4to36 D)

------------------------------------------------------------------------
-- 3.  THE CANDIDATE EXISTS — and is computed, not assumed.
--
-- Bhskara is handed a congruence class mod |k| (the solutions m of
-- k | (a + bm), which RYABHAA's kuaka produces, ryabhaya
-- Gaṇitapāda 32–33, 499 CE) and told to minimise |m² − D| over it.  For
-- the bound of §2 to bite, the class must CONTAIN a straddling member.
-- It does, and the proof is a search that terminates by construction:
-- walk j = 0, 1, 2, … until 4D ≤ (2(r + jK) + K)²; the first j that
-- succeeds either is 0 — and then |2r − K| ≤ K does the job, because
-- 1 ≤ r ≤ K — or has a predecessor that failed, and the failure IS the
-- lower straddle.
--
-- `firstHit` is the whole search.  It recurses on the KNOWN upper bound
-- J, not on a measure, so `--safe` accepts it without a termination
-- argument, and it computes.
------------------------------------------------------------------------

private
  idMul1 : (x : ℕ) → x · 1 ≡ x
  idMul1 x = solveℕ!

  idTwoK : (K : ℕ) → 2 · K ≡ K + K
  idTwoK K = solveℕ!

  data FirstHit (P : ℕ → Type₀) : Type₀ where
    hit0   : P 0 → FirstHit P
    hitSuc : (j : ℕ) → P (suc j) → ¬ P j → FirstHit P

  firstHit : (P : ℕ → Type₀) → ((n : ℕ) → Dec (P n))
           → (J : ℕ) → P J → FirstHit P
  firstHit P dec zero    p = hit0 p
  firstHit P dec (suc J) p with dec J
  ... | yes q = firstHit P dec J q
  ... | no ¬q = hitSuc J p ¬q

  -- ¬ (x ≤ y) is a bad thing to reason with; this turns it into y ≤ x.
  ¬≤→≤ : (x y : ℕ) → ¬ (x ≤ y) → y ≤ x
  ¬≤→≤ x y h with splitℕ-≤ y x
  ... | inl p    = p
  ... | inr x<y  = ⊥rec (h (<-weaken x<y))

straddleExists : (D K r : ℕ)
  → 1 ≤ D → 1 ≤ K → 1 ≤ r → r ≤ K
  → K · K ≤ 4 · D
  → Σ[ j ∈ ℕ ] Σ[ A ∈ ℕ ]
       ( ((A + K ≡ 2 · (r + j · K)) ⊎ (A + 2 · (r + j · K) ≡ K))
       × ((A · A ≤ 4 · D)
       × (4 · D ≤ (2 · (r + j · K) + K) · (2 · (r + j · K) + K))) )
straddleExists D K r hD1 hK1 hr1 hrK hKK = go (firstHit P decP D PD)
  where
  M : ℕ → ℕ
  M j = r + j · K

  P : ℕ → Type₀
  P j = 4 · D ≤ (2 · M j + K) · (2 · M j + K)

  decP : (j : ℕ) → Dec (P j)
  decP j = ≤Dec (4 · D) ((2 · M j + K) · (2 · M j + K))

  -- D ≤ D·K ≤ r + D·K = M D, so 2D ≤ 2·M D + K, so 4D ≤ 4D² ≤ (2·M D+K)².
  D≤DK : D ≤ D · K
  D≤DK = subst (_≤ D · K) (idMul1 D) (≤-k·' D hK1)

  D≤MD : D ≤ M D
  D≤MD = ≤-trans D≤DK (≤SumRight {k = r})

  2D≤ : 2 · D ≤ 2 · M D + K
  2D≤ = ≤-trans (≤-k·' 2 D≤MD) (≤SumLeft {k = K})

  4D≤4DD : 4 · D ≤ 4 · (D · D)
  4D≤4DD = ≤-k·' 4 (subst (_≤ D · D) (idMul1 D) (≤-k·' D hD1))

  PD : P D
  PD = ≤-trans (subst (4 · D ≤_) (sym (idTwoN D)) 4D≤4DD) (sq≤ 2D≤)

  m0 : r + 0 · K ≡ r
  m0 = Cubical.Data.Nat.+-zero r

  go : FirstHit P
     → Σ[ j ∈ ℕ ] Σ[ A ∈ ℕ ]
         ( ((A + K ≡ 2 · (r + j · K)) ⊎ (A + 2 · (r + j · K) ≡ K))
         × ((A · A ≤ 4 · D)
         × (4 · D ≤ (2 · (r + j · K) + K) · (2 · (r + j · K) + K))) )
  go (hit0 p) with splitℕ-≤ (2 · r) K
  ... | inl (A , hA') =
        0 , A
          , inr (cong (λ w → A + 2 · w) m0 ∙ hA')
          , ≤-trans (sq≤ {n = K} (2 · r , +-comm (2 · r) A ∙ hA')) hKK
          , p
  ... | inr K<2r =
        let (A , hA') = <-weaken K<2r
            A≤K : A ≤ K
            A≤K = ≤-+k-cancel (subst2 _≤_ (sym hA') (idTwoK K) (≤-k·' 2 hrK))
        in 0 , A
             , inl (hA' ∙ sym (cong (2 ·_) m0))
             , ≤-trans (sq≤ A≤K) hKK
             , p
  go (hitSuc j p ¬q) =
        suc j , (2 · M j + K)
              , inl ( sym (idStrad (M j) K)
                    ∙ cong (2 ·_) (sym (idSuc· r K (j · K))) )
              , ¬≤→≤ (4 · D) ((2 · M j + K) · (2 · M j + K)) ¬q
              , p

------------------------------------------------------------------------
-- 4.  THE INVARIANT — |k| ≤ 2√D is preserved, and strictly.
--
-- This is the theorem the file exists for.  Read K = |k|, K' = |k'|,
-- E_s = |m*² − D| where m* is the m Bhskara's rule actually selects.
-- The descent's own equation k·k' = m*² − D says E_s = K·K'; that is the
-- hypothesis `Es ≡ K · K'`, and §5 shows it is exactly `abs·` applied to
-- `CakravalaDescent`'s conclusion.
--
-- The choice rule enters ONLY as `Es ≤ E` for the straddling candidate.
-- That is weaker than minimality over the class, and deliberately so:
-- the theorem is then true of any rule that beats the straddler, and
-- Bhskara's is the simplest such rule.
------------------------------------------------------------------------

-- |a − b| as a natural, with the case distinction that names its sign.
diffNat : (a b : ℕ) → Σ[ E ∈ ℕ ] ((a ≡ b + E) ⊎ (b ≡ a + E))
diffNat a b with splitℕ-≤ b a
... | inl (d , hd) = d , inl (sym hd ∙ +-comm d b)
... | inr a<b = let (d , hd) = <-weaken a<b in d , inr (sym hd ∙ +-comm d a)

-- THE SHARP FORM.  Cancelling K² off the inequality of §2 leaves
--   16·k'² ≤ 36·D,   i.e.   |k'| ≤ (3/2)√D.
-- This is what is actually proved; the window k'² < 4D below is its
-- consequence, and the one the induction wants because it is the same
-- shape as its own hypothesis.
kBoundSharp : (D K K' Es E : ℕ)
            → 1 ≤ K
            → Es ≡ K · K'
            → Es ≤ E
            → 16 · (E · E) ≤ 36 · (D · (K · K))
            → 16 · (K' · K') ≤ 36 · D
kBoundSharp D K K' Es E hK1 hEs hmin hbig =
  ·-cancel-≤ (K · K) (16 · (K' · K')) (36 · D) 1≤KK s3
  where
  1≤KK : 1 ≤ K · K
  1≤KK = subst (_≤ K · K) (idMul1 1) (sq≤ hK1)

  s2 : 16 · (Es · Es) ≤ 36 · (D · (K · K))
  s2 = ≤-trans (≤-k·' 16 (sq≤ hmin)) hbig

  s3 : (K · K) · (16 · (K' · K')) ≤ (K · K) · (36 · D)
  s3 = subst2 _≤_
         (cong (16 ·_) (cong₂ _·_ hEs hEs ∙ idMulSq K K') ∙ idPull16 K (K' · K'))
         (sym (idFinal K D))
         s2

kBound : (D K K' Es E : ℕ)
       → 1 ≤ D → 1 ≤ K
       → Es ≡ K · K'
       → Es ≤ E
       → 16 · (E · E) ≤ 36 · (D · (K · K))
       → K' · K' < 4 · D
kBound D K K' Es E hD1 hK1 hEs hmin hbig =
  ·-cancel-< 16 (K' · K') (4 · D) (15 , refl) final
  where
  s4 : 16 · (K' · K') ≤ 36 · D
  s4 = kBoundSharp D K K' Es E hK1 hEs hmin hbig

  36<64 : 36 · D < 64 · D
  36<64 = let (D' , hD') = posPred D hD1
          in subst (λ w → 36 · w < 64 · w) (sym hD') (<-·sk {m = 36} {n = 64} (27 , refl))

  final : 16 · (K' · K') < 16 · (4 · D)
  final = subst (16 · (K' · K') <_) (sym (id64 D)) (≤<-trans s4 36<64)

-- THE STEP OF THE WHEEL, BOUNDED.  Congruence class r mod K; Bhskara's
-- rule as `minim`; conclusion |k'| < 2√D.
cakravalaKBound :
    (D K r K' Es : ℕ)
  → 1 ≤ D → 1 ≤ K → 1 ≤ r → r ≤ K
  → K · K ≤ 4 · D
  → Es ≡ K · K'
  → ( (j E : ℕ)
      → ( ((r + j · K) · (r + j · K) ≡ D + E)
        ⊎ (D ≡ (r + j · K) · (r + j · K) + E) )
      → Es ≤ E )
  → K' · K' < 4 · D
cakravalaKBound D K r K' Es hD1 hK1 hr1 hrK hKK hEs minim =
  kBound D K K' Es E hD1 hK1 hEs (minim j E hE)
         (straddleBound D K (r + j · K) A E hKK hA hAK hHi hE)
  where
  str = straddleExists D K r hD1 hK1 hr1 hrK hKK

  j   = fst str
  A   = fst (snd str)
  hAK = fst (snd (snd str))
  hA  = fst (snd (snd (snd str)))
  hHi = snd (snd (snd (snd str)))

  dif = diffNat ((r + j · K) · (r + j · K)) D
  E   = fst dif
  hE  = snd dif

------------------------------------------------------------------------
-- 4b.  THE SEED IS ALREADY INSIDE THE WINDOW.
--
-- Every cakravla starts from the trivial triple (n, 1, n² − D) with
-- n = ⌊√D⌋ — `CakravalaWitness` starts at (7, 1, −12) for D = 61, and
-- 12² = 144 ≤ 244 = 4·61.  That is not luck: D − n² ≤ 2n always, because
-- (n+1)² > D.  So k² ≤ 4D holds at turn 0 with no work, and
-- `cakravalaKBound` then carries it round the wheel forever.
------------------------------------------------------------------------

seedBound : (D n E : ℕ)
          → n · n ≤ D
          → D < (n + 1) · (n + 1)
          → D ≡ n · n + E
          → E · E ≤ 4 · D
seedBound D n E hlo hhi hE =
  ≤-trans (subst (E · E ≤_) (idTwoN n) (sq≤ E≤2n)) (≤-k·' 4 hlo)
  where
  shifted : n · n + E < n · n + (2 · n + 1)
  shifted = subst2 _<_ hE (idSeed n) hhi

  -- 2n + 1 is not definitionally suc (2n); 1 + 2n is.
  shifted' : n · n + E < n · n + suc (2 · n)
  shifted' = subst (λ w → n · n + E < n · n + w) (+-comm (2 · n) 1) shifted

  E≤2n : E ≤ 2 · n
  E≤2n = pred-≤-pred (<-k+-cancel {k = n · n} shifted')

------------------------------------------------------------------------
-- 5.  THE BRIDGE TO ℤ, which is where `CakravalaDescent` lives.
--
-- The whole file above is over ℕ because that is where the ORDER is
-- (cubical ships no order on ℤ) and because cubical's ℤ product is unary.
-- The one place ℤ is genuinely needed is the hypothesis `Es ≡ K · K'`:
-- it is the descent's own equation m² − D = k·k', read through | · |.
-- That reading is `abs·`, one line, and it is done here rather than
-- asserted in a comment.
--
-- `stepAbs` below takes the ℤ equation as a hypothesis.
------------------------------------------------------------------------

module ZBridge where

  open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; abs)
    renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; _-_ to _-ℤ_ ; -_ to -ℤ_)
  open import Cubical.Data.Int.Properties using (abs· ; abs- ; pos+ ; plusMinus)
  open import Cubical.Algebra.CommRing using (CommRingStr ; CommRing→Ring)
  open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
  open import Cubical.Algebra.Ring.Properties using (module RingTheory)

  open RingTheory (CommRing→Ring ℤCommRing) using (-Dist ; -Idempotent)
  open CommRingStr (snd ℤCommRing) using () renaming (+Comm to +Commℤ)

  -- |k·k'| = |k|·|k'|: the descent's product read through the norm's sign.
  absStep : (x k k' : ℤ) → x ≡ k ·ℤ k' → abs x ≡ abs k · abs k'
  absStep x k k' p = cong abs p ∙ abs· k k'

  negSub : (x y : ℤ) → -ℤ (x -ℤ y) ≡ y -ℤ x
  negSub x y = sym (-Dist x (-ℤ y))
             ∙ cong (λ w → (-ℤ x) +ℤ w) (-Idempotent y)
             ∙ +Commℤ (-ℤ x) y

  posSubAbs : (b E : ℕ) → abs (pos (b + E) -ℤ pos b) ≡ E
  posSubAbs b E =
      cong (λ w → abs (w -ℤ pos b)) (pos+ b E ∙ +Commℤ (pos b) (pos E))
    ∙ cong abs (plusMinus (pos b) (pos E))

  posSubAbs' : (a E : ℕ) → abs (pos a -ℤ pos (a + E)) ≡ E
  posSubAbs' a E =
      sym (abs- (pos a -ℤ pos (a + E)))
    ∙ cong abs (negSub (pos a) (pos (a + E)))
    ∙ posSubAbs a E

  -- the ℕ discriminant of §2 IS the ℤ absolute value
  absDiff : (a b E : ℕ) → ((a ≡ b + E) ⊎ (b ≡ a + E))
          → abs (pos a -ℤ pos b) ≡ E
  absDiff a b E (inl p) = cong (λ w → abs (pos w -ℤ pos b)) p ∙ posSubAbs b E
  absDiff a b E (inr p) = cong (λ w → abs (pos a -ℤ pos w)) p ∙ posSubAbs' a E

  -- THE HYPOTHESIS `Es ≡ K · K'`, DISCHARGED.
  stepAbs : (m D : ℕ) (k k' : ℤ) (E : ℕ)
          → ((m · m ≡ D + E) ⊎ (D ≡ m · m + E))
          → pos (m · m) -ℤ pos D ≡ k ·ℤ k'
          → E ≡ abs k · abs k'
  stepAbs m D k k' E hE p =
    sym (absDiff (m · m) D E hE) ∙ absStep (pos (m · m) -ℤ pos D) k k' p

  -- THE INVARIANT, stated in the descent's own variables.  k is the
  -- current interim value, k' the next; m is the m Bhskara's rule picks
  -- out of the class r mod |k|, and `minim` is that rule.
  cakravalaKBoundℤ :
      (D r : ℕ) (k k' : ℤ) (m E : ℕ)
    → 1 ≤ D → 1 ≤ abs k → 1 ≤ r → r ≤ abs k
    → abs k · abs k ≤ 4 · D
    → ((m · m ≡ D + E) ⊎ (D ≡ m · m + E))
    → pos (m · m) -ℤ pos D ≡ k ·ℤ k'
    → ( (j F : ℕ)
        → ( ((r + j · abs k) · (r + j · abs k) ≡ D + F)
          ⊎ (D ≡ (r + j · abs k) · (r + j · abs k) + F) )
        → E ≤ F )
    → abs k' · abs k' < 4 · D
  cakravalaKBoundℤ D r k k' m E hD1 hK1 hr1 hrK hKK hE hstep minim =
    cakravalaKBound D (abs k) r (abs k') E hD1 hK1 hr1 hrK hKK
                    (stepAbs m D k k' E hE hstep) minim

------------------------------------------------------------------------
-- 6.  D = 61, COMPUTED — and the bound catching a false claim.
--
-- `CakravalaWitness` runs Bhskara's own hardest example.  Its turn 0 is
-- (7, 1, −12): n = ⌊√61⌋ = 7, k = 7² − 61 = −12.  The window is
-- k² ≤ 4·61 = 244, and 12² = 144.  `seedBound` says that is forced, not
-- fortunate; here it is instantiated, so the kernel does the arithmetic.
------------------------------------------------------------------------

seed61 : 12 · 12 ≤ 4 · 61
seed61 = seedBound 61 7 12 (12 , refl) (2 , refl) refl

------------------------------------------------------------------------
-- 7.  A CLAIM IN THIS REPOSITORY THAT THE BOUND REFUTES.
--
-- `CakravalaWitness.agda` says, of every turn it certifies: "The m on
-- each line is the one BHSKARA'S CHOICE RULE selects: among the m with
-- k | (a + bm), the one minimising |m² − D|."  `machine/NalandaEmit.hs` (absent from this repository)
-- prints the same sentence into the file it generates.
--
-- At turn 7 that is false, and this file's theorem is what makes it
-- visible rather than a matter of opinion.  Turn 7 is
-- (a, b, k) = (29718, 3805, −1) with m = 7.  Since |k| = 1 the congruence
-- k | (a + bm) is vacuous, so EVERY integer is a candidate, and
--
--        |8² − 61| = 3        <        12 = |7² − 61|.
--
-- So the rule selects m = 8, not m = 7.  Both are checked below by the
-- kernel.  The generator's source says why: `machine/Nalanda.hs` (absent from this repository),
-- `chooseM`, line 167 — `if n == 1 then Just (isqrt d)` — special-cases
-- |k| = 1 to return ⌊√D⌋ = 7 instead of minimising.  That is a different
-- rule, and for D = 61 the two differ.
--
-- The step is still SOUND: any m satisfying the congruence gives a valid
-- descent, so nothing `CakravalaWitness` proves is wrong.  What is wrong
-- is the sentence attributing the choice to Bhskara, and the cost is
-- real — m = 7 sends |k'| to 12 where m = 8 sends it to 3.
--
-- And the bound is exactly what detects it: §2–4 give 16·k'² ≤ 36·D for
-- any step obeying the rule, and 16·12² = 2304 > 2196 = 36·61.  So no m
-- obeying Bhāskara's rule can produce |k'| = 12 here — a proof, not an
-- observation, that the rule was not obeyed.
------------------------------------------------------------------------

-- the two candidates, |m² − 61| for m = 8 and m = 7
cand8 : 8 · 8 ≡ 61 + 3
cand8 = refl

cand7 : 7 · 7 + 12 ≡ 61
cand7 = refl

-- 3 < 12, so Bhskara's rule selects 8 and the generator selected 7
minimalIs8 : 3 < 12
minimalIs8 = 8 , refl

-- and the conclusion of `cakravalaKBound` fails at |k'| = 12, D = 61,
-- which is a PROOF that its minimality hypothesis fails at turn 7.
turn7ViolatesBound : ¬ (16 · (12 · 12) ≤ 36 · 61)
turn7ViolatesBound = <-asym (107 , refl)
