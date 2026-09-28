{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- गुणक-क्षेपौ — the wheel's state is bounded, and it carries its own next
-- class.  (Guaka = the multiplier m; kepa = the interpolator k.  Both
-- are Bhskara's own words for these two quantities in the
-- वर्गप्रकृति chapter of the बीजगणितम्, 1150 CE; the cycle itself is
-- JAYADEVA's, ~950, surviving through Udayadivākara's सुन्दरी, 1073.
-- Nothing below claims either of them stated any theorem in this file.
-- What is claimed is that these are the two quantities their algorithm
-- carries from turn to turn, and this file is about that pair.)
--
-- This file gives a checked turn cap.  It does not close termination.
-- It closes something else, which is what a turn cap actually needs and
-- which is strictly weaker than termination:
--
--     IF the wheel reaches क्षेप = 1 AT ALL, it does so within B² turns,
--     where B is the least natural with 4D < B².
--
-- That implication needs only (i) the state (गुणक, क्षेप) lying in a box of
-- side B, and (ii) the next state being a function of the current one.
-- It does NOT need the wheel to reach 1.  §1–§4 prove (i) outright.  §5
-- proves the algebraic core of (ii).
--
-- AND ONE CORRECTION TO THE CITATION THAT `2·D` RESTS ON, §7.  The
-- justification recorded for `turnCap d = 2·d` is "the pairs (P, Q) with
-- 0 < P < √D and 0 < Q < 2√D".  The cakravāla's own multiplier does NOT
-- satisfy P < √D: for D = 1989 the wheel's first turn takes m = 62 and
-- √1989 < 45.  So that count is a count of something else — reduced surds
-- of the continued fraction — and the claim that the cakravāla is a
-- "sub-walk" of it is a third unchecked input, not a restatement of the
-- first two.  The bound proved here, m² ≤ 4D, is the one the algorithm's
-- own state actually satisfies.
--
-- WHAT IS PROVED.
--
--   गुणक-बन्धः        THE MULTIPLIER IS IN THE SAME WINDOW AS THE
--                    INTERPOLATOR: m² ≤ 4D, from `CakravalaBound`'s own
--                    conclusion 16E² ≤ 36·D·K² together with K² ≤ 4D.
--                    `CakravalaBound` bounds K and never bounds m; without
--                    an m-bound the state is not in a box and none of the
--                    counting below can start.
--   कोष्ठकः           x² ≤ c < B² gives x < B.  The box, as an inequality
--                    between naturals with no square root anywhere.
--   अङ्कनम् / अङ्कन-एकत्वम्
--                    the state (m, K) coded as m·B + K, and that code is
--                    INJECTIVE on the box — so a repeated code is a
--                    repeated state and not merely a collision.
--   अवस्था-पुनरावृत्तिः  THE COUNT.  Any B²+1 turns whose states lie in the
--                    box contain two DISTINCT turns with the SAME state.
--                    Cubical's `pigeonhole`; the finiteness is the content.
--   प्रत्यावृत्तिः      THE WHEEL CARRIES ITS OWN NEXT CLASS.  Over ℤ, from
--                    the three exact divisions of the cakravla step,
--                        a' + b'·(−m)  ≡  k'·(−b),
--                    i.e. −m ALREADY SOLVES the next turn's congruence
--                    k' | (a' + b'·m'), with cofactor −b.  So the next
--                    multiplier's residue class is −m mod k', which is a
--                    function of the current state alone.  This is the
--                    algebraic core of determinism, and it is three ring
--                    identities.
--   षष्ट्येक-प्रत्यावृत्तिः  D = 61, turn 0 → turn 1, computed in the kernel.
--
--   * What is
--     established is a CONDITIONAL cap: exceeding B² turns proves a state
--     repeated, and, given determinism, that the wheel is in a
--     cycle that will never reach क्षेप = 1.  A cap is a resource limit
--     whose failure now carries a mathematical claim instead of a shrug.
--   * DETERMINISM.  §5 gives that −m solves the next
--     congruence.
--   * `CakravalaBound.agda`'s hypotheses are taken here as hypotheses.
--     §1's input `16·E² ≤ 36·(D·K²)` is that file's `straddleBound`
--     conclusion; this file does not import it.
------------------------------------------------------------------------

module GunakaKsepa_TheWheelsStateIsBoundedAndSelfPropagating where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-comm ; +-suc ; inj-m+)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Fin.Properties using (pigeonhole)
open import Cubical.Tactics.NatSolver using (solveℕ!)

------------------------------------------------------------------------
-- ० · order toolkit.  Cubical ships `≤-·k` but not its mirror, squaring's
-- monotonicity, squaring's REFLECTION, or cancellation.  Four lemmas.
------------------------------------------------------------------------

private
  ≤-k·' : {m n : ℕ} (k : ℕ) → m ≤ n → k · m ≤ k · n
  ≤-k·' {m} {n} k h = subst2 _≤_ (·-comm m k) (·-comm n k) (≤-·k {k = k} h)
    where open import Cubical.Data.Nat using (·-comm)

  वर्ग-क्रमः : {m n : ℕ} → m ≤ n → m · m ≤ n · n
  वर्ग-क्रमः {m} {n} h = ≤-trans (≤-·k {k = m} h) (≤-k·' n h)

  पूर्व-पदम् : (c : ℕ) → 1 ≤ c → Σ[ c' ∈ ℕ ] c ≡ suc c'
  पूर्व-पदम् c (k , hk) = k , sym hk ∙ +-comm k 1

  -- squaring REFLECTS the order: x² ≤ y² gives x ≤ y.
  वर्ग-प्रतिलोमः : (x y : ℕ) → x · x ≤ y · y → x ≤ y
  वर्ग-प्रतिलोमः x y h with splitℕ-≤ x y
  ... | inl p = p
  ... | inr y<x = ⊥rec (¬m<m (<≤-trans yy<xx h))
    where
    1≤x : 1 ≤ x
    1≤x = ≤-trans (suc-≤-suc zero-≤) y<x

    yx<xx : y · x < x · x
    yx<xx = let (x' , hx') = पूर्व-पदम् x 1≤x
            in subst (λ w → y · w < x · w) (sym hx') (<-·sk {m = y} {n = x} {k = x'} y<x)

    yy<xx : y · y < x · x
    yy<xx = ≤<-trans (≤-k·' y (<-weaken y<x)) yx<xx

  ·-रद्दः : (c x y : ℕ) → 1 ≤ c → c · x ≤ c · y → x ≤ y
  ·-रद्दः c x y hc h with splitℕ-≤ x y
  ... | inl p = p
  ... | inr y<x =
        let (c' , hc') = पूर्व-पदम् c hc
            stepB : c · y < c · x
            stepB = subst2 _<_ (·-comm y (suc c') ∙ cong (_· y) (sym hc'))
                               (·-comm x (suc c') ∙ cong (_· x) (sym hc'))
                               (<-·sk y<x)
        in ⊥rec (¬m<m (<≤-trans stepB h))
    where open import Cubical.Data.Nat using (·-comm)

private
  id16   : (E : ℕ) → 16 · (E · E) ≡ (4 · E) · (4 · E)
  id16 E = solveℕ!

  id144  : (D : ℕ) → 36 · (D · (4 · D)) ≡ (12 · D) · (12 · D)
  id144 D = solveℕ!

  id12   : (D : ℕ) → 12 · D ≡ 4 · (3 · D)
  id12 D = solveℕ!

  id4D   : (D : ℕ) → 3 · D + D ≡ 4 · D
  id4D D = solveℕ!

  idD3D  : (D : ℕ) → D + 3 · D ≡ 4 · D
  idD3D D = solveℕ!

  idShift : (d m B K : ℕ) → ((1 + d) + m) · B + K ≡ m · B + (B + (d · B + K))
  idShift d m B K = solveℕ!

------------------------------------------------------------------------
-- १ · गुणक-बन्धः — THE MULTIPLIER IS INSIDE THE WINDOW TOO.
--
-- `CakravalaBound.straddleBound` ends at 16·E² ≤ 36·D·K², where E is the
-- discriminant |m² − D| of the m the rule selects and K = |k|.  Feed it
-- the invariant K² ≤ 4D that the same file preserves, and E ≤ 3D falls
-- out; then m² = D ± E ≤ 4D.  Two lines of order algebra, and it is the
-- half of the state box that nothing in this repository had.
--
-- Note which way the case split goes.  Below the root (D ≡ m² + E) the
-- bound is free — m² ≤ D ≤ 4D — and nothing about E is used.  Above the
-- root (m² ≡ D + E) is where the work is, and it is exactly where the
-- classical account says nothing, because the classical account is
-- carrying √D around and this file is not.
------------------------------------------------------------------------

गुणक-बन्धः : (D K m E : ℕ)
          → K · K ≤ 4 · D
          → 16 · (E · E) ≤ 36 · (D · (K · K))
          → ((m · m ≡ D + E) ⊎ (D ≡ m · m + E))
          → m · m ≤ 4 · D

गुणक-बन्धः D K m E hK hbig (inr hD) =
  ≤-trans (E , +-comm E (m · m) ∙ sym hD) (3 · D , id4D D)

गुणक-बन्धः D K m E hK hbig (inl hD) =
  subst (_≤ 4 · D) (sym hD) (subst (D + E ≤_) (idD3D D) (≤-k+ E≤3D))
  where
  chain : 16 · (E · E) ≤ 36 · (D · (4 · D))
  chain = ≤-trans hbig (≤-k·' 36 (≤-k·' D hK))

  sq : (4 · E) · (4 · E) ≤ (12 · D) · (12 · D)
  sq = subst2 _≤_ (id16 E) (id144 D) chain

  E≤3D : E ≤ 3 · D
  E≤3D = ·-रद्दः 4 E (3 · D) (3 , refl)
           (subst (4 · E ≤_) (id12 D) (वर्ग-प्रतिलोमः (4 · E) (12 · D) sq))

------------------------------------------------------------------------
-- २ · कोष्ठकः — the box, with no square root in sight.
--
-- B is any natural with 4D < B·B — for the reactor, ⌊√(4D)⌋ + 1.  Then a
-- quantity whose square is at most 4D is strictly below B.  Applied twice:
-- once to the गुणक via §1, once to the क्षेप via `CakravalaBound`'s
-- invariant.
------------------------------------------------------------------------

कोष्ठकः : (B x c : ℕ) → x · x ≤ c → c < B · B → x < B
कोष्ठकः B x c hx hc with splitℕ-< x B
... | inl p = p
... | inr B≤x = ⊥rec (¬m<m (≤<-trans (≤-trans (वर्ग-क्रमः B≤x) hx) hc))

------------------------------------------------------------------------
-- ३ · अङ्कनम् — the state, coded, and the code is injective on the box.
--
-- A repeated CODE is worth nothing unless it is a repeated STATE, so the
-- injectivity is not bookkeeping: it is what makes §4 a statement about
-- the wheel rather than about an arithmetic accident.  This is division
-- with remainder's uniqueness, done by hand because it is one case split.
------------------------------------------------------------------------

अङ्कनम् : ℕ → ℕ × ℕ → ℕ
अङ्कनम् B p = fst p · B + snd p

अङ्कन-सीमा : (B m K : ℕ) → m < B → K < B → m · B + K < B · B
अङ्कन-सीमा B m K hm hK = <≤-trans lt1 le1
  where
  lt1 : m · B + K < m · B + B
  lt1 = subst (_≤ m · B + B) (+-suc (m · B) K) (≤-k+ {k = m · B} hK)

  le1 : m · B + B ≤ B · B
  le1 = subst (_≤ B · B) (+-comm B (m · B)) (≤-·k {k = B} hm)

private
  अङ्कन-अर्धम् : (B m₁ K₁ m₂ K₂ : ℕ) → K₁ < B → m₁ ≤ m₂
              → m₁ · B + K₁ ≡ m₂ · B + K₂
              → (m₁ ≡ m₂) × (K₁ ≡ K₂)
  अङ्कन-अर्धम् B m₁ K₁ m₂ K₂ hK₁ (zero , hd) e =
    hd , inj-m+ {m = m₁ · B} (e ∙ cong (λ w → w · B + K₂) (sym hd))
  अङ्कन-अर्धम् B m₁ K₁ m₂ K₂ hK₁ (suc d , hd) e =
    ⊥rec (¬m<m (≤<-trans B≤K₁ hK₁))
    where
    chain : m₂ · B + K₂ ≡ m₁ · B + (B + (d · B + K₂))
    chain = cong (λ w → w · B + K₂) (sym hd) ∙ idShift d m₁ B K₂

    K₁≡ : K₁ ≡ B + (d · B + K₂)
    K₁≡ = inj-m+ {m = m₁ · B} (e ∙ chain)

    B≤K₁ : B ≤ K₁
    B≤K₁ = subst (B ≤_) (sym K₁≡) (≤SumLeft {n = B} {k = d · B + K₂})

अङ्कन-एकत्वम् : (B m₁ K₁ m₂ K₂ : ℕ) → K₁ < B → K₂ < B
             → m₁ · B + K₁ ≡ m₂ · B + K₂
             → (m₁ ≡ m₂) × (K₁ ≡ K₂)
अङ्कन-एकत्वम् B m₁ K₁ m₂ K₂ hK₁ hK₂ e with splitℕ-≤ m₁ m₂
... | inl p = अङ्कन-अर्धम् B m₁ K₁ m₂ K₂ hK₁ p e
... | inr q = let (u , v) = अङ्कन-अर्धम् B m₂ K₂ m₁ K₁ hK₂ (<-weaken q) (sym e)
              in sym u , sym v

------------------------------------------------------------------------
-- ४ · अवस्था-पुनरावृत्तिः — THE COUNT.
--
-- अवस्था बद्धा । यत् धार्यं तत् परिमितम् ।  (`AHIMSA_SUTRA_VISTARA` §46,
-- said there of Pāṇini's त्रिपादी: an unspecified order is an unbounded
-- state.  Here the state IS bounded, and this is the theorem that says
-- what bounded buys.)
--
-- Given B²+1 turns, each of whose states lies in the box of side B, two
-- DISTINCT turns carry the SAME state.  Nothing about the cakravla is
-- used — this is `pigeonhole` with the coding of §3 — and that is the
-- point: the algorithm's contribution was §1 and §2, and once the box is
-- established the counting is generic.
------------------------------------------------------------------------

अवस्था-पुनरावृत्तिः :
    (B : ℕ)
  → (s : Fin (suc (B · B)) → ℕ × ℕ)
  → ((i : Fin (suc (B · B))) → (fst (s i) < B) × (snd (s i) < B))
  → Σ[ i ∈ Fin (suc (B · B)) ] Σ[ j ∈ Fin (suc (B · B)) ]
      ((¬ i ≡ j) × (s i ≡ s j))
अवस्था-पुनरावृत्तिः B s box = i , j , i≢j , ≡-× u v
  where
  g : Fin (suc (B · B)) → Fin (B · B)
  g i = अङ्कनम् B (s i)
      , अङ्कन-सीमा B (fst (s i)) (snd (s i)) (fst (box i)) (snd (box i))

  hole = pigeonhole {m = B · B} {n = suc (B · B)} ≤-refl g

  i    = fst hole
  j    = fst (snd hole)
  i≢j  = fst (snd (snd hole))
  code = cong fst (snd (snd (snd hole)))

  uv = अङ्कन-एकत्वम् B (fst (s i)) (snd (s i)) (fst (s j)) (snd (s j))
                    (snd (box i)) (snd (box j)) code
  u = fst uv
  v = snd uv

------------------------------------------------------------------------
-- ५ · प्रत्यावृत्तिः — THE WHEEL CARRIES ITS OWN NEXT CLASS.
--
-- The step is: given a² − D b² = k and an m with k | (a + bm), set
-- a' = (am + Db)/k, b' = (a + bm)/k, k' = (m² − D)/k.  The NEXT turn must
-- solve k' | (a' + b'·m').  The claim is that a solution is already in
-- hand, and it is −m:
--
--     k·(a' + b'·(−m))
--       = k·a' + (k·b')·(−m)
--       = (am + Db) − (a + bm)·m          [the three exact divisions]
--       = Db − b·m²  =  (−b)·(m² − D)  =  (−b)·(k·k')
--       = k·(k'·(−b)),
--
-- and cancelling k gives a' + b'·(−m) ≡ k'·(−b).  Three ring identities
-- and two rewrites; the cofactor is −b, written out.
--
-- WHAT THIS IS FOR.  It is half of "the next state is a function of the
-- current state" — the half that says the next multiplier's RESIDUE CLASS
-- is determined.  Note
-- that this is also the standard fact P_{i+1} ≡ −P_i (mod Q_{i+1}) of the
-- continued-fraction recursion, arrived at here from the cakravla's own
-- three divisions rather than imported from the theory that displaced it.
--
-- Stated over ℤ rather than an arbitrary CommRing, because the reactor is
-- over ℤ and because the ring solver wants a concrete ring.  The proof
-- uses nothing beyond commutativity.
------------------------------------------------------------------------

open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Algebra.CommRing using (CommRingStr)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)

open CommRingStr (snd ℤCommRing)
  using () renaming (_·_ to _·ℤ_ ; _+_ to _+ℤ_ ; -_ to -ℤ_ ; _-_ to _-ℤ_)

प्रत्यावृत्ति-मापिता :
    (D a b m k a' b' k' : ℤ)
  → a ·ℤ m +ℤ D ·ℤ b ≡ k ·ℤ a'
  → a +ℤ b ·ℤ m      ≡ k ·ℤ b'
  → m ·ℤ m -ℤ D      ≡ k ·ℤ k'
  → k ·ℤ (a' +ℤ b' ·ℤ (-ℤ m)) ≡ k ·ℤ (k' ·ℤ (-ℤ b))
प्रत्यावृत्ति-मापिता D a b m k a' b' k' ea eb ek =
    lhsSplit
  ∙ cong₂ _+ℤ_ (sym ea) (cong (_·ℤ (-ℤ m)) (sym eb))
  ∙ core
  ∙ cong ((-ℤ b) ·ℤ_) ek
  ∙ sym rhsSplit
  where
  lhsSplit : k ·ℤ (a' +ℤ b' ·ℤ (-ℤ m)) ≡ k ·ℤ a' +ℤ (k ·ℤ b') ·ℤ (-ℤ m)
  lhsSplit = solve! ℤCommRing

  core : (a ·ℤ m +ℤ D ·ℤ b) +ℤ (a +ℤ b ·ℤ m) ·ℤ (-ℤ m)
       ≡ (-ℤ b) ·ℤ (m ·ℤ m -ℤ D)
  core = solve! ℤCommRing

  rhsSplit : k ·ℤ (k' ·ℤ (-ℤ b)) ≡ (-ℤ b) ·ℤ (k ·ℤ k')
  rhsSplit = solve! ℤCommRing

-- and with k cancelling — over ℤ that is k ≠ 0, and k = 0 would say
-- a² = D b², i.e. the descent had already produced a square root of D —
-- the divisibility itself, cofactor and all.
प्रत्यावृत्तिः :
    (D a b m k a' b' k' : ℤ)
  → ((x y : ℤ) → k ·ℤ x ≡ k ·ℤ y → x ≡ y)
  → a ·ℤ m +ℤ D ·ℤ b ≡ k ·ℤ a'
  → a +ℤ b ·ℤ m      ≡ k ·ℤ b'
  → m ·ℤ m -ℤ D      ≡ k ·ℤ k'
  → a' +ℤ b' ·ℤ (-ℤ m) ≡ k' ·ℤ (-ℤ b)
प्रत्यावृत्तिः D a b m k a' b' k' cancel ea eb ek =
  cancel (a' +ℤ b' ·ℤ (-ℤ m)) (k' ·ℤ (-ℤ b))
         (प्रत्यावृत्ति-मापिता D a b m k a' b' k' ea eb ek)

------------------------------------------------------------------------
-- ६ · षष्ट्येकम् — D = 61, turn 0 to turn 1, in the kernel.
--
-- BHSKARA's own hardest example.  Turn 0 is the trivial triple
-- (7, 1, −12); the rule selects m = 5, and
--
--     a' = (7·5 + 61·1)/(−12) = 96/(−12)  = −8
--     b' = (7 + 1·5)/(−12)    = 12/(−12)  = −1
--     k' = (25 − 61)/(−12)    = (−36)/(−12) = 3
--
-- and the wheel's next multiplier is 7, which is ≡ −5 (mod 3).  §5 says
-- that was forced; here the three premises and the conclusion are each
-- `refl`, so the kernel does the arithmetic rather than the reader.
--
-- (Cubical's ℤ product is unary, which is why this is stated at turn 0 —
-- where the numbers are two digits — and not at turn 7, where they are
-- ten.  `CakravalaNat.agda` records the same constraint and the same
-- reason.)
------------------------------------------------------------------------

module षष्ट्येकम् where

  -- the three exact divisions, checked
  premiseA : pos 7 ·ℤ pos 5 +ℤ pos 61 ·ℤ pos 1 ≡ negsuc 11 ·ℤ negsuc 7
  premiseA = refl

  premiseB : pos 7 +ℤ pos 1 ·ℤ pos 5 ≡ negsuc 11 ·ℤ negsuc 0
  premiseB = refl

  premiseK : pos 5 ·ℤ pos 5 -ℤ pos 61 ≡ negsuc 11 ·ℤ pos 3
  premiseK = refl

  -- and the class of the next multiplier, obtained from the theorem and
  -- not recomputed: a' + b'·(−m) = k'·(−b).
  प्रत्यावृत्तिः-६१ : negsuc 7 +ℤ negsuc 0 ·ℤ (-ℤ pos 5) ≡ pos 3 ·ℤ (-ℤ pos 1)
  प्रत्यावृत्तिः-६१ = refl

------------------------------------------------------------------------
-- ७ · एकोननवत्यधिकनवदशशतम् — D = 1989, and the citation §7 of the header
-- corrects, checked in the kernel rather than asserted.
--
-- `machine/Nalanda.hs` (absent from this repository)'s turn cap is justified by "the pairs (P, Q) with
-- 0 < P < √D and 0 < Q < 2√D".  The cakravāla's own multiplier does not
-- obey the first: for D = 1989 the reactor's turn 0 is (44, 1, −53) and
-- the rule selects m = 62, with 62² = 3844 and D = 1989 — so m² is nearly
-- TWICE D, and m is half again as large as √D.  Below, in ℕ, which is
-- GMP-backed and so computes:
--
--   * 1989 < 62², the refutation of "P < √D" for this algorithm's state;
--   * §1 applied at that turn, giving 62² ≤ 4·1989 — the bound the state
--     DOES obey, and the above-the-root branch of §1, which is the branch
--     with content;
--   * §2 at B = 90 = ⌊√(4·1989)⌋ + 1, putting the turn in the box.
--
-- One turn of one D refutes a universal and is worth exactly that; it
-- says nothing about how OFTEN it happens.  For the record and as a
-- finite exhaustive check of a finite range: over every non-square
-- D ≤ 5000, 35 060 of the reactor's turns have m² > D.  That number is a
-- count of a range, not a law, and nothing is computed downstream of it.
------------------------------------------------------------------------

module एकोननवत्यधिकनवदशशतम् where

  -- the multiplier the rule selects at turn 0 is ABOVE the root
  गुणकः-मूलात्-अधिकः : 1989 < 62 · 62
  गुणकः-मूलात्-अधिकः = 1854 , refl

  -- §1 at that turn: K = 53, E = |62² − 1989| = 1855.
  हेतुः-क्षेपः : 53 · 53 ≤ 4 · 1989
  हेतुः-क्षेपः = 5147 , refl

  हेतुः-विवेकः : 16 · (1855 · 1855) ≤ 36 · (1989 · (53 · 53))
  हेतुः-विवेकः = 146079236 , refl

  गुणक-बन्धः-१९८९ : 62 · 62 ≤ 4 · 1989
  गुणक-बन्धः-१९८९ =
    गुणक-बन्धः 1989 53 62 1855 हेतुः-क्षेपः हेतुः-विवेकः (inl refl)

  -- §2 at B = 90: 4·1989 = 7956 < 8100 = 90², so the turn is in the box.
  कोष्ठकः-१९८९ : 62 < 90
  कोष्ठकः-१९८९ = कोष्ठकः 90 62 (4 · 1989) गुणक-बन्धः-१९८९ (143 , refl)

  क्षेप-कोष्ठकः-१९८९ : 53 < 90
  क्षेप-कोष्ठकः-१९८९ = कोष्ठकः 90 53 (4 · 1989) हेतुः-क्षेपः (143 , refl)
