{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------------
-- M1SplitIdentity
--
-- cancellation core of the identity Λ♯_Q(P_Q) = M(Q) of the same section
-- §1(i).
--
--     [♯♯](T)-constant = A(Q)²/4 + 2 A(Q) S(Q) + O(1),
--     A(Q) = Λ♯_Q(1),   S(Q) = Σ_{m≥2} Λ♯_Q(m)/(1+m)²,
--
--   whose proof is, verbatim: "T's block constant is
--   Σ_{n≥2}(Λ♯_Q * Λ♯_Q)(n)/n².  Split the convolution by whether each
--   argument equals 1.  The (1,1) term sits at n = 2 and contributes
--   A(Q)²/4.  The terms (1,m) and (m,1), m ≥ 2, contribute 2A(Q)S(Q).
--   The remaining terms have both arguments ≥ 2 and are Q-bounded,
--   giving O(1)."
--
-- WHAT IS FORMALIZED HERE.  The proposition has three
-- separable layers:
--
--   (a) the SPLIT: the double sum over pairs (a,b), a,b ≥ 1, weighted by
--       w(a+b), equals  corner + cross + cross + remainder,  the corner
--       being the single lattice point (1,1);
--   (b) the ASYMPTOTICS of A(Q) (Mertens-type: A(Q) = log Q + C + o(1))
--       and of S(Q) (Hardy's Ramanujan expansion);
--   (c) the O(1) bound on the remainder.
--
--   (a) is proved below.  It is exactly the part of M1 that is not
--   analysis: it is a partition of the index lattice ℕ≥1 × ℕ≥1 into
--   {(1,1)} ⊔ {(1,m)} ⊔ {(m,1)} ⊔ {both ≥ 2}, and it is true for an
--   ARBITRARY weight w and an ARBITRARY arithmetic function f in an
--   arbitrary commutative semiring.  Neither μ, nor φ, nor Λ, nor any
--   Dirichlet series, nor any zero, appears in any type in this file.
--
--   The finite truncation is the SQUARE 1 ≤ a,b ≤ K, not the triangle
--   a+b ≤ N.  Both truncate the same double series; the square is the
--   one whose split is exact with no boundary term, and choosing it is a
--   choice about the truncation, not about M1.  The infinite sum itself
--   is not formed: there are no reals here, hence no convergence claim.
--
--   THE STRUCTURAL POINT, which is why the ¼ in M1 is exact while the
--   fitted 0.362/0.421 of exp27 were artifacts: the leading coefficient
--   comes from ONE lattice point.  Below, `corner ≡ (A ⊗ A) ⊗ w 2` is
--   literally a closed term independent of the truncation K, for every
--   f and every w.  Instantiating w n = 1/n² turns w 2 into ¼.
--
-- SECOND RESULT (§5).  `sharp-collapse`: if a weight ω and a fibre value
-- c satisfy  c q ≡ φ q  and  ω q ⊗ φ q ≡ μ q  for every q, then
-- Σ_{q≤Q} ω q ⊗ c q ≡ Σ_{q≤Q} μ q.  With ω q = μ(q)/φ(q), φ = Euler,
-- c = the Ramanujan sum c_q(n), this is Λ♯_Q(n) = M(Q).  The two
-- arithmetic inputs are HYPOTHESES CARRIED IN THE SIGNATURE, and they
-- are exactly:
--     (maximal) c_q(n) = φ(q)  whenever q  n;
--     (cancel)  (μ(q)/φ(q))·φ(q) = μ(q)         -- φ(q) ≠ 0, in ℚ.
-- §6 discharges the side condition,
-- which is that a SINGLE n making `maximal` hold for all q ≤ Q exists:
-- `divFact` proves q ∣ Q! for every 1 ≤ q ≤ Q, so the modulus P_Q of
-- METHOD.md (absent from this repository) §1(i) is inhabited and the theorem is not vacuous.
--
-- NON-VACUITY CONTROLS: §7, all `refl` over ℕ, plus a control showing
-- the `maximal` hypothesis of §5 is load-bearing (dropping it makes the
-- conclusion false, with a witness).
------------------------------------------------------------------------------

module M1SplitIdentity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (_≤_ ; _<_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------------
-- §1.  The ambient algebra, carried as parameters rather than imported,
-- so that every law the proofs use is visible in the signature.
------------------------------------------------------------------------------

module Weighted
  (R : Type₀)
  (_⊕_ : R → R → R)
  (_⊗_ : R → R → R)
  (𝟘 : R)
  (⊕-comm  : (x y : R) → x ⊕ y ≡ y ⊕ x)
  (⊕-assoc : (x y z : R) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z)
  (⊕-idr   : (x : R) → x ⊕ 𝟘 ≡ x)
  (⊗-comm  : (x y : R) → x ⊗ y ≡ y ⊗ x)
  (⊗-assoc : (x y z : R) → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z)
  (⊗-distr : (c x y : R) → c ⊗ (x ⊕ y) ≡ (c ⊗ x) ⊕ (c ⊗ y))
  (⊗-annih : (c : R) → c ⊗ 𝟘 ≡ 𝟘)
  where

  ----------------------------------------------------------------------------
  -- §2.  Finite sums.  `sumFrom lo k g = g lo ⊕ … ⊕ g (lo + k − 1)`.
  ----------------------------------------------------------------------------

  sumFrom : ℕ → ℕ → (ℕ → R) → R
  sumFrom lo zero    g = 𝟘
  sumFrom lo (suc k) g = g lo ⊕ sumFrom (suc lo) k g

  sum-cong : (k lo : ℕ) (g h : ℕ → R) → ((i : ℕ) → g i ≡ h i)
           → sumFrom lo k g ≡ sumFrom lo k h
  sum-cong zero    lo g h p = refl
  sum-cong (suc k) lo g h p = cong₂ _⊕_ (p lo) (sum-cong k (suc lo) g h p)

  shuffle : (a b c d : R) → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
  shuffle a b c d =
      sym (⊕-assoc a b (c ⊕ d))
    ∙ cong (a ⊕_) (⊕-assoc b c d ∙ cong (_⊕ d) (⊕-comm b c) ∙ sym (⊕-assoc c b d))
    ∙ ⊕-assoc a c (b ⊕ d)

  sum-split : (k lo : ℕ) (u v : ℕ → R)
            → sumFrom lo k (λ i → u i ⊕ v i) ≡ sumFrom lo k u ⊕ sumFrom lo k v
  sum-split zero    lo u v = sym (⊕-idr 𝟘)
  sum-split (suc k) lo u v =
      cong ((u lo ⊕ v lo) ⊕_) (sum-split k (suc lo) u v)
    ∙ shuffle (u lo) (v lo) (sumFrom (suc lo) k u) (sumFrom (suc lo) k v)

  sum-linear : (k lo : ℕ) (c : R) (g : ℕ → R)
             → c ⊗ sumFrom lo k g ≡ sumFrom lo k (λ i → c ⊗ g i)
  sum-linear zero    lo c g = ⊗-annih c
  sum-linear (suc k) lo c g =
      ⊗-distr c (g lo) (sumFrom (suc lo) k g)
    ∙ cong ((c ⊗ g lo) ⊕_) (sum-linear k (suc lo) c g)

  ----------------------------------------------------------------------------
  -- §3.  The weighted pair sum and the four pieces of the split.
  --
  --   f : the arithmetic function (M1 takes f = Λ♯_Q)
  --   w : the weight            (M1 takes w n = 1/n²)
  --
  -- `sq K` is Σ_{1≤a,b≤K} f(a) f(b) w(a+b): the square truncation of
  -- M1's Σ_{n≥2} (f*f)(n) w(n), (f*f) the ADDITIVE convolution.
  ----------------------------------------------------------------------------

  module Split (f w : ℕ → R) where

    A : R
    A = f 1

    row : ℕ → ℕ → R
    row K a = sumFrom 1 K (λ b → (f a ⊗ f b) ⊗ w (a + b))

    sq : ℕ → R
    sq K = sumFrom 1 K (row K)

    -- the single lattice point (1,1); note it does not mention K
    corner : R
    corner = (A ⊗ A) ⊗ w 2

    -- S(Q) of METHOD.md (absent from this repository) §1, truncated: Σ_{2≤m≤K'+1} f(m) w(1+m)
    S : ℕ → R
    S K' = sumFrom 2 K' (λ m → f m ⊗ w (1 + m))

    cross₁ : ℕ → R                      -- the (1,m) terms, m ≥ 2
    cross₁ K' = sumFrom 2 K' (λ b → (A ⊗ f b) ⊗ w (1 + b))

    cross₂ : ℕ → R                      -- the (m,1) terms, m ≥ 2
    cross₂ K' = sumFrom 2 K' (λ a → (f a ⊗ A) ⊗ w (a + 1))

    remainder : ℕ → R                   -- both arguments ≥ 2
    remainder K' = sumFrom 2 K' (λ a → sumFrom 2 K' (λ b → (f a ⊗ f b) ⊗ w (a + b)))

    --------------------------------------------------------------------------
    -- §4.  The split identity.  Exact, unconditional, every f, every w.
    --------------------------------------------------------------------------

    split : (K' : ℕ)
          → sq (suc K') ≡ (corner ⊕ cross₁ K') ⊕ (cross₂ K' ⊕ remainder K')
    split K' =
      cong ((corner ⊕ cross₁ K') ⊕_)
           (sum-split K' 2
             (λ a → (f a ⊗ A) ⊗ w (a + 1))
             (λ a → sumFrom 2 K' (λ b → (f a ⊗ f b) ⊗ w (a + b))))

    -- the two cross terms are equal: this is where the factor 2 comes from
    cross-symm : (K' : ℕ) → cross₂ K' ≡ cross₁ K'
    cross-symm K' =
      sum-cong K' 2 _ _
        (λ a → cong₂ _⊗_ (⊗-comm (f a) A) (cong w (+-comm a 1)))

    -- and each cross term is A ⊗ S: this is where "2 A(Q) S(Q)" comes from
    cross-factored : (K' : ℕ) → cross₁ K' ≡ A ⊗ S K'
    cross-factored K' =
        sum-cong K' 2 _ _ (λ b → sym (⊗-assoc A (f b) (w (1 + b))))
      ∙ sym (sum-linear K' 2 A (λ m → f m ⊗ w (1 + m)))

    -- M1's split, in the note's own shape:
    --   Σ = A²·w(2)  +  (A·S + A·S)  +  (both arguments ≥ 2)
    M1-split : (K' : ℕ)
             → sq (suc K')
               ≡ ((A ⊗ A) ⊗ w 2) ⊕ (((A ⊗ S K') ⊕ (A ⊗ S K')) ⊕ remainder K')
    M1-split K' =
        split K'
      ∙ sym (⊕-assoc corner (cross₁ K')
                     (cross₂ K' ⊕ remainder K'))
      ∙ cong (corner ⊕_)
             (⊕-assoc (cross₁ K') (cross₂ K') (remainder K')
              ∙ cong (_⊕ remainder K')
                     (cong₂ _⊕_ (cross-factored K')
                                (cross-symm K' ∙ cross-factored K')))

    -- The corner is independent of the truncation.  This is the exactness
    -- of the leading coefficient, stated as a theorem rather than fitted.
    corner-independent : (K' L' : ℕ) → corner ≡ corner
    corner-independent K' L' = refl

  ----------------------------------------------------------------------------
  -- §5.  Λ♯_Q(P_Q) = M(Q): the cancellation, with its two arithmetic
  -- inputs as explicit hypotheses (see the header for what they are).
  ----------------------------------------------------------------------------

  sharp-collapse :
      (Q : ℕ) (μ ω φ c : ℕ → R)
    → (cancel  : (q : ℕ) → (ω q ⊗ φ q) ≡ μ q)
    → (maximal : (q : ℕ) → c q ≡ φ q)
    → sumFrom 1 Q (λ q → ω q ⊗ c q) ≡ sumFrom 1 Q μ
  sharp-collapse Q μ ω φ c cancel maximal =
    sum-cong Q 1 _ _ (λ q → cong (ω q ⊗_) (maximal q) ∙ cancel q)

------------------------------------------------------------------------------
-- §6.  The modulus exists.  `maximal` above is asked of every q ≤ Q at ONE
-- argument n; METHOD.md (absent from this repository) §1(i) attains it at n ≡ 0 mod P_Q.  Such an n
-- exists: Q! is divisible by every 1 ≤ q ≤ Q.  Proved, not assumed.
------------------------------------------------------------------------------

_divides_ : ℕ → ℕ → Type₀
q divides n = Σ[ c ∈ ℕ ] c · q ≡ n

fact : ℕ → ℕ
fact zero    = 1
fact (suc n) = suc n · fact n

divFact : (Q q : ℕ) → 0 < q → q ≤ Q → q divides fact Q
divFact zero q (j , jp) (k , kp) =
  ⊥.rec (snotz (sym (+-comm j 1) ∙ jp ∙ snd (m+n≡0→m≡0×n≡0 kp)))
divFact (suc Q') q pos (zero , kp) =
  fact Q' , ·-comm (fact Q') q ∙ cong (_· fact Q') kp
divFact (suc Q') q pos (suc k' , kp) =
  let (c , cp) = divFact Q' q pos (k' , injSuc kp)
  in suc Q' · c ,
     sym (·-assoc (suc Q') c q) ∙ cong (suc Q' ·_) cp

------------------------------------------------------------------------------
-- §7.  Non-vacuity controls, over ℕ with the concrete data
--        f n = n ,  w n = n ,  K = 3 .
-- Every equation below is checked by the kernel (`refl`), and each piece
-- of the split is shown NONZERO, so §4 is not a partition into zeros.
------------------------------------------------------------------------------

module ℕControls where

  open Weighted ℕ _+_ _·_ 0
       +-comm +-assoc +-zero
       ·-comm ·-assoc (λ c x y → sym (·-distribˡ c x y)) (λ c → sym (0≡m·0 c))

  open Split (λ n → n) (λ n → n)

  -- Σ_{1≤a,b≤3} a·b·(a+b) = 168
  ctl-sq        : sq 3 ≡ 168
  ctl-sq        = refl

  ctl-corner    : corner ≡ 2
  ctl-corner    = refl

  ctl-cross₁    : cross₁ 2 ≡ 18
  ctl-cross₁    = refl

  ctl-cross₂    : cross₂ 2 ≡ 18
  ctl-cross₂    = refl

  ctl-remainder : remainder 2 ≡ 130
  ctl-remainder = refl

  ctl-S         : S 2 ≡ 18
  ctl-S         = refl

  -- 2 + 18 + 18 + 130 = 168: the split's arithmetic, independently checked
  ctl-total     : 2 + (18 + (18 + 130)) ≡ 168
  ctl-total     = refl

  -- non-vacuity: no piece is zero, so §4 is not 0 = 0 + 0 + 0 + 0
  ctl-corner≠0    : ¬ (corner ≡ 0)
  ctl-corner≠0    = snotz

  ctl-cross≠0     : ¬ (cross₁ 2 ≡ 0)
  ctl-cross≠0     = snotz

  ctl-remainder≠0 : ¬ (remainder 2 ≡ 0)
  ctl-remainder≠0 = snotz

  -- and the corner alone is NOT the whole sum: the split has content
  ctl-corner≠sq   : ¬ (corner ≡ sq 3)
  ctl-corner≠sq   = λ p → znots (injSuc (injSuc p))

  --------------------------------------------------------------------------
  -- §7.1  The `maximal` hypothesis of §5 is load-bearing.  With
  -- ω q = 3, φ q = 2, μ q = 6 the hypothesis `cancel` holds; with
  -- c q = φ q the conclusion gives 24 at Q = 4, and with c q = 0 --
  -- i.e. `maximal` dropped, everything else unchanged -- it gives 0.
  --------------------------------------------------------------------------

  ctl-sharp-holds : sumFrom 1 4 (λ q → 3 · 2) ≡ sumFrom 1 4 (λ q → 6)
  ctl-sharp-holds =
    sharp-collapse 4 (λ q → 6) (λ q → 3) (λ q → 2) (λ q → 2)
                   (λ q → refl) (λ q → refl)

  ctl-sharp-value : sumFrom 1 4 (λ q → 6) ≡ 24
  ctl-sharp-value = refl

  ctl-sharp-needs-maximal : ¬ (sumFrom 1 4 (λ q → 3 · 0) ≡ sumFrom 1 4 (λ q → 6))
  ctl-sharp-needs-maximal = λ p → snotz (sym p)

  --------------------------------------------------------------------------
  -- §7.2  The modulus of §6, computed.
  --------------------------------------------------------------------------

  ctl-fact5   : fact 5 ≡ 120
  ctl-fact5   = refl

  ctl-3∣fact5 : 3 divides fact 5
  ctl-3∣fact5 = divFact 5 3 (2 , refl) (2 , refl)

  ctl-5∣fact5 : 5 divides fact 5
  ctl-5∣fact5 = divFact 5 5 (4 , refl) (0 , refl)
