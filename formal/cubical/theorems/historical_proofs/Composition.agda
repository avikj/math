{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Bhavana — Brahmagupta's composition law for the form x² − D y²,
-- checked over an arbitrary commutative ring.
--
-- SOURCE AND PRIORITY.  The identity below is Brahmagupta's *bhvan*
-- ("production", "composition"), Brhmasphuasiddhnta, 628 CE,
-- chapter 18 (kuakdhyya).  It is the oldest known statement of the
-- multiplicativity of the norm of ℤ[√D], and it is the load-bearing
-- lemma of the cakravla (Jayadeva ~950 CE, Bhskara II 1150 CE), which
-- solved x² − D y² = 1 six centuries before Brouncker and Lagrange.
-- Euler's misattribution to Pell is later still and concerns a man who
-- never worked on the equation.  The step itself is `CakravalaDescent`.
-- such note and there never had been — a citation pointing at work that
-- was never done, which a reader takes as "it is handled over there".  It
-- is repaired by pointing at a module that exists, not by writing a note
-- to satisfy the reference.)
--
-- WHAT IS CHECKED HERE.  Exactly the algebra, and only the algebra:
--
--   bhavana        N D a₁ b₁ · N D a₂ b₂ ≡ N D (a₁a₂ + D b₁b₂)
--                                              (a₁b₂ + a₂b₁)
--                  — samāsa-bhāvanā, the "additive" composition.
--   bhavanaMinus   the antara-bhvan ("difference" composition), the
--                  same identity with b₂ ↦ −b₂; Brahmagupta gives both.
--   cakravalaCleared   the composition specialised to the trivial
--                  triple (m, 1, m² − D) — the one instance the
--                  cakravla actually uses.
--   choiceToNumerator / choiceToDiscriminant
--                  two exact polynomial identities that convert
--                  Bhskara's single divisibility condition
--                  k | (a + bm) into the other two.  These are the
--                  reason the cyclic method needs only ONE congruence.
--   normScale      (k²)·N D a b ≡ N D (ka) (kb): the homogeneity that
--                  lets the descent divide by k without leaving ℤ.
--
-- NO SOLVER.  Every proof below is a hand chain over the CommRing
-- structure plus `RingTheory`/`CommRingTheory`.  This is deliberate.
-- `CayleyPairChart` records the `1r`-inside-`solve!` hazard, and
-- BUILD.md (absent from this repository) records that the repository's solver spelling (`solve!`) is
-- v0.9-only while some containers still carry cubical v0.5 (`solve`).
-- A solver-free module is the one presentation that is stable across
-- both surfaces, and it costs about sixty lines of chaining.
------------------------------------------------------------------------

module Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties using (module RingTheory)
open import Cubical.Algebra.CommRing.Properties using (module CommRingTheory)

private
  variable
    ℓ : Level

module Form (CR : CommRing ℓ) where

  open CommRingStr (snd CR)
  open RingTheory (CommRing→Ring CR)
  open CommRingTheory CR

  R : Type ℓ
  R = fst CR

  ----------------------------------------------------------------------
  -- 0.  Toolkit.  Ring rearrangements the library does not ship.
  ----------------------------------------------------------------------

  ·DistL- : (x y z : R) → (x - y) · z ≡ x · z - y · z
  ·DistL- x y z = ·DistL+ x (- y) z ∙ cong (λ w → x · z + w) (-DistL· y z)

  ·DistR- : (x y z : R) → x · (y - z) ≡ x · y - x · z
  ·DistR- x y z = ·DistR+ x y (- z) ∙ cong (λ w → x · y + w) (-DistR· x z)

  negMulNeg : (x y : R) → (- x) · (- y) ≡ x · y
  negMulNeg x y = -DistL· x (- y)
                ∙ cong (λ w → - w) (-DistR· x y)
                ∙ -Idempotent (x · y)

  private
    negOut : (S T : R) → - (S - T) ≡ (- S) + T
    negOut S T = sym (-Dist S (- T)) ∙ cong (λ w → (- S) + w) (-Idempotent T)

    -- (P − Q) − (S − T) ≡ (P + T) − (Q + S)
    abShuffle : (P Q S T : R) → (P - Q) - (S - T) ≡ (P + T) - (Q + S)
    abShuffle P Q S T =
        cong (λ w → (P - Q) + w) (negOut S T)
      ∙ cong (λ w → (P - Q) + w) (+Comm (- S) T)
      ∙ +ShufflePairs P (- Q) T (- S)
      ∙ cong (λ w → (P + T) + w) (-Dist Q S)

    -- (P + G) − (B + G) ≡ P − B
    cancelCross : (A B G : R) → (A + G) - (B + G) ≡ A - B
    cancelCross A B G =
        cong (λ w → (A + G) + w) (sym (-Dist B G))
      ∙ +ShufflePairs A G (- B) (- G)
      ∙ cong (λ w → (A - B) + w) (+InvR G)
      ∙ +IdR (A - B)

    -- (P + Q) − (P − S) ≡ Q + S
    cancelHead : (P Q S : R) → (P + Q) - (P - S) ≡ Q + S
    cancelHead P Q S =
        cong (λ w → (P + Q) + w) (negOut P S)
      ∙ +ShufflePairs P Q (- P) S
      ∙ cong (λ w → w + (Q + S)) (+InvR P)
      ∙ +IdL (Q + S)

    -- (P − Q) + (S − P) ≡ S − Q
    cancelMid : (P Q S : R) → (P - Q) + (S - P) ≡ S - Q
    cancelMid P Q S =
        cong (λ w → w + (S - P)) (+Comm P (- Q))
      ∙ +ShufflePairs (- Q) P S (- P)
      ∙ cong (λ w → ((- Q) + S) + w) (+InvR P)
      ∙ +IdR ((- Q) + S)
      ∙ +Comm (- Q) S

    -- (P − Q) + (Q − S) ≡ P − S
    cancelMid2 : (P Q S : R) → (P - Q) + (Q - S) ≡ P - S
    cancelMid2 P Q S =
        cong (λ w → (P - Q) + w) (+Comm Q (- S))
      ∙ +ShufflePairs P (- Q) (- S) Q
      ∙ cong (λ w → (P - S) + w) (+InvL Q)
      ∙ +IdR (P - S)

    mulDiff : (p q s t : R)
            → (p - q) · (s - t) ≡ (p · s + q · t) - (p · t + q · s)
    mulDiff p q s t =
        ·DistL- p q (s - t)
      ∙ cong₂ _-_ (·DistR- p s t) (·DistR- q s t)
      ∙ abShuffle (p · s) (p · t) (q · s) (q · t)

    sqSum : (X Y : R) → (X + Y) · (X + Y) ≡ (X · X + Y · Y) + (X · Y + X · Y)
    sqSum X Y =
        ·DistL+ X Y (X + Y)
      ∙ cong₂ _+_ (·DistR+ X X Y) (·DistR+ Y X Y)
      ∙ cong (λ w → (X · X + X · Y) + (w + Y · Y)) (·Comm Y X)
      ∙ cong (λ w → (X · X + X · Y) + w) (+Comm (X · Y) (Y · Y))
      ∙ +ShufflePairs (X · X) (X · Y) (Y · Y) (X · Y)

  sumTimesDiff : (u v : R) → (u + v) · (v - u) ≡ v · v - u · u
  sumTimesDiff u v =
      ·DistL+ u v (v - u)
    ∙ cong₂ _+_ (·DistR- u v u) (·DistR- v v u)
    ∙ cong (λ w → (u · v - u · u) + (v · v - w)) (·Comm v u)
    ∙ cancelMid (u · v) (u · u) (v · v)

  ----------------------------------------------------------------------
  -- 1.  The form and its composition
  ----------------------------------------------------------------------

  -- N D a b  is  a² − D b²  : the norm of a + b√D.
  N : R → R → R → R
  N D a b = a · a - D · (b · b)

  -- The two coordinates of Brahmagupta's samsa-bhvan.
  bhA bhB : R → R → R → R → R → R
  bhA D a₁ b₁ a₂ b₂ = a₁ · a₂ + D · (b₁ · b₂)
  bhB D a₁ b₁ a₂ b₂ = a₁ · b₂ + a₂ · b₁

  -- The unit of the composition is (1r, 0r): the identity monoid axiom at
  -- the coordinate level, for BOTH sides (samsa is commutative but a unit is
  -- a unit on each side and both are shown).  With ⊛CommA/⊛CommB in the
  -- generative lane this supplies the unit half of the monoid axioms; only
  -- associativity of the coordinates remains for the full monoid.
  bhA-idR : (D a b : R) → bhA D a b 1r 0r ≡ a
  bhA-idR D a b =
      cong₂ _+_ (·IdR a) (cong (D ·_) (0RightAnnihilates b) ∙ 0RightAnnihilates D)
    ∙ +IdR a

  bhB-idR : (D a b : R) → bhB D a b 1r 0r ≡ b
  bhB-idR D a b =
      cong₂ _+_ (0RightAnnihilates a) (·Comm 1r b ∙ ·IdR b)
    ∙ +IdL b

  bhA-idL : (D a b : R) → bhA D 1r 0r a b ≡ a
  bhA-idL D a b =
      cong₂ _+_ (·Comm 1r a ∙ ·IdR a)
                (cong (D ·_) (0LeftAnnihilates b) ∙ 0RightAnnihilates D)
    ∙ +IdR a

  bhB-idL : (D a b : R) → bhB D 1r 0r a b ≡ b
  bhB-idL D a b =
      cong₂ _+_ (·Comm 1r b ∙ ·IdR b) (0RightAnnihilates a)
    ∙ +IdR b

  -- Associativity of the two coordinates — the last monoid axiom for the
  -- bhāvanā composition ℤ[√D] over an ABSTRACT commutative ring, solver-free.
  -- Each side expands (distributivity) to the same four monomials; they are
  -- matched by ·Assoc/·Comm/·CommAssocl and one four-term sum reordering.
  private
    -- (w+x)+(y+z) ≡ (w+y)+(x+z): swap the inner two summands.
    reassoc4 : (w x y z : R) → (w + x) + (y + z) ≡ (w + y) + (x + z)
    reassoc4 w x y z =
        sym (+Assoc w x (y + z))
      ∙ cong (w +_) (+Assoc x y z)
      ∙ cong (w +_) (cong (_+ z) (+Comm x y))
      ∙ cong (w +_) (sym (+Assoc y x z))
      ∙ +Assoc w y (x + z)

  bhA-assoc : (D a b c d e f : R)
            → bhA D (bhA D a b c d) (bhB D a b c d) e f
            ≡ bhA D a b (bhA D c d e f) (bhB D c d e f)
  bhA-assoc D a b c d e f =
      cong₂ _+_ (·DistL+ (a · c) (D · (b · d)) e)
                (cong (D ·_) (·DistL+ (a · d) (c · b) f)
                  ∙ ·DistR+ D ((a · d) · f) ((c · b) · f))
    ∙ cong₂ _+_
        (cong₂ _+_ (sym (·Assoc a c e))
                   (sym (·Assoc D (b · d) e) ∙ cong (D ·_) (sym (·Assoc b d e))))
        (cong₂ _+_ (cong (D ·_) (sym (·Assoc a d f)))
                   (cong (D ·_) (cong (_· f) (·Comm c b) ∙ sym (·Assoc b c f))))
    ∙ reassoc4 (a · (c · e)) (D · (b · (d · e)))
               (D · (a · (d · f))) (D · (b · (c · f)))
    ∙ cong ((a · (c · e) + D · (a · (d · f))) +_)
           (+Comm (D · (b · (d · e))) (D · (b · (c · f))))
    ∙ sym
      ( cong₂ _+_ (·DistR+ a (c · e) (D · (d · f)))
                  (cong (D ·_) (·DistR+ b (c · f) (e · d))
                    ∙ ·DistR+ D (b · (c · f)) (b · (e · d)))
      ∙ cong₂ _+_
          (cong₂ _+_ refl (·CommAssocl a D (d · f)))
          (cong₂ _+_ refl (cong (λ w → D · (b · w)) (·Comm e d))) )

  bhB-assoc : (D a b c d e f : R)
            → bhB D (bhA D a b c d) (bhB D a b c d) e f
            ≡ bhB D a b (bhA D c d e f) (bhB D c d e f)
  bhB-assoc D a b c d e f =
      cong₂ _+_ (·DistL+ (a · c) (D · (b · d)) f)
                (·DistR+ e (a · d) (c · b))
    ∙ cong₂ _+_
        (cong₂ _+_ (sym (·Assoc a c f))
                   (sym (·Assoc D (b · d) f) ∙ cong (D ·_) (sym (·Assoc b d f))))
        (cong₂ _+_ (·CommAssocl e a d)
                   (·CommAssocl e c b ∙ ·Assoc c e b))
    ∙ reassoc4 (a · (c · f)) (D · (b · (d · f)))
               (a · (e · d)) ((c · e) · b)
    ∙ cong ((a · (c · f) + a · (e · d)) +_)
           (+Comm (D · (b · (d · f))) ((c · e) · b))
    ∙ sym
      ( cong₂ _+_ (·DistR+ a (c · f) (e · d))
                  (·DistL+ (c · e) (D · (d · f)) b)
      ∙ cong₂ _+_
          refl
          (cong₂ _+_ refl
                     (sym (·Assoc D (d · f) b) ∙ cong (D ·_) (·Comm (d · f) b))) )

  ----------------------------------------------------------------------
  -- 2.  Bhvan (Brhmasphuasiddhnta 18, 628 CE)
  --
  --   (a₁² − D b₁²)(a₂² − D b₂²)
  --      = (a₁a₂ + D b₁b₂)² − D (a₁b₂ + a₂b₁)²
  --
  -- Both sides are normalised to the SAME four-monomial form
  --      (ps + qt) − (pt + qs),
  -- p = a₁², q = D b₁², s = a₂², t = D b₂².  The cross terms on the
  -- right cancel because a₁a₂ · D b₁b₂ = D · (a₁b₂)(a₂b₁), which is the
  -- only content of the identity; everything else is bookkeeping.
  ----------------------------------------------------------------------

  bhavana : (D a₁ b₁ a₂ b₂ : R)
          → N D a₁ b₁ · N D a₂ b₂
            ≡ N D (bhA D a₁ b₁ a₂ b₂) (bhB D a₁ b₁ a₂ b₂)
  bhavana D a₁ b₁ a₂ b₂ = left ∙ sym right
    where
    X Y Z W : R
    X = a₁ · a₂
    Y = D · (b₁ · b₂)
    Z = a₁ · b₂
    W = a₂ · b₁

    p q s t : R
    p = a₁ · a₁
    q = D · (b₁ · b₁)
    s = a₂ · a₂
    t = D · (b₂ · b₂)

    NF : R
    NF = (p · s + q · t) - (p · t + q · s)

    left : N D a₁ b₁ · N D a₂ b₂ ≡ NF
    left = mulDiff p q s t

    xx : X · X ≡ p · s
    xx = ·CommAssocSwap a₁ a₂ a₁ a₂

    yy : Y · Y ≡ q · t
    yy = ·CommAssocSwap D (b₁ · b₂) D (b₁ · b₂)
       ∙ cong (λ w → (D · D) · w) (·CommAssocSwap b₁ b₂ b₁ b₂)
       ∙ sym (·CommAssocSwap D (b₁ · b₁) D (b₂ · b₂))

    zz : D · (Z · Z) ≡ p · t
    zz = cong (λ w → D · w) (·CommAssocSwap a₁ b₂ a₁ b₂)
       ∙ ·CommAssocl D (a₁ · a₁) (b₂ · b₂)

    ww : D · (W · W) ≡ q · s
    ww = cong (λ w → D · w) (·CommAssocSwap a₂ b₁ a₂ b₁)
       ∙ ·CommAssocl D (a₂ · a₂) (b₁ · b₁)
       ∙ ·Comm (a₂ · a₂) (D · (b₁ · b₁))

    -- the cross terms agree: this is the whole identity
    cross : X · Y ≡ D · (Z · W)
    cross = sym ( cong (λ w → D · w) (·CommAssocSwap a₁ b₂ a₂ b₁)
                ∙ cong (λ w → D · ((a₁ · a₂) · w)) (·Comm b₂ b₁)
                ∙ ·CommAssocl D (a₁ · a₂) (b₁ · b₂) )

    distD : D · ((Z · Z + W · W) + (Z · W + Z · W))
            ≡ (D · (Z · Z) + D · (W · W)) + (D · (Z · W) + D · (Z · W))
    distD = ·DistR+ D (Z · Z + W · W) (Z · W + Z · W)
          ∙ cong₂ _+_ (·DistR+ D (Z · Z) (W · W)) (·DistR+ D (Z · W) (Z · W))

    right : N D (bhA D a₁ b₁ a₂ b₂) (bhB D a₁ b₁ a₂ b₂) ≡ NF
    right =
        cong₂ _-_ (sqSum X Y) (cong (λ w → D · w) (sqSum Z W) ∙ distD)
      ∙ cong (λ g → ((X · X + Y · Y) + g)
                    - ((D · (Z · Z) + D · (W · W)) + (D · (Z · W) + D · (Z · W))))
             (cong₂ _+_ cross cross)
      ∙ cancelCross (X · X + Y · Y)
                    (D · (Z · Z) + D · (W · W))
                    (D · (Z · W) + D · (Z · W))
      ∙ cong₂ _-_ (cong₂ _+_ xx yy) (cong₂ _+_ zz ww)

  ----------------------------------------------------------------------
  -- 3.  The form is even in b, hence the antara-bhvan
  ----------------------------------------------------------------------

  normNegB : (D a b : R) → N D a (- b) ≡ N D a b
  normNegB D a b = cong (λ w → a · a - D · w) (negMulNeg b b)

  bhavanaMinus : (D a₁ b₁ a₂ b₂ : R)
               → N D a₁ b₁ · N D a₂ b₂
                 ≡ N D (a₁ · a₂ - D · (b₁ · b₂)) (a₂ · b₁ - a₁ · b₂)
  bhavanaMinus D a₁ b₁ a₂ b₂ =
      cong (λ w → N D a₁ b₁ · w) (sym (normNegB D a₂ b₂))
    ∙ bhavana D a₁ b₁ a₂ (- b₂)
    ∙ cong₂ (N D) eA eB
    where
    eA : a₁ · a₂ + D · (b₁ · (- b₂)) ≡ a₁ · a₂ - D · (b₁ · b₂)
    eA = cong (λ w → a₁ · a₂ + D · w) (-DistR· b₁ b₂)
       ∙ cong (λ w → a₁ · a₂ + w) (-DistR· D (b₁ · b₂))

    eB : a₁ · (- b₂) + a₂ · b₁ ≡ a₂ · b₁ - a₁ · b₂
    eB = cong (λ w → w + a₂ · b₁) (-DistR· a₁ b₂)
       ∙ +Comm (- (a₁ · b₂)) (a₂ · b₁)

  ----------------------------------------------------------------------
  -- 4.  The instance the cakravla uses: compose with (m, 1, m² − D)
  ----------------------------------------------------------------------

  cakravalaCleared : (D a b m : R)
                   → N D a b · (m · m - D) ≡ N D (a · m + D · b) (a + b · m)
  cakravalaCleared D a b m =
      cong (λ w → N D a b · w) (sym trivial)
    ∙ bhavana D a b m 1r
    ∙ cong₂ (N D) eA eB
    where
    trivial : N D m 1r ≡ m · m - D
    trivial = cong (λ w → m · m - D · w) (·IdR 1r)
            ∙ cong (λ w → m · m - w) (·IdR D)

    eA : a · m + D · (b · 1r) ≡ a · m + D · b
    eA = cong (λ w → a · m + D · w) (·IdR b)

    eB : a · 1r + m · b ≡ a + b · m
    eB = cong₂ _+_ (·IdR a) (·Comm m b)

  ----------------------------------------------------------------------
  -- 5.  Why ONE congruence suffices (Bhskara's choice rule)
  --
  -- Bhskara requires only  k | (a + bm).  These two exact identities
  -- are the reason the other two divisibilities come for free (up to
  -- the factor b, which is where coprimality — i.e. a kuṭṭaka — enters;
  -- that step is in CakravalaDescent).
  ----------------------------------------------------------------------

  choiceToNumerator : (D a b m : R)
                    → b · (a · m + D · b) ≡ a · (a + b · m) - N D a b
  choiceToNumerator D a b m =
      ·DistR+ b (a · m) (D · b)
    ∙ cong₂ _+_ (·CommAssocl b a m) (·CommAssocl b D b)
    ∙ sym (cancelHead (a · a) (a · (b · m)) (D · (b · b)))
    ∙ cong (λ w → w - N D a b) (sym (·DistR+ a a (b · m)))

  choiceToDiscriminant : (D a b m : R)
                       → (b · b) · (m · m - D)
                         ≡ (a + b · m) · (b · m - a) + N D a b
  choiceToDiscriminant D a b m =
      ·DistR- (b · b) (m · m) D
    ∙ cong₂ _-_ (sym (·CommAssocSwap b m b m)) (·Comm (b · b) D)
    ∙ sym (cancelMid2 ((b · m) · (b · m)) (a · a) (D · (b · b)))
    ∙ cong (λ w → w + (a · a - D · (b · b))) (sym (sumTimesDiff a (b · m)))

  ----------------------------------------------------------------------
  -- 6.  Homogeneity: the descent may clear denominators
  ----------------------------------------------------------------------

  normScale : (k D a b : R) → (k · k) · N D a b ≡ N D (k · a) (k · b)
  normScale k D a b =
      ·DistR- (k · k) (a · a) (D · (b · b))
    ∙ cong₂ _-_ (sym (·CommAssocSwap k a k a))
                ( ·CommAssocl (k · k) D (b · b)
                ∙ cong (λ w → D · w) (sym (·CommAssocSwap k b k b)) )
