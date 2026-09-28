{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Gamma0PartnerRigidity
--
-- THE THIRD LEG OF R0033, AND THE ONE THAT MAKES THE OTHER TWO A SIGN.
--
-- `Gamma0Partner` builds a two-sided stabilizer K from a divisibility
-- witness k (c = k·q).  `Gamma0Converse` reads a witness back off any
-- stabilizer.  Two functions in opposite directions is not yet an
-- identification: nothing so far says they are inverse, and nothing
-- says the partner built in `Gamma0Partner` is the ONLY one.
--
-- It is.  Over ℤ, with d₁ ≠ 0 and q ≠ 0, the two-sided stabilizer of
-- D = diag(d₁, q·d₁) by a unimodular H = (a b / c e) is a SINGLE
-- matrix, and it is exactly the one `Gamma0Partner` writes down:
--
--     K  =  ( ε·e   -ε·b·q )        ε = det H,  ε² = 1,  c = k·q.
--           ( -ε·k   ε·a   )
--
-- Consequences, all checked below:
--
--   §2 `canonical`     — every partner equals that matrix, entrywise.
--   §3 `isPropPartner` — so the type of partners is a PROPOSITION;
--      `isPropWitness`   so is the type of witnesses (q ≠ 0);
--      `partner≃witness` and the two are EQUIVALENT.  Γ₀-membership and
--      two-sided stabilization are not two facts that imply each other,
--      they are one type presented twice, and the transition is the
--      content.
--      `isContrPartner` — given a witness the partner type is
--      contractible: the partner is not a choice.
--
-- TORSOR.md` (absent from this repository) Theorem 1 gets uniqueness from "over ℚ, HDK = D forces
-- K = D⁻¹H⁻¹D".  That step leaves ℤ, inverts D and inverts H.  §2 below
-- reaches the same conclusion with NO division, NO inverse and NO
-- passage to ℚ: it eliminates one unknown between two entries of the
-- product, and cancels d₁ and q by integrality of ℤ (`·lCancel`).  The
-- rational formula is replaced by four integer polynomials.
--
-- §4 is the other half of "a sign is a relation, not a label": the
-- witness COMPOSES, and not additively.
--
--   `stabAnti`   — stabilizing pairs are closed under the GL × GLᵒᵖ law
--                  (H,K)·(H',K') = (H·H', K'·K).  Pure associativity,
--                  no hypotheses on D or on unimodularity at all.  This
--                  is the precision that `collab/messages/0440-fleet-
--                  blind-r0033-audit-verdict.md` (absent from this repository) recorded in prose from
--                  a Python audit ("the pair set is a group under the
--                  GL×GLᵒᵖ law, not the componentwise product"); here it
--                  is a checked term.
--   `gamma0Mul`  — Γ₀(q) is closed, WITH the witness of the product
--                  computed rather than searched for:
--                      k(H·H')  =  k(H)·a'  +  e·k(H').
--                  A crossed homomorphism (1-cocycle) for the action of
--                  Γ₀ through the diagonal entries.  Standard object,
--                  no novelty claimed (searched: "crossed homomorphism",
--                  nLab / Encyclopedia of Mathematics — the general
--                  notion φ(ab) = φ(a)·(a·φ(b)) is classical; the Γ₀
--                  instance is the (2,1) entry of a matrix product).
--   `twistNeeded`— the twist is not decoration.  At q = 1, k = 1, e = 1,
--                  a' = 2, k' = 1 the cocycle gives 3 and the additive
--                  law gives 2.  So the witness, as a map from the
--                  monoid (Γ₀(q), ·, I) to the monoid (ℤ, +, 0), is NOT
--                  a monoid homomorphism.  Contrast — the comparison is
--                  a contrast, not an application, the domains differ —
--                  `TermFreeMonoid.rec-additive`: every
--                  measure defined by the free-monoid recursion into a
--                  monoid IS automatically additive.  The Γ₀ witness
--                  falls outside that class, and the thing it carries
--                  that a rec-measure does not is the index (a', e').
--
------------------------------------------------------------------------

module Gamma0PartnerRigidity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; propBiimpl→Equiv)
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (injSuc ; snotz)
open import Cubical.Data.Int using (ℤ ; pos ; isSetℤ ; injPos ; ·lCancel ; ·rCancel)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

import Gamma0Partner  as GP
import Gamma0Converse as GC
open GP using (R ; M ; mul ; dia)
open import Gamma0Freeness using (mulAssoc)

open CommRingStr (ℤCommRing .snd)

------------------------------------------------------------------------
-- 1.  Solver lemmas: pure polynomial regroupings over ℤ.
--
-- `sXY` eliminates one unknown between two entries of the product
-- H·D·K; `tXY` normalises the right-hand side after the two entry
-- equations are substituted.  Nothing here knows what a matrix is.
------------------------------------------------------------------------

private
  s11 : (a b c e d1 q k11 k21 : R)
      → d1 · ((a · e - b · c) · k11)
        ≡ e · ((a · d1 + b · 0r) · k11 + (a · 0r + b · (q · d1)) · k21)
          - b · ((c · d1 + e · 0r) · k11 + (c · 0r + e · (q · d1)) · k21)
  s11 _ _ _ _ _ _ _ _ = solve! ℤCommRing

  t11 : (b e d1 : R) → e · d1 - b · 0r ≡ d1 · e
  t11 _ _ _ = solve! ℤCommRing

  s12 : (a b c e d1 q k12 k22 : R)
      → d1 · ((a · e - b · c) · k12)
        ≡ e · ((a · d1 + b · 0r) · k12 + (a · 0r + b · (q · d1)) · k22)
          - b · ((c · d1 + e · 0r) · k12 + (c · 0r + e · (q · d1)) · k22)
  s12 _ _ _ _ _ _ _ _ = solve! ℤCommRing

  t12 : (b e q d1 : R) → e · 0r - b · (q · d1) ≡ d1 · (- (b · q))
  t12 _ _ _ _ = solve! ℤCommRing

  s21 : (a b c e d1 q k11 k21 : R)
      → d1 · ((a · e - b · c) · (q · k21))
        ≡ (- c) · ((a · d1 + b · 0r) · k11 + (a · 0r + b · (q · d1)) · k21)
          + a · ((c · d1 + e · 0r) · k11 + (c · 0r + e · (q · d1)) · k21)
  s21 _ _ _ _ _ _ _ _ = solve! ℤCommRing

  t21 : (a c d1 : R) → (- c) · d1 + a · 0r ≡ d1 · (- c)
  t21 _ _ _ = solve! ℤCommRing

  s22 : (a b c e d1 q k12 k22 : R)
      → d1 · ((a · e - b · c) · (q · k22))
        ≡ (- c) · ((a · d1 + b · 0r) · k12 + (a · 0r + b · (q · d1)) · k22)
          + a · ((c · d1 + e · 0r) · k12 + (c · 0r + e · (q · d1)) · k22)
  s22 _ _ _ _ _ _ _ _ = solve! ℤCommRing

  t22 : (a c q d1 : R) → (- c) · 0r + a · (q · d1) ≡ d1 · (q · a)
  t22 _ _ _ _ = solve! ℤCommRing

  oneMul : (x : R) → 1r · x ≡ x
  oneMul _ = solve! ℤCommRing

  sqAssoc : (ε x : R) → (ε · ε) · x ≡ ε · (ε · x)
  sqAssoc _ _ = solve! ℤCommRing

  swapQ : (ε q k : R) → q · (ε · k) ≡ ε · (q · k)
  swapQ _ _ _ = solve! ℤCommRing

  negQ : (k q : R) → - (k · q) ≡ q · (- k)
  negQ _ _ = solve! ℤCommRing

  negOut : (ε k : R) → ε · (- k) ≡ - (ε · k)
  negOut _ _ = solve! ℤCommRing

  -- ε·x ≡ y  and  ε² = 1  give  x ≡ ε·y.  Used four times.
  scaleBack : (ε x y : R) → ε · ε ≡ 1r → ε · x ≡ y → x ≡ ε · y
  scaleBack ε x y hε p =
    sym (oneMul x) ∙ cong (_· x) (sym hε) ∙ sqAssoc ε x ∙ cong (ε ·_) p

isSetM : isSet M
isSetM = isSet× isSetℤ (isSet× isSetℤ (isSet× isSetℤ isSetℤ))

------------------------------------------------------------------------
-- 2.  Rigidity: the two-sided partner is unique, and is the one
--     `Gamma0Partner` builds.
------------------------------------------------------------------------

module _ (a b c e d1 q ε : R)
         (d1n : (d1 ≡ 0r) → ⊥)
         (qn  : (q  ≡ 0r) → ⊥)
         (hdet : a · e - b · c ≡ ε)
         (hε   : ε · ε ≡ 1r) where

  H : M
  H = (a , b , c , e)

  D : M
  D = dia d1 (q · d1)

  Stab : M → Type
  Stab K = mul (mul H D) K ≡ D

  Partner : Type
  Partner = Σ[ K ∈ M ] Stab K

  Witness : Type
  Witness = Σ[ k ∈ R ] c ≡ k · q

  module _ (k11 k12 k21 k22 : R)
           (hstab : Stab (k11 , k12 , k21 , k22)) where

    -- the four entries of the stabilization equation
    q11 : (a · d1 + b · 0r) · k11 + (a · 0r + b · (q · d1)) · k21 ≡ d1
    q11 i = fst (hstab i)

    q12 : (a · d1 + b · 0r) · k12 + (a · 0r + b · (q · d1)) · k22 ≡ 0r
    q12 i = fst (snd (hstab i))

    q21 : (c · d1 + e · 0r) · k11 + (c · 0r + e · (q · d1)) · k21 ≡ 0r
    q21 i = fst (snd (snd (hstab i)))

    q22 : (c · d1 + e · 0r) · k12 + (c · 0r + e · (q · d1)) · k22 ≡ q · d1
    q22 i = snd (snd (snd (hstab i)))

    -- K₁₁ : eliminate k21 between rows, then cancel d₁
    c11 : d1 · (ε · k11) ≡ d1 · e
    c11 = cong (λ x → d1 · (x · k11)) (sym hdet)
          ∙ s11 a b c e d1 q k11 k21
          ∙ cong₂ (λ x y → e · x - b · y) q11 q21
          ∙ t11 b e d1

    p11 : k11 ≡ ε · e
    p11 = scaleBack ε k11 e hε (·lCancel d1 (ε · k11) e c11 d1n)

    -- K₁₂ : same elimination on the second column
    c12 : d1 · (ε · k12) ≡ d1 · (- (b · q))
    c12 = cong (λ x → d1 · (x · k12)) (sym hdet)
          ∙ s12 a b c e d1 q k12 k22
          ∙ cong₂ (λ x y → e · x - b · y) q12 q22
          ∙ t12 b e q d1

    p12 : k12 ≡ - (ε · (b · q))
    p12 = scaleBack ε k12 (- (b · q)) hε
            (·lCancel d1 (ε · k12) (- (b · q)) c12 d1n)
          ∙ negOut ε (b · q)

    -- K₂₂ : eliminate k12, cancel d₁, then cancel q
    c22 : d1 · (ε · (q · k22)) ≡ d1 · (q · a)
    c22 = cong (λ x → d1 · (x · (q · k22))) (sym hdet)
          ∙ s22 a b c e d1 q k12 k22
          ∙ cong₂ (λ x y → (- c) · x + a · y) q12 q22
          ∙ t22 a c q d1

    c22' : q · (ε · k22) ≡ q · a
    c22' = swapQ ε q k22 ∙ ·lCancel d1 (ε · (q · k22)) (q · a) c22 d1n

    p22 : k22 ≡ ε · a
    p22 = scaleBack ε k22 a hε (·lCancel q (ε · k22) a c22' qn)

    -- K₂₁ : eliminate k11, cancel d₁; the witness enters here and only
    -- here, because the (2,1) entry is where the level lives
    c21 : d1 · (ε · (q · k21)) ≡ d1 · (- c)
    c21 = cong (λ x → d1 · (x · (q · k21))) (sym hdet)
          ∙ s21 a b c e d1 q k11 k21
          ∙ cong₂ (λ x y → (- c) · x + a · y) q11 q21
          ∙ t21 a c d1

    module _ (k : R) (hk : c ≡ k · q) where

      c21' : q · (ε · k21) ≡ q · (- k)
      c21' = swapQ ε q k21
             ∙ ·lCancel d1 (ε · (q · k21)) (- c) c21 d1n
             ∙ cong (-_) hk
             ∙ negQ k q

      p21 : k21 ≡ - (ε · k)
      p21 = scaleBack ε k21 (- k) hε (·lCancel q (ε · k21) (- k) c21' qn)
            ∙ negOut ε k

      -- THE RIGIDITY STATEMENT
      canonical : (k11 , k12 , k21 , k22)
                ≡ (ε · e , - (ε · (b · q)) , - (ε · k) , ε · a)
      canonical i = (p11 i , p12 i , p21 i , p22 i)

------------------------------------------------------------------------
-- 3.  Hence the two presentations of Γ₀-membership are one type.
------------------------------------------------------------------------

  isPropWitness : isProp Witness
  isPropWitness (k , hk) (k' , hk') =
    Σ≡Prop (λ _ → isSetℤ _ _) (·rCancel q k k' (sym hk ∙ hk') qn)

  -- read the witness off a partner  (Gamma0Converse)
  fromPartner : Partner → Witness
  fromPartner ((k11 , k12 , k21 , k22) , hs) =
    GC.membership a b c e d1 q ε k11 k12 k21 k22 d1n hdet hε hs

  -- build the partner from a witness  (Gamma0Partner)
  toPartner : Witness → Partner
  toPartner (k , hk) = Kc , st
    where
      Kc : M
      Kc = (ε · e , - (ε · (b · q)) , - (ε · k) , ε · a)

      hdet' : a · e - b · (k · q) ≡ ε
      hdet' = cong (λ x → a · e - b · x) (sym hk) ∙ hdet

      st0 : mul (mul (a , b , k · q , e) D) Kc ≡ D
      st0 = GP.stab a b e d1 q k ε hdet' hε

      st : Stab Kc
      st = subst (λ x → mul (mul (a , b , x , e) D) Kc ≡ D) (sym hk) st0

  isPropPartner : isProp Partner
  isPropPartner ((k11 , k12 , k21 , k22) , hs)
                ((l11 , l12 , l21 , l22) , hs') =
    Σ≡Prop (λ _ → isSetM _ _)
      ( canonical k11 k12 k21 k22 hs (fst w) (snd w)
      ∙ sym (canonical l11 l12 l21 l22 hs' (fst w) (snd w)) )
    where
      w : Witness
      w = GC.membership a b c e d1 q ε k11 k12 k21 k22 d1n hdet hε hs

  -- the transition IS the content: not two implications, one identity
  partner≃witness : Witness ≃ Partner
  partner≃witness =
    propBiimpl→Equiv isPropWitness isPropPartner toPartner fromPartner

  -- and the partner is not a choice
  isContrPartner : Witness → isContr Partner
  isContrPartner w = toPartner w , isPropPartner (toPartner w)

  -- no witness, no partner (the contrapositive, as a program)
  partnerNeedsWitness : (Witness → ⊥) → Partner → ⊥
  partnerNeedsWitness nw p = nw (fromPartner p)

------------------------------------------------------------------------
-- 4.  The witness composes, and the composition is twisted.
------------------------------------------------------------------------

-- Stabilizing pairs are closed under the GL × GLᵒᵖ law.  Associativity
-- only: D is arbitrary, no determinant hypothesis anywhere.
stabAnti : (X Y Dm K L : M)
         → mul (mul X Dm) K ≡ Dm
         → mul (mul Y Dm) L ≡ Dm
         → mul (mul (mul X Y) Dm) (mul L K) ≡ Dm
stabAnti X Y Dm K L hX hY =
    cong (λ z → mul z (mul L K)) (mulAssoc X Y Dm)
  ∙ mulAssoc X (mul Y Dm) (mul L K)
  ∙ cong (mul X) (sym (mulAssoc (mul Y Dm) L K))
  ∙ cong (λ z → mul X (mul z K)) hY
  ∙ sym (mulAssoc X Dm K)
  ∙ hX

private
  cocy : (a e k a' e' k' q : R)
       → (k · q) · a' + e · (k' · q) ≡ (k · a' + e · k') · q
  cocy _ _ _ _ _ _ _ = solve! ℤCommRing

-- Γ₀(q) is closed under multiplication, and the witness of the product
-- is  k·a' + e·k'  — a crossed homomorphism, not a homomorphism.
gamma0Mul : (a b e k a' b' e' k' q : R)
          → mul (a , b , k · q , e) (a' , b' , k' · q , e')
            ≡ ( a · a' + b · (k' · q)
              , a · b' + b · e'
              , (k · a' + e · k') · q
              , (k · q) · b' + e · e' )
gamma0Mul a b e k a' b' e' k' q i =
  ( a · a' + b · (k' · q)
  , a · b' + b · e'
  , cocy a e k a' e' k' q i
  , (k · q) · b' + e · e' )

-- the inverse's witness (ε·adj is the inverse of a unimodular matrix)
gamma0InvWitness : (k q ε : R) → ε · (- (k · q)) ≡ (- (ε · k)) · q
gamma0InvWitness _ _ _ = solve! ℤCommRing

gamma0IdWitness : (q : R) → 0r ≡ 0r · q
gamma0IdWitness _ = solve! ℤCommRing

-- CONTROL.  The twist is necessary: at q = 1, k = 1, e = 1, a' = 2,
-- k' = 1 the cocycle value is 3 and the additive value is 2.  So the
-- witness is not a monoid homomorphism, and TermFreeMonoid's
-- `rec-additive` does not and cannot apply to it.
cocycleValue : (pos 1 · pos 2 + pos 1 · pos 1) ≡ pos 3
cocycleValue = refl

additiveValue : (pos 1 + pos 1) ≡ pos 2
additiveValue = refl

twistNeeded : (pos 3 ≡ pos 2) → ⊥
twistNeeded p = snotz (injSuc (injSuc (injPos p)))

-- the same, in matrix form: (1 0 / 1 1)·(2 1 / 1 1) = (2 1 / 3 2),
-- whose (2,1) entry is 3, not 1 + 1.
productExample : mul (pos 1 , pos 0 , pos 1 , pos 1) (pos 2 , pos 1 , pos 1 , pos 1)
               ≡ (pos 2 , pos 1 , pos 3 , pos 2)
productExample = refl

------------------------------------------------------------------------
-- 5.  Controls.
--
-- §2 and §3 are statements under five hypotheses; a contradictory
-- hypothesis set would make them vacuous and they would still check.
-- These two terms rule that out by computation, and the second is the
-- planted-false control: the partner is unique, so a DIFFERENT integer
-- matrix must fail to stabilize, and here it does.
------------------------------------------------------------------------

-- H = (1 0 / 2 1) ∈ Γ₀(2), det = 1, D = diag(1, 2·1).  The partner
-- predicted by §2 with ε = 1, k = 1 is (ε·e, -ε·b·q, -ε·k, ε·a)
-- = (1, 0, -1, 1), and it stabilizes.
exampleStab : mul (mul (pos 1 , pos 0 , pos 2 , pos 1) (dia (pos 1) (pos 2 · pos 1)))
                  (pos 1 , pos 0 , - (pos 1) , pos 1)
            ≡ dia (pos 1) (pos 2 · pos 1)
exampleStab = refl

-- PLANTED FALSE.  Flip the sign of the (2,1) entry and stabilization
-- fails: the (2,1) entry of the product is 4, not 0.
exampleUnique : (mul (mul (pos 1 , pos 0 , pos 2 , pos 1) (dia (pos 1) (pos 2 · pos 1)))
                     (pos 1 , pos 0 , pos 1 , pos 1)
                 ≡ dia (pos 1) (pos 2 · pos 1))
              → ⊥
exampleUnique p = snotz (injPos (cong (λ z → fst (snd (snd z))) p))
