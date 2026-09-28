{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CenterRelative
--
-- Prime-Pair Atlas Delta 16, formalisation targets 1-4, machine-checked.
--
-- Delta 16 asks for four things in Cubical Agda:
--
--   1. the integral equivalence  Pair ≃ CR  (parity-compatible lattice);
--   2. the one-leg reflection    J₂ (W , R) = (- R , - W);
--   3. positivity  W > |R|  and a proof that J₂ leaves it;
--   4. the quadratic invariant  Q = W² - R² = 4pq  with  Q ∘ J₂ = - Q.
--
-- All four are below.  The mathematical content Delta 16 flags as its
-- "strongest new compression" is thm16-8: the founding additive
-- center/gap geometry and multiplication meet in one quadratic form.
--
-- The delta's own Corollary 16.5 is the statement this module pins
-- down: the positive-cone obstruction is NOT the exchange τ (which
-- preserves the cone, exchangePreservesCone) but the one-leg reflection
-- J₂ (which cannot preserve it, thm16-4).
------------------------------------------------------------------------

module CenterRelative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; suc ; zero) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool using (Bool ; true ; isSetBool)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Int
  using (ℤ ; pos ; negsuc ; _+_ ; _-_ ; _·_ ; -_ ; isSetℤ ; isEven
        ; posNotnegsuc ; injPos ; ·lCancel ; fromNatℤ ; pos+)
open import Cubical.Data.Int.IsEven using (isEvenTrue ; trueIsEven)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

------------------------------------------------------------------------
-- 1.  The two coordinate systems
------------------------------------------------------------------------

-- A pair of legs (p , q).
Pair : Type
Pair = ℤ × ℤ

-- Raw center-relative coordinates, before the parity constraint:
--   W = p + q  (center / sum),  R = q - p  (signed gap).
Φraw : Pair → ℤ × ℤ
Φraw (p , q) = (p + q , q - p)

-- Exchange of the two legs.
τ : Pair → Pair
τ (p , q) = (q , p)

-- One-leg sign reflection: the operation turning a sum into a difference.
J₂ : Pair → Pair
J₂ (p , q) = (p , - q)

-- Their center-relative forms, as Delta 16 states them.
τCR : ℤ × ℤ → ℤ × ℤ
τCR (W , R) = (W , - R)

J₂CR : ℤ × ℤ → ℤ × ℤ
J₂CR (W , R) = (- R , - W)

------------------------------------------------------------------------
-- 2.  Ring identities (all discharged by the commutative-ring solver)
------------------------------------------------------------------------

private
  -- Φraw intertwines the two presentations of each involution.
  e-τ-fst : (p q : ℤ) → q + p ≡ p + q
  e-τ-fst _ _ = solve! ℤCommRing
  e-τ-snd : (p q : ℤ) → p - q ≡ - (q - p)
  e-τ-snd _ _ = solve! ℤCommRing

  e-J-fst : (p q : ℤ) → p + (- q) ≡ - (q - p)
  e-J-fst _ _ = solve! ℤCommRing
  e-J-snd : (p q : ℤ) → (- q) - p ≡ - (p + q)
  e-J-snd _ _ = solve! ℤCommRing

  -- The two cone coordinates are the doubled legs.
  e-diff : (p q : ℤ) → (p + q) - (q - p) ≡ p + p
  e-diff _ _ = solve! ℤCommRing
  e-sum  : (p q : ℤ) → (p + q) + (q - p) ≡ q + q
  e-sum _ _ = solve! ℤCommRing

  -- Quadratic invariant.
  e-Qτ : (W R : ℤ) → W · W - (- R) · (- R) ≡ W · W - R · R
  e-Qτ _ _ = solve! ℤCommRing
  e-QJ : (W R : ℤ) → (- R) · (- R) - (- W) · (- W) ≡ - (W · W - R · R)
  e-QJ _ _ = solve! ℤCommRing
  e-Q4 : (p q : ℤ) →
         (p + q) · (p + q) - (q - p) · (q - p) ≡ (p · q) + (p · q) + ((p · q) + (p · q))
  e-Q4 _ _ = solve! ℤCommRing

  -- Round-trip identities for the equivalence.
  e-halfΦ : (p q : ℤ) → (p + q) - (q - p) ≡ pos 2 · p
  e-halfΦ _ _ = solve! ℤCommRing
  e-recoverq : (p q : ℤ) → (p + q) - p ≡ q
  e-recoverq _ _ = solve! ℤCommRing
  e-recoverW : (W m : ℤ) → m + (W - m) ≡ W
  e-recoverW _ _ = solve! ℤCommRing
  e-recoverR : (W R : ℤ) → R ≡ W - (W - R)
  e-recoverR _ _ = solve! ℤCommRing
  e-shift : (W m : ℤ) → W - pos 2 · m ≡ (W - m) - m
  e-shift _ _ = solve! ℤCommRing

------------------------------------------------------------------------
-- 3.  Target 2 — Theorem 16.1: J₂ swaps center and relative coordinates
------------------------------------------------------------------------

-- Exchange acts on (W , R) by negating the relative coordinate only.
thm16-1-τ : (x : Pair) → Φraw (τ x) ≡ τCR (Φraw x)
thm16-1-τ (p , q) i = e-τ-fst p q i , e-τ-snd p q i

-- The one-leg reflection swaps the two coordinates, up to sign.
-- This is Delta 16's Theorem 16.1 and its Corollary 16.2: the fixed-center
-- foliation is carried to the fixed-relative foliation.
thm16-1 : (x : Pair) → Φraw (J₂ x) ≡ J₂CR (Φraw x)
thm16-1 (p , q) i = e-J-fst p q i , e-J-snd p q i

-- Both are involutions of the center-relative plane.
τCR-involutive : (x : ℤ × ℤ) → τCR (τCR x) ≡ x
τCR-involutive (W , R) i = W , -Invol R i
  where
  -Invol : (n : ℤ) → - (- n) ≡ n
  -Invol (pos zero) = refl
  -Invol (pos (suc n)) = refl
  -Invol (negsuc n) = refl

J₂CR-involutive : (x : ℤ × ℤ) → J₂CR (J₂CR x) ≡ x
J₂CR-involutive (W , R) i = -Invol W i , -Invol R i
  where
  -Invol : (n : ℤ) → - (- n) ≡ n
  -Invol (pos zero) = refl
  -Invol (pos (suc n)) = refl
  -Invol (negsuc n) = refl

------------------------------------------------------------------------
-- 4.  Target 4 — the quadratic invariant Q = W² - R²
------------------------------------------------------------------------

Q : ℤ × ℤ → ℤ
Q (W , R) = W · W - R · R

-- Theorem 16.6, first half: exchange preserves Q.
thm16-6-τ : (x : ℤ × ℤ) → Q (τCR x) ≡ Q x
thm16-6-τ (W , R) = e-Qτ W R

-- Theorem 16.6, second half: the one-leg reflection negates Q.
thm16-6-J : (x : ℤ × ℤ) → Q (J₂CR x) ≡ - Q x
thm16-6-J (W , R) = e-QJ W R

-- Corollary 16.8, the delta's "strongest new compression":
--   (p+q)² - (q-p)² = 4pq.
-- The additive center/gap geometry and multiplication meet in one form.
thm16-8 : (p q : ℤ) → Q (Φraw (p , q)) ≡ (p · q) + (p · q) + ((p · q) + (p · q))
thm16-8 p q = e-Q4 p q

------------------------------------------------------------------------
-- 5.  Target 3 — the positive cone, and that J₂ leaves it
------------------------------------------------------------------------

-- Strict positivity, constructor-based (cubical v0.5 has no ℤ order module).
Pos : ℤ → Type
Pos n = Σ[ m ∈ ℕ ] n ≡ pos (suc m)

-- The interior W > |R| is exactly "both cone coordinates are positive":
--   W > R  and  W > - R,  i.e.  W - R > 0  and  W + R > 0.
InCone : ℤ × ℤ → Type
InCone (W , R) = Pos (W - R) × Pos (W + R)

-- A nonzero integer and its negation are never both positive.
posAnti : (n : ℤ) → Pos n → Pos (- n) → ⊥
posAnti n (a , pa) (b , pb) = posNotnegsuc (suc a) b (sym pa ∙ negEq)
  where
  -Invol : (k : ℤ) → - (- k) ≡ k
  -Invol (pos zero) = refl
  -Invol (pos (suc k)) = refl
  -Invol (negsuc k) = refl

  negEq : n ≡ negsuc b
  negEq = sym (-Invol n) ∙ cong -_ pb

-- Theorem 16.3, in the form that avoids an absolute value: the cone
-- coordinates of Φraw are the doubled legs.  So membership of the cone
-- is exactly positivity of both legs, doubled.
thm16-3-diff : (p q : ℤ) → (p + q) - (q - p) ≡ p + p
thm16-3-diff = e-diff

thm16-3-sum : (p q : ℤ) → (p + q) + (q - p) ≡ q + q
thm16-3-sum = e-sum

-- Corollary 16.5, positive half: exchange PRESERVES the cone.
-- (τCR negates R, which swaps the two cone coordinates.)
exchangePreservesCone : (x : ℤ × ℤ) → InCone x → InCone (τCR x)
exchangePreservesCone (W , R) (d , s) =
  subst Pos (sym (e1 W R)) s , subst Pos (sym (e2 W R)) d
  where
  e1 : (W R : ℤ) → W - (- R) ≡ W + R
  e1 _ _ = solve! ℤCommRing
  e2 : (W R : ℤ) → W + (- R) ≡ W - R
  e2 _ _ = solve! ℤCommRing

-- Theorem 16.4 / Corollary 16.5, the load-bearing half: the one-leg
-- reflection cannot preserve the cone.  It would demand that W + R and
-- its negation both be positive.
thm16-4 : (x : ℤ × ℤ) → InCone x → ¬ InCone (J₂CR x)
thm16-4 (W , R) (_ , s) (_ , s') =
  posAnti (W + R) s (subst Pos (e W R) s')
  where
  e : (W R : ℤ) → (- R) + (- W) ≡ - (W + R)
  e _ _ = solve! ℤCommRing

------------------------------------------------------------------------
-- 6.  Target 1 — the integral equivalence Pair ≃ CR
------------------------------------------------------------------------

-- The parity constraint W ≡ R (mod 2).  Because `isEven` is a decidable
-- Bool-valued function, the fibre is a proposition for free.
EvenT : ℤ → Type
EvenT n = isEven n ≡ true

isPropEvenT : (n : ℤ) → isProp (EvenT n)
isPropEvenT n = isSetBool (isEven n) true

-- L = {(W , R) ∈ ℤ² : W ≡ R mod 2}, as a Σ-type.
CR : Type
CR = Σ[ W ∈ ℤ ] Σ[ R ∈ ℤ ] EvenT (W - R)

2≢0 : ¬ (pos 2 ≡ pos 0)
2≢0 h = snotz (injPos h)
  where
  open import Cubical.Data.Nat using (snotz)

-- Doubling is injective on ℤ.
doubleInj : (m n : ℤ) → pos 2 · m ≡ pos 2 · n → m ≡ n
doubleInj m n h = ·lCancel (pos 2) m n h 2≢0

Φ : Pair → CR
Φ (p , q) =
  (p + q) , (q - p) , trueIsEven ((p + q) - (q - p)) (p , e-halfΦ p q)

Ψ : CR → Pair
Ψ (W , R , ev) = m , (W - m)
  where
  m : ℤ
  m = fst (isEvenTrue (W - R) ev)

ΨΦ : (x : Pair) → Ψ (Φ x) ≡ x
ΨΦ (p , q) = ΣPathP (mp , λ i → recover i)
  where
  ev : EvenT ((p + q) - (q - p))
  ev = trueIsEven ((p + q) - (q - p)) (p , e-halfΦ p q)

  m : ℤ
  m = fst (isEvenTrue ((p + q) - (q - p)) ev)

  mspec : ((p + q) - (q - p)) ≡ pos 2 · m
  mspec = snd (isEvenTrue ((p + q) - (q - p)) ev)

  mp : m ≡ p
  mp = sym (doubleInj p m (sym (e-halfΦ p q) ∙ mspec))

  recover : PathP (λ i → ℤ) ((p + q) - m) q
  recover = cong (λ z → (p + q) - z) mp ∙ e-recoverq p q

ΦΨ : (y : CR) → Φ (Ψ y) ≡ y
ΦΨ (W , R , ev) =
  ΣPathP (wpath ,
    ΣPathP (rpath ,
      isProp→PathP (λ i → isPropEvenT (wpath i - rpath i)) _ _))
  where
  m : ℤ
  m = fst (isEvenTrue (W - R) ev)

  mspec : (W - R) ≡ pos 2 · m
  mspec = snd (isEvenTrue (W - R) ev)

  wpath : m + (W - m) ≡ W
  wpath = e-recoverW W m

  rpath : PathP (λ i → ℤ) ((W - m) - m) R
  rpath = sym (e-recoverR W R ∙ cong (λ z → W - z) mspec ∙ e-shift W m)

Pair≅CR : Iso Pair CR
Pair≅CR = iso Φ Ψ ΦΨ ΨΦ

-- Delta 16 target 1: the integral, parity-compatible equivalence.
Pair≃CR : Pair ≃ CR
Pair≃CR = isoToEquiv Pair≅CR

-- ... and therefore a path, so every dependent structure transports.
Pair≡CR : Pair ≡ CR
Pair≡CR = ua Pair≃CR

------------------------------------------------------------------------
-- 7.  Controls (PROTOCOL.md (absent from this repository) §7: a claim ships with its own falsifiers)
------------------------------------------------------------------------

-- Control 1 — the cone is inhabited, so thm16-4 is not vacuous.
-- The pair (1 , 1) has centre 2 and gap 0.
coneInhabited : InCone (Φraw (pos 1 , pos 1))
coneInhabited = (1 , refl) , (1 , refl)

-- Control 2 — Pos is a real constraint: zero is not positive.
notPosZero : ¬ Pos (pos 0)
notPosZero (m , p) = snotz (sym (injPos p))
  where
  open import Cubical.Data.Nat using (snotz)

-- Control 3 — a worked instance of the quadratic compression, by refl:
-- the pair (2 , 3) has W = 5, R = 1, and 5² - 1² = 24 = 4·2·3.
thm16-8-instance : Q (Φraw (pos 2 , pos 3)) ≡ pos 24
thm16-8-instance = refl

-- Control 4 — the two involutions genuinely differ on the cone.
-- Exchange preserves it (exchangePreservesCone); the one-leg reflection
-- provably cannot (thm16-4).  This pair is Delta 16's Corollary 16.5.
corollary16-5 :
  ((x : ℤ × ℤ) → InCone x → InCone (τCR x)) ×
  ((x : ℤ × ℤ) → InCone x → ¬ InCone (J₂CR x))
corollary16-5 = exchangePreservesCone , thm16-4

------------------------------------------------------------------------
-- 8.  Delta 17 — the same cone at every place
--
-- Delta 17 §17.1 names u₋ = W - R and u₊ = W + R the "light-cone
-- coordinates" and observes they are the original factors doubled.
-- That is thm16-3-diff / thm16-3-sum above; it is restated here under
-- Delta 17's names and reused, not reproved.
--
-- The new content is T17.13 and C17.14: at every finite place ℓ the
-- valuation pair (v_ℓ p , v_ℓ q) carries its own centre-relative cone,
--   s = v_ℓ p + v_ℓ q,   d = v_ℓ q - v_ℓ p,   s ≥ |d|,  s ≡ d mod 2,
-- which Delta 17 calls "a genuine self-similarity" with the archimedean
-- pair geometry.  Section 8.3 makes precise in what sense it is one.
------------------------------------------------------------------------

-- 8.1  Light-cone coordinates (Delta 17 §17.1)

u₋ u₊ : ℤ × ℤ → ℤ
u₋ (W , R) = W - R
u₊ (W , R) = W + R

thm17-1-lower : (p q : ℤ) → u₋ (Φraw (p , q)) ≡ p + p
thm17-1-lower = thm16-3-diff

thm17-1-upper : (p q : ℤ) → u₊ (Φraw (p , q)) ≡ q + q
thm17-1-upper = thm16-3-sum

-- 8.2  T17.13 — the quadrant is exactly the closed cone

-- Valuations are non-negative, so the relevant cone is closed (s ≥ |d|),
-- not open (W > |R|) as in Delta 16's archimedean case.
NonNeg : ℤ → Type
NonNeg n = Σ[ m ∈ ℕ ] n ≡ pos m

-- s ≥ |d| without an absolute value: both light-cone coordinates ≥ 0.
ConeNN : ℤ × ℤ → Type
ConeNN x = NonNeg (u₋ x) × NonNeg (u₊ x)

private
  negsucDouble : (k : ℕ) → negsuc k + negsuc k ≡ negsuc (k +ℕ suc k)
  negsucDouble k = eNeg (pos (suc k)) ∙ cong -_ (sym (pos+ (suc k) (suc k)))
    where
    eNeg : (a : ℤ) → (- a) + (- a) ≡ - (a + a)
    eNeg _ = solve! ℤCommRing

  nonNegDouble : (n : ℤ) → NonNeg n → NonNeg (n + n)
  nonNegDouble n (m , p) = (m +ℕ m) , (cong₂ _+_ p p ∙ sym (pos+ m m))

  nonNegUndouble : (n : ℤ) → NonNeg (n + n) → NonNeg n
  nonNegUndouble (pos m) _ = m , refl
  nonNegUndouble (negsuc k) (m , p) =
    ⊥rec (posNotnegsuc m (k +ℕ suc k) (sym p ∙ negsucDouble k))

-- T17.13, forward: a non-negative valuation pair lands in the cone.
thm17-13-fwd : (a b : ℤ) → NonNeg a × NonNeg b → ConeNN (Φraw (a , b))
thm17-13-fwd a b (na , nb) =
  subst NonNeg (sym (thm17-1-lower a b)) (nonNegDouble a na) ,
  subst NonNeg (sym (thm17-1-upper a b)) (nonNegDouble b nb)

-- T17.13, backward: the cone contains nothing else.
thm17-13-bwd : (a b : ℤ) → ConeNN (Φraw (a , b)) → NonNeg a × NonNeg b
thm17-13-bwd a b (cl , cu) =
  nonNegUndouble a (subst NonNeg (thm17-1-lower a b) cl) ,
  nonNegUndouble b (subst NonNeg (thm17-1-upper a b) cu)

-- 8.3  C17.14 — in what sense the self-similarity is real
--
-- Delta 17 reads the repetition of (sum , difference) at the archimedean
-- place and at every finite place as a self-similarity between additive
-- pair geometry and multiplicative valuation geometry.
--
-- It is real, and it is weaker than it looks: there are not two theorems
-- here that happen to match.  There is ONE theorem about a pair of
-- integers, used twice.  The two instantiations below are the SAME TERM;
-- Agda accepts them by definition, with no proof in between.
--
--   archimedeanCone — a and b are the two legs (p , q);
--   localCone       — a and b are the two valuations (v_ℓ p , v_ℓ q).
--
-- So C17.14 is earned, but what it earns is a re-use, not a coincidence.
-- The parity constraint s ≡ d mod 2 that Delta 17 states alongside is
-- likewise not new here: it is exactly the sublattice CR of section 6,
-- and Pair≃CR already gives the equivalence for arbitrary integers.

archimedeanCone : (p q : ℤ) → NonNeg p × NonNeg q → ConeNN (Φraw (p , q))
archimedeanCone = thm17-13-fwd

localCone : (vp vq : ℤ) → NonNeg vp × NonNeg vq → ConeNN (Φraw (vp , vq))
localCone = thm17-13-fwd

sameTheorem : archimedeanCone ≡ localCone
sameTheorem = refl

-- Control — the closed cone is strictly larger than Delta 16's open one:
-- the zero valuation pair is in ConeNN and not in InCone.
zeroInClosedCone : ConeNN (Φraw (pos 0 , pos 0))
zeroInClosedCone = (0 , refl) , (0 , refl)

zeroNotInOpenCone : ¬ InCone (Φraw (pos 0 , pos 0))
zeroNotInOpenCone ((m , p) , _) = snotz (sym (injPos p))
  where
  open import Cubical.Data.Nat using (snotz)
