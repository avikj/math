{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.PythagoreanTransition
--
-- `SuccessorIsNotTropical` ends with a sentence this corpus never acted
-- on:  "The object to build is the transition itself."
--
-- Here it is built.  Not on the line, where it does not exist, but on the
-- conic, where it does — and the construction is Brahmagupta's, 628 CE.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT WAS ACTUALLY PROVED IN `SuccessorIsNotTropical`
--
-- `disjoint-support` says: no prime divides two consecutive integers, so
-- n and n+1 share NOT ONE coordinate in the multiplicative chart.  That
-- was read here as "the parity barrier is a chart incompatibility".
--
-- That reading over-claims, and this module is the correction.  What was
-- proved is a fact about ℕ **with the successor as its additive law**.
-- It is not a fact about arithmetic.  It is a fact about a particular
-- additive structure whose generator, 1, is multiplicatively invisible —
-- a unit, hence norm 1 in a chart where norms are all that is seen.
--
-- ────────────────────────────────────────────────────────────────────
-- THE CONIC HAS THE TRANSITION, EXACTLY
--
-- Put the additive law on a circle instead of a line.  A point is a pair
-- (a,b); the norm is a² + b²; and the group law is
--
--     (a₁,b₁) ⊗ (a₂,b₂) = (a₁a₂ − b₁b₂ , a₁b₂ + a₂b₁).
--
-- This is **samāsa-bhāvanā at D = −1** — Brāhmasphuṭasiddhānta ch. 18,
-- 628 CE, the composition law whose whole content is that the norm is
-- multiplicative.  `Bhavana.agda` (absent from this repository) in this repository already checks the
-- general D; this module takes D = −1, which is the case that is a
-- CIRCLE, and asks what the circle's additive law does to the chart.
--
-- The answer is the sharpest possible contrast with `disjoint-support`:
--
--     N (u ⊗ g)  ≡  N u · N g                       (`rot-norm`)
--
-- The conic's successor — translation by a fixed g — is not merely
-- visible in the multiplicative chart.  It is MULTIPLICATION BY A
-- CONSTANT there.  Where ℕ's successor has zero locality, the circle's
-- has total locality.  Same arithmetic, different additive law, opposite
-- answer.  So the barrier is not arithmetic's; it belongs to the line.
--
-- ────────────────────────────────────────────────────────────────────
-- THE TRIPLES ARE THE GROUP, AND EUCLID'S FORMULA IS SQUARING
--
-- A Pythagorean triple is a pair whose norm is a square.  Then:
--
--   * `triple-⊗`  triples are CLOSED under bhvan.  (3,4,5) composed
--     with (5,12,13) is (33,56,65) — checked by `refl` at the bottom of
--     this file.  Triples are not a list; they are a monoid.
--
--   * `euclid`  every pair squares to a triple, with hypotenuse its own
--     norm: gen (p,q) = (p²−q², 2pq) and N (gen t) = (N t)².  Euclid's
--     parametrisation is the single word **squaring**, once the pair is
--     the object rather than the number.
--
--   * `gen-hom`  and this is the transition map: squaring is a monoid
--     homomorphism,  gen (s ⊗ t) ≡ gen s ⊗ gen t.  The parameter chart
--     and the triple chart carry the SAME composition, intertwined by
--     the parametrisation.  One chart change, no defect, exactly.
--
-- ────────────────────────────────────────────────────────────────────
-- WHERE UNIVALENCE ENTERS, AND IT IS NOT DECORATION
--
-- When N g ≡ 1, `rot g` is invertible — its inverse is composition with
-- the conjugate, which is antara-bhvan, Brahmagupta's second law.  So
-- `rotEquiv` is an equivalence of the pair-type with itself, `rotPath`
-- is the identification univalence supplies, and `defect-vanishes`
-- computes Delta 15's structured defect for the norm along it: it is
-- refl-level zero.  The circle's translations are identifications of
-- the circle carrying its structure with itself.
--
-- The line has no such family: by `disjoint-support` the successor
-- carries NO multiplicative structure along.  Two additive laws, one
-- arithmetic; one is a family of structured identifications and one is
-- not.  That difference — not any statement about primes — is what the
-- barrier language has been pointing at.
--
-- Everything below is proved over an ARBITRARY commutative ring, so it
-- holds over ℤ, over ℚ, and over every ring the repository may later
-- want.  Ring identities go through the CommRingSolver — exact symbolic
-- computation, which CLAUDE.md (absent from this repository) admits as proof; nothing is measured.
------------------------------------------------------------------------

module NaturalMachine.PythagoreanTransition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The circle over any commutative ring
------------------------------------------------------------------------

module Circle (R : CommRing ℓ) where

  open CommRingStr (snd R)

  A : Type ℓ
  A = fst R

  Pair : Type ℓ
  Pair = A × A

  -- the norm: this is the form x² + y², i.e. x² − D y² at D = −1
  N : Pair → A
  N u = fst u · fst u + snd u · snd u

  infixl 7 _⊗_

  -- समास-भावना, D = −1
  _⊗_ : Pair → Pair → Pair
  u ⊗ v = ((fst u · fst v) - (snd u · snd v))
        , ((fst u · snd v) + (fst v · snd u))

  -- अन्तर-भावना: the same law with the second sign flipped
  conj : Pair → Pair
  conj u = fst u , (- snd u)

  one : Pair
  one = 1r , 0r

  ----------------------------------------------------------------------
  -- The ring identities.  Each is a polynomial identity in the ring's
  -- own variables, discharged by the solver: exact, not measured.
  ----------------------------------------------------------------------

  private
    brahmagupta :
      (a₁ b₁ a₂ b₂ : A) →
        ((a₁ · a₂) - (b₁ · b₂)) · ((a₁ · a₂) - (b₁ · b₂))
      + ((a₁ · b₂) + (a₂ · b₁)) · ((a₁ · b₂) + (a₂ · b₁))
      ≡ (a₁ · a₁ + b₁ · b₁) · (a₂ · a₂ + b₂ · b₂)
    brahmagupta a₁ b₁ a₂ b₂ = solve! R

    sq-· : (z w : A) → (z · z) · (w · w) ≡ (z · w) · (z · w)
    sq-· z w = solve! R

    ·-one : (x : A) → x · 1r ≡ x
    ·-one x = solve! R

    idʳ-fst : (a b : A) → (a · 1r) - (b · 0r) ≡ a
    idʳ-fst a b = solve! R

    idʳ-snd : (a b : A) → (a · 0r) + (1r · b) ≡ b
    idʳ-snd a b = solve! R

    comm-fst : (a₁ b₁ a₂ b₂ : A) →
               (a₁ · a₂) - (b₁ · b₂) ≡ (a₂ · a₁) - (b₂ · b₁)
    comm-fst a₁ b₁ a₂ b₂ = solve! R

    comm-snd : (a₁ b₁ a₂ b₂ : A) →
               (a₁ · b₂) + (a₂ · b₁) ≡ (a₂ · b₁) + (a₁ · b₂)
    comm-snd a₁ b₁ a₂ b₂ = solve! R

    assoc-fst : (a₁ b₁ a₂ b₂ a₃ b₃ : A) →
        (((a₁ · a₂) - (b₁ · b₂)) · a₃) - (((a₁ · b₂) + (a₂ · b₁)) · b₃)
      ≡ (a₁ · ((a₂ · a₃) - (b₂ · b₃))) - (b₁ · ((a₂ · b₃) + (a₃ · b₂)))
    assoc-fst a₁ b₁ a₂ b₂ a₃ b₃ = solve! R

    assoc-snd : (a₁ b₁ a₂ b₂ a₃ b₃ : A) →
        (((a₁ · a₂) - (b₁ · b₂)) · b₃) + (a₃ · ((a₁ · b₂) + (a₂ · b₁)))
      ≡ (a₁ · ((a₂ · b₃) + (a₃ · b₂))) + (((a₂ · a₃) - (b₂ · b₃)) · b₁)
    assoc-snd a₁ b₁ a₂ b₂ a₃ b₃ = solve! R

    conj-fst : (a b : A) → (a · a) - (b · (- b)) ≡ a · a + b · b
    conj-fst a b = solve! R

    conj-snd : (a b : A) → (a · (- b)) + (a · b) ≡ 0r
    conj-snd a b = solve! R

  ----------------------------------------------------------------------
  -- 1.  Brahmagupta: the norm is multiplicative
  ----------------------------------------------------------------------

  N-⊗ : (u v : Pair) → N (u ⊗ v) ≡ N u · N v
  N-⊗ u v = brahmagupta (fst u) (snd u) (fst v) (snd v)

  ----------------------------------------------------------------------
  -- 2.  (Pair, ⊗, one) is a commutative monoid
  ----------------------------------------------------------------------

  ⊗-idʳ : (u : Pair) → u ⊗ one ≡ u
  ⊗-idʳ u = ΣPathP (idʳ-fst (fst u) (snd u) , idʳ-snd (fst u) (snd u))

  ⊗-comm : (u v : Pair) → u ⊗ v ≡ v ⊗ u
  ⊗-comm u v = ΣPathP ( comm-fst (fst u) (snd u) (fst v) (snd v)
                      , comm-snd (fst u) (snd u) (fst v) (snd v) )

  ⊗-assoc : (u v w : Pair) → (u ⊗ v) ⊗ w ≡ u ⊗ (v ⊗ w)
  ⊗-assoc u v w =
    ΣPathP ( assoc-fst (fst u) (snd u) (fst v) (snd v) (fst w) (snd w)
           , assoc-snd (fst u) (snd u) (fst v) (snd v) (fst w) (snd w) )

  ⊗-conj : (u : Pair) → u ⊗ conj u ≡ (N u , 0r)
  ⊗-conj u = ΣPathP (conj-fst (fst u) (snd u) , conj-snd (fst u) (snd u))

  ----------------------------------------------------------------------
  -- 3.  THE CONTRAST WITH `SuccessorIsNotTropical`.
  --
  -- On the line, `disjoint-support`: the successor shares no coordinate
  -- with its argument in the multiplicative chart.  On the circle, the
  -- successor multiplies the norm by a constant.  Total locality.
  ----------------------------------------------------------------------

  rot : Pair → Pair → Pair
  rot g u = u ⊗ g

  rot-norm : (g u : Pair) → N (rot g u) ≡ N u · N g
  rot-norm g u = N-⊗ u g

  ----------------------------------------------------------------------
  -- 4.  Triples: closed under bhvan, generated by squaring
  ----------------------------------------------------------------------

  IsTriple : Pair → A → Type ℓ
  IsTriple u z = N u ≡ z · z

  triple-⊗ : (u v : Pair) (z w : A)
           → IsTriple u z → IsTriple v w → IsTriple (u ⊗ v) (z · w)
  triple-⊗ u v z w hu hv = N-⊗ u v ∙ cong₂ _·_ hu hv ∙ sq-· z w

  -- Euclid's parametrisation IS squaring in this monoid
  gen : Pair → Pair
  gen t = t ⊗ t

  euclid : (t : Pair) → IsTriple (gen t) (N t)
  euclid t = N-⊗ t t

  -- THE TRANSITION MAP: the parametrisation intertwines the two
  -- composition laws, so parameter chart and triple chart are one chart.
  gen-hom : (s t : Pair) → gen (s ⊗ t) ≡ gen s ⊗ gen t
  gen-hom s t =
      ⊗-assoc s t (s ⊗ t)
    ∙ cong (s ⊗_) ( sym (⊗-assoc t s t)
                  ∙ cong (_⊗ t) (⊗-comm t s)
                  ∙ ⊗-assoc s t t )
    ∙ sym (⊗-assoc s s (t ⊗ t))

  ----------------------------------------------------------------------
  -- 5.  Norm-one rotations are equivalences (Voevodsky), and their
  --     structured defect for the norm vanishes (Delta 15).
  ----------------------------------------------------------------------

  rot-invˡ : (g u : Pair) → N g ≡ 1r → rot (conj g) (rot g u) ≡ u
  rot-invˡ g u h =
      ⊗-assoc u g (conj g)
    ∙ cong (u ⊗_) (⊗-conj g ∙ cong (λ x → (x , 0r)) h)
    ∙ ⊗-idʳ u

  rot-invʳ : (g u : Pair) → N g ≡ 1r → rot g (rot (conj g) u) ≡ u
  rot-invʳ g u h =
      ⊗-assoc u (conj g) g
    ∙ cong (u ⊗_) ( ⊗-comm (conj g) g
                  ∙ ⊗-conj g
                  ∙ cong (λ x → (x , 0r)) h )
    ∙ ⊗-idʳ u

  rotIso : (g : Pair) → N g ≡ 1r → Iso Pair Pair
  Iso.fun      (rotIso g h)   = rot g
  Iso.inv      (rotIso g h)   = rot (conj g)
  Iso.rightInv (rotIso g h) u = rot-invʳ g u h
  Iso.leftInv  (rotIso g h) u = rot-invˡ g u h

  rotEquiv : (g : Pair) → N g ≡ 1r → Pair ≃ Pair
  rotEquiv g h = isoToEquiv (rotIso g h)

  -- univalence: a translation of the circle IS an identification of the
  -- circle with itself
  rotPath : (g : Pair) → N g ≡ 1r → Pair ≡ Pair
  rotPath g h = ua (rotEquiv g h)

  -- and it carries the structure exactly: zero structured defect
  rot-preserves-N : (g : Pair) → N g ≡ 1r → (u : Pair) → N (rot g u) ≡ N u
  rot-preserves-N g h u = rot-norm g u ∙ cong (N u ·_) h ∙ ·-one (N u)

  Defect : (g : Pair) → N g ≡ 1r → Type ℓ
  Defect g h = (λ u → N (rot g u)) ≡ N

  defect-vanishes : (g : Pair) (h : N g ≡ 1r) → Defect g h
  defect-vanishes g h = funExt (rot-preserves-N g h)

------------------------------------------------------------------------
-- 6.  It runs.  Over ℤ, by computation.
--
--   gen (2,1)        = (3,4)          — the 3-4-5 triple, by squaring
--   (3,4) ⊗ (5,12)   = (−33,56)       — 33² + 56² = 65² = (5·13)²
--
-- Triples compose.  The two smallest primitive triples produce a third
-- by Brahmagupta's law, and its hypotenuse is the product of theirs.
------------------------------------------------------------------------

open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)

open Circle ℤCommRing

t₂₁ : Pair
t₂₁ = pos 2 , pos 1

gen-2-1 : gen t₂₁ ≡ (pos 3 , pos 4)
gen-2-1 = refl

tri345 : Pair
tri345 = pos 3 , pos 4

tri51213 : Pair
tri51213 = pos 5 , pos 12

composite : tri345 ⊗ tri51213 ≡ (negsuc 32 , pos 56)
composite = refl

-- and its norm is 65², the product of the two hypotenuses
composite-norm : N (tri345 ⊗ tri51213) ≡ pos 4225
composite-norm = refl

composite-is-triple : IsTriple (tri345 ⊗ tri51213) (pos 65)
composite-is-triple = refl
