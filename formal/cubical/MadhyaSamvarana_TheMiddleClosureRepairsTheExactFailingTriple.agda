{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- मध्य-संवरणम् — madhya-saṃvaraṇa, "middle closing".
--
-- ON THE NAME.  Descriptive , formed to match
-- `EkaparsvaSamvarana` (एकपार्श्व, one-sided) in the companion module:
-- मध्य madhya "middle" + संवरण saṃvaraṇa "closing".  NO classical source
-- is claimed and none exists; the mathematics is 20th/21st century.
-- The label is a gloss and asserts no provenance.  The standard the
-- file is written to is the owner's own constitutional maxim,
-- समता प्रमाणेन — equivalence by proof, not resemblance (D0026 §10.6).
--
-- SOURCE.  collab/upstream/raw/D0026-owner-egb-core-transmission-v2-2026-08-16.md (absent from this repository)
-- §2.5 "Two-sided contextual saturation repairs composition", captured
-- 2026-08-16, `content_origin: direct-user`.  §2.5 marks itself
-- "↳ Exact theorem in the inherited middle-type calculus; ◆ contextual
-- repair inside DSO"; both marks stand and this module does not upgrade
-- either.  Verbatim from §2.5:
--
--     M₃(x,b,z) = p(xbz) − p(x) − p(b) − p(z)
--     N(b,(x,z)) = M₃(x,b,z)
--     N*f(x,z)  = inf_b   ( M₃(x,b,z) − f(b) )
--     N_*g(b)   = inf_{x,z} ( M₃(x,b,z) − g(x,z) )
--     f ⊙ g    := N_* N*(f ⋆ g)
--     (f ⊙ g) ⊙ h = f ⊙ (g ⊙ h)
--
-- WHAT IS CHECKED.  §2.5's associativity is a GENERAL theorem,
-- quantified over all profiles.  What is proved here is the sharp
-- instance: the exact
-- triple that breaks one-sided closure in §2.4 — ℓ_c, ℓ_a, ℓ_c — is
-- repaired by the middle closure, pointwise, by `refl`.
--
--     §2.4:  (ℓ_c ⊙ᴸ ℓ_a) ⊙ᴸ ℓ_c  =  (−8,−2,−2,−8)
--            ℓ_c ⊙ᴸ (ℓ_a ⊙ᴸ ℓ_c)  =  (−5,−2,−2,−5)      DIFFERENT
--
--     here:  (ℓ_c ⊙  ℓ_a) ⊙  ℓ_c  ≡  ℓ_c ⊙  (ℓ_a ⊙  ℓ_c)  EQUAL
--
-- So clause four of D0026 §14.1 ("middle associativity") is NOT
-- discharged.  Its one decisive instance is.  Saying otherwise would be
-- the move §0's alphabet forbids: promoting ☑ (finite mechanical
-- verification) to ⊢ or ↳.
--
-- Every infimum below is over the four-element carrier or the sixteen
-- element context space C × C, so all of them are finite `minℤ` nests
-- and the ambient-ordered-algebra question of §14.1 does not arise
-- here.  It arises for the general theorem, and there it is open.
------------------------------------------------------------------------

module MadhyaSamvarana_TheMiddleClosureRepairsTheExactFailingTriple where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; _+_ ; _-_)
open import Cubical.Data.Int.Properties using (injNegsuc)
open import Cubical.Data.Nat.Properties using (injSuc ; snotz)
open import Cubical.Relation.Nullary using (¬_)

open import EkaparsvaSamvarana_TheOneSidedClosureCounterexampleIsExact
  using ( C ; e ; a ; c ; d ; _⋆_ ; p ; M ; Prof
        ; minℤ ; conv ; _⊙ᴸ_ ; ℓc ; ℓa ; leℤ )

------------------------------------------------------------------------
-- 1.  The middle kernel, D0026 §2.5.
--
-- M₃ is taken at the right-associated bracketing; by `assoc⋆` in the
-- companion module the choice is immaterial for this carrier.
------------------------------------------------------------------------

M₃ : C → C → C → ℤ
M₃ x b z = (((p (x ⋆ (b ⋆ z)) - p x) - p b) - p z)

-- §2.5 states  M₃(x,b,z) = M(x,bz) + M(b,z) = M(xb,z) + M(x,b).
-- Both decompositions, on this carrier, by refl.  (The general form of
-- the first needs no hypothesis; the second needs p-associativity, which
-- here is a consequence of `assoc⋆` and is checked below case by case.)

M₃-right : (x b z : C) → M₃ x b z ≡ (M x (b ⋆ z)) + (M b z)
M₃-right e e e = refl
M₃-right e e a = refl
M₃-right e e c = refl
M₃-right e e d = refl
M₃-right e a e = refl
M₃-right e a a = refl
M₃-right e a c = refl
M₃-right e a d = refl
M₃-right e c e = refl
M₃-right e c a = refl
M₃-right e c c = refl
M₃-right e c d = refl
M₃-right e d e = refl
M₃-right e d a = refl
M₃-right e d c = refl
M₃-right e d d = refl
M₃-right a e e = refl
M₃-right a e a = refl
M₃-right a e c = refl
M₃-right a e d = refl
M₃-right a a e = refl
M₃-right a a a = refl
M₃-right a a c = refl
M₃-right a a d = refl
M₃-right a c e = refl
M₃-right a c a = refl
M₃-right a c c = refl
M₃-right a c d = refl
M₃-right a d e = refl
M₃-right a d a = refl
M₃-right a d c = refl
M₃-right a d d = refl
M₃-right c e e = refl
M₃-right c e a = refl
M₃-right c e c = refl
M₃-right c e d = refl
M₃-right c a e = refl
M₃-right c a a = refl
M₃-right c a c = refl
M₃-right c a d = refl
M₃-right c c e = refl
M₃-right c c a = refl
M₃-right c c c = refl
M₃-right c c d = refl
M₃-right c d e = refl
M₃-right c d a = refl
M₃-right c d c = refl
M₃-right c d d = refl
M₃-right d e e = refl
M₃-right d e a = refl
M₃-right d e c = refl
M₃-right d e d = refl
M₃-right d a e = refl
M₃-right d a a = refl
M₃-right d a c = refl
M₃-right d a d = refl
M₃-right d c e = refl
M₃-right d c a = refl
M₃-right d c c = refl
M₃-right d c d = refl
M₃-right d d e = refl
M₃-right d d a = refl
M₃-right d d c = refl
M₃-right d d d = refl

M₃-left : (x b z : C) → M₃ x b z ≡ (M (x ⋆ b) z) + (M x b)
M₃-left e e e = refl
M₃-left e e a = refl
M₃-left e e c = refl
M₃-left e e d = refl
M₃-left e a e = refl
M₃-left e a a = refl
M₃-left e a c = refl
M₃-left e a d = refl
M₃-left e c e = refl
M₃-left e c a = refl
M₃-left e c c = refl
M₃-left e c d = refl
M₃-left e d e = refl
M₃-left e d a = refl
M₃-left e d c = refl
M₃-left e d d = refl
M₃-left a e e = refl
M₃-left a e a = refl
M₃-left a e c = refl
M₃-left a e d = refl
M₃-left a a e = refl
M₃-left a a a = refl
M₃-left a a c = refl
M₃-left a a d = refl
M₃-left a c e = refl
M₃-left a c a = refl
M₃-left a c c = refl
M₃-left a c d = refl
M₃-left a d e = refl
M₃-left a d a = refl
M₃-left a d c = refl
M₃-left a d d = refl
M₃-left c e e = refl
M₃-left c e a = refl
M₃-left c e c = refl
M₃-left c e d = refl
M₃-left c a e = refl
M₃-left c a a = refl
M₃-left c a c = refl
M₃-left c a d = refl
M₃-left c c e = refl
M₃-left c c a = refl
M₃-left c c c = refl
M₃-left c c d = refl
M₃-left c d e = refl
M₃-left c d a = refl
M₃-left c d c = refl
M₃-left c d d = refl
M₃-left d e e = refl
M₃-left d e a = refl
M₃-left d e c = refl
M₃-left d e d = refl
M₃-left d a e = refl
M₃-left d a a = refl
M₃-left d a c = refl
M₃-left d a d = refl
M₃-left d c e = refl
M₃-left d c a = refl
M₃-left d c c = refl
M₃-left d c d = refl
M₃-left d d e = refl
M₃-left d d a = refl
M₃-left d d c = refl
M₃-left d d d = refl

------------------------------------------------------------------------
-- 2.  The middle conjugates and the middle closure.
--
-- A context is a pair (x,z); the context space here has sixteen
-- elements, so N_* is a nest of fifteen `minℤ`.
------------------------------------------------------------------------

Ctx : Type₀
Ctx = C → C → ℤ

min4 : (C → ℤ) → ℤ
min4 h = minℤ (h e) (minℤ (h a) (minℤ (h c) (h d)))

conjN* : Prof → Ctx                       -- N*f(x,z) = inf_b (M₃(x,b,z) − f b)
conjN* f x z = min4 (λ b → M₃ x b z - f b)

conjN⋆ : Ctx → Prof                       -- N_*g(b) = inf_{x,z} (M₃(x,b,z) − g x z)
conjN⋆ g b = min4 (λ x → min4 (λ z → M₃ x b z - g x z))

infixl 6 _⊙_
_⊙_ : Prof → Prof → Prof
f ⊙ g = conjN⋆ (conjN* (conv f g))

------------------------------------------------------------------------
-- 3.  The repair, on the exact triple that broke one-sided closure.
--
-- §2.4's failure, reproduced in the companion module:
--     (ℓ_c ⊙ᴸ ℓ_a) ⊙ᴸ ℓ_c ≠ ℓ_c ⊙ᴸ (ℓ_a ⊙ᴸ ℓ_c)   at e and at d.
--
-- The same triple under the middle closure:
------------------------------------------------------------------------

middle-assoc-on-the-failing-triple
  : (t : C) → ((ℓc ⊙ ℓa) ⊙ ℓc) t ≡ (ℓc ⊙ (ℓa ⊙ ℓc)) t
middle-assoc-on-the-failing-triple e = refl
middle-assoc-on-the-failing-triple a = refl
middle-assoc-on-the-failing-triple c = refl
middle-assoc-on-the-failing-triple d = refl

------------------------------------------------------------------------
-- 3.1  The value, which is not either one-sided answer.
--
-- Not stated in §2.5, and worth recording, because the obvious guess is
-- wrong.  On the failing triple:
--
--     (ℓ_c ⊙ᴸ ℓ_a) ⊙ᴸ ℓ_c  =  (−8, −2, −2, −8)     §2.4, left
--      ℓ_c ⊙ᴸ (ℓ_a ⊙ᴸ ℓ_c) =  (−5, −2, −2, −5)     §2.4, right
--     (ℓ_c ⊙  ℓ_a) ⊙  ℓ_c  =  (−8, −5, −2, −8)     middle, either way
--
-- The middle closure does not adjudicate between the two one-sided
-- answers by choosing one.  It returns a third profile, pointwise ≤
-- both, strictly below both at `a`.  Saturating against every insertion
-- context costs information at a point where NEITHER one-sided
-- bracketing lost any — which is §2.5's own condition read exactly:
-- "a distinction may be discarded only after proving every supported
-- insertion context is insensitive to it."  Here no context is
-- insensitive at `a`, so nothing may be discarded there, and the
-- profile drops.
------------------------------------------------------------------------

mid-e : ((ℓc ⊙ ℓa) ⊙ ℓc) e ≡ negsuc 7 ;  mid-e = refl   -- −8
mid-a : ((ℓc ⊙ ℓa) ⊙ ℓc) a ≡ negsuc 4 ;  mid-a = refl   -- −5
mid-c : ((ℓc ⊙ ℓa) ⊙ ℓc) c ≡ negsuc 1 ;  mid-c = refl   -- −2
mid-d : ((ℓc ⊙ ℓa) ⊙ ℓc) d ≡ negsuc 7 ;  mid-d = refl   -- −8

-- and it sits below both one-sided bracketings, pointwise
mid≤left : (t : C) → leℤ (((ℓc ⊙ ℓa) ⊙ ℓc) t) (((ℓc ⊙ᴸ ℓa) ⊙ᴸ ℓc) t)
mid≤left e = refl
mid≤left a = refl
mid≤left c = refl
mid≤left d = refl

mid≤right : (t : C) → leℤ (((ℓc ⊙ ℓa) ⊙ ℓc) t) ((ℓc ⊙ᴸ (ℓa ⊙ᴸ ℓc)) t)
mid≤right e = refl
mid≤right a = refl
mid≤right c = refl
mid≤right d = refl

-- strictly below both at `a`:  −5 ≠ −2
mid-drops-at-a : ¬ (((ℓc ⊙ ℓa) ⊙ ℓc) a ≡ ((ℓc ⊙ᴸ ℓa) ⊙ᴸ ℓc) a)
mid-drops-at-a h = snotz (injSuc (injNegsuc h))

------------------------------------------------------------------------
-- 4.  The side condition.
--
-- §2.5's own lesson is stated as a side condition and is
-- worth carrying verbatim rather than paraphrased:
--
--     "The exact lesson is not that every microscopic detail must be
--      retained.  It is that a distinction may be discarded only after
--      proving every supported insertion context is insensitive to it."
--
-- Which is why the context space, not the carrier, is what N_* ranges
-- over — and why §3.1's drop at `a` is the repair working rather than
-- the repair costing something.
------------------------------------------------------------------------
