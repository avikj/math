{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- एकपार्श्व-संवरणम् — ekapārśva-saṃvaraṇa, "one-sided closing".
--
-- ON THE NAME.  Descriptive  for the operation D0026 §2.4 calls
-- one-sided closure (एक eka "one" + पार्श्व pārśva "side" + संवरण
-- savaraa "closing, shutting").
--
-- SOURCE.  collab/upstream/raw/D0026-owner-egb-core-transmission-v2-2026-08-16.md (absent from this repository)
-- §2.4 "One-sided closure can destroy associativity", captured
-- 2026-08-16, `content_origin: direct-user`, SHA-256 in
-- collab/upstream/catalog.jsonl.  §2.4 marks itself
--
--     "↳ Exact inherited counterexample; ☑ reproduced by the corpus
--      finite calibration."
--
-- so under the epistemic alphabet of §0 the counterexample is INHERITED
-- (↳), not originated in that corpus, and its reproduction is a finite
-- mechanical check (☑).  This module does not upgrade either mark.  It
-- adds a third reproduction, in a kernel, and reports what it found.
--
-- WHY.  D0026 §14.1 states the acceptance test:
--
--     "Acceptance: a kernel-checked Lean, Agda, or Coq development
--      reproducing the trefoil law, Isbell closures, the exact
--      counterexample, middle associativity, residual laws, and
--      derived-nucleus construction under explicit constructive
--      assumptions."
--
-- Clause one is discharged in
-- `EqualityPramanena_TheTrefoilLawIsExactlyPAssociativity (absent from this repository).agda` (absent from this repository).  This
-- module discharges the clause named "the exact counterexample", and
-- with it the Isbell conjugates and one-sided closure it is stated in
-- terms of.
--
-- WHAT IS CHECKED.  Everything below is a finite exhaustive computation
-- on a four-element carrier with integer weights, decided by `refl` in
-- the kernel.  Per CLAUDE.md (absent from this repository), exact/certified symbolic computation IS
-- proof; no floating point, no measurement, no fitted quantity appears.
------------------------------------------------------------------------

module EkaparsvaSamvarana_TheOneSidedClosureCounterexampleIsExact where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Properties using (injSuc ; snotz)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; _+_ ; _-_)
open import Cubical.Data.Int.Properties using (injNegsuc)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 0.  max and min on ℤ.
--
-- The cubical library (v0.5) carries no order on ℤ, so both are
-- defined here by structural recursion on the constructors.  `negsuc n`
-- denotes −(n+1), so on that branch the order reverses: the larger of
-- two negsuc values is the one with the SMALLER ℕ index.
------------------------------------------------------------------------

maxℕ : ℕ → ℕ → ℕ
maxℕ zero    n       = n
maxℕ (suc m) zero    = suc m
maxℕ (suc m) (suc n) = suc (maxℕ m n)

minℕ : ℕ → ℕ → ℕ
minℕ zero    _       = zero
minℕ (suc m) zero    = zero
minℕ (suc m) (suc n) = suc (minℕ m n)

maxℤ : ℤ → ℤ → ℤ
maxℤ (pos m)    (pos n)    = pos (maxℕ m n)
maxℤ (pos m)    (negsuc _) = pos m
maxℤ (negsuc _) (pos n)    = pos n
maxℤ (negsuc m) (negsuc n) = negsuc (minℕ m n)

minℤ : ℤ → ℤ → ℤ
minℤ (pos m)    (pos n)    = pos (minℕ m n)
minℤ (pos _)    (negsuc n) = negsuc n
minℤ (negsuc m) (pos _)    = negsuc m
minℤ (negsuc m) (negsuc n) = negsuc (maxℕ m n)

-- sanity, by refl: the reversal on the negative branch is not a typo
max-neg : maxℤ (negsuc 5) (negsuc 2) ≡ negsuc 2      -- max(−6,−3) = −3
max-neg = refl

min-neg : minℤ (negsuc 5) (negsuc 2) ≡ negsuc 5      -- min(−6,−3) = −6
min-neg = refl

max-mixed : maxℤ (negsuc 5) (pos 1) ≡ pos 1          -- max(−6, 1) =  1
max-mixed = refl

-- and the order itself, decided, for the direction of §6(ii)
_≤ᵇℕ_ : ℕ → ℕ → Bool
zero  ≤ᵇℕ _     = true
suc _ ≤ᵇℕ zero  = false
suc m ≤ᵇℕ suc n = m ≤ᵇℕ n

_≤ᵇ_ : ℤ → ℤ → Bool
pos m    ≤ᵇ pos n    = m ≤ᵇℕ n
pos _    ≤ᵇ negsuc _ = false
negsuc _ ≤ᵇ pos _    = true
negsuc m ≤ᵇ negsuc n = n ≤ᵇℕ m           -- −(m+1) ≤ −(n+1)  ⟺  n ≤ m

leℤ : ℤ → ℤ → Type₀
leℤ x y = (x ≤ᵇ y) ≡ true

le-neg : leℤ (negsuc 7) (negsuc 4)                   -- −8 ≤ −5
le-neg = refl

------------------------------------------------------------------------
-- 1.  The carrier and the multiplication table, verbatim from §2.4.
--
--        ·  | e  a  c  d
--        ---+------------
--        e  | e  a  c  d
--        a  | a  e  c  d
--        c  | c  d  c  d
--        d  | d  c  c  d
------------------------------------------------------------------------

data C : Type₀ where
  e a c d : C

infixl 7 _⋆_
_⋆_ : C → C → C
e ⋆ y = y
a ⋆ e = a
a ⋆ a = e
a ⋆ c = c
a ⋆ d = d
c ⋆ e = c
c ⋆ a = d
c ⋆ c = c
c ⋆ d = d
d ⋆ e = d
d ⋆ a = c
d ⋆ c = c
d ⋆ d = d

------------------------------------------------------------------------
-- 1.1  The table is associative.  All 64 triples, by refl.
--
-- §2.4's point is that ONE-SIDED CLOSURE destroys associativity even
-- when EXECUTION is associative, so the associativity of ⋆ is a
-- hypothesis of the counterexample and not an afterthought.  §2.4 does
-- not state it; it is checked here because without it the example shows
-- nothing.
------------------------------------------------------------------------

assoc⋆ : (x y z : C) → (x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z)
assoc⋆ e e e = refl
assoc⋆ e e a = refl
assoc⋆ e e c = refl
assoc⋆ e e d = refl
assoc⋆ e a e = refl
assoc⋆ e a a = refl
assoc⋆ e a c = refl
assoc⋆ e a d = refl
assoc⋆ e c e = refl
assoc⋆ e c a = refl
assoc⋆ e c c = refl
assoc⋆ e c d = refl
assoc⋆ e d e = refl
assoc⋆ e d a = refl
assoc⋆ e d c = refl
assoc⋆ e d d = refl
assoc⋆ a e e = refl
assoc⋆ a e a = refl
assoc⋆ a e c = refl
assoc⋆ a e d = refl
assoc⋆ a a e = refl
assoc⋆ a a a = refl
assoc⋆ a a c = refl
assoc⋆ a a d = refl
assoc⋆ a c e = refl
assoc⋆ a c a = refl
assoc⋆ a c c = refl
assoc⋆ a c d = refl
assoc⋆ a d e = refl
assoc⋆ a d a = refl
assoc⋆ a d c = refl
assoc⋆ a d d = refl
assoc⋆ c e e = refl
assoc⋆ c e a = refl
assoc⋆ c e c = refl
assoc⋆ c e d = refl
assoc⋆ c a e = refl
assoc⋆ c a a = refl
assoc⋆ c a c = refl
assoc⋆ c a d = refl
assoc⋆ c c e = refl
assoc⋆ c c a = refl
assoc⋆ c c c = refl
assoc⋆ c c d = refl
assoc⋆ c d e = refl
assoc⋆ c d a = refl
assoc⋆ c d c = refl
assoc⋆ c d d = refl
assoc⋆ d e e = refl
assoc⋆ d e a = refl
assoc⋆ d e c = refl
assoc⋆ d e d = refl
assoc⋆ d a e = refl
assoc⋆ d a a = refl
assoc⋆ d a c = refl
assoc⋆ d a d = refl
assoc⋆ d c e = refl
assoc⋆ d c a = refl
assoc⋆ d c c = refl
assoc⋆ d c d = refl
assoc⋆ d d e = refl
assoc⋆ d d a = refl
assoc⋆ d d c = refl
assoc⋆ d d d = refl

------------------------------------------------------------------------
-- 2.  The declared measurement, verbatim from §2.4:
--     p(e)=0, p(a)=−3, p(c)=1, p(d)=4.
------------------------------------------------------------------------

p : C → ℤ
p e = pos 0
p a = negsuc 2      -- −3
p c = pos 1
p d = pos 4

-- D0026 §2.2:  M(a,b) = p(ab) − p(a) − p(b)
M : C → C → ℤ
M x y = (p (x ⋆ y) - p x) - p y

------------------------------------------------------------------------
-- 3.  Profiles, convolution, Isbell conjugates, one-sided closure.
--
-- §2.4, verbatim:
--
--     (f ⋆ g)(y) = sup_{ab=y} ( f(a) + g(b) − M(a,b) )
--     M*f(b)     = inf_a ( M(a,b) − f(a) )
--     M_*g(a)    = inf_b ( M(a,b) − g(b) )
--     f ⊙_L g   := M_* M* (f ⋆ g)
--
-- The carrier has four elements, so every sup and inf below is a
-- nested max/min over an explicitly listed finite set.  The sups are
-- over the fibres of ⋆, enumerated in §3.1 and audited in §3.2.
------------------------------------------------------------------------

Prof : Type₀
Prof = C → ℤ

-- 3.1  The fibres of the multiplication.  Reading the table by columns
--      of equal product:
--
--        ⋆⁻¹(e) = {(e,e), (a,a)}
--        ⋆⁻¹(a) = {(e,a), (a,e)}
--        ⋆⁻¹(c) = {(e,c), (a,c), (c,e), (c,c), (d,a), (d,c)}
--        ⋆⁻¹(d) = {(e,d), (a,d), (c,a), (c,d), (d,e), (d,d)}
--
--      2 + 2 + 6 + 6 = 16 = |C|², so the four fibres partition all
--      pairs; §3.2 checks that each listed pair lands where claimed.

conv : Prof → Prof → Prof
conv f g t = go t
  where
  v : C → C → ℤ
  v x y = (f x + g y) - M x y
  go : C → ℤ
  go e = maxℤ (v e e) (v a a)
  go a = maxℤ (v e a) (v a e)
  go c = maxℤ (v e c) (maxℤ (v a c) (maxℤ (v c e) (maxℤ (v c c) (maxℤ (v d a) (v d c)))))
  go d = maxℤ (v e d) (maxℤ (v a d) (maxℤ (v c a) (maxℤ (v c d) (maxℤ (v d e) (v d d)))))

-- 3.2  Audit of the fibre enumeration above: every listed pair really
--      multiplies to the stated target, by refl.  (The converse — that
--      nothing is missing — is the count 2+2+6+6 = 16 with all pairs
--      distinct, visible in the four lists.)

fib-e-1 : e ⋆ e ≡ e ;  fib-e-1 = refl
fib-e-2 : a ⋆ a ≡ e ;  fib-e-2 = refl
fib-a-1 : e ⋆ a ≡ a ;  fib-a-1 = refl
fib-a-2 : a ⋆ e ≡ a ;  fib-a-2 = refl
fib-c-1 : e ⋆ c ≡ c ;  fib-c-1 = refl
fib-c-2 : a ⋆ c ≡ c ;  fib-c-2 = refl
fib-c-3 : c ⋆ e ≡ c ;  fib-c-3 = refl
fib-c-4 : c ⋆ c ≡ c ;  fib-c-4 = refl
fib-c-5 : d ⋆ a ≡ c ;  fib-c-5 = refl
fib-c-6 : d ⋆ c ≡ c ;  fib-c-6 = refl
fib-d-1 : e ⋆ d ≡ d ;  fib-d-1 = refl
fib-d-2 : a ⋆ d ≡ d ;  fib-d-2 = refl
fib-d-3 : c ⋆ a ≡ d ;  fib-d-3 = refl
fib-d-4 : c ⋆ d ≡ d ;  fib-d-4 = refl
fib-d-5 : d ⋆ e ≡ d ;  fib-d-5 = refl
fib-d-6 : d ⋆ d ≡ d ;  fib-d-6 = refl

conj* : Prof → Prof                       -- M*f
conj* f b = minℤ (w e) (minℤ (w a) (minℤ (w c) (w d)))
  where
  w : C → ℤ
  w x = M x b - f x

conj⋆ : Prof → Prof                       -- M_*g
conj⋆ g x = minℤ (u e) (minℤ (u a) (minℤ (u c) (u d)))
  where
  u : C → ℤ
  u y = M x y - g y

infixl 6 _⊙ᴸ_
_⊙ᴸ_ : Prof → Prof → Prof
f ⊙ᴸ g = conj⋆ (conj* (conv f g))

------------------------------------------------------------------------
-- 4.  The two closed profiles of §2.4, as vectors over (e, a, c, d):
--
--        ℓ_c = (−6, 0,  0, −6)
--        ℓ_a = (−6, 0, −4, −7)
------------------------------------------------------------------------

ℓc : Prof
ℓc e = negsuc 5     -- −6
ℓc a = pos 0
ℓc c = pos 0
ℓc d = negsuc 5     -- −6

ℓa : Prof
ℓa e = negsuc 5     -- −6
ℓa a = pos 0
ℓa c = negsuc 3     -- −4
ℓa d = negsuc 6     -- −7

------------------------------------------------------------------------
-- 4.1  §2.4 calls these "closed profiles".  Checked, not assumed:
--      each is a fixed point of the left biorthogonal closure
--      cl_L = M_* ∘ M*, pointwise, by refl.
------------------------------------------------------------------------

clL : Prof → Prof
clL f = conj⋆ (conj* f)

ℓc-closed-e : clL ℓc e ≡ ℓc e ;  ℓc-closed-e = refl
ℓc-closed-a : clL ℓc a ≡ ℓc a ;  ℓc-closed-a = refl
ℓc-closed-c : clL ℓc c ≡ ℓc c ;  ℓc-closed-c = refl
ℓc-closed-d : clL ℓc d ≡ ℓc d ;  ℓc-closed-d = refl

ℓa-closed-e : clL ℓa e ≡ ℓa e ;  ℓa-closed-e = refl
ℓa-closed-a : clL ℓa a ≡ ℓa a ;  ℓa-closed-a = refl
ℓa-closed-c : clL ℓa c ≡ ℓa c ;  ℓa-closed-c = refl
ℓa-closed-d : clL ℓa d ≡ ℓa d ;  ℓa-closed-d = refl

------------------------------------------------------------------------
-- 5.  The counterexample, value by value.
--
-- §2.4 states, in this order:
--
--     ℓ_c ⊙_L ℓ_a  =  ℓ_a ⊙_L ℓ_c  =  (−6,−3,−3,−6)
--     (ℓ_c ⊙_L ℓ_a) ⊙_L ℓ_c        =  (−8,−2,−2,−8)
--     ℓ_c ⊙_L (ℓ_a ⊙_L ℓ_c)        =  (−5,−2,−2,−5)
--
-- Every one of these twelve integers is checked below by `refl`, in the
-- order (e, a, c, d).  All twelve agree with the source.
------------------------------------------------------------------------

ca-e : (ℓc ⊙ᴸ ℓa) e ≡ negsuc 5 ;  ca-e = refl      -- −6
ca-a : (ℓc ⊙ᴸ ℓa) a ≡ negsuc 2 ;  ca-a = refl      -- −3
ca-c : (ℓc ⊙ᴸ ℓa) c ≡ negsuc 2 ;  ca-c = refl      -- −3
ca-d : (ℓc ⊙ᴸ ℓa) d ≡ negsuc 5 ;  ca-d = refl      -- −6

ac-e : (ℓa ⊙ᴸ ℓc) e ≡ negsuc 5 ;  ac-e = refl      -- −6
ac-a : (ℓa ⊙ᴸ ℓc) a ≡ negsuc 2 ;  ac-a = refl      -- −3
ac-c : (ℓa ⊙ᴸ ℓc) c ≡ negsuc 2 ;  ac-c = refl      -- −3
ac-d : (ℓa ⊙ᴸ ℓc) d ≡ negsuc 5 ;  ac-d = refl      -- −6

-- so the two one-sided products agree pointwise
ca≡ac : (t : C) → (ℓc ⊙ᴸ ℓa) t ≡ (ℓa ⊙ᴸ ℓc) t
ca≡ac e = refl
ca≡ac a = refl
ca≡ac c = refl
ca≡ac d = refl

left-e : ((ℓc ⊙ᴸ ℓa) ⊙ᴸ ℓc) e ≡ negsuc 7 ;  left-e = refl    -- −8
left-a : ((ℓc ⊙ᴸ ℓa) ⊙ᴸ ℓc) a ≡ negsuc 1 ;  left-a = refl    -- −2
left-c : ((ℓc ⊙ᴸ ℓa) ⊙ᴸ ℓc) c ≡ negsuc 1 ;  left-c = refl    -- −2
left-d : ((ℓc ⊙ᴸ ℓa) ⊙ᴸ ℓc) d ≡ negsuc 7 ;  left-d = refl    -- −8

right-e : (ℓc ⊙ᴸ (ℓa ⊙ᴸ ℓc)) e ≡ negsuc 4 ;  right-e = refl  -- −5
right-a : (ℓc ⊙ᴸ (ℓa ⊙ᴸ ℓc)) a ≡ negsuc 1 ;  right-a = refl  -- −2
right-c : (ℓc ⊙ᴸ (ℓa ⊙ᴸ ℓc)) c ≡ negsuc 1 ;  right-c = refl  -- −2
right-d : (ℓc ⊙ᴸ (ℓa ⊙ᴸ ℓc)) d ≡ negsuc 4 ;  right-d = refl  -- −5

------------------------------------------------------------------------
-- 6.  The conclusion of §2.4, as a proposition:
--
--     (A ⊙_L B) ⊙_L C  ⊊  A ⊙_L (B ⊙_L C)
--
-- with A = C = ℓ_c and B = ℓ_a.  Two halves, both checked:
--
--   (i)  the two bracketings are NOT equal — they differ at e;
--   (ii) the failure is one-directional: the left bracketing is
--        pointwise ≤ the right, so the inclusion really is strict and
--        not a crossing.
--
-- §2.4's own reading — "exact path dependence created by premature
-- closure, not numerical instability" — is what (i) says once the
-- arithmetic is exact rather than measured.
------------------------------------------------------------------------

one-sided-closure-is-not-associative
  : ¬ (((ℓc ⊙ᴸ ℓa) ⊙ᴸ ℓc) e ≡ (ℓc ⊙ᴸ (ℓa ⊙ᴸ ℓc)) e)
one-sided-closure-is-not-associative h =
  snotz (injSuc (injSuc (injSuc (injSuc (injNegsuc h)))))

-- (ii) the direction of the failure, value by value.
-- −8 ≤ −5, −2 ≤ −2, −2 ≤ −2, −8 ≤ −5.
left≤right : (t : C) → leℤ (((ℓc ⊙ᴸ ℓa) ⊙ᴸ ℓc) t) ((ℓc ⊙ᴸ (ℓa ⊙ᴸ ℓc)) t)
left≤right e = refl
left≤right a = refl
left≤right c = refl
left≤right d = refl

------------------------------------------------------------------------
-- 7.  What is added.
--
-- One thing IS added rather than reproduced: §2.4 does not state that
-- its four-element table is associative, and the counterexample is
-- vacuous without it, since its whole content is that execution can be
-- associative while one-sided closure is not.  §1.1 above checks all
-- sixty-four triples.
------------------------------------------------------------------------
