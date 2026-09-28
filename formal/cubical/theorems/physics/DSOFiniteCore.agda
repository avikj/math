{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- DSOFiniteCore
--
-- D0026 §14.1's finite acceptance core, discharged in one module
-- D0026 §§2.2, 2.4, 2.5, 14.1
-- (`collab/upstream/raw/D0026-owner-egb-core-transmission-v2-2026-08-16.md` (absent from this repository)).
--
-- CONTENTS
--
--   §1  _⊖_, TrefoilAlgebra    the two abelian telescope identities, at a
--                              VARIABLE CommRing (per BUILD.md (absent from this repository)'s rule:
--                              state ring identities over an arbitrary
--                              ring, instantiate afterwards), by solve!
--   §2  General                D0026 §2.2's trefoil identity
--                                M(ab,c) + M(a,b) = M(a,bc) + M(b,c)
--                              proved GENERALLY: any type with an
--                              associative composition and a measurement
--                              p into ℤ.  Both sides are shown equal to
--                              the ternary defect
--                                M3(x,y,z) = p(xyz) − p x − p y − p z,
--                              which yields §2.5's two displayed
--                              decompositions of M3 as the two halves of
--                              the proof.  No unit is used: the trefoil
--                              is a semigroup fact, so it holds for any
--                              monoid a fortiori.
--   §3  D4, _·F_               D0026 §2.4's four-element carrier {e,a,c,d}
--                              as Fin 4 (Cubical.Data.SumFin), with the
--                              multiplication table explicit, the full
--                              16-entry table certified by refl, unit
--                              laws, and associativity by 64-case
--                              exhaustion — all kernel reductions.
--   §4  pF, F.M                the declared measurement p = (0,−3,1,4)
--                              and its derived execution defect M; the
--                              complete M table certified by refl; the
--                              finite trefoil now a COROLLARY of §2
--                              (where the prior in-repo treatment,
--                              DSONucleusExecutionCalibration, needed 64
--                              refl clauses — the general proof replaces
--                              them, which is queue Q2's own point:
--                              "provable generally, not just finitely").
--   §5  Mstar/Msub/clL/star/⊙L D0026 §2.4's left Isbell closure and
--                              one-sided product on profiles Fin 4 → ℤ,
--                              every extremum over the full finite fiber
--                              dictated by the table; the two calibration
--                              profiles, their closedness, both binary
--                              products, and the exact associativity
--                              FAILURE
--                                ((ℓc ⊙L ℓa) ⊙L ℓc) e = −8
--                                (ℓc ⊙L (ℓa ⊙L ℓc)) e = −5,
--                              hence ¬ (left ≡ right).
--
-- TRANSMISSION NUMBERS.  NO transmitted output vector is inserted into
-- any definition — the definitions consume only the multiplication
-- table, p, and the two profile vectors; every output is a kernel
-- reduction.  The kernel values AGREE with D0026 §2.4's displayed values
-- at every entry:
--
--     M rows                  (0,0,0,0) (0,6,3,3) (0,6,−1,−1) (0,0,−4,−4)
--     ℓc ⊙L ℓa = ℓa ⊙L ℓc     (−6,−3,−3,−6)
--     (ℓc ⊙L ℓa) ⊙L ℓc        (−8,−2,−2,−8)
--     ℓc ⊙L (ℓa ⊙L ℓc)        (−5,−2,−2,−5)
--
-- and with the independent in-repo kernel-checked reproduction (Delta
-- 29 lane, see below).
--
-- PRIOR ART IN THIS REPOSITORY: the same finite
-- calibration was landed from the Delta 29 transmission as
-- `DSONucleusExecutionCalibration` (table, M, 64-case trefoil) and
-- `DSONucleusOneSidedProduct` (closure, product, the −8 vs −5 defect),
-- and the middle/ternary repair lane lives in
-- `DSONucleusMiddleProduct` + `DSONucleusMiddleAssociativityAudit`.
-- What is NEW here: (i) the trefoil proved generally, for every
-- associative execution with a ℤ-measurement, rather than by finite
-- exhaustion; (ii) the finite §2.4 instance derived from that general
-- theorem on a Fin 4 encoding, making this module a self-contained
-- discharge of D0026 §14.1's named finite core against D0026's own
-- text.  The middle-nucleus associativity REPAIR is deliberately not
-- duplicated here; consumers should import the modules above for it.
--
-- Rigor boundary: everything below is exact finite/symbolic
-- computation or algebra — the kind of object CLAUDE.md (absent from this repository) licenses
-- unconditionally.  Nothing here is a measurement, and no claim about
-- ℝ-valued profiles, infinite carriers, or the middle nucleus is made.
------------------------------------------------------------------------

module DSOFiniteCore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int
  using (ℤ ; pos ; negsuc ; min ; max)
  renaming (_+_ to _+ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.SumFin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection using (solve!)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1  Subtraction and the two telescope identities
--
-- ⊖ is spelled out as +/negation so that the variable-ring lemmas below
-- apply definitionally; on ℤ it is the usual subtraction.
------------------------------------------------------------------------

infixl 6 _⊖_

_⊖_ : ℤ → ℤ → ℤ
x ⊖ y = x +ℤ (-ℤ y)

-- The two abelian-group shuffles behind D0026 §2.2/§2.5, at a variable
-- CommRing per BUILD.md (absent from this repository) (only + and − occur; degree 1, solver-trivial).
-- Both right-hand sides are the ternary telescope P − A − B − C.
module TrefoilAlgebra (R : CommRing ℓ) where
  open CommRingStr (snd R)

  telescopeL : (P Q A B C : ⟨ R ⟩)
    → ((P + (- Q)) + (- C)) + ((Q + (- A)) + (- B))
      ≡ (((P + (- A)) + (- B)) + (- C))
  telescopeL _ _ _ _ _ = solve! R

  telescopeR : (P Q A B C : ⟨ R ⟩)
    → ((P + (- A)) + (- Q)) + ((Q + (- B)) + (- C))
      ≡ (((P + (- A)) + (- B)) + (- C))
  telescopeR _ _ _ _ _ = solve! R

private
  telescopeLℤ : (P Q A B C : ℤ)
    → ((P ⊖ Q) ⊖ C) +ℤ ((Q ⊖ A) ⊖ B) ≡ (((P ⊖ A) ⊖ B) ⊖ C)
  telescopeLℤ = TrefoilAlgebra.telescopeL ℤCommRing

  telescopeRℤ : (P Q A B C : ℤ)
    → ((P ⊖ A) ⊖ Q) +ℤ ((Q ⊖ B) ⊖ C) ≡ (((P ⊖ A) ⊖ B) ⊖ C)
  telescopeRℤ = TrefoilAlgebra.telescopeR ℤCommRing

------------------------------------------------------------------------
-- §2  D0026 §2.2, proved generally
--
-- Any composition _∙_ that is associative, and any declared measurement
-- p into ℤ (additivity NOT assumed).  The unit of a monoid is never
-- used, so this covers every monoid and every semigroup.
------------------------------------------------------------------------

-- The execution operation is named _·X_ rather than _∙_ so that the
-- Prelude's path composition _∙_ stays visible inside the proofs.
module General (X : Type ℓ)
               (_·X_ : X → X → X)
               (·X-assoc : (x y z : X) → (x ·X y) ·X z ≡ x ·X (y ·X z))
               (p : X → ℤ) where

  -- D0026 §2.2: the execution defect M(a,b) = p(ab) − p(a) − p(b).
  M : X → X → ℤ
  M x y = (p (x ·X y) ⊖ p x) ⊖ p y

  -- D0026 §2.5: the ternary defect M3(x,b,z) = p(xbz) − p x − p b − p z.
  M3 : X → X → X → ℤ
  M3 x y z = ((p (x ·X (y ·X z)) ⊖ p x) ⊖ p y) ⊖ p z

  -- §2.5, first displayed decomposition: M3 = M(xb,z) + M(x,b).
  -- Associativity of execution enters exactly once, through cong p.
  trefoil-left : (x y z : X) → M (x ·X y) z +ℤ M x y ≡ M3 x y z
  trefoil-left x y z =
    cong (λ w → ((w ⊖ p (x ·X y)) ⊖ p z)
                  +ℤ ((p (x ·X y) ⊖ p x) ⊖ p y))
         (cong p (·X-assoc x y z))
    ∙ telescopeLℤ (p (x ·X (y ·X z))) (p (x ·X y)) (p x) (p y) (p z)

  -- §2.5, second displayed decomposition: M3 = M(x,bz) + M(b,z).
  trefoil-right : (x y z : X) → M x (y ·X z) +ℤ M y z ≡ M3 x y z
  trefoil-right x y z =
    telescopeRℤ (p (x ·X (y ·X z))) (p (y ·X z)) (p x) (p y) (p z)

  -- D0026 §2.2, the trefoil identity, boxed form:
  --   M(ab,c) + M(a,b) = M(a,bc) + M(b,c).
  trefoil : (x y z : X)
    → M (x ·X y) z +ℤ M x y ≡ M x (y ·X z) +ℤ M y z
  trefoil x y z = trefoil-left x y z ∙ sym (trefoil-right x y z)

------------------------------------------------------------------------
-- §3  D0026 §2.4's four-element monoid, on Fin 4
--
-- Carrier order e, a, c, d = fzero, fsuc fzero, fsuc² fzero, fsuc³ fzero.
-- The table is transcribed from §2.4 row by row (rows = left factor).
------------------------------------------------------------------------

D4 : Type₀
D4 = Fin 4

pattern ke = fzero
pattern ka = fsuc fzero
pattern kc = fsuc (fsuc fzero)
pattern kd = fsuc (fsuc (fsuc fzero))

_·F_ : D4 → D4 → D4
ke ·F y  = y
ka ·F ke = ka
ka ·F ka = ke
ka ·F kc = kc
ka ·F kd = kd
kc ·F ke = kc
kc ·F ka = kd
kc ·F kc = kc
kc ·F kd = kd
kd ·F ke = kd
kd ·F ka = kc
kd ·F kc = kc
kd ·F kd = kd

-- The complete 16-entry table as refl certificates.  Besides checking
-- the transcription, these enumerate every factorization of every
-- element, which is exactly the fiber bookkeeping `star` needs in §5:
-- e and a have two factorizations each, c and d have six each; the four
-- fibers partition all 2+2+6+6 = 16 pairs.
·F-e-row : (ke ·F ke ≡ ke) × (ke ·F ka ≡ ka) × (ke ·F kc ≡ kc) × (ke ·F kd ≡ kd)
·F-e-row = refl , refl , refl , refl

·F-a-row : (ka ·F ke ≡ ka) × (ka ·F ka ≡ ke) × (ka ·F kc ≡ kc) × (ka ·F kd ≡ kd)
·F-a-row = refl , refl , refl , refl

·F-c-row : (kc ·F ke ≡ kc) × (kc ·F ka ≡ kd) × (kc ·F kc ≡ kc) × (kc ·F kd ≡ kd)
·F-c-row = refl , refl , refl , refl

·F-d-row : (kd ·F ke ≡ kd) × (kd ·F ka ≡ kc) × (kd ·F kc ≡ kc) × (kd ·F kd ≡ kd)
·F-d-row = refl , refl , refl , refl

-- ke is a two-sided unit, so the carrier is a monoid, not merely a
-- semigroup.  (The general trefoil in §2 never needs this.)
·F-unitL : (y : D4) → ke ·F y ≡ y
·F-unitL y = refl

·F-unitR : (x : D4) → x ·F ke ≡ x
·F-unitR ke = refl
·F-unitR ka = refl
·F-unitR kc = refl
·F-unitR kd = refl

-- Associativity, by 64-case exhaustion; every case a kernel reduction.
-- Provenance for §5: the later nonassociativity is created by one-sided
-- CLOSURE, not smuggled in at the execution layer.
·F-assoc : (x y z : D4) → (x ·F y) ·F z ≡ x ·F (y ·F z)
·F-assoc ke ke ke = refl
·F-assoc ke ke ka = refl
·F-assoc ke ke kc = refl
·F-assoc ke ke kd = refl
·F-assoc ke ka ke = refl
·F-assoc ke ka ka = refl
·F-assoc ke ka kc = refl
·F-assoc ke ka kd = refl
·F-assoc ke kc ke = refl
·F-assoc ke kc ka = refl
·F-assoc ke kc kc = refl
·F-assoc ke kc kd = refl
·F-assoc ke kd ke = refl
·F-assoc ke kd ka = refl
·F-assoc ke kd kc = refl
·F-assoc ke kd kd = refl
·F-assoc ka ke ke = refl
·F-assoc ka ke ka = refl
·F-assoc ka ke kc = refl
·F-assoc ka ke kd = refl
·F-assoc ka ka ke = refl
·F-assoc ka ka ka = refl
·F-assoc ka ka kc = refl
·F-assoc ka ka kd = refl
·F-assoc ka kc ke = refl
·F-assoc ka kc ka = refl
·F-assoc ka kc kc = refl
·F-assoc ka kc kd = refl
·F-assoc ka kd ke = refl
·F-assoc ka kd ka = refl
·F-assoc ka kd kc = refl
·F-assoc ka kd kd = refl
·F-assoc kc ke ke = refl
·F-assoc kc ke ka = refl
·F-assoc kc ke kc = refl
·F-assoc kc ke kd = refl
·F-assoc kc ka ke = refl
·F-assoc kc ka ka = refl
·F-assoc kc ka kc = refl
·F-assoc kc ka kd = refl
·F-assoc kc kc ke = refl
·F-assoc kc kc ka = refl
·F-assoc kc kc kc = refl
·F-assoc kc kc kd = refl
·F-assoc kc kd ke = refl
·F-assoc kc kd ka = refl
·F-assoc kc kd kc = refl
·F-assoc kc kd kd = refl
·F-assoc kd ke ke = refl
·F-assoc kd ke ka = refl
·F-assoc kd ke kc = refl
·F-assoc kd ke kd = refl
·F-assoc kd ka ke = refl
·F-assoc kd ka ka = refl
·F-assoc kd ka kc = refl
·F-assoc kd ka kd = refl
·F-assoc kd kc ke = refl
·F-assoc kd kc ka = refl
·F-assoc kd kc kc = refl
·F-assoc kd kc kd = refl
·F-assoc kd kd ke = refl
·F-assoc kd kd ka = refl
·F-assoc kd kd kc = refl
·F-assoc kd kd kd = refl

------------------------------------------------------------------------
-- §4  The declared measurement and its derived defect
------------------------------------------------------------------------

-- D0026 §2.4: p(e) = 0, p(a) = −3, p(c) = 1, p(d) = 4.
pF : D4 → ℤ
pF ke = pos 0
pF ka = negsuc 2
pF kc = pos 1
pF kd = pos 4

-- Instantiate the general development of §2 on the finite monoid.
module F = General D4 _·F_ ·F-assoc pF

-- The finite trefoil is now a corollary of the GENERAL theorem — no
-- 64-case exhaustion (contrast DSONucleusExecutionCalibration.trefoil).
trefoilF : (x y z : D4)
  → F.M (x ·F y) z +ℤ F.M x y ≡ F.M x (y ·F z) +ℤ F.M y z
trefoilF = F.trefoil

-- Complete derived M table, recomputed by hand and certified by the
-- kernel, in row/column order e,a,c,d.  Derived, never transcribed:
-- F.M consumes only _·F_ and pF.
M-e-row : (F.M ke ke ≡ pos 0) × (F.M ke ka ≡ pos 0)
        × (F.M ke kc ≡ pos 0) × (F.M ke kd ≡ pos 0)
M-e-row = refl , refl , refl , refl

M-a-row : (F.M ka ke ≡ pos 0) × (F.M ka ka ≡ pos 6)
        × (F.M ka kc ≡ pos 3) × (F.M ka kd ≡ pos 3)
M-a-row = refl , refl , refl , refl

M-c-row : (F.M kc ke ≡ pos 0) × (F.M kc ka ≡ pos 6)
        × (F.M kc kc ≡ negsuc 0) × (F.M kc kd ≡ negsuc 0)
M-c-row = refl , refl , refl , refl

M-d-row : (F.M kd ke ≡ pos 0) × (F.M kd ka ≡ pos 0)
        × (F.M kd kc ≡ negsuc 3) × (F.M kd kd ≡ negsuc 3)
M-d-row = refl , refl , refl , refl

------------------------------------------------------------------------
-- §5  D0026 §2.4: one-sided closure destroys associativity — exactly
--
-- Profiles are total functions Fin 4 → ℤ, so on this finite carrier
-- every inf/sup of §2.3–§2.4 is a finite min/max and no ℝ̄, no −∞, and
-- no convention for empty fibers is needed (every fiber is inhabited,
-- by the §3 table certificates).
------------------------------------------------------------------------

Profile : Type₀
Profile = D4 → ℤ

min4 : ℤ → ℤ → ℤ → ℤ → ℤ
min4 w x y z = min (min w x) (min y z)

max6 : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
max6 u v w x y z = max (max (max u v) (max w x)) (max y z)

-- Isbell conjugates for the left closure (D0026 §2.3):
--   M* f (b) = inf_a ( M(a,b) − f(a) ),   M_* g (a) = inf_b ( M(a,b) − g(b) ).
Mstar : Profile → Profile
Mstar f b =
  min4 (F.M ke b ⊖ f ke) (F.M ka b ⊖ f ka)
       (F.M kc b ⊖ f kc) (F.M kd b ⊖ f kd)

Msub : Profile → Profile
Msub g x =
  min4 (F.M x ke ⊖ g ke) (F.M x ka ⊖ g ka)
       (F.M x kc ⊖ g kc) (F.M x kd ⊖ g kd)

-- Left biorthogonal closure cl_L = M_* M*.
clL : Profile → Profile
clL f = Msub (Mstar f)

-- Profile convolution (f ⋆ g)(y) = sup_{ab=y} ( f(a) + g(b) − M(a,b) ),
-- the sup taken over the exact multiplication fibers certified in §3.
term : Profile → Profile → D4 → D4 → ℤ
term f g x z = (f x +ℤ g z) ⊖ F.M x z

star : Profile → Profile → Profile
star f g ke = max (term f g ke ke) (term f g ka ka)
star f g ka = max (term f g ke ka) (term f g ka ke)
star f g kc =
  max6 (term f g ke kc) (term f g ka kc)
       (term f g kc ke) (term f g kc kc)
       (term f g kd ka) (term f g kd kc)
star f g kd =
  max6 (term f g ke kd) (term f g ka kd)
       (term f g kc ka) (term f g kc kd)
       (term f g kd ke) (term f g kd kd)

-- D0026 §2.4's one-sided product: close on the left only.
_⊙L_ : Profile → Profile → Profile
f ⊙L g = clL (star f g)

-- The two calibration profiles of §2.4, in carrier order (e,a,c,d):
--   ℓc = (−6, 0, 0, −6),   ℓa = (−6, 0, −4, −7).
ell-c ell-a : Profile
ell-c ke = negsuc 5
ell-c ka = pos 0
ell-c kc = pos 0
ell-c kd = negsuc 5

ell-a ke = negsuc 5
ell-a ka = pos 0
ell-a kc = negsuc 3
ell-a kd = negsuc 6

-- Both really lie in the left nucleus for the derived M
-- (hand-recomputed: M*ℓc = (0,6,−1,−1), M*ℓa = (0,6,3,3)).
ell-c-closed : clL ell-c ≡ ell-c
ell-c-closed = funExt λ { ke → refl ; ka → refl ; kc → refl ; kd → refl }

ell-a-closed : clL ell-a ≡ ell-a
ell-a-closed = funExt λ { ke → refl ; ka → refl ; kc → refl ; kd → refl }

-- §2.4's displayed binary product (−6,−3,−3,−6), in BOTH orders.
control : Profile
control ke = negsuc 5
control ka = negsuc 2
control kc = negsuc 2
control kd = negsuc 5

ell-c⊙ell-a : ell-c ⊙L ell-a ≡ control
ell-c⊙ell-a = funExt λ { ke → refl ; ka → refl ; kc → refl ; kd → refl }

ell-a⊙ell-c : ell-a ⊙L ell-c ≡ control
ell-a⊙ell-c = funExt λ { ke → refl ; ka → refl ; kc → refl ; kd → refl }

-- The two associations, evaluated exactly.  Hand recomputation and the
-- transmitted §2.4 values agree: (−8,−2,−2,−8) versus (−5,−2,−2,−5).
leftAssociated rightAssociated : Profile
leftAssociated  = (ell-c ⊙L ell-a) ⊙L ell-c
rightAssociated = ell-c ⊙L (ell-a ⊙L ell-c)

left-associated-values :
  (leftAssociated ke ≡ negsuc 7)
  × ((leftAssociated ka ≡ negsuc 1)
  × ((leftAssociated kc ≡ negsuc 1)
  × (leftAssociated kd ≡ negsuc 7)))
left-associated-values = refl , (refl , (refl , refl))

right-associated-values :
  (rightAssociated ke ≡ negsuc 4)
  × ((rightAssociated ka ≡ negsuc 1)
  × ((rightAssociated kc ≡ negsuc 1)
  × (rightAssociated kd ≡ negsuc 4)))
right-associated-values = refl , (refl , (refl , refl))

-- −8 and −5 are distinct integers.
minus-eight≢minus-five : ¬ (negsuc 7 ≡ negsuc 4)
minus-eight≢minus-five path = subst distinguish path tt
  where
  distinguish : ℤ → Type₀
  distinguish (pos _)    = ⊥
  distinguish (negsuc 4) = ⊥
  distinguish (negsuc _) = Unit

-- D0026 §2.4, boxed conclusion, as an exact finite computation: the
-- one-sided closure product on an ASSOCIATIVE execution (·F-assoc,
-- trefoilF above) is itself NOT associative.  Premature one-sided
-- closure, not execution, creates the path dependence.
one-sided-product-not-associative :
  ¬ (((ell-c ⊙L ell-a) ⊙L ell-c) ≡ (ell-c ⊙L (ell-a ⊙L ell-c)))
one-sided-product-not-associative equality =
  minus-eight≢minus-five
    (sym (fst left-associated-values)
    ∙ cong (λ profile → profile ke) equality
    ∙ fst right-associated-values)

------------------------------------------------------------------------
-- Rigor boundary
--
-- Checked: the two telescope identities at a variable
-- CommRing; the trefoil identity and both §2.5 decompositions of M3 for
-- EVERY associative execution with a ℤ-measurement; the Fin 4 table,
-- its unit laws and 64-case associativity; the derived M table; nuclear
-- closedness of both calibration profiles; both binary products; both
-- associations of the triple product; and the −8 ≠ −5 defect at e.
--
------------------------------------------------------------------------
