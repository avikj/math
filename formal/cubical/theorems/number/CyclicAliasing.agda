{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CyclicAliasing
--
-- The exact aliasing condition of
-- coefficient extraction and aliasing"), as checked terms.
--
-- WHAT THE NOTE SAYS.  For a polynomial A(z) = Σ_{r=0}^{R} A_r z^r and
-- ζ = e^{2πi/M}, finite Fourier inversion gives (note (2.1))
--
--     (1/M) Σ_{ν=0}^{M-1} ζ^{-sν} A(ζ^ν)  =  Σ_{0≤r≤R, r≡s (mod M)} A_r.
--
-- The note calls this "the exact aliasing theorem": the cyclic
-- projector returns not the coefficient A_s but the SUM OF THE WHOLE
-- RESIDUE CLASS of s mod M that is supported in [0,R].  It is exact
-- iff no other supported charge is congruent to s; M > R is the simple
-- sufficient condition.
--
-- Thm 4.3 computes the absolute condition number of the root-of-unity
-- (DFT) charge-atom extractor and finds κ_DFT = 1 — perfect
-- conditioning, the best of the three routes it compares, and the basis
-- of that note's operational recommendation.  That computation is done
-- for n = R+1 phase samples.  **Conditioning is not exactness.**  If
-- n ≤ R the very same inverse-DFT row is still perfectly conditioned
-- and still returns the wrong functional: aliasing is a MODEL error
-- (the projector targets a different linear functional of the
-- coefficient vector), not noise amplification, and no condition number
-- can see it.  So κ_DFT = 1 is a statement CONDITIONAL on n > R, and
-- the corpus must check that inequality at every use site before
-- quoting it.
--
-- Two consequences worth stating explicitly, both visible below:
--
--   * The hypothesis is per-d, not uniform.  Applied to the divisor
--     charge polynomial a_z(d) (note §1) the degree is R = Ω(d), which
--     is unbounded on any infinite set of d.  No single M serves all d;
--     a uniform statement needs an independent truncation of the
--     supported charges.  The note says exactly this after (2.3):
--     "Parity is exact only after an independent hypothesis truncates
--     the supported endpoint charges to {1,2}".
--   * M = 2 is the standard trap.  `parity-*` below certifies the
--     note's remark that the parity phase "is not primality in
--     general": at M = 2 the s = 1 projector returns Σ_{r odd} κ_r, and
--     for d = p²q that is 2, not κ₁ = 1.
--
-- WHAT IS FORMALIZED.  The step from the left side of
-- (2.1) to the right side is character orthogonality over ℂ — inherited
-- elementary harmonic analysis, and the note claims no novelty for it.
-- No root of unity and no complex number
-- occurs in this module.  What IS formalized is everything (2.1)
-- reduces to once that step is taken, which is where the operational
-- content lives: the right-hand side of (2.1) is taken as the
-- DEFINITION of the projector (`aliasSum`), over a discrete carrier
-- with coefficient-index arithmetic mod n, and the exact/aliased
-- dichotomy is proved about it.  Coefficients live in ℤ; sums are ℤ
-- sums; the whole module is finite index combinatorics.
--
-- What is proved, and how:
--
--   * `classInjective` — GENERAL in n and R.  If R < n then r ↦ r mod n
--     is injective on the index window [0,R]: each residue class mod n
--     contains at most one index ≤ R.  This is the combinatorial heart
--     of "no aliasing", and it is one line once `modIndBase` (x < n ⟹
--     x mod n = x) is in hand.
--
--   * `exact` — GENERAL in A, n, R, j.  R < n and j ≤ R imply
--     aliasSum A n j R ≡ A j.  Exact recovery of the charge atom, no
--     hypothesis on A whatsoever.  Proof: `classInjective` kills every
--     other index in the window, and `sumSupport` (a sum whose summand
--     vanishes off one point equals its value there) collapses the sum.
--
--   * `collisionIndices` — GENERAL in n, R, j.  If 0 < n and j+n ≤ R
--     then j and j+n are DISTINCT indices, both in the window, both in
--     the same class mod n.  This is the aliasing witness in the form
--     the dichotomy needs: as soon as n ≤ R (take j = 0) the projector
--     has two supported indices it cannot separate.  `collisionAtZero`
--     is that specialization, stated as the literal negation of
--     `exact`'s hypothesis.  Note both are general — the note's n ≤ R
--     case never needs an instance to exhibit a collision.
--
--   * `firstShell` — GENERAL.  For n ≤ R < 2n and j < n, the only
--     indices in the window congruent to j mod n are j and j+n.
--
--   * `aliased` — GENERAL in A, n, j, R.  For j < n, j+n ≤ R, R < 2n:
--
--         aliasSum A n j R  ≡  A (j+n) + A j,
--
--     the EXACT aliased value, i.e. the note's Σ_{r≡j} A_r written out
--     on the first aliasing shell.  So the failure at n ≤ R is not
--     "approximate"; the projector exactly computes a different
--     functional, and `aliased` names it.
--
--   * Instances (refl, i.e. exact finite computation, which CLAUDE.md (absent from this repository)
--     rates as proof).  The coefficients come from the note's §1: from
--     a_z(d) = z^ρ (z-1)^j with ρ = Ω(d)-ω(d), j = ω(d), the module
--     defines `kappa` by the structural recursion of (z-1)^{j+1} =
--     z·(z-1)^j - (z-1)^j — no binomials, no monus, and `kappa-*`
--     certifies the resulting coefficient vectors against (1.2).
--     For d = p²q (ρ=1, j=2, R=Ω=3, κ = (0,1,-2,1)):
--         M = 4 > R   →  projector returns 1 = κ₁      (exact)
--         M = 2 ≤ R   →  projector returns 2 = κ₁+κ₃   (aliased)
--     For d = pqr (ρ=0, j=3, R=3, κ = (-1,3,-3,1)):
--         M = 4 → 3 = κ₁ ;  M = 2 → 4 = κ₁+κ₃.
--     Both M=2 values are cross-checked against the note's independent
--     closed form (2.3), Σ_{r odd} κ_r = -½(-1)^{ρ}(-2)^{ω}, in the
--     cleared form 2·Σ_odd ≡ -((-1)^ρ · (-2)^ω) (`parity-23-*`).  The
--     two derivations of these numbers are independent: one runs the
--     index-class sum, the other evaluates the note's formula.
--
-- This module establishes the
-- precondition n > R under which the κ=1 projector is the identity on
-- the targeted atom, and the exact functional it becomes when the
-- precondition fails.  --safe throughout; no postulates, no holes.
------------------------------------------------------------------------

module CyclicAliasing where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ; zero; suc; +-zero; +-suc; inj-m+; injSuc; snotz)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
  using (_<_; _≤_; ≤-refl; ≤-suc; ≤SumLeft; suc-≤-suc; pred-≤-pred;
         ≤-trans; ≤<-trans; <-trans; <-asym; ¬-<-zero; <-split; splitℕ-<;
         ≤-+k-cancel)
open import Cubical.Data.Nat.Mod using (_mod_; modIndBase; mod-rUnit)
open import Cubical.Data.Int using (ℤ; pos; negsuc; -_; _+_; _·_; pos0+)
open import Cubical.Data.Int.Properties using (injPos)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 0.  Order scraps.  Two facts about ℕ that the library states in the
--     ≤ direction only.

<→≢ : (a b : ℕ) → a < b → ¬ (a ≡ b)
<→≢ a b a<b e = <-asym (subst (λ x → suc a ≤ x) (sym e) a<b) ≤-refl

>→≢ : (a b : ℕ) → b < a → ¬ (a ≡ b)
>→≢ a b b<a e = <→≢ b a b<a (sym e)

------------------------------------------------------------------------
-- 1.  Decidable equality of indices, as a Bool, so the projector below
--     computes on numerals (the instances at the end are `refl`).

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc k) = eqℕ m k

eqℕ-refl : (m : ℕ) → eqℕ m m ≡ true
eqℕ-refl zero    = refl
eqℕ-refl (suc m) = eqℕ-refl m

eqℕ-neq : (m k : ℕ) → ¬ (m ≡ k) → eqℕ m k ≡ false
eqℕ-neq zero    zero    p = ⊥.rec (p refl)
eqℕ-neq zero    (suc k) _ = refl
eqℕ-neq (suc m) zero    _ = refl
eqℕ-neq (suc m) (suc k) p = eqℕ-neq m k (λ q → p (cong suc q))

------------------------------------------------------------------------
-- 2.  The divisor charge polynomial of note §1.
--
--     a_z(d) = z^{ρ(d)} (z-1)^{j(d)},   ρ = Ω-ω,  j = ω        (1.1)
--
--     κ_r(d) = coefficient of z^r.                              (1.2)
--
-- (z-1)^{j+1} = z·(z-1)^j − (z-1)^j, so with P = (z-1)^j:
--     [z^0]   = −P₀,      [z^{k+1}] = P_k − P_{k+1}.
-- Purely structural: no binomial coefficients and no truncated
-- subtraction enter, and the vectors are certified against (1.2) below.

shellCoeff : ℕ → ℕ → ℤ            -- [z^k] (z-1)^j
shellCoeff zero    zero    = pos 1
shellCoeff zero    (suc _) = pos 0
shellCoeff (suc j) zero    = - shellCoeff j zero
shellCoeff (suc j) (suc k) = shellCoeff j k + (- shellCoeff j (suc k))

kappa : ℕ → ℕ → ℕ → ℤ             -- κ_r for the pair (ρ , j)
kappa zero    j r       = shellCoeff j r
kappa (suc _) _ zero    = pos 0
kappa (suc ρ) j (suc r) = kappa ρ j r

-- (1.2) at ρ = 1, j = 2 (d = p²q, Ω = 3):  a_z = z(z-1)² = z³−2z²+z.
kappa-p2q-0 : kappa 1 2 0 ≡ pos 0
kappa-p2q-0 = refl
kappa-p2q-1 : kappa 1 2 1 ≡ pos 1
kappa-p2q-1 = refl
kappa-p2q-2 : kappa 1 2 2 ≡ negsuc 1        -- −2
kappa-p2q-2 = refl
kappa-p2q-3 : kappa 1 2 3 ≡ pos 1
kappa-p2q-3 = refl

-- (1.2) at ρ = 0, j = 3 (d = pqr, Ω = 3):  a_z = (z-1)³ = z³−3z²+3z−1.
kappa-pqr-0 : kappa 0 3 0 ≡ negsuc 0        -- −1
kappa-pqr-0 = refl
kappa-pqr-1 : kappa 0 3 1 ≡ pos 3
kappa-pqr-1 = refl
kappa-pqr-2 : kappa 0 3 2 ≡ negsuc 2        -- −3
kappa-pqr-2 = refl
kappa-pqr-3 : kappa 0 3 3 ≡ pos 1
kappa-pqr-3 = refl

------------------------------------------------------------------------
-- 3.  Sums over the index window [0 , k).

sumBelow : (ℕ → ℤ) → ℕ → ℤ
sumBelow f zero    = pos 0
sumBelow f (suc k) = f k + sumBelow f k

-- A summand that vanishes everywhere sums to zero.
sumZero : (f : ℕ → ℤ) (k : ℕ)
        → ((r : ℕ) → r < k → f r ≡ pos 0)
        → sumBelow f k ≡ pos 0
sumZero f zero    _ = refl
sumZero f (suc k) h =
  cong₂ _+_ (h k ≤-refl) (sumZero f k (λ r r<k → h r (≤-suc r<k)))

-- A summand supported at one point of the window sums to its value.
sumSupport : (f : ℕ → ℤ) (k j : ℕ) → j < k
           → ((r : ℕ) → r < k → ¬ (r ≡ j) → f r ≡ pos 0)
           → sumBelow f k ≡ f j
sumSupport f zero j j<0 _ = ⊥.rec (¬-<-zero j<0)
sumSupport f (suc k) j j<sk h with <-split j<sk
... | inl j<k =
      cong₂ _+_ (h k ≤-refl (>→≢ k j j<k))
                (sumSupport f k j j<k (λ r r<k → h r (≤-suc r<k)))
      ∙ sym (pos0+ (f j))
... | inr j≡k =
      cong₂ _+_ (cong f (sym j≡k))
                (sumZero f k (λ r r<k →
                   h r (≤-suc r<k)
                     (<→≢ r j (subst (λ x → r < x) (sym j≡k) r<k))))

-- A summand supported at two points of the window sums to their values.
sumSupport2 : (f : ℕ → ℤ) (k j₁ j₂ : ℕ) → j₁ < j₂ → j₂ < k
            → ((r : ℕ) → r < k → ¬ (r ≡ j₁) → ¬ (r ≡ j₂) → f r ≡ pos 0)
            → sumBelow f k ≡ f j₂ + f j₁
sumSupport2 f zero j₁ j₂ _ j₂<0 _ = ⊥.rec (¬-<-zero j₂<0)
sumSupport2 f (suc k) j₁ j₂ j₁<j₂ j₂<sk h with <-split j₂<sk
... | inl j₂<k =
      cong₂ _+_ (h k ≤-refl (>→≢ k j₁ (<-trans j₁<j₂ j₂<k))
                            (>→≢ k j₂ j₂<k))
                (sumSupport2 f k j₁ j₂ j₁<j₂ j₂<k
                   (λ r r<k → h r (≤-suc r<k)))
      ∙ sym (pos0+ (f j₂ + f j₁))
... | inr j₂≡k =
      cong₂ _+_ (cong f (sym j₂≡k))
                (sumSupport f k j₁ (subst (λ x → j₁ < x) j₂≡k j₁<j₂)
                   (λ r r<k r≢j₁ →
                      h r (≤-suc r<k) r≢j₁
                        (<→≢ r j₂ (subst (λ x → r < x) (sym j₂≡k) r<k))))

------------------------------------------------------------------------
-- 4.  The cyclic projector, as the right-hand side of note (2.1).
--
--     Π^cyc_{s,n} A  :=  Σ_{0 ≤ r ≤ R,  r ≡ s (mod n)}  A_r .
--
-- `pick` is the indicator-weighted summand; `aliasSum` sums it over the
-- window [0,R].  No root of unity appears: by (2.1) this IS the value
-- of the Fourier average, and the whole question of exactness is about
-- which indices the class picks up.

pick : (ℕ → ℤ) → ℕ → ℕ → ℕ → ℤ
pick A n s r = if eqℕ (r mod n) (s mod n) then A r else pos 0

aliasSum : (ℕ → ℤ) → ℕ → ℕ → ℕ → ℤ
aliasSum A n s R = sumBelow (pick A n s) (suc R)

pick-hit : (A : ℕ → ℤ) (n s : ℕ) → pick A n s s ≡ A s
pick-hit A n s = cong (λ b → if b then A s else pos 0) (eqℕ-refl (s mod n))

pick-class : (A : ℕ → ℤ) (n s r : ℕ) → r mod n ≡ s mod n → pick A n s r ≡ A r
pick-class A n s r p =
  cong (λ b → if b then A r else pos 0)
       (cong (eqℕ (r mod n)) (sym p) ∙ eqℕ-refl (r mod n))

pick-miss : (A : ℕ → ℤ) (n s r : ℕ) → ¬ (r mod n ≡ s mod n)
          → pick A n s r ≡ pos 0
pick-miss A n s r p =
  cong (λ b → if b then A r else pos 0) (eqℕ-neq (r mod n) (s mod n) p)

-- x < n ⟹ x mod n = x, spelled for n in successor form.
modSmall : (n' x : ℕ) → x < suc n' → x mod (suc n') ≡ x
modSmall n' x p = modIndBase n' x p

------------------------------------------------------------------------
-- 5.  (a)  n > R  ⟹  NO ALIASING, and exact recovery.

-- Each residue class mod n contains at most one index of the window.
-- GENERAL in n and R.
classInjective : (n R : ℕ) → R < n → (r s : ℕ) → r ≤ R → s ≤ R
               → r mod n ≡ s mod n → r ≡ s
classInjective zero R R<0 _ _ _ _ _ = ⊥.rec (¬-<-zero R<0)
classInjective (suc n') R R<n r s r≤R s≤R p =
    sym (modSmall n' r (≤<-trans r≤R R<n))
  ∙ p
  ∙ modSmall n' s (≤<-trans s≤R R<n)

-- THE EXACTNESS THEOREM.  GENERAL in A, n, R, j: with n > R the cyclic
-- projector at s = j returns the coefficient a_j itself.  This is the
-- hypothesis under which the κ_DFT = 1 projector of
-- PRIME_ATOM_TOMOGRAPHY_CONDITIONING Thm 4.3 is an exact extractor.
exact : (A : ℕ → ℤ) (n R j : ℕ) → R < n → j ≤ R
      → aliasSum A n j R ≡ A j
exact A n R j R<n j≤R =
    sumSupport (pick A n j) (suc R) j (suc-≤-suc j≤R) miss
  ∙ pick-hit A n j
  where
  miss : (r : ℕ) → r < suc R → ¬ (r ≡ j) → pick A n j r ≡ pos 0
  miss r r<sR r≢j =
    pick-miss A n j r
      (λ q → r≢j (classInjective n R R<n r j (pred-≤-pred r<sR) j≤R q))

------------------------------------------------------------------------
-- 6.  (b)  n ≤ R  ⟹  a collision, and the exact aliased functional.

-- The collision witness, GENERAL in n, R, j: j and j+n are two
-- DISTINCT indices of the window lying in the SAME class mod n.  Taking
-- j = 0 this fires whenever n ≤ R, which is the exact negation of the
-- hypothesis of `exact`.
collisionIndices : (n R j : ℕ) → 0 < n → (j +ℕ n) ≤ R
                 → (j ≤ R)                          -- j is in the window
                 × (¬ (j ≡ j +ℕ n))                 -- …and j+n is another index
                 × ((j +ℕ n) mod n ≡ j mod n)       -- …in the same class
collisionIndices n R j 0<n j+n≤R =
  ≤-trans ≤SumLeft j+n≤R , distinct , sym (mod-rUnit n j)
  where
  distinct : ¬ (j ≡ j +ℕ n)
  distinct e =
    ¬-<-zero (subst (λ x → 0 < x) (sym (inj-m+ (+-zero j ∙ e))) 0<n)

-- The dichotomy's other side, stated as the literal negation of the
-- hypothesis of `exact`: as soon as n ≤ R the window carries a
-- collision (take j = 0), so no argument of the form "the projector is
-- perfectly conditioned" can rescue exactness.
collisionAtZero : (n R : ℕ) → 0 < n → n ≤ R
                → (0 ≤ R) × (¬ (0 ≡ n)) × (n mod n ≡ 0 mod n)
collisionAtZero n R 0<n n≤R = collisionIndices n R 0 0<n n≤R

-- j < j+n whenever n is a successor.
j<j+n : (j n' : ℕ) → j < (j +ℕ suc n')
j<j+n j n' = subst (λ x → suc j ≤ x) (sym (+-suc j n')) (suc-≤-suc ≤SumLeft)

-- On the FIRST aliasing shell n ≤ R < 2n the class of j (with j < n)
-- meets the window in exactly {j , j+n}.  GENERAL.
firstShell : (n' j r R : ℕ) → j < suc n' → r ≤ R → R < (suc n' +ℕ suc n')
           → r mod (suc n') ≡ j mod (suc n')
           → (r ≡ j) ⊎ (r ≡ (j +ℕ suc n'))
firstShell n' j r R j<n r≤R R<2n p with splitℕ-< r (suc n')
... | inl r<n = inl (sym (modSmall n' r r<n) ∙ p ∙ modSmall n' j j<n)
... | inr n≤r = inr (sym (n≤r .snd) ∙ cong (_+ℕ suc n') t≡j)
  where
  t : ℕ
  t = n≤r .fst

  t+n≡r : (t +ℕ suc n') ≡ r
  t+n≡r = n≤r .snd

  -- t + n ≤ R < n + n, and suc (t + n) is definitionally (suc t) + n,
  -- so left-cancelling the common summand n gives t < n.
  t<n : t < suc n'
  t<n = ≤-+k-cancel {m = suc t} {k = suc n'} {n = suc n'}
          (≤<-trans (subst (_≤ R) (sym t+n≡r) r≤R) R<2n)

  t≡j : t ≡ j
  t≡j =   sym (modSmall n' t t<n)
        ∙ mod-rUnit (suc n') t
        ∙ cong (_mod (suc n')) t+n≡r
        ∙ p
        ∙ modSmall n' j j<n

-- THE ALIASING THEOREM.  GENERAL in A, n, j, R.  Once n ≤ R (first
-- shell: j < n, j+n ≤ R, R < 2n) the projector does not fail softly —
-- it computes exactly the wrong functional, and this names it:
--
--     Π^cyc_{j,n} A  =  A_{j+n} + A_j.
--
-- The κ = 1 conditioning of the inverse is untouched by this; a
-- perfectly conditioned map onto the wrong target is still wrong.
aliased : (A : ℕ → ℤ) (n' j R : ℕ)
        → j < suc n' → (j +ℕ suc n') ≤ R → R < (suc n' +ℕ suc n')
        → aliasSum A (suc n') j R ≡ A (j +ℕ suc n') + A j
aliased A n' j R j<n j+n≤R R<2n =
    sumSupport2 (pick A (suc n') j) (suc R) j (j +ℕ suc n')
                (j<j+n j n') (suc-≤-suc j+n≤R) off
  ∙ cong₂ _+_ (pick-class A (suc n') j (j +ℕ suc n')
                          (sym (mod-rUnit (suc n') j)))
              (pick-hit A (suc n') j)
  where
  off : (r : ℕ) → r < suc R → ¬ (r ≡ j) → ¬ (r ≡ (j +ℕ suc n'))
      → pick A (suc n') j r ≡ pos 0
  off r r<sR r≢j r≢j+n =
    pick-miss A (suc n') j r
      (λ q → ⊎rec (firstShell n' j r R j<n (pred-≤-pred r<sR) R<2n q))
    where
    ⊎rec : (r ≡ j) ⊎ (r ≡ (j +ℕ suc n')) → ⊥
    ⊎rec (inl e) = r≢j e
    ⊎rec (inr e) = r≢j+n e

------------------------------------------------------------------------
-- 7.  Instances: the dichotomy on the note's own kernels — each side
--     first as an application of the general theorem above, then as the
--     concrete integer it evaluates to (refl).
--
-- d = p²q  (ρ = 1, j = 2, R = Ω(d) = 3, κ = (0, 1, −2, 1), κ₁ = 1).

-- M = 4 > R = 3: exact, by the general theorem…
p2q-exact-general : aliasSum (kappa 1 2) 4 1 3 ≡ kappa 1 2 1
p2q-exact-general = exact (kappa 1 2) 4 3 1 (0 , refl) (2 , refl)

-- …and the value is κ₁ = 1.
p2q-exact-value : aliasSum (kappa 1 2) 4 1 3 ≡ pos 1
p2q-exact-value = refl

-- M = 2 ≤ R = 3: aliased.  The general theorem predicts κ₃ + κ₁…
p2q-aliased-general : aliasSum (kappa 1 2) 2 1 3 ≡ kappa 1 2 3 + kappa 1 2 1
p2q-aliased-general = aliased (kappa 1 2) 1 1 3 ≤-refl ≤-refl ≤-refl

-- …and that value is 2, NOT κ₁ = 1.  This is the note's "the parity
-- phase M = 2 is not primality in general".
p2q-parity-value : aliasSum (kappa 1 2) 2 1 3 ≡ pos 2
p2q-parity-value = refl

p2q-parity-wrong : ¬ (aliasSum (kappa 1 2) 2 1 3 ≡ kappa 1 2 1)
p2q-parity-wrong e = snotz (injSuc (injPos e))

-- d = pqr  (ρ = 0, j = 3, R = 3, κ = (−1, 3, −3, 1), κ₁ = 3).

pqr-exact-general : aliasSum (kappa 0 3) 4 1 3 ≡ kappa 0 3 1
pqr-exact-general = exact (kappa 0 3) 4 3 1 (0 , refl) (2 , refl)

pqr-exact-value : aliasSum (kappa 0 3) 4 1 3 ≡ pos 3
pqr-exact-value = refl

pqr-aliased-general : aliasSum (kappa 0 3) 2 1 3 ≡ kappa 0 3 3 + kappa 0 3 1
pqr-aliased-general = aliased (kappa 0 3) 1 1 3 ≤-refl ≤-refl ≤-refl

pqr-parity-value : aliasSum (kappa 0 3) 2 1 3 ≡ pos 4
pqr-parity-value = refl

------------------------------------------------------------------------
-- 8.  Cross-check against the note's independent closed form (2.3).
--
--     Σ_{r odd} κ_r(d) = −½ a_{−1}(d) = −½ (−1)^{ρ(d)} (−2)^{ω(d)}.
--
-- Cleared of the ½ (ℤ has no division):
--
--     2 · Σ_{r odd} κ_r  ≡  −( (−1)^ρ · (−2)^ω ).
--
-- The two sides run through disjoint code: the left is the index-class
-- sum of §4 at n = 2, s = 1 over the coefficient vector; the right
-- never touches `kappa` at all, being the note's closed form evaluated
-- from (ρ , ω) alone.  Agreement therefore checks both.

negOnePow : ℕ → ℤ
negOnePow zero    = pos 1
negOnePow (suc m) = - negOnePow m

negTwoPow : ℕ → ℤ
negTwoPow zero    = pos 1
negTwoPow (suc m) = negsuc 1 · negTwoPow m

parity-23-p2q : pos 2 · aliasSum (kappa 1 2) 2 1 3
              ≡ - (negOnePow 1 · negTwoPow 2)
parity-23-p2q = refl

parity-23-pqr : pos 2 · aliasSum (kappa 0 3) 2 1 3
              ≡ - (negOnePow 0 · negTwoPow 3)
parity-23-pqr = refl
