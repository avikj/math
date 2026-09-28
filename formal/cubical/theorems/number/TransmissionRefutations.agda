{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TransmissionRefutations
--
-- Three displays of the owner's fifth transmission
-- (`collab/upstream/raw/D0020-owner-fifth-transmission-2026-08-15.md` (absent from this repository)),
-- here as terms rather than as one reader's arithmetic.
--
-- SECTION A  §8's Π_∂ identity.  Archive line 393:
--
--     1 ≤ Ω(ν) ≤ 2  ⇒  Π_∂(ν) = (1 − λ(ν))/2 − 1_℘(ν)
--     Π_∂(ν) := μ(ν)² − π₁(ν),      π₁(ν) := ω(ν) − 1
--
--   Refuted.  Smallest witness ν = 2 (the smallest prime):
--   LHS = 1, RHS = 0.  The failure is by
--   exactly 1 on every prime; the UNIVERSAL half is proved as
--   `prime-row-fails-by-one`, from the values the four arithmetic
--   functions take at a prime.
--
-- SECTION B  §1's Mbius display.  Archive line 83:
--
--     Σ_{δ | ν} μ(δ) ⌊ν/δ⌋ = 1
--
--   Refuted at ν = 3 by computation with a Mbius function DEFINED here
--   (trial division with fuel), not tabulated: the sum is 2.  The value
--   is φ(ν), also computed here from an independent definition
--   (counting coprime residues), agreeing at ν = 1..12; and the
--   classical identity the display is one character from,
--   Σ_{δ ≤ ν} μ(δ) ⌊ν/δ⌋ = 1, is verified at ν = 1..12.
--
-- SECTION C  §0's tower.  Archive lines 33–36:
--
--     κ(Θ) := ⋂ { Υ ⊇ Θ | Υ closed under the nine operations }
--     Θ_{ν+1} := κ(Θ_ν),   Θ_λ := ⋃_{ν<λ} Θ_ν,   Θ_∞ := ⋃_λ Θ_λ
--
--   The collapse is formalised in the form the ledger's §5.1 argument
--   actually uses: ANY operator that is extensive, produces closed
--   sets, and is least among closed supersets is idempotent, and its
--   tower is constant from stage one.  What is formalised is (i) the
--   abstract theorem and (ii) a witness that its hypotheses are
--   satisfiable, namely the
--   inductively generated closure over an arbitrary sign type with
--   unary and binary operations.  Scope limits are stated in full at
------------------------------------------------------------------------

module TransmissionRefutations where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; not; _and_; true≢false)
open import Cubical.Data.Int using (ℤ; pos; negsuc; _+_; _-_; _·_; -_)
open import Cubical.Data.Sigma using (_×_; _,_; Σ; fst; snd)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 0.  Elementary computable arithmetic on ℕ.
--
-- Written out rather than imported so that the refutations do not
-- depend on which of the two pinned cubical versions is in use, and so
-- that every value below reduces definitionally.
------------------------------------------------------------------------

addN : ℕ → ℕ → ℕ
addN zero n = n
addN (suc m) n = suc (addN m n)

sub : ℕ → ℕ → ℕ
sub m zero = m
sub zero (suc _) = zero
sub (suc m) (suc n) = sub m n

leb : ℕ → ℕ → Bool          -- m ≤ n
leb zero _ = true
leb (suc _) zero = false
leb (suc m) (suc n) = leb m n

ltb : ℕ → ℕ → Bool          -- m < n
ltb m n = not (leb n m)

eqb : ℕ → ℕ → Bool
eqb zero zero = true
eqb zero (suc _) = false
eqb (suc _) zero = false
eqb (suc m) (suc n) = eqb m n

-- remainder and quotient, fuel-bounded so that they are structurally
-- recursive; called only with fuel ≥ the dividend, where they are exact.
remF : ℕ → ℕ → ℕ → ℕ
remF zero n _ = n
remF (suc f) n d = if ltb n d then n else remF f (sub n d) d

quoF : ℕ → ℕ → ℕ → ℕ
quoF zero _ _ = zero
quoF (suc f) n d = if ltb n d then zero else suc (quoF f (sub n d) d)

_mod_ : ℕ → ℕ → ℕ
n mod d = remF n n d

_div_ : ℕ → ℕ → ℕ          -- ⌊n/d⌋ for d ≥ 1
n div d = quoF n n d

dividesb : ℕ → ℕ → Bool     -- d ∣ n
dividesb d n = eqb (n mod d) zero

-- least divisor ≥ k of n (returns n if none below n); with k = 2 and
-- n ≥ 2 this is the least prime factor.
spfF : ℕ → ℕ → ℕ → ℕ
spfF zero _ n = n
spfF (suc f) k n =
  if ltb n k then n
  else (if dividesb k n then k else spfF f (suc k) n)

spf : ℕ → ℕ
spf n = spfF n 2 n

isPrimeb : ℕ → Bool
isPrimeb n = (leb 2 n) and eqb (spf n) n

------------------------------------------------------------------------
-- 1.  The arithmetic functions of the two displays, DEFINED (not
--     tabulated): μ, φ, ω (distinct prime factors), Ω (with
--     multiplicity), λ = (−1)^Ω, and the primality indicator 1_℘.
------------------------------------------------------------------------

negZ : ℤ → ℤ
negZ z = pos zero - z

muF : ℕ → ℕ → ℤ
muF zero _ = pos zero
muF (suc f) n =
  if eqb n 1 then pos 1
  else (if dividesb (spf n) (n div spf n)
          then pos zero
          else negZ (muF f (n div spf n)))

mu : ℕ → ℤ
mu n = muF n n

-- Ω(n): number of prime factors with multiplicity.
bigOmegaF : ℕ → ℕ → ℕ
bigOmegaF zero _ = zero
bigOmegaF (suc f) n = if eqb n 1 then zero else suc (bigOmegaF f (n div spf n))

bigOmega : ℕ → ℕ
bigOmega n = bigOmegaF n n

-- ω(n): number of DISTINCT primes dividing n, by exhaustive scan.
omegaCount : ℕ → ℕ → ℕ
omegaCount zero _ = zero
omegaCount (suc k) n =
  addN (if (isPrimeb (suc k)) and (dividesb (suc k) n) then 1 else 0)
       (omegaCount k n)

smallOmega : ℕ → ℕ
smallOmega n = omegaCount n n

-- λ(n) = (−1)^{Ω(n)}, computed from Ω's parity.
parity : ℕ → ℤ
parity zero = pos 1
parity (suc zero) = negsuc 0
parity (suc (suc n)) = parity n

lambdaL : ℕ → ℤ
lambdaL n = parity (bigOmega n)

indP : ℕ → ℤ
indP n = if isPrimeb n then pos 1 else pos zero

-- gcd and φ, for the independent identification of the divisor sum.
gcdF : ℕ → ℕ → ℕ → ℕ
gcdF zero a _ = a
gcdF (suc f) a b = if eqb b zero then a else gcdF f b (a mod b)

gcdN : ℕ → ℕ → ℕ
gcdN a b = gcdF (addN (addN a b) 1) a b

phiCount : ℕ → ℕ → ℕ
phiCount zero _ = zero
phiCount (suc k) n =
  addN (if eqb (gcdN (suc k) n) 1 then 1 else 0) (phiCount k n)

phi : ℕ → ℕ
phi n = phiCount n n

------------------------------------------------------------------------
-- 2.  Disequality of integers, by an injection into Bool.
------------------------------------------------------------------------

isPos1 : ℤ → Bool
isPos1 (pos (suc zero)) = true
isPos1 _ = false

isPos0 : ℤ → Bool
isPos0 (pos zero) = true
isPos0 _ = false

2≢1 : ¬ (pos 2 ≡ pos 1)
2≢1 p = true≢false (cong (λ z → not (isPos1 z)) p)

1≢0 : ¬ (pos 1 ≡ pos zero)
1≢0 p = true≢false (cong (λ z → not (isPos0 z)) p)

------------------------------------------------------------------------
-- SECTION A.  §8's Π_∂ identity (archive line 393; ledger rows 8.5, 5.3)
--
-- The display, verbatim from the archive:
--
--     Π_∂(ν) := μ(ν)² − π₁(ν),      π₁(ν) := ω(ν) − 1
--     1 ≤ Ω(ν) ≤ 2  ⇒  Π_∂(ν) = (1 − λ(ν))/2 − 1_℘(ν)
--
-- Both sides are transcribed as functions of ν below, with (1−λ)/2
-- given by an explicit halving whose correctness is itself certified
-- (`half-is-half`), so that no division is assumed.
------------------------------------------------------------------------

-- μ(ν)²
mu² : ℕ → ℤ
mu² n = mu n · mu n

-- π₁(ν) := ω(ν) − 1
pi1 : ℕ → ℤ
pi1 n = pos (smallOmega n) - pos 1

-- Π_∂(ν) := μ(ν)² − π₁(ν)
PiPartial : ℕ → ℤ
PiPartial n = mu² n - pi1 n

-- (1 − l)/2 for l ∈ {+1, −1}, as an explicit function.
halfOneMinus : ℤ → ℤ
halfOneMinus (pos (suc zero)) = pos zero          -- l = +1 ↦ 0
halfOneMinus (negsuc zero) = pos 1                -- l = −1 ↦ 1
halfOneMinus _ = pos zero

-- The halving is a genuine halving on the two values λ takes.
half-is-half-plus : pos 2 · halfOneMinus (pos 1) ≡ pos 1 - pos 1
half-is-half-plus = refl

half-is-half-minus : pos 2 · halfOneMinus (negsuc 0) ≡ pos 1 - (negsuc 0)
half-is-half-minus = refl

-- the transmission's right-hand side, as written
RHS : ℕ → ℤ
RHS n = halfOneMinus (lambdaL n) - indP n

-- the ledger's proposed repair: the same display with 1_℘ deleted
RHS-repaired : ℕ → ℤ
RHS-repaired n = halfOneMinus (lambdaL n)

------------------------------------------------------------------------
-- A.1  The smallest counterexample, located here rather than taken on
--      trust.  ν = 1 is excluded by the display's own hypothesis
--      (Ω(1) = 0), so ν = 2 is the smallest candidate at all, and it
--      already fails.
------------------------------------------------------------------------

Omega-1-is-0 : bigOmega 1 ≡ 0
Omega-1-is-0 = refl

-- ν = 2 : hypothesis satisfied, and the identity fails.
Omega-2 : bigOmega 2 ≡ 1
Omega-2 = refl

lhs-at-2 : PiPartial 2 ≡ pos 1
lhs-at-2 = refl

rhs-at-2 : RHS 2 ≡ pos zero
rhs-at-2 = refl

-- THE REFUTATION at the smallest witness.
Pi-fails-at-2 : ¬ (PiPartial 2 ≡ RHS 2)
Pi-fails-at-2 p = 1≢0 ((sym lhs-at-2 ∙ p) ∙ rhs-at-2)

-- and the failure is by exactly 1
Pi-gap-at-2 : PiPartial 2 ≡ RHS 2 + pos 1
Pi-gap-at-2 = refl

------------------------------------------------------------------------
-- A.2  Further instances: the next primes fail identically; the two
--      Ω = 2 shapes hold.  Finite exhaustive verification over every
--      ν ≤ 25 with 1 ≤ Ω(ν) ≤ 2 is given in A.3.
------------------------------------------------------------------------

Pi-gap-at-3 : PiPartial 3 ≡ RHS 3 + pos 1
Pi-gap-at-3 = refl

Pi-gap-at-5 : PiPartial 5 ≡ RHS 5 + pos 1
Pi-gap-at-5 = refl

Pi-gap-at-7 : PiPartial 7 ≡ RHS 7 + pos 1
Pi-gap-at-7 = refl

Pi-holds-at-4 : PiPartial 4 ≡ RHS 4          -- p²
Pi-holds-at-4 = refl

Pi-holds-at-9 : PiPartial 9 ≡ RHS 9          -- p²
Pi-holds-at-9 = refl

Pi-holds-at-6 : PiPartial 6 ≡ RHS 6          -- pq
Pi-holds-at-6 = refl

Pi-holds-at-15 : PiPartial 15 ≡ RHS 15       -- pq
Pi-holds-at-15 = refl

------------------------------------------------------------------------
-- A.3  Exhaustive check over an explicit range.
--
--   `gapOK n` says: EITHER the display's hypothesis 1 ≤ Ω(n) ≤ 2 fails
--   at n (so n is out of scope), OR Π_∂(n) = RHS(n) + 1_℘(n) — that is,
--   the display is off by exactly the indicator it should not carry.
--   Checking `allGapOK 25 ≡ true` therefore verifies, at one stroke and
--   over every ν ≤ 25 in scope, both the refutation and its exact size.
------------------------------------------------------------------------

inScope : ℕ → Bool
inScope n = (leb 1 (bigOmega n)) and (leb (bigOmega n) 2)

eqZb : ℤ → ℤ → Bool
eqZb (pos m) (pos n) = eqb m n
eqZb (negsuc m) (negsuc n) = eqb m n
eqZb _ _ = false

gapOK : ℕ → Bool
gapOK n = if inScope n then eqZb (PiPartial n) (RHS n + indP n) else true

allGapOK : ℕ → Bool
allGapOK zero = true
allGapOK (suc k) = (gapOK (suc k)) and allGapOK k

-- Every ν ≤ 25 with 1 ≤ Ω(ν) ≤ 2 satisfies Π_∂(ν) = RHS(ν) + 1_℘(ν):
-- the display is exactly one indicator wrong, and wrong precisely on
-- the primes (where 1_℘ = 1) and nowhere else in range.
exhaustive-to-25 : allGapOK 25 ≡ true
exhaustive-to-25 = refl

-- The ledger's repair, verified over the same range.
repairOK : ℕ → Bool
repairOK n = if inScope n then eqZb (PiPartial n) (RHS-repaired n) else true

allRepairOK : ℕ → Bool
allRepairOK zero = true
allRepairOK (suc k) = (repairOK (suc k)) and allRepairOK k

repair-holds-to-25 : allRepairOK 25 ≡ true
repair-holds-to-25 = refl

------------------------------------------------------------------------
-- A.4  The universal half: "false on every prime".
--
--   * "the display fails by 1 at ν, given the prime values" — THEOREM.
--   * "every prime has those values"                        — checked
--     here at ν = 2, 3, 5, 7, 11, 13, 17, 19, 23 (A.5), by
--     computation with the definitions of §1.
------------------------------------------------------------------------

PiPartial-abs : ℤ → ℤ → ℤ            -- from μ², ω
PiPartial-abs m w = m - (w - pos 1)

RHS-abs : ℤ → ℤ → ℤ                  -- from λ, 1_℘
RHS-abs l i = halfOneMinus l - i

prime-row-fails-by-one :
  (m w l i : ℤ)
  → m ≡ pos 1 → w ≡ pos 1 → l ≡ negsuc 0 → i ≡ pos 1
  → PiPartial-abs m w ≡ RHS-abs l i + pos 1
prime-row-fails-by-one m w l i pm pw pl pi =
  cong₂ PiPartial-abs pm pw ∙ sym (cong (λ z → z + pos 1) (cong₂ RHS-abs pl pi))

-- the same statement in the strong form: the two sides are never equal
-- under the prime hypotheses.
prime-row-refutes :
  (m w l i : ℤ)
  → m ≡ pos 1 → w ≡ pos 1 → l ≡ negsuc 0 → i ≡ pos 1
  → ¬ (PiPartial-abs m w ≡ RHS-abs l i)
prime-row-refutes m w l i pm pw pl pi q =
  1≢0 ((sym (cong₂ PiPartial-abs pm pw) ∙ q) ∙ cong₂ RHS-abs pl pi)

-- The two Ω = 2 shapes, likewise abstractly: the display HOLDS there.
semiprime-row-holds :
  (m w l i : ℤ)
  → m ≡ pos 1 → w ≡ pos 2 → l ≡ pos 1 → i ≡ pos zero
  → PiPartial-abs m w ≡ RHS-abs l i
semiprime-row-holds m w l i pm pw pl pi =
  cong₂ PiPartial-abs pm pw ∙ sym (cong₂ RHS-abs pl pi)

primesquare-row-holds :
  (m w l i : ℤ)
  → m ≡ pos zero → w ≡ pos 1 → l ≡ pos 1 → i ≡ pos zero
  → PiPartial-abs m w ≡ RHS-abs l i
primesquare-row-holds m w l i pm pw pl pi =
  cong₂ PiPartial-abs pm pw ∙ sym (cong₂ RHS-abs pl pi)

------------------------------------------------------------------------
-- A.5  The prime values, computed at the primes below 25.
------------------------------------------------------------------------

primeValues : ℕ → Bool
primeValues n =
  (eqZb (mu² n) (pos 1)) and
  ((eqZb (pos (smallOmega n)) (pos 1)) and
   ((eqZb (lambdaL n) (negsuc 0)) and (eqZb (indP n) (pos 1))))

allPrimeValues : ℕ → Bool
allPrimeValues zero = true
allPrimeValues (suc k) =
  (if isPrimeb (suc k) then primeValues (suc k) else true) and allPrimeValues k

prime-values-to-25 : allPrimeValues 25 ≡ true
prime-values-to-25 = refl

------------------------------------------------------------------------
-- SECTION B.  §1's Mbius display (archive line 83; ledger rows 1.5, 5.2)
--
-- The display, verbatim: Σ_{δ | ν} μ(δ) ⌊ν/δ⌋ = 1.
------------------------------------------------------------------------

-- Σ over the divisors δ ≤ k of n, of μ(δ)·⌊n/δ⌋.
divSumTo : ℕ → ℕ → ℤ
divSumTo zero _ = pos zero
divSumTo (suc k) n =
  (if dividesb (suc k) n then mu (suc k) · pos (n div (suc k)) else pos zero)
    + divSumTo k n

-- the transmission's left-hand side
mobiusDivSum : ℕ → ℤ
mobiusDivSum n = divSumTo n n

-- the classical identity's left-hand side: the SAME summand over ALL
-- δ ≤ ν, not only the divisors.
allSumTo : ℕ → ℕ → ℤ
allSumTo zero _ = pos zero
allSumTo (suc k) n = (mu (suc k) · pos (n div (suc k))) + allSumTo k n

mobiusFullSum : ℕ → ℤ
mobiusFullSum n = allSumTo n n

------------------------------------------------------------------------
-- B.1  The refutation at ν = 3, the witness the ledger names.
------------------------------------------------------------------------

mu-at-1 : mu 1 ≡ pos 1
mu-at-1 = refl

mu-at-3 : mu 3 ≡ negsuc 0
mu-at-3 = refl

mobius-at-3 : mobiusDivSum 3 ≡ pos 2
mobius-at-3 = refl

-- THE REFUTATION.
mobius-display-false : ¬ (mobiusDivSum 3 ≡ pos 1)
mobius-display-false p = 2≢1 (sym mobius-at-3 ∙ p)

-- ν = 3 is the smallest witness: at ν = 1 and ν = 2 the display holds,
-- since φ(1) = φ(2) = 1.
mobius-at-1 : mobiusDivSum 1 ≡ pos 1
mobius-at-1 = refl

mobius-at-2 : mobiusDivSum 2 ≡ pos 1
mobius-at-2 = refl

------------------------------------------------------------------------
-- B.2  What the divisor sum actually is: φ, on an independent
--      definition of φ (counting coprime residues, §1).
------------------------------------------------------------------------

phiAgrees : ℕ → Bool
phiAgrees n = eqZb (mobiusDivSum n) (pos (phi n))

allPhiAgrees : ℕ → Bool
allPhiAgrees zero = true
allPhiAgrees (suc k) = phiAgrees (suc k) and allPhiAgrees k

-- Σ_{δ | ν} μ(δ)⌊ν/δ⌋ = φ(ν) for every ν ≤ 12.
divsum-is-phi-to-12 : allPhiAgrees 12 ≡ true
divsum-is-phi-to-12 = refl

------------------------------------------------------------------------
-- B.3  The repair: the classical identity, over ALL δ ≤ ν.
------------------------------------------------------------------------

fullIsOne : ℕ → Bool
fullIsOne n = eqZb (mobiusFullSum n) (pos 1)

allFullIsOne : ℕ → Bool
allFullIsOne zero = true
allFullIsOne (suc k) = fullIsOne (suc k) and allFullIsOne k

-- Σ_{δ ≤ ν} μ(δ) ⌊ν/δ⌋ = 1 for every ν ≤ 12: the display with the
-- range of summation corrected.
full-sum-is-one-to-12 : allFullIsOne 12 ≡ true
full-sum-is-one-to-12 = refl

-- The companion display of the same archive line, Σ_{δ|ν} μ(δ) = [ν=1],
-- which the ledger reports as correct — checked here too.
divSumMu : ℕ → ℕ → ℤ
divSumMu zero _ = pos zero
divSumMu (suc k) n =
  (if dividesb (suc k) n then mu (suc k) else pos zero) + divSumMu k n

muDivSumOK : ℕ → Bool
muDivSumOK n = eqZb (divSumMu n n) (if eqb n 1 then pos 1 else pos zero)

allMuDivSumOK : ℕ → Bool
allMuDivSumOK zero = true
allMuDivSumOK (suc k) = muDivSumOK (suc k) and allMuDivSumOK k

companion-display-holds-to-12 : allMuDivSumOK 12 ≡ true
companion-display-holds-to-12 = refl

------------------------------------------------------------------------
-- SECTION C.  §0's tower collapses at stage one (ledger rows 0.3, 5.1)
--
-- The archive's κ is  κ(Θ) := ⋂ { Υ ⊇ Θ | Υ closed under the nine
-- operations }.  As the ledger's row 0.2 records, no ambient set is
-- supplied, so this intersection ranges over a class and κ does not
-- denote as written.  What
-- IS formalised is the argument the ledger's §5.1 actually runs, in the
-- form in which it is independent of the ambient:
--
--   (C.1)  ANY operator K on subsets that is extensive, closed-valued
--          and least among closed supersets is idempotent, and its
--          tower is constant from stage one.  This is the whole content
--          of §5.1; the intersection enters only as one way of
--          producing such a K.
--
--   (C.2)  The hypotheses of (C.1) are satisfiable, so the theorem is
--          not vacuous: the inductively generated closure `Gen` over an
--          arbitrary type of signs with an arbitrary family of unary
--          and binary operations satisfies all three.
--
-- MISSING DEFINITIONS, named rather than supplied:
--   * the ambient set 𝒮 (row 0.2);
--   * the meaning of the nine operations ⊕, ⊗, ∘, ∂, δ, Γ, Φ, (−)^∨,
--     ⌜−⌝ as operations on signs.  Here they are only assumed to be
--     unary or binary relations — which is all §5.1's finitary-arity
--     step uses, and all the display's own bracketing determines.
--     In particular Γ is NOT assumed to be a function: ledger row 0.6
--     refutes exactly that, and the arity-only treatment below is
--     compatible with Γ being multivalued.
------------------------------------------------------------------------

module Collapse {ℓ : Level} (S : Type ℓ)
                (U₁ : S → S → Type ℓ)           -- unary  ops: U₁ a x  ≔ "x = op a"
                (U₂ : S → S → S → Type ℓ)       -- binary ops: U₂ a b x ≔ "x = op a b"
  where

  Subset : Type (ℓ-suc ℓ)
  Subset = S → Type ℓ

  _⊑_ : Subset → Subset → Type ℓ
  A ⊑ B = (x : S) → A x → B x

  record Closed (A : Subset) : Type ℓ where
    field
      c₁ : {a x : S} → U₁ a x → A a → A x
      c₂ : {a b x : S} → U₂ a b x → A a → A b → A x
  open Closed public

  ----------------------------------------------------------------
  -- C.1  The abstract theorem: least closed superset ⇒ idempotent.
  ----------------------------------------------------------------

  record ClosureOp (K : Subset → Subset) : Type (ℓ-suc ℓ) where
    field
      ext   : (A : Subset) → A ⊑ K A                       -- extensive
      cl    : (A : Subset) → Closed (K A)                  -- closed-valued
      least : (A B : Subset) → Closed B → A ⊑ B → K A ⊑ B  -- least such
  open ClosureOp public

  module _ (K : Subset → Subset) (κ : ClosureOp K) where

    -- the ledger's §5.1 step, in two lines
    idem→ : (A : Subset) → K (K A) ⊑ K A
    idem→ A = least κ (K A) (K A) (cl κ A) (λ _ z → z)

    idem← : (A : Subset) → K A ⊑ K (K A)
    idem← A = ext κ (K A)

    -- the tower Θ_{ν+1} := κ(Θ_ν), at stages indexed by ℕ
    tower : Subset → ℕ → Subset
    tower A zero = A
    tower A (suc n) = K (tower A n)

    -- C.2  every stage from the first onwards equals the first
    collapse→ : (A : Subset) (n : ℕ) → tower A (suc n) ⊑ tower A 1
    collapse→ A zero = λ _ z → z
    collapse→ A (suc n) x z = collapse→ A n x (idem→ (tower A n) x z)

    collapse← : (A : Subset) (n : ℕ) → tower A 1 ⊑ tower A (suc n)
    collapse← A zero = λ _ z → z
    collapse← A (suc n) x z = idem← (tower A n) x (collapse← A n x z)

    -- C.3  hence Θ_∞ over the ω-stage is Θ_1: the union adds nothing.
    Union : Subset → Subset
    Union A = λ x → Σ ℕ (λ n → tower A (suc n) x)

    union-is-stage-one→ : (A : Subset) → Union A ⊑ tower A 1
    union-is-stage-one→ A x (n , z) = collapse→ A n x z

    union-is-stage-one← : (A : Subset) → tower A 1 ⊑ Union A
    union-is-stage-one← A x z = (0 , z)

  ----------------------------------------------------------------
  -- C.4  Non-vacuity: the inductively generated closure is such a K.
  --      (This is the same object as ⋂{closed supersets} whenever the
  --      latter denotes; that equivalence is classical and is not
  --      needed for the collapse, which only uses leastness.)
  ----------------------------------------------------------------

  data Gen (A : Subset) : S → Type ℓ where
    inc : {x : S} → A x → Gen A x
    g₁  : {a x : S} → U₁ a x → Gen A a → Gen A x
    g₂  : {a b x : S} → U₂ a b x → Gen A a → Gen A b → Gen A x

  genExt : (A : Subset) → A ⊑ Gen A
  genExt A _ = inc

  genClosed : (A : Subset) → Closed (Gen A)
  c₁ (genClosed A) = g₁
  c₂ (genClosed A) = g₂

  genLeast : (A B : Subset) → Closed B → A ⊑ B → Gen A ⊑ B
  genLeast A B cB h x (inc a) = h x a
  genLeast A B cB h x (g₁ r p) = c₁ cB r (genLeast A B cB h _ p)
  genLeast A B cB h x (g₂ r p q) =
    c₂ cB r (genLeast A B cB h _ p) (genLeast A B cB h _ q)

  GenIsClosureOp : ClosureOp Gen
  ext GenIsClosureOp = genExt
  cl GenIsClosureOp = genClosed
  least GenIsClosureOp = genLeast

  -- the collapse, instantiated: Θ_{n+1} = Θ_1 for every n, and the
  -- ω-union is Θ_1.
  gen-collapse→ : (A : Subset) (n : ℕ) → tower Gen GenIsClosureOp A (suc n) ⊑ tower Gen GenIsClosureOp A 1
  gen-collapse→ = collapse→ Gen GenIsClosureOp

  gen-collapse← : (A : Subset) (n : ℕ) → tower Gen GenIsClosureOp A 1 ⊑ tower Gen GenIsClosureOp A (suc n)
  gen-collapse← = collapse← Gen GenIsClosureOp
