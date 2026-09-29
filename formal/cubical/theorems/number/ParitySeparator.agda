{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ParitySeparator
--
-- The sieve parity barrier, as a behavioural separator — elementary,
-- finite, and with no operator algebra in it.
--
-- WHERE THIS COMES FROM.  `notes/GAUGE.md` (absent from this repository) Theorem F proves that the
-- unique KMS state of the critical affine system annihilates every
-- gauge-charged observable, so "sieves cannot see parity" is an exact
-- invariance rather than a want of technique.  That proof is three lines
-- ON TOP OF Cuntz's uniqueness theorem, which is deep, and the note says
-- so: "the proof is short because Cuntz's uniqueness theorem is deep".
--
-- WHAT THIS MODULE ADDS.  The arithmetic core of that no-go needs none of
-- it.  Strip the C*-algebra and what is left is a statement about two
-- completely multiplicative ±1 functions that no neutral observation can
-- tell apart — a COLLISION, in the sense `runtime/CRYSTAL.md` (absent from this repository) §3.2 gives
-- the word: "not a failure; it is a specification of the missing
-- distinction."  `EndogenousHorizon` already carries that
-- shape for trial division (Delta 22 T22.4).  This module carries it for
-- parity, which is the one that blocks Goldbach and twin primes.
--
-- THE STATEMENT.  A completely multiplicative ±1 function is exactly a
-- sign assignment σ on the primes; a number is its multiset of prime
-- factors, so Ω(n) is a length.  Let σ' be σ with EVERY prime sign
-- flipped.  Then
--
--     val σ' n  =  (-1)^{Ω(n)} · val σ n,
--
-- so σ and σ' agree at every n of even Ω and differ at every n of odd Ω.
-- An observer restricted to even-Ω arguments — the neutral sector, which
-- is where Theorem F says the equilibrium lives — therefore returns
-- literally the same data on both, and no post-processing whatsoever can
-- separate them.  That is `no-decision` below, and its proof is `cong`:
-- the two observation vectors are not merely close, they are equal.
--
-- WHY THE FLIP IS THE RIGHT ADVERSARY.  σ ↦ σ' is the gauge action of
-- the element (-1,-1,-1,…) of GAUGE.md (absent from this repository) §F.1's torus — the single group
-- element whose character is exactly the parity grading.  So this is
-- Theorem F's mechanism, at the one point of the torus that matters,
-- with the equilibrium argument replaced by an equality of finite lists.
--
-- Contents (no holes, no postulates, --safe):
--
--   Signs, val                 completely multiplicative ±1 functions,
--                              as sign assignments evaluated on factor
--                              multisets
--   flip                       the parity gauge element
--   flip-law                   val σ' n = (-1)^{Ω(n)} · val σ n
--   neutral-blind              even Ω ⇒ the two agree
--   charged-separates          odd Ω ⇒ the two differ, everywhere
--   obs, obs-agree             an observer's whole transcript on even-Ω
--                              queries is EQUAL for σ and σ'
--   no-decision                hence no decision procedure on that
--                              transcript can separate them
--   the-missing-distinction    …and one odd-Ω query does separate them,
--                              so the collision specifies its own repair
--
------------------------------------------------------------------------

module ParitySeparator where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length ; map)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- §1  The group of signs.
--
-- {±1} is Bool with `true` = +1, and multiplication is `·`.  Everything
-- below is abelian-group bookkeeping in ℤ/2; the four-case proofs are
-- written out because they are the whole computation.
------------------------------------------------------------------------

infixl 6 _·_

_·_ : Bool → Bool → Bool
true  · b = b
false · b = not b

·-unit : (b : Bool) → true · b ≡ b
·-unit b = refl

·-comm : (a b : Bool) → a · b ≡ b · a
·-comm true  true  = refl
·-comm true  false = refl
·-comm false true  = refl
·-comm false false = refl

·-assoc : (a b c : Bool) → (a · b) · c ≡ a · (b · c)
·-assoc true  b c = refl
·-assoc false true  c = refl
·-assoc false false true  = refl
·-assoc false false false = refl

-- (-1)^n, i.e. the parity character of ℕ.  `true` at even n.
sgn : ℕ → Bool
sgn zero    = true
sgn (suc n) = not (sgn n)

-- multiplying by −1 is `not`, which is the fact the induction needs.
neg : (b : Bool) → false · b ≡ not b
neg b = refl

------------------------------------------------------------------------
-- §2  Completely multiplicative ±1 functions.
--
-- A number is presented by its multiset of prime factors — a list of
-- prime indices — so Ω(n) is `length` and complete multiplicativity is
-- the fold.  This is not a modelling convenience: the barrier is about
-- the FACTORIZATION monoid, and the free commutative monoid on the
-- primes is what that monoid is.
------------------------------------------------------------------------

Signs : Type
Signs = ℕ → Bool

Number : Type
Number = List ℕ           -- the multiset of prime indices; Ω = length

Ω : Number → ℕ
Ω = length

val : Signs → Number → Bool
val σ []       = true
val σ (p ∷ ns) = σ p · val σ ns

-- The parity gauge element: flip the sign at every prime at once.
flip : Signs → Signs
flip σ p = not (σ p)

------------------------------------------------------------------------
-- §3  The flip law, and the two consequences.
------------------------------------------------------------------------

not-· : (a b : Bool) → (not a) · b ≡ false · (a · b)
not-· true  b = refl
not-· false true  = refl
not-· false false = refl

flip-law : (σ : Signs) (n : Number) → val (flip σ) n ≡ sgn (Ω n) · val σ n
flip-law σ []       = refl
flip-law σ (p ∷ ns) =
    cong (λ z → (not (σ p)) · z) (flip-law σ ns)
  ∙ not-· (σ p) (sgn (Ω ns) · val σ ns)
  ∙ cong (λ z → false · z) (sym (·-assoc (σ p) (sgn (Ω ns)) (val σ ns))
                           ∙ cong (λ z → z · val σ ns) (·-comm (σ p) (sgn (Ω ns)))
                           ∙ ·-assoc (sgn (Ω ns)) (σ p) (val σ ns))
  ∙ sym (·-assoc false (sgn (Ω ns)) (σ p · val σ ns))

-- Even Ω: the flip is invisible.  This is the neutral sector.
neutral-blind : (σ : Signs) (n : Number) → sgn (Ω n) ≡ true
              → val (flip σ) n ≡ val σ n
neutral-blind σ n e = flip-law σ n ∙ cong (λ z → z · val σ n) e

-- Odd Ω: the flip is visible, at EVERY such argument — not just at one.
charged-separates : (σ : Signs) (n : Number) → sgn (Ω n) ≡ false
                  → val (flip σ) n ≡ not (val σ n)
charged-separates σ n o = flip-law σ n ∙ cong (λ z → z · val σ n) o

------------------------------------------------------------------------
-- §4  The collision: an observer's entire transcript is EQUAL.
--
-- An observation is a finite list of queries.  If every query has even Ω,
-- the transcripts of σ and of flip σ are not approximately equal, not
-- equal to within an error term — they are the same list.  Hence no
-- decision procedure on transcripts, however powerful, separates them:
-- the proof is `cong`, because there is nothing to separate.
--
-- This is the exact analogue of `EndogenousHorizon.no-decision`, and it
-- is deliberately stated the same way so the two read as one phenomenon.
------------------------------------------------------------------------

obs : Signs → List Number → List Bool
obs σ qs = map (val σ) qs

-- "every query is parity-neutral", as a list predicate carried by hand so
-- the module needs no extra imports.
AllEven : List Number → Type
AllEven []       = Unit
AllEven (n ∷ qs) = (sgn (Ω n) ≡ true) × AllEven qs

obs-agree : (σ : Signs) (qs : List Number) → AllEven qs
          → obs σ qs ≡ obs (flip σ) qs
obs-agree σ []       tt        = refl
obs-agree σ (n ∷ qs) (e , rest) =
  cong₂ _∷_ (sym (neutral-blind σ n e)) (obs-agree σ qs rest)

-- No decision procedure on a parity-neutral transcript can tell the two
-- sign assignments apart, whatever it is allowed to compute.
no-decision : (σ : Signs) (qs : List Number) → AllEven qs
            → (decide : List Bool → Bool)
            → ¬ ((decide (obs σ qs) ≡ true) × (decide (obs (flip σ) qs) ≡ false))
no-decision σ qs all decide (yes , no) =
  true≢false (sym yes ∙ cong decide (obs-agree σ qs all) ∙ no)

------------------------------------------------------------------------
-- §5  The collision specifies its repair.
--
-- CRYSTAL.md (absent from this repository) §3.2: a collision is a specification of the missing
-- distinction.  Here the missing distinction is exhibited — a single
-- odd-Ω query separates, for every σ.  So the barrier is not "nothing
-- works"; it is "exactly the charged queries work", which is the form
-- that tells a method designer what to go and get.
------------------------------------------------------------------------

one-prime : Number
one-prime = 0 ∷ []

one-prime-is-odd : sgn (Ω one-prime) ≡ false
one-prime-is-odd = refl

the-missing-distinction : (σ : Signs)
                        → val (flip σ) one-prime ≡ not (val σ one-prime)
the-missing-distinction σ = charged-separates σ one-prime one-prime-is-odd

-- …and a two-prime query does not, which is what makes the previous line
-- informative rather than trivial: the separating power is a function of
-- the CHARGE of the query, not of its size.
two-primes : Number
two-primes = 0 ∷ 0 ∷ []

two-primes-blind : (σ : Signs) → val (flip σ) two-primes ≡ val σ two-primes
two-primes-blind σ = neutral-blind σ two-primes refl
