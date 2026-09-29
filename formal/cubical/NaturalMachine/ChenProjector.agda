{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.ChenProjector
--
-- Factory IV's Theorem 58 and the saturation dichotomy, in the
-- ParitySeparator vocabulary — and their composition with the checked
-- parity barrier, which is the part that is new to the corpus.
--
-- WHERE THIS COMES FROM.  The owner's delta
-- `collab/upstream/library/raw/ETERNAL_GOLDEN_BRAID_THEOREM_FACTORY_IV_2026-08-14.md` (absent from this repository)
-- grades the prime-pair field by factorization charge and observes that on
-- the Chen envelope — second leg of charge Ω ∈ {1,2}, the sieve-inhabited
-- field — the Liouville sign (1−λ)/2 is EXACTLY the charge-one projector:
-- parity, which forgets almost everything on unrestricted integers, is
-- informationally complete once the charge support has two points.
--
-- WHAT THIS MODULE PROVES (no holes, no postulates, --safe):
--
--   Envelope                the charge support {1,2}, as a sum type
--   projector               (1−λ)/2, i.e. `not (sgn (Ω n))`
--   theorem-58              on the envelope, projector ≡ true ⟺ Ω ≡ 1,
--                           both directions (`projector-sound`,
--                           `projector-complete`), with `projector-null`
--                           the charge-two evaluation and
--                           `charges-exclusive` ruling out overlap
--   count-split             oddCount + evenCount ≡ length — the exact
--                           content of Factory IV's G = (C−L)/2 in
--                           two-counter form: C = O+E and L = E−O are
--                           bookkeeping on top of this identity, and the
--                           subtraction-free form is the one that lives
--                           in ℕ
--   saturated→allEven       charge saturation (oddCount ≡ 0) makes the
--                           witness list parity-neutral in exactly
--                           ParitySeparator's sense
--   saturation-blinds       …hence, by `obs-agree`, a saturated witness
--                           list produces IDENTICAL transcripts on σ and
--                           flip σ
--   saturation-no-decision  …hence, by `no-decision`, no post-processing
--                           of a saturated transcript separates them
--   twin-witness-separates  the constructive converse: one odd-charge
--                           witness yields a separating query
--
-- THE COMPOSITION, IN ONE SENTENCE.  In a twin-free world the radius-one
-- Chen witnesses are charge-saturated, so the very transcript witnessing
-- Chen's theorem is a parity-neutral query set, and the checked barrier
-- (`ParitySeparator.no-decision`) applies to it verbatim: the data cannot
-- separate the world from its gauge flip.  Factory IV's "asymptotic
-- even-charge saturation" and this corpus's parity collision are one
-- statement, and this module is the identification.
------------------------------------------------------------------------

module NaturalMachine.ChenProjector where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-suc ; snotz ; injSuc ; znots)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import ParitySeparator

------------------------------------------------------------------------
-- §1  The Chen envelope.
--
-- A query lies on the envelope when its charge is one or two.  This is
-- the charge support that Chen's theorem inhabits; here it is carried as
-- a hypothesis.  Defined as a sum rather than an indexed family so that
-- everything below computes (the `ChargeCriterion` precedent: a
-- criterion that does not compute is not a test).
------------------------------------------------------------------------

Envelope : Number → Type
Envelope n = (Ω n ≡ 1) ⊎ (Ω n ≡ 2)

------------------------------------------------------------------------
-- §2  Theorem 58: the projector (1−λ)/2, and its exactness on the
-- envelope.
--
-- `sgn (Ω n)` is λ(n) with true = +1, so `not (sgn (Ω n))` is the
-- Boolean (1−λ(n))/2.  On unrestricted numbers it detects odd charge —
-- any odd charge.  Theorem 58 is the statement that on the envelope it
-- detects charge EXACTLY one, because {1,2} → {−1,+1} is a bijection.
------------------------------------------------------------------------

projector : Number → Bool
projector n = not (sgn (Ω n))

-- charge one evaluates to true: (1−λ(prime))/2 = 1.
projector-complete : (n : Number) → Ω n ≡ 1 → projector n ≡ true
projector-complete n e = cong (λ k → not (sgn k)) e

-- charge two evaluates to false: (1−λ(semiprime))/2 = 0.
projector-null : (n : Number) → Ω n ≡ 2 → projector n ≡ false
projector-null n e = cong (λ k → not (sgn k)) e

-- on the envelope the projector is not merely sufficient but sound:
-- a true reading forces charge one, because the only other admissible
-- charge evaluates to false.
projector-sound : (n : Number) → Envelope n → projector n ≡ true → Ω n ≡ 1
projector-sound n (inl e) _ = e
projector-sound n (inr e) h =
  Empty.rec (true≢false (sym h ∙ projector-null n e))

-- the two charges of the envelope are exclusive, so the criterion is
-- not satisfiable vacuously (the `ChargeCriterion.not-both` discipline).
charges-exclusive : (n : Number) → Ω n ≡ 1 → Ω n ≡ 2 → ⊥
charges-exclusive n e₁ e₂ = znots (injSuc (sym e₁ ∙ e₂))

-- Theorem 58, assembled: on the envelope, projector ≡ true ⟺ charge 1.
theorem-58 : (n : Number) → Envelope n
           → (projector n ≡ true → Ω n ≡ 1) × (Ω n ≡ 1 → projector n ≡ true)
theorem-58 n env = projector-sound n env , projector-complete n

------------------------------------------------------------------------
-- §3  The counting identity, subtraction-free.
--
-- Factory IV §IV writes G = (C − L)/2 and T = (C_T − L_T)/2.  With
-- O = #odd-charge witnesses and E = #even-charge witnesses these are
-- C = O + E, L = E − O, C − L = 2O: the signed identities are ℤ-side
-- bookkeeping on ONE ℕ-side fact, which is the one proved here.
------------------------------------------------------------------------

bit : Bool → ℕ
bit true  = 1
bit false = 0

oddCount : List Number → ℕ
oddCount []       = 0
oddCount (n ∷ qs) = bit (projector n) + oddCount qs

evenCount : List Number → ℕ
evenCount []       = 0
evenCount (n ∷ qs) = bit (not (projector n)) + evenCount qs

private
  split-step : (b : Bool) (o e : ℕ)
             → (bit b + o) + (bit (not b) + e) ≡ suc (o + e)
  split-step true  o e = refl
  split-step false o e = +-suc o e

count-split : (qs : List Number) → oddCount qs + evenCount qs ≡ length qs
count-split []       = refl
count-split (n ∷ qs) =
  split-step (projector n) (oddCount qs) (evenCount qs)
  ∙ cong suc (count-split qs)

------------------------------------------------------------------------
-- §4  Saturation, and the identification with the checked barrier.
--
-- Factory IV: a twin-free world is forced into even-charge saturation
-- of the radius-one Chen field.  Here: saturation IS parity-neutrality
-- of the witness list, so the collision of `ParitySeparator` applies to
-- the Chen transcript itself.  The two documents' obstructions are one.
------------------------------------------------------------------------

Saturated : List Number → Type
Saturated qs = oddCount qs ≡ 0

private
  bit-zero : (b : Bool) (m : ℕ) → bit b + m ≡ 0 → (b ≡ false) × (m ≡ 0)
  bit-zero true  m h = Empty.rec (snotz h)
  bit-zero false m h = refl , h

  not-false : (b : Bool) → not b ≡ false → b ≡ true
  not-false true  _ = refl
  not-false false p = Empty.rec (true≢false p)

  not-true : (b : Bool) → not b ≡ true → b ≡ false
  not-true false _ = refl
  not-true true  p = Empty.rec (true≢false (sym p))

saturated→allEven : (qs : List Number) → Saturated qs → AllEven qs
saturated→allEven []       _ = tt
saturated→allEven (n ∷ qs) h =
  let z = bit-zero (projector n) (oddCount qs) h
  in  not-false (sgn (Ω n)) (fst z) , saturated→allEven qs (snd z)

-- A saturated witness list yields literally the same transcript on a
-- sign assignment and on its gauge flip.
saturation-blinds : (σ : Signs) (qs : List Number) → Saturated qs
                  → obs σ qs ≡ obs (flip σ) qs
saturation-blinds σ qs h = obs-agree σ qs (saturated→allEven qs h)

-- …so no decision procedure on that transcript separates the two.
saturation-no-decision : (σ : Signs) (qs : List Number) → Saturated qs
  → (decide : List Bool → Bool)
  → ¬ ((decide (obs σ qs) ≡ true) × (decide (obs (flip σ) qs) ≡ false))
saturation-no-decision σ qs h = no-decision σ qs (saturated→allEven qs h)

-- The constructive converse: one odd-charge witness — one twin, in the
-- radius-one reading — yields a query that separates σ from flip σ.
-- Anti-saturation is not merely compatible with breaking the blindness;
-- each witness breaks it individually.
twin-witness-separates : (σ : Signs) (n : Number) → projector n ≡ true
                       → val (flip σ) n ≡ not (val σ n)
twin-witness-separates σ n h =
  charged-separates σ n (not-true (sgn (Ω n)) h)

------------------------------------------------------------------------
-- §5  Worked instances: the two points of the envelope.
--
-- A prime (charge one) and a semiprime (charge two), with the projector
-- evaluated by the kernel.  The semiprime is the LARGER multiset — the
-- `ChargeCriterion.probe-6` lesson again: what matters is charge, never
-- size.
------------------------------------------------------------------------

prime-leg : Number
prime-leg = 0 ∷ []

semiprime-leg : Number
semiprime-leg = 0 ∷ 1 ∷ []

prime-on-envelope : Envelope prime-leg
prime-on-envelope = inl refl

semiprime-on-envelope : Envelope semiprime-leg
semiprime-on-envelope = inr refl

projector-prime : projector prime-leg ≡ true
projector-prime = refl

projector-semiprime : projector semiprime-leg ≡ false
projector-semiprime = refl

-- and the smallest saturated list is blind, by evaluation:
-- a transcript of semiprime witnesses alone separates nothing.
smallest-saturation : Saturated (semiprime-leg ∷ [])
smallest-saturation = refl
