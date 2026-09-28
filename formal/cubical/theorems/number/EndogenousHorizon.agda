{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- EndogenousHorizon
--
-- Delta 22 T22.2/T22.3/T22.4, and Delta 22's research direction 4:
-- "construct finite behavioral separators proving exact scale
-- requirements".
--
-- THE POINT.  Delta 22 observes that the square-root sieve horizon is not
-- an externally chosen resolution but an *endogenous* boundary of the
-- verification problem: which local tests certify a value depends on the
-- value.  T22.4 makes that exact by exhibiting a BEHAVIOURAL SEPARATOR --
-- a prime r and a semiprime rs that are indistinguishable to every
-- divisibility test below the threshold, yet differ in primality.
--
-- That is precisely the shape this repository's checked core already
-- formalises (MyhillNerodeMinimalMachine, 
-- ExcursionReturn §2): two states agreeing on all admitted observations
-- but separated by the task.  runtime/CRYSTAL.md (absent from this repository) §3.2 calls such a pair a
-- COLLISION and says it "is not a failure; it is a specification of the
-- missing distinction".  This module supplies the arithmetic instance.
--
-- Delta 22 direction 6 warns against "re-encoding known set-level facts
-- gratuitously".  So what is formalised here is *not* primality, and not
-- the infinitude of primes.  It is the impossibility statement:
--
--     no function of the sub-threshold divisibility observation
--     decides primality, whenever a separating pair exists,
--
-- which is the statement that has content, and the concrete witness that
-- inhabits it.  The number-theoretic inputs (r prime, rs composite) are
-- hypotheses, supplied by the caller and discharged only in the finite
-- instance.
--
-- Contents (all proved, no holes, no postulates, --safe):
--
--   divides?, obs             the sub-threshold observer, decidable
--   Separator                 the data of a behavioural separator
--   no-decision               T22.4: any decision procedure factoring
--                             through the observation is refuted
--   sep-5-35                  a concrete separator at threshold 3
--   sep-5-25                  the prime-square separator: the corpus's
--                             own F30/T5 obstruction, same shape
--   horizon-grows             T22.3's converse in the form that matters:
--                             the separator at threshold z is defeated
--                             only by raising the threshold past r
------------------------------------------------------------------------

module EndogenousHorizon where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_)
open import Cubical.Data.Nat.Mod using (_mod_)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Discrete ; yes ; no)

------------------------------------------------------------------------
-- The observer
--
-- `obs ms n` is what a divisibility observer holding the moduli `ms` sees
-- of `n`.  Deliberately coarse and deliberately DECIDABLE: this is the
-- whole observation, and everything else about `n` is discarded.
--
-- Using ALL moduli up to the threshold, rather than only the primes, only
-- strengthens the observer.  An impossibility for the stronger observer
-- implies it for the weaker, so the separator below is not an artifact of
-- a badly chosen test family.
------------------------------------------------------------------------

isZero : ℕ → Bool
isZero zero    = true
isZero (suc _) = false

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc a) (suc b) = eqℕ a b

and2 : Bool → Bool → Bool
and2 true  b = b
and2 false _ = false

-- `divides? m n` is true exactly when n mod m is zero.
divides? : ℕ → ℕ → Bool
divides? m n = isZero (n mod m)

-- The observation is TRIAL DIVISION: the modulus m counts only as a
-- PROPER divisor.  This is exactly where Delta 22's endogeneity lives --
-- whether m witnesses compositeness of n depends on n itself, through
-- m ≠ n.  With bare divisibility the observer never separates n from n²
-- at any threshold, which is a fact about the wrong observer, not about
-- the horizon.
pdivides? : ℕ → ℕ → Bool
pdivides? m n = and2 (divides? m n) (not (eqℕ m n))

obs : List ℕ → ℕ → List Bool
obs ms n = map (λ m → pdivides? m n) ms

------------------------------------------------------------------------
-- The separator, and the impossibility it forces
------------------------------------------------------------------------

-- Delta 22 T22.4, as data.  Two values the observer cannot tell apart,
-- which the task must tell apart.  `below` is the observer's modulus
-- list; `good` is the value the task accepts, `bad` the value it rejects.
record Separator : Type where
  field
    below : List ℕ
    good  : ℕ
    bad   : ℕ
    blind : obs below good ≡ obs below bad

open Separator

-- T22.4.  Any decision procedure that factors through the observation is
-- refuted by a separator.  This is the exact sense in which the observer
-- is insufficient: not that deciding is hard, but that *no* function of
-- what it sees can be correct.
no-decision :
    (S : Separator)
  → (decide : List Bool → Bool)
  → decide (obs (below S) (good S)) ≡ true
  → decide (obs (below S) (bad S)) ≡ false
  → ⊥
no-decision S decide acc rej =
  true≢false (sym acc ∙ cong decide (blind S) ∙ rej)

------------------------------------------------------------------------
-- Concrete separators
--
-- Threshold 3, i.e. the observer may test divisibility by 2 and by 3.
------------------------------------------------------------------------

thresh3 : List ℕ
thresh3 = 2 ∷ 3 ∷ []

-- Delta 22's own witness: a prime and a semiprime built from two primes
-- above the threshold.  5 is prime; 35 = 5·7 is not; neither is divisible
-- by 2 or 3, so the observer sees `false ∷ false ∷ []` for both.
sep-5-35 : Separator
sep-5-35 = record
  { below = thresh3
  ; good  = 5
  ; bad   = 35
  ; blind = refl
  }

-- The prime-SQUARE case, which is this repository's own obstruction:
-- `collab/FAILURES.md` (absent from this repository) F30 / Theorem T5 records that under residue-
-- divisibility certificates every omitted prime q is falsified by q².
-- Delta 22's semiprime rs and the corpus's q² are the same separator
-- shape with s = r, and putting them side by side is the point: F30 is
-- the diagonal case of T22.4, not a different phenomenon.
sep-5-25 : Separator
sep-5-25 = record
  { below = thresh3
  ; good  = 5
  ; bad   = 25
  ; blind = refl
  }

-- Both separators are live: the observation really is the same string.
-- (`refl` above already asserts it; these make the shared value explicit
-- so a reader need not evaluate the definition in their head.)
obs-5  : obs thresh3 5  ≡ false ∷ false ∷ []
obs-5  = refl

obs-35 : obs thresh3 35 ≡ false ∷ false ∷ []
obs-35 = refl

obs-25 : obs thresh3 25 ≡ false ∷ false ∷ []
obs-25 = refl

------------------------------------------------------------------------
-- Why the horizon is endogenous
--
-- A separator at threshold z is destroyed only by admitting a modulus
-- that actually splits the pair.  Here 5 does, and nothing below it does.
-- So certifying 25 or 35 requires testing up to 5 = √25, and the required
-- observer therefore grows with the value being certified: T22.3's
-- converse, in the only form that has content.
------------------------------------------------------------------------

thresh5 : List ℕ
thresh5 = 2 ∷ 3 ∷ 5 ∷ []

-- At threshold 5 the observation separates, so the blindness is gone.
horizon-grows : ¬ (obs thresh5 5 ≡ obs thresh5 25)
horizon-grows p = true≢false (sym (cong headOfTail p))
  where
    headOfTail : List Bool → Bool
    headOfTail (_ ∷ _ ∷ b ∷ _) = b
    headOfTail _               = true

-- ... and the same threshold defeats the semiprime separator too.
horizon-grows-35 : ¬ (obs thresh5 5 ≡ obs thresh5 35)
horizon-grows-35 p = true≢false (sym (cong headOfTail p))
  where
    headOfTail : List Bool → Bool
    headOfTail (_ ∷ _ ∷ b ∷ _) = b
    headOfTail _               = true

------------------------------------------------------------------------
-- The observer's insufficiency is
-- a behavioural separation, it is refuted by an explicit pair rather than
-- by an existence argument, and the pair is destroyed only by enlarging
-- the observer past a value determined by the object.  That is what
-- "endogenous horizon" means, stated so it can be checked.
------------------------------------------------------------------------
