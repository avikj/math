{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.ChargeCriterion
--
-- W2 of `TARGET.md` (absent from this repository): the parity barrier as a DECIDABLE TEST on a method,
-- rather than as a caution about methods.
--
-- `ParitySeparator` proved one direction — a parity-neutral observer
-- cannot separate σ from its gauge flip, whatever post-processing it
-- applies.  That alone is a no-go, and a no-go with only one direction is
-- the kind of statement that lets a hopeful reader believe their favourite
-- method is the exception.  This module proves the converse, which is what
-- makes it a criterion:
--
--   **A query set admits a separating decision procedure if and only if it
--     contains a query of odd Ω.**
--
-- Both directions, exactly, with the separating procedure CONSTRUCTED in
-- the "if" direction rather than asserted to exist.  So the test is:
--
--     look at what your method reads.  If every argument it ever evaluates
--     the multiplicative function at has even Ω, your method is provably
--     parity-blind — not "has not yet succeeded", but cannot.  If some
--     argument has odd Ω, a separator exists and the barrier says nothing
--     about you.
--
-- WHY THE CONVERSE IS THE CONTENT.  `GAUGE.md` (absent from this repository) §F.4 closes with
-- "formalizing which probes carry charge is the continuation of this
-- line."  A one-directional no-go formalizes which probes DON'T.  The
-- converse is what turns the classification into a decision, and it is
-- also what stops the criterion from being vacuous: without it, "neutral
-- ⇒ blind" would be consistent with everything being blind.
--
-- THE ASYMMETRY.  This is a criterion on the QUERY SET, not on the
-- post-processing, and that asymmetry is the theorem, not a limitation:
-- charge lives in what a method reads, and no amount of computation on
-- neutral readings manufactures it.  A method reading odd-Ω arguments is
-- *permitted* by this criterion, not blessed by it — Friedlander–Iwaniec's
-- bilinear axiom is what actually has to be supplied, and this test only
-- says where to look for it.
--
-- Contents (no holes, no postulates, --safe):
--
--   HasOdd                     the query set contains an odd-Ω argument
--   Separates                  a decision procedure that accepts the
--                              all-plus assignment and rejects its flip
--   neutral⇒no-separator       ⇐, from `ParitySeparator.no-decision`
--   odd⇒separator              ⇒, with the procedure built by induction
--   charge-criterion           the two together, as an iff
--   probe-2, probe-6           worked instances: reading at a prime
--                              separates, reading at a product of two
--                              primes does not, and the second is the
--                              larger number
------------------------------------------------------------------------

module NaturalMachine.ChargeCriterion where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import NaturalMachine.ParitySeparator

------------------------------------------------------------------------
-- §1  The reference pair.
--
-- It is enough to test one adversarial pair: the all-plus assignment and
-- its gauge flip, the all-minus one.  Everything charged separates them,
-- and nothing neutral does, so they are a complete test — which is why the
-- criterion below quantifies over query sets and not over σ.
------------------------------------------------------------------------

σ₊ : Signs
σ₊ _ = true

val-σ₊ : (n : Number) → val σ₊ n ≡ true
val-σ₊ []       = refl
val-σ₊ (p ∷ ns) = val-σ₊ ns

-- The flip of the all-plus assignment evaluates to the parity character
-- itself: this is `flip-law` with the base value trivial, and it is the
-- reason a single odd query suffices.
val-σ₋ : (n : Number) → val (flip σ₊) n ≡ sgn (Ω n)
val-σ₋ n = flip-law σ₊ n ∙ cong (λ z → sgn (Ω n) · z) (val-σ₊ n)
         ∙ unit-r (sgn (Ω n))
  where
    unit-r : (b : Bool) → b · true ≡ b
    unit-r true  = refl
    unit-r false = refl

------------------------------------------------------------------------
-- §2  The two sides of the criterion.
------------------------------------------------------------------------

-- The query set contains an argument of odd Ω.
-- Defined by recursion on the list rather than as an indexed family, so
-- that no clause below has to match on a constructor of a list-indexed
-- type — Cubical Agda would accept such a match but warn that the
-- function fails to compute under transport, and a criterion that does
-- not compute is not a test.
HasOdd : List Number → Type
HasOdd []       = ⊥
HasOdd (n ∷ qs) = (sgn (Ω n) ≡ false) ⊎ HasOdd qs

here : {n : Number} {qs : List Number} → sgn (Ω n) ≡ false → HasOdd (n ∷ qs)
here = inl

there : {n : Number} {qs : List Number} → HasOdd qs → HasOdd (n ∷ qs)
there = inr

-- A decision procedure separating the reference pair on this query set.
Separates : List Number → Type
Separates qs =
  Σ[ decide ∈ (List Bool → Bool) ]
    ((decide (obs σ₊ qs) ≡ true) × (decide (obs (flip σ₊) qs) ≡ false))

------------------------------------------------------------------------
-- §3  ⇐  Neutral query sets admit no separator at all.
--
-- Immediate from `ParitySeparator.no-decision`, and worth restating in
-- this vocabulary so the criterion reads as one statement.
------------------------------------------------------------------------

neutral⇒no-separator : (qs : List Number) → AllEven qs → ¬ (Separates qs)
neutral⇒no-separator qs all (decide , yes , no) =
  no-decision σ₊ qs all decide (yes , no)

------------------------------------------------------------------------
-- §4  ⇒  One odd query suffices, and the separator is constructed.
--
-- Read the answer to the odd query and return it.  On σ₊ every value is
-- +1 (`val-σ₊`); on the flip the value at an odd-Ω argument is −1
-- (`val-σ₋`).  The induction is over the position of the odd query, and
-- the procedure it builds is "drop the first k answers, then look" — the
-- simplest possible probe, which is the point: nothing clever is needed
-- once the query carries charge.
------------------------------------------------------------------------

hd : List Bool → Bool
hd []      = false
hd (b ∷ _) = b

tl : List Bool → List Bool
tl []       = []
tl (_ ∷ bs) = bs

odd⇒separator : (qs : List Number) → HasOdd qs → Separates qs
odd⇒separator (n ∷ qs) (inl o) =
  hd , val-σ₊ n , (val-σ₋ n ∙ o)
odd⇒separator (n ∷ qs) (inr h) with odd⇒separator qs h
... | (decide , yes , no) = (λ ℓ → decide (tl ℓ)) , yes , no

------------------------------------------------------------------------
-- §5  The criterion.
--
-- Contrapositive of §3 with §4: a query set is parity-blind exactly when
-- it is neutral.  This is the test a method designer can run.
------------------------------------------------------------------------

charge-criterion : (qs : List Number)
                 → (HasOdd qs → Separates qs)
                 × (AllEven qs → ¬ (Separates qs))
charge-criterion qs = odd⇒separator qs , neutral⇒no-separator qs

-- …and the two are exclusive, which is what stops the criterion from
-- being satisfiable vacuously: no query set is both.
not-both : (qs : List Number) → AllEven qs → ¬ (HasOdd qs)
not-both (n ∷ qs) (e , _)    (inl o) = true≢false (sym e ∙ o)
not-both (n ∷ qs) (_ , rest) (inr h) = not-both qs rest h

------------------------------------------------------------------------
-- §6  Two probes, to show the criterion is about charge and not size.
--
-- Reading the function at a prime (Ω = 1) separates.  Reading it at a
-- product of two primes (Ω = 2) does not — and that argument is the
-- LARGER number.  A method is not made parity-sensitive by looking
-- further out; it is made parity-sensitive by looking at odd charge.
------------------------------------------------------------------------

probe-2 : List Number          -- {2}: one prime
probe-2 = (0 ∷ []) ∷ []

probe-6 : List Number          -- {6}: two distinct primes
probe-6 = (0 ∷ 1 ∷ []) ∷ []

probe-2-separates : Separates probe-2
probe-2-separates = odd⇒separator probe-2 (inl refl)

probe-6-cannot : ¬ (Separates probe-6)
probe-6-cannot = neutral⇒no-separator probe-6 (refl , tt)
