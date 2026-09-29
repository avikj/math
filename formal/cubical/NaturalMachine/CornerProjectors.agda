{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.CornerProjectors
--
-- Factory IV §XI — "the projectors commute; the information does not" —
-- at the type level.
--
-- WHERE THIS COMES FROM.  The owner's delta
-- `collab/upstream/library/raw/ETERNAL_GOLDEN_BRAID_THEOREM_FACTORY_IV_2026-08-14.md` (absent from this repository)
-- §XI observes that the two extractions defining the hard corner of the
-- prime-pair field — P_r (radius one) and P_c (factorization charge one)
-- — commute as operators, P_r P_c = P_c P_r, so the twin corner is NOT
-- an operator-noncommutation obstruction.  And yet the two known
-- recurrence statements (charge-one mass summed over radii ≤ 123 is
-- infinite — Maynard's side; radius-one mass at charge ≤ 2 is infinite —
-- Chen's side) do not imply recurrence of the JOINT corner P_r P_c 𝒞,
-- because "a nonnegative field may place all exact-prime mass at radius
-- two and all radius-one mass at charge two."  The true problem is a
-- marginal-to-joint lower-bound problem.  Factory I sibling
-- (`UNIVALENT_PERSPECTIVAL_THEOREM_FACTORY_DELTA_14_2026-08-13.md` (absent from this repository) §A,
-- T14.6/C14.7) carries the same shape one level up: an ambient
-- equivalence restricts to a sector precisely when the sector predicate
-- is invariant — selection, not conjugation, is where information dies.
--
-- THE NOETHER READING.  Boolean predicates on witnesses act on witness
-- lists by filtering, and pointwise predicates generate a COMMUTATIVE
-- monoid of such actions: composition of filters is filtering by the
-- pointwise conjunction (`filter-and`, an action identity), and the
-- conjunction is commutative, so the actions commute (`filters-commute`
-- — the general lemma, then `projectors-commute`, its instance at
-- radius/charge).  The invariant that the group-theoretic bookkeeping
-- does NOT control is the joint mass: knowing the orbit of each
-- projector separately (both marginals inhabited) fixes nothing about
-- their meet.  That failure is not argued but CONSTRUCTED: a two-witness
-- world, Factory IV's own, where each marginal filter returns a
-- nonempty list and both orders of the joint filter return [].
--
-- WHAT THIS MODULE PROVES (no holes, no postulates, --safe):
--
--   Witness                a radius r : ℕ together with a leg
--                          n : Number (ParitySeparator's factor
--                          multiset; Ω = length)
--   radiusOne, chargeOne   the two Boolean projectors: r ≡ᵇ 1 (by a
--                          recursive decidable equality defined here)
--                          and ChenProjector's (1−λ)/2
--   filter-and             filtering twice is filtering by the
--                          pointwise conjunction
--   filters-commute        hence ANY two pointwise filters commute —
--                          Boolean and-commutativity lifted to lists
--   projectors-commute     Factory IV §XI's boxed identity
--                          P_r P_c = P_c P_r, as the instance
--                          filterR (filterC ws) ≡ filterC (filterR ws)
--   theWorld               the counterexample field: one prime leg at
--                          radius 2, one charge-two leg at radius 1
--   charge-marginal,       both marginals evaluate, by refl, to
--   radius-marginal        nonempty lists (and are proved ≢ [])
--   corner-empty,          both orders of the joint filter evaluate,
--   corner-empty'          by refl, to []
--   marginal-to-joint-gap  the three facts bundled: this is the gap
--                          made checkable — commutation holds, and the
--                          marginals still say nothing about the joint
------------------------------------------------------------------------

module NaturalMachine.CornerProjectors where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz)
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Relation.Nullary using (¬_)

open import ParitySeparator using (Number ; Ω ; sgn)
open import NaturalMachine.ChenProjector
  using (projector ; prime-leg ; semiprime-leg)

------------------------------------------------------------------------
-- §1  Witnesses.
--
-- A witness carries the two graded coordinates §XI projects on: the
-- radius (distance of the pair's center from the nearest admissible
-- shift; here just a natural number, since only the fiber r ≡ 1 is
-- interrogated) and the second leg, as ParitySeparator's factor
-- multiset, so that charge is Ω = length and the Chen projector
-- applies verbatim.
------------------------------------------------------------------------

record Witness : Type where
  constructor witness
  field
    radius : ℕ
    leg    : Number

open Witness

------------------------------------------------------------------------
-- §2  The two projectors.
--
-- Radius one is tested by a decidable equality on ℕ, defined by
-- recursion so it computes; charge one is ChenProjector's (1−λ)/2,
-- reused rather than redefined — on the envelope it is EXACTLY the
-- charge-one indicator (ChenProjector.theorem-58), and here it is
-- evaluated only at envelope points.
------------------------------------------------------------------------

_≡ᵇ_ : ℕ → ℕ → Bool
zero  ≡ᵇ zero  = true
zero  ≡ᵇ suc _ = false
suc _ ≡ᵇ zero  = false
suc m ≡ᵇ suc n = m ≡ᵇ n

radiusOne : Witness → Bool
radiusOne w = radius w ≡ᵇ 1

chargeOne : Witness → Bool
chargeOne w = projector (leg w)

------------------------------------------------------------------------
-- §3  Pointwise filters, and that they commute.
--
-- The general lemma first, in two steps that are each one Boolean case
-- split: composing filters is filtering by the pointwise conjunction,
-- and the conjunction commutes.  This is the entire content of §XI's
-- boxed P_r P_c = P_c P_r: projector commutation is and-commutativity
-- worn as an operator identity, which is WHY it cannot be where the
-- difficulty lives.
------------------------------------------------------------------------

-- keep-or-drop, with the Boolean exposed so lemmas can split on it.
consIf : {A : Type} → Bool → A → List A → List A
consIf true  x xs = x ∷ xs
consIf false x xs = xs

filterBy : {A : Type} → (A → Bool) → List A → List A
filterBy f []       = []
filterBy f (x ∷ xs) = consIf (f x) x (filterBy f xs)

private
  and-comm : (a b : Bool) → a and b ≡ b and a
  and-comm true  true  = refl
  and-comm true  false = refl
  and-comm false true  = refl
  and-comm false false = refl

  filter-consIf : {A : Type} (f : A → Bool) (b : Bool) (x : A) (ys : List A)
                → filterBy f (consIf b x ys) ≡ consIf (b and f x) x (filterBy f ys)
  filter-consIf f true  x ys = refl
  filter-consIf f false x ys = refl

-- Composing two pointwise filters is filtering by the conjunction.
filter-and : {A : Type} (f g : A → Bool) (xs : List A)
           → filterBy f (filterBy g xs) ≡ filterBy (λ a → g a and f a) xs
filter-and f g []       = refl
filter-and f g (x ∷ xs) =
    filter-consIf f (g x) x (filterBy g xs)
  ∙ cong (consIf (g x and f x) x) (filter-and f g xs)

-- Hence any two pointwise filters commute: lift and-comm along
-- filter-and on both sides.
filters-commute : {A : Type} (f g : A → Bool) (xs : List A)
                → filterBy f (filterBy g xs) ≡ filterBy g (filterBy f xs)
filters-commute f g xs =
    filter-and f g xs
  ∙ cong (λ h → filterBy h xs) (funExt (λ a → and-comm (g a) (f a)))
  ∙ sym (filter-and g f xs)

------------------------------------------------------------------------
-- §4  The instance: P_r P_c = P_c P_r on witness fields.
------------------------------------------------------------------------

filterR filterC : List Witness → List Witness
filterR = filterBy radiusOne
filterC = filterBy chargeOne

-- Factory IV §XI, first box.  The corner is order-independent; the
-- obstruction, whatever it is, is not operator noncommutation.
projectors-commute : (ws : List Witness)
                   → filterR (filterC ws) ≡ filterC (filterR ws)
projectors-commute = filters-commute radiusOne chargeOne

------------------------------------------------------------------------
-- §5  The information does not: the constructed counterexample.
--
-- Factory IV's own two mass placements, one witness each:
--
--   primeAtRadiusTwo      exact-prime mass (charge 1) at radius 2 —
--                         feeds the charge marginal, misses the corner;
--   chargeTwoAtRadiusOne  radius-one mass at charge 2 — feeds the
--                         radius marginal, misses the corner.
--
-- Each marginal filter is nonempty; the joint filter, in either order,
-- is empty.  This is the marginal-to-joint gap made checkable: both
-- known recurrences can be inhabited while the corner is bare, so no
-- argument from the marginals alone — commutation included — can reach
-- the corner.  Two witnesses suffice, and everything evaluates by refl
-- because every projector here computes.
------------------------------------------------------------------------

primeAtRadiusTwo : Witness
primeAtRadiusTwo = witness 2 prime-leg

chargeTwoAtRadiusOne : Witness
chargeTwoAtRadiusOne = witness 1 semiprime-leg

theWorld : List Witness
theWorld = primeAtRadiusTwo ∷ chargeTwoAtRadiusOne ∷ []

-- Both marginals evaluate to nonempty lists…
charge-marginal : filterC theWorld ≡ primeAtRadiusTwo ∷ []
charge-marginal = refl

radius-marginal : filterR theWorld ≡ chargeTwoAtRadiusOne ∷ []
radius-marginal = refl

-- …and the joint corner is empty, in both orders (as it must be, by
-- projectors-commute — the two refl's below are that theorem's
-- evaluation at theWorld).
corner-empty : filterR (filterC theWorld) ≡ []
corner-empty = refl

corner-empty' : filterC (filterR theWorld) ≡ []
corner-empty' = refl

-- Nonemptiness stated negatively, so the gap can be bundled as one
-- proposition rather than read off from normal forms.
private
  cons≢nil : {A : Type} (x : A) (xs ys : List A)
           → ys ≡ x ∷ xs → ¬ (ys ≡ [])
  cons≢nil x xs ys e h = snotz (cong length (sym e ∙ h))

-- The marginal-to-joint gap, in one term: the charge face is
-- inhabited, the radius face is inhabited, the joint corner is empty.
-- §XI's second box — "a marginal-to-joint lower-bound problem" — is
-- the demand for a hypothesis on witness fields that this term shows
-- cannot be dropped.
marginal-to-joint-gap :
    (¬ (filterC theWorld ≡ []))
  × (¬ (filterR theWorld ≡ []))
  × (filterR (filterC theWorld) ≡ [])
marginal-to-joint-gap =
    cons≢nil primeAtRadiusTwo [] (filterC theWorld) charge-marginal
  , cons≢nil chargeTwoAtRadiusOne [] (filterR theWorld) radius-marginal
  , corner-empty
