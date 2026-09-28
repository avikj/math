{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Vikaladesa_TheDominationVerdictIsAFunctionOfTheDeclaredFamilyNotOfTheObject
--
-- WHAT IS CHECKED
--
--   sep                     separation of two states by a DECLARED
--                           FAMILY of Bool-valued observations, given
--                           as a list
--   sep-mono-left/right     extending the family can only ADD
--                           separations
--   sep-refines             contrapositive: indistinguishability under
--                           the larger family implies it under the
--                           smaller
--   full-separates/-sound   a family that separates every pair is
--                           exactly the equality relation on a
--                           three-element state type
--   partial-blind           a one-observation family merges s₁ and s₂,
--                           which are apart (s₁≢s₂)
--   dominates-ext-same      appending the SAME coordinate to both
--                           profiles preserves a domination verdict
--   myClaimIsFalse          appending DIFFERENT coordinates does not.
--   small-verdict           dominates [1,1] [2,4] = true
--   large-verdict           dominates [1,1,101] [2,4,0] = false
--   large-verdict-reverse   dominates [2,4,0] [1,1,101] = false —
--                           incomparable, so the second route is not
--                           merely undominated, it is back
--   survivors-under-*       the survivor count on a FIXED pair of
--                           routes is 1 under the two-coordinate
--                           family and 2 under the three-coordinate
--                           family
--   coarse-merges /         a bearing family of one point merges two
--   fine-separates          headings a three-point family separates
--
-- PROVENANCE OF THE MATHEMATICS.  Not Indian and not Carolinian; it is
-- this repository's, from three artifacts:
--
--   * notes/DSO_QUERY_EXTENSION_BOUNDARY.md (absent from this repository), whose two tables give the
--     numbers [1,1] / [2,4] / [1,1,101] / [2,4,0], used here
--     verbatim.  It states the
--     phenomenon in prose and executes it as a GHC regression
--     (`checkDSOQueryExtension` in machine/MathMachine.hs (absent from this repository), returning
--     `Left ["true/direct"]`).  This module
--     checks it.
--   * the observation
--     — "next action ≠ f(scalar remainder)": three states sharing one
--     visible invariant carry three future-response laws.  §2 below is
--     that shape at its smallest: `partial` is the visible invariant,
--     {s₁,s₂} is a fiber of it, and `full` splits the fiber.
--     The bound is exact for this three-state witness, not for all
--     Smith states; §4 is why.
--   * machinery/test_changed_domain_separation.py (absent from this repository): the
--     minimal changed domain is not a function of the block graph, nor
--     of the labelled block graph.  Same shape: a coarse invariant that
--     is not a sufficient statistic for the question asked of it.
--
-- ON THE NAME.  *vikalādeśa* — the partial statement, made from one
-- standpoint (naya) — against *sakalādeśa*, the total statement, which
-- is prama.  Malliea, *Sydvdamajar*, 1292 CE; the distinction is
-- already carried in this corpus by notes/ANEKANTA_THE_MACHINE_HAS_
-- THREE_STANDPOINTS.md (absent from this repository) and formal/cubical/SaptabhangiNaya.agda, which
-- use it for expressibility and the seven-fold predication.  The object
-- here is different: an ORDERING VERDICT issued under a partial
-- standpoint.  The word
-- names the object — a verdict that holds under one declared standpoint
-- and is not a property of what it is a verdict about.  The received name for the order on profiles is Pareto's; it
-- is used nowhere below, where the relation is called `dominates`.
--
-- THE ANCIENT FIELD.  Polynesian and Micronesian navigation; the
-- procedure, with source and date.
-- Thomas Gladwin, *East Is a Big Bird: Navigation and Logic on Puluwat
-- Atoll*, Harvard University Press, 1970, from the navigator Hipour of
-- the Weriyeng school; David Lewis, *We, the Navigators*, University
-- Press of Hawaii, 1972.  The horizon is divided into 32 points, one
-- for each rising and each setting of a named star, a point being
-- *paafu* in Satawalese.  In *etak* the canoe is held stationary and a
-- reference island, chosen off to one side of the course and usually
-- below the horizon, is taken to slide backwards under the successive
-- star points; the passage is divided into etak segments and the
-- running count is the position.  Ben Finney's 1976 Hkleʻa voyage
-- from Hawaiʻi to Tahiti, navigated by Mau Piailug of Satawal, is what
-- put the practice on record outside the Carolines; nothing here
-- depends on it.
--
-- What it gave: §5, and only §5.  A bearing family is a DECLARED FINITE
-- FAMILY whose size fixes a resolution, and two headings inside one
-- point are not separated by it.  That is the one feature used, and it
-- is used as an instance, not as a source.
--
-- §5 checks 1 point against 3, because the content is refinement and
-- not the number.  A sibling module carries etak
-- (NaturalMachine.Prastara_TheGaugeStreamCostsZeroCarriedBitsAndInvisibilityIsWeakerThanGauge).
-- §§3 and 4
-- show that the
-- verdicts a family issues are not monotone in the family even though
-- its separations are.
--
-- WHAT IS REFUTED.  Reading the material through
-- "the units you assumed were individuals may be collaborations", the
-- natural claim is that the number of behaviours hiding inside a
-- visible state is a property of the object, so a verdict separating
-- two of them cannot be undone by looking harder.  Written out:
-- `DominationSurvivesEveryExtension`.  `myClaimIsFalse` kills it, on
-- the note's own four numbers.  `dominates-ext-same` is the true
-- lemma that makes the false one tempting, and is proved first so the
-- temptation is on the page.
--
------------------------------------------------------------------------

module NaturalMachine.Partialdesa_TheDominationVerdictIsAFunctionOfTheDeclaredFamilyNotOfTheObject where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; _and_ ; _or_ ; _⊕_ ; true≢false ; false≢true)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Relation.Nullary using (¬_)

import Cubical.Data.Empty as ⊥
open ⊥ using (⊥)

private
  variable
    ℓ : Level
    A : Type ℓ

------------------------------------------------------------------------
-- 1.  A declared family, and what it can see
--
-- A family is a LIST of Bool-valued observations.  The list, not the
-- set: the family is declared, and its declaration is the thing every
-- verdict below is relative to.
------------------------------------------------------------------------

sep : List (A → Bool) → A → A → Bool
sep []       x y = false
sep (f ∷ fs) x y = (f x ⊕ f y) or sep fs x y

-- Extending the family on the right can only add separations.
sep-mono-right : (O O' : List (A → Bool)) (x y : A)
               → sep O x y ≡ true → sep (O ++ O') x y ≡ true
sep-mono-right []       O' x y p = ⊥.rec (false≢true p)
sep-mono-right (f ∷ fs) O' x y p with f x ⊕ f y
... | true  = refl
... | false = sep-mono-right fs O' x y p

-- And on the left.
sep-mono-left : (O O' : List (A → Bool)) (x y : A)
              → sep O' x y ≡ true → sep (O ++ O') x y ≡ true
sep-mono-left []       O' x y p = p
sep-mono-left (f ∷ fs) O' x y p with f x ⊕ f y
... | true  = refl
... | false = sep-mono-left fs O' x y p

-- The contrapositive, which is the statement that matters below:
-- indistinguishability is ANTITONE in the family.  A larger standpoint
-- never merges what a smaller one told apart.
sep-refines : (O O' : List (A → Bool)) (x y : A)
            → sep (O ++ O') x y ≡ false → sep O x y ≡ false
sep-refines []       O' x y p = refl
sep-refines (f ∷ fs) O' x y p with f x ⊕ f y
... | true  = ⊥.rec (true≢false p)
... | false = sep-refines fs O' x y p

------------------------------------------------------------------------
-- 2.  A fiber of a visible invariant, and the family that splits it
--
-- The smallest form of the shape named in the header: a coarse observation
-- whose fiber holds two states that a finer family tells apart.
------------------------------------------------------------------------

data St : Type where
  s₀ s₁ s₂ : St

isS₀ isS₁ isS₂ : St → Bool
isS₀ s₀ = true
isS₀ s₁ = false
isS₀ s₂ = false
isS₁ s₀ = false
isS₁ s₁ = true
isS₁ s₂ = false
isS₂ s₀ = false
isS₂ s₁ = false
isS₂ s₂ = true

-- The complete family: one observation per state.
full : List (St → Bool)
full = isS₀ ∷ isS₁ ∷ isS₂ ∷ []

-- The visible invariant: "is it s₀?".
partial : List (St → Bool)
partial = isS₀ ∷ []

full-refl : (x : St) → sep full x x ≡ false
full-refl s₀ = refl
full-refl s₁ = refl
full-refl s₂ = refl

full-separates : (x y : St) → ¬ (x ≡ y) → sep full x y ≡ true
full-separates s₀ s₀ n = ⊥.rec (n refl)
full-separates s₀ s₁ _ = refl
full-separates s₀ s₂ _ = refl
full-separates s₁ s₀ _ = refl
full-separates s₁ s₁ n = ⊥.rec (n refl)
full-separates s₁ s₂ _ = refl
full-separates s₂ s₀ _ = refl
full-separates s₂ s₁ _ = refl
full-separates s₂ s₂ n = ⊥.rec (n refl)

full-sound : (x y : St) → sep full x y ≡ true → ¬ (x ≡ y)
full-sound x y p q =
  true≢false (sym p ∙ sym (cong (sep full x) q) ∙ full-refl x)

-- s₁ and s₂ are apart …
s₁≢s₂ : ¬ (s₁ ≡ s₂)
s₁≢s₂ p = true≢false (cong isS₁ p)

-- … and the visible invariant cannot see it.
partial-blind : sep partial s₁ s₂ ≡ false
partial-blind = refl

-- One further observation is enough.
partial-extended-sees : sep (partial ++ (isS₁ ∷ [])) s₁ s₂ ≡ true
partial-extended-sees = refl

------------------------------------------------------------------------
-- 3.  Profiles, and the verdict a family issues about two of them
--
-- A route's profile is one cost per active context.  Declaring more
-- contexts makes the profiles longer.  `dominates p q` is the verdict
-- "q is beaten by p": pointwise no worse, and strictly better
-- somewhere.
------------------------------------------------------------------------

leℕ : ℕ → ℕ → Bool
leℕ zero    _       = true
leℕ (suc _) zero    = false
leℕ (suc m) (suc n) = leℕ m n

leℕ-refl : (n : ℕ) → leℕ n n ≡ true
leℕ-refl zero    = refl
leℕ-refl (suc n) = leℕ-refl n

ltℕ : ℕ → ℕ → Bool
ltℕ m n = not (leℕ n m)

Profile : Type
Profile = List ℕ

leAll : Profile → Profile → Bool
leAll []       []       = true
leAll []       (_ ∷ _)  = false
leAll (_ ∷ _)  []       = false
leAll (a ∷ as) (b ∷ bs) = (leℕ a b) and (leAll as bs)

ltSome : Profile → Profile → Bool
ltSome []       []       = false
ltSome []       (_ ∷ _)  = false
ltSome (_ ∷ _)  []       = false
ltSome (a ∷ as) (b ∷ bs) = (ltℕ a b) or (ltSome as bs)

dominates : Profile → Profile → Bool
dominates p q = (leAll p q) and (ltSome p q)

-- Bool plumbing.
and-split₁ : (a b : Bool) → (a and b) ≡ true → a ≡ true
and-split₁ true  _ _ = refl
and-split₁ false _ p = ⊥.rec (false≢true p)

and-split₂ : (a b : Bool) → (a and b) ≡ true → b ≡ true
and-split₂ true  _ p = p
and-split₂ false _ p = ⊥.rec (false≢true p)

and-join : (a b : Bool) → a ≡ true → b ≡ true → (a and b) ≡ true
and-join a b p q = cong₂ _and_ p q

leAll-ext : (p q : Profile) (c d : ℕ)
          → leAll p q ≡ true → leℕ c d ≡ true
          → leAll (p ++ (c ∷ [])) (q ++ (d ∷ [])) ≡ true
leAll-ext []       []       c d _ hcd = cong (λ b → b and true) hcd
leAll-ext []       (_ ∷ _)  c d h _   = ⊥.rec (false≢true h)
leAll-ext (_ ∷ _)  []       c d h _   = ⊥.rec (false≢true h)
leAll-ext (a ∷ as) (b ∷ bs) c d h hcd with leℕ a b
... | true  = leAll-ext as bs c d h hcd
... | false = ⊥.rec (false≢true h)

ltSome-ext : (p q : Profile) (c : ℕ)
           → ltSome p q ≡ true
           → ltSome (p ++ (c ∷ [])) (q ++ (c ∷ [])) ≡ true
ltSome-ext []       []       c h = ⊥.rec (false≢true h)
ltSome-ext []       (_ ∷ _)  c h = ⊥.rec (false≢true h)
ltSome-ext (_ ∷ _)  []       c h = ⊥.rec (false≢true h)
ltSome-ext (a ∷ as) (b ∷ bs) c h with ltℕ a b
... | true  = refl
... | false = ltSome-ext as bs c h

-- THE TRUE LEMMA.  If the newly declared context charges both routes
-- the SAME cost, the verdict stands.  This is what makes the false
-- claim in §4 tempting: it is the case one imagines when one imagines
-- "adding information".
dominates-ext-same : (p q : Profile) (c : ℕ)
                   → dominates p q ≡ true
                   → dominates (p ++ (c ∷ [])) (q ++ (c ∷ [])) ≡ true
dominates-ext-same p q c h =
  and-join _ _
    (leAll-ext p q c c (and-split₁ _ _ h) (leℕ-refl c))
    (ltSome-ext p q c (and-split₂ _ _ h))

------------------------------------------------------------------------
-- 4.  The refutation, on the note's own numbers
--
-- notes/DSO_QUERY_EXTENSION_BOUNDARY.md (absent from this repository), its two tables.  Active
-- dependencies ["answer"] give two contexts, goal and robustness:
--
--     false/direct  [1,1]      sole surviving class
--     true/direct   [2,4]      dominated
--
-- Extending to ["answer","audit"] activates a third context,
-- diagnostic:
--
--     false/direct  [1,1,101]  survives
--     true/direct   [2,4,0]    survives; resurrected
------------------------------------------------------------------------

falseDirect trueDirect : Profile
falseDirect = 1 ∷ 1 ∷ []
trueDirect  = 2 ∷ 4 ∷ []

diagFalseDirect diagTrueDirect : ℕ
diagFalseDirect = 101
diagTrueDirect  = 0

falseDirect⁺ trueDirect⁺ : Profile
falseDirect⁺ = falseDirect ++ (diagFalseDirect ∷ [])
trueDirect⁺  = trueDirect  ++ (diagTrueDirect  ∷ [])

small-verdict : dominates falseDirect trueDirect ≡ true
small-verdict = refl

large-verdict : dominates falseDirect⁺ trueDirect⁺ ≡ false
large-verdict = refl

-- Not merely undominated: incomparable.  Neither beats the other.
large-verdict-reverse : dominates trueDirect⁺ falseDirect⁺ ≡ false
large-verdict-reverse = refl

-- THE FALSE CLAIM.  Reading §2 as "the
-- visible state is a collaboration of several behaviours, and how many
-- there are is a property of the object", the verdict that one route
-- beats another looks like a fact about the two routes.  It is not.
DominationSurvivesEveryExtension : Type
DominationSurvivesEveryExtension =
  (p q : Profile) (c d : ℕ)
  → dominates p q ≡ true
  → dominates (p ++ (c ∷ [])) (q ++ (d ∷ [])) ≡ true

myClaimIsFalse : ¬ DominationSurvivesEveryExtension
myClaimIsFalse H =
  true≢false
    (sym (H falseDirect trueDirect diagFalseDirect diagTrueDirect small-verdict)
     ∙ large-verdict)

-- The same thing as a count, so that "the verdict moved" is a number
-- and not a reading.  The archive is FIXED — the same two routes — and
-- only the declared family changes.
anyDominates : Profile → List Profile → Bool
anyDominates r []       = false
anyDominates r (s ∷ ss) = (dominates s r) or (anyDominates r ss)

bToℕ : Bool → ℕ
bToℕ true  = 1
bToℕ false = 0

countSurvivors : List Profile → List Profile → ℕ
countSurvivors arch []       = 0
countSurvivors arch (r ∷ rs) =
  bToℕ (not (anyDominates r arch)) + countSurvivors arch rs

routes⁻ routes⁺ : List Profile
routes⁻ = falseDirect  ∷ trueDirect  ∷ []
routes⁺ = falseDirect⁺ ∷ trueDirect⁺ ∷ []

survivors-under-small-family : countSurvivors routes⁻ routes⁻ ≡ 1
survivors-under-small-family = refl

survivors-under-large-family : countSurvivors routes⁺ routes⁺ ≡ 2
survivors-under-large-family = refl

------------------------------------------------------------------------
-- 5.  A bearing family
--
-- The one thing the ancient field gave.  A family of named
-- horizon points is a declared finite family, and its size is the
-- resolution of any position read against it: two headings falling
-- inside one point are not separated, and a finer family separates
-- them.  1 point against 3 here; the Carolinian 32 is not used.
------------------------------------------------------------------------

Dir : Type
Dir = Bool × (Bool × Bool)

b₀ b₁ b₂ : Dir → Bool
b₀ (x , _)       = x
b₁ (_ , (y , _)) = y
b₂ (_ , (_ , z)) = z

coarse fine : List (Dir → Bool)
coarse = b₀ ∷ []
fine   = b₀ ∷ b₁ ∷ b₂ ∷ []

d₁ d₂ : Dir
d₁ = (true , (false , false))
d₂ = (true , (false , true))

coarse-merges : sep coarse d₁ d₂ ≡ false
coarse-merges = refl

fine-separates : sep fine d₁ d₂ ≡ true
fine-separates = refl
