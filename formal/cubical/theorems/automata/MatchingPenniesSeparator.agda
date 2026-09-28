{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- MatchingPenniesSeparator
--
-- Source: owner Delta 30,
-- `collab/upstream/raw/D0026-owner-egb-core-transmission-v2-2026-08-16.md` (absent from this repository).
--
-- THE POINT OF THE MODULE, stated before any code.
--
--   On the four pure profiles 𝒜 = {H,T}² of matching pennies, three
--   summary maps are available:
--
--     * social welfare  W = u₁ + u₂         — ONE fiber (constant);
--     * the pure-Nash predicate  pne        — ONE fiber (constant false,
--                                             because no pure profile is
--                                             an equilibrium);
--     * the best-response composite β₂ ∘ π₁ — TWO fibers.
--
--   By the corpus's level-set theorem (T) (f factors through q
--   iff f is constant on every q-fiber), a summary with a SINGLE fiber
--   forces every map factoring through it to be constant.  Hence the
--   best-response structure descends through NEITHER W NOR pne.  That is
--   the whole separator, and it is (T) again — not a new theorem, a
--   fourth costume for an old one.
--
--   Consequently, and this is the finding the source note was written
--   for: `VERIFIER_BLIND_FIBER_REWARD` Theorem A (a reward that is a
--   function of a one-fiber observable carries zero bits about position
--   inside the fiber) and von Neumann's oldest game example ARE THE SAME
--   THEOREM.  One is a number-theoretic witness for it, the other a
--   strategic one.  `VERIFIER_BLIND_FIBER_REWARD`'s Theorem A and this
--   module's `separator-W` / `separator-pne` are two instantiations of
--   (T) at different q.
--
-- NORMALIZATION (source note §5.5).  The textbook payoffs are ±1, which
-- would drag in ℤ.  Best responses are invariant under a PER-PLAYER
-- positive affine map, so apply x ↦ (x+1)/2 to each player separately:
--
--     u₁(a,b) = [a = b] ∈ {0,1},   u₂ = 1 − u₁.
--
--   β₁ and β₂ are unchanged by construction; W ≡ 1 replaces W ≡ 0.  The
--   constancy of W — the only thing §5.2 uses — survives verbatim, and
--   everything below is decidable on Bool with ℕ-valued payoffs in
--   {0,1}: no Int, no Rationals, no order-completeness.  H := true,
--   T := false.
--
-- CONTENTS
--
--   §1  u₁ u₂ W          the normalized payoffs (4 clauses each) and
--                        `welfare-const`, §5.2: W ≡ 1 by four refls.
--   §2  β₁-best β₂-best  §5.3's best-response maps β₁ = id, β₂ = not,
--                        each certified as a genuine maximum over the
--                        deviating player's whole action set (4 clauses
--                        each, every clause an explicit ≤-witness).
--   §3  IsNash           §5.3: no pure profile is Nash.  Four clauses,
--       no-pure-nash     each discharged by the deviation named in the
--                        best-response 4-cycle, and each reducing to the
--                        SAME refutation ¬ (1 ≤ 0).
--   §4  pne              the Boolean pure-Nash test read off β₁, β₂; its
--                        constancy by four refls.
--   §5  one-fiber-       theorem (T) in its degenerate one-fiber form,
--       forces-constant  proved generally (no case split), then
--       separator-W      applied to W and to pne against
--       separator-pne    β = β₂ ∘ π₁, whose two fibers are exhibited by
--                        `β-surjective`.
--
-- WHAT IS CHECKED.
--
--   Every statement of §§5.2–5.4 of the source note, as exact
--   finite computation on Bool with ℕ payoffs in {0,1}: the constancy of
--   W; that β₁ = id and β₂ = not really are best responses (a maximum
--   over the full action set, not an assertion); the emptiness of the
--   pure-Nash set; the constancy of the Boolean Nash test; the
--   two-valuedness of β₂ ∘ π₁; and the two non-factorization statements
--   that are Theorem 5.1.  `one-fiber-forces-constant` is proved for
--   ARBITRARY codomains, so the separator is the general lemma applied,
--   not a coincidence of Bool.
--
------------------------------------------------------------------------

module MatchingPenniesSeparator where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; false≢true)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; snotz)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤0→≡0)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (_×_ ; Σ-syntax ; _,_)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- §0  The profile set
--
-- 𝒜 = {H,T}², with H := true and T := false.  Four elements, and every
-- statement below is a finite check over them.
------------------------------------------------------------------------

Action : Type₀
Action = Bool

Profile : Type₀
Profile = Action × Action

------------------------------------------------------------------------
-- §1  The normalized payoffs, and §5.2: welfare is constant
--
-- u₁(a,b) = [a = b].  u₂ = 1 − u₁, spelled out as four clauses rather
-- than through ∸ so that every goal below reduces without a lemma.
------------------------------------------------------------------------

u₁ : Action → Action → ℕ
u₁ true  true  = 1
u₁ true  false = 0
u₁ false true  = 0
u₁ false false = 1

u₂ : Action → Action → ℕ
u₂ true  true  = 0
u₂ true  false = 1
u₂ false true  = 1
u₂ false false = 0

-- The zero-sum condition, normalized.  This is §5.2: the welfare summary
-- is a CONSTANT function on the profile set, which is the only property
-- of it the separator uses.
welfare-const : (a b : Action) → u₁ a b + u₂ a b ≡ 1
welfare-const true  true  = refl
welfare-const true  false = refl
welfare-const false true  = refl
welfare-const false false = refl

W : Profile → ℕ
W (a , b) = u₁ a b + u₂ a b

------------------------------------------------------------------------
-- §2  §5.3's best responses: β₁ = id, β₂ = swap
--
-- These are not asserted.  Each is certified as a maximum over the
-- deviating player's ENTIRE action set: β₁-best says that for every
-- alternative a, player 1's payoff at (a,b) is at most the payoff at
-- (b,b) — i.e. b = β₁(b) is optimal — and dually for β₂ = not.
--
-- With Cubical's  m ≤ n = Σ[ k ∈ ℕ ] k + m ≡ n, each witness is (0,refl)
-- when the value is already maximal and (1,refl) when it is 0 against 1.
------------------------------------------------------------------------

β₁ : Action → Action
β₁ b = b

β₂ : Action → Action
β₂ a = not a

β₁-best : (a b : Action) → u₁ a b ≤ u₁ (β₁ b) b
β₁-best true  true  = 0 , refl
β₁-best true  false = 1 , refl
β₁-best false true  = 1 , refl
β₁-best false false = 0 , refl

β₂-best : (a b : Action) → u₂ a b ≤ u₂ a (β₂ a)
β₂-best true  true  = 1 , refl
β₂-best true  false = 0 , refl
β₂-best false true  = 0 , refl
β₂-best false false = 1 , refl

------------------------------------------------------------------------
-- §3  No pure profile is a Nash equilibrium
--
-- The single refutation every clause reduces to.  A deviation that
-- improves from 0 to 1 contradicts the equilibrium inequality 1 ≤ 0.
------------------------------------------------------------------------

one-not≤zero : ¬ (1 ≤ 0)
one-not≤zero bounded = snotz (≤0→≡0 bounded)

IsNash : Action → Action → Type₀
IsNash a b = ((x : Action) → u₁ x b ≤ u₁ a b)
           × ((y : Action) → u₂ a y ≤ u₂ a b)

-- §5.3's improvement 4-cycle, discharged clause by clause:
--   (H,H) --2--> (H,T) --1--> (T,T) --2--> (T,H) --1--> (H,H).
-- The labelled player is the one whose component of IsNash is used.
no-pure-nash : (a b : Action) → IsNash a b → ⊥
no-pure-nash true  true  (_  , d₂) = one-not≤zero (d₂ false)
no-pure-nash true  false (d₁ , _ ) = one-not≤zero (d₁ false)
no-pure-nash false true  (d₁ , _ ) = one-not≤zero (d₁ true)
no-pure-nash false false (_  , d₂) = one-not≤zero (d₂ true)

------------------------------------------------------------------------
-- §4  The Boolean pure-Nash summary, and its single fiber
--
-- pne is the equilibrium test read off the two best-response maps:
-- (a,b) is a fixed point of the joint best response iff a = β₁ b and
-- b = β₂ a.  §5.3 shows the pure-Nash set is empty; here the Boolean
-- test is shown constant, so the SUMMARY pne has one fiber.
-- The two facts are established independently and
-- neither is used to prove the other.
------------------------------------------------------------------------

eqb : Bool → Bool → Bool
eqb true  c = c
eqb false c = not c

pne : Profile → Bool
pne (a , b) = eqb a (β₁ b) and eqb b (β₂ a)

pne-const : (p : Profile) → pne p ≡ false
pne-const (true  , true ) = refl
pne-const (true  , false) = refl
pne-const (false , true ) = refl
pne-const (false , false) = refl

------------------------------------------------------------------------
-- §5  Theorem (T), and Theorem 5.1 as two of its instances
--
-- `factorsThrough q f` is the data of a factorization f = g ∘ q.  The
-- lemma is the degenerate one-fiber case of
-- `OBSERVABLE_DESCENT_COMMON_OBJECT` §1: if q is constant then its only
-- fiber is everything, so any f descending through it is constant.  It
-- is proved for ARBITRARY B and C, with no case analysis anywhere — the
-- content is a path composition, and Bool never appears.
------------------------------------------------------------------------

factorsThrough : {B C : Type₀} → (Profile → B) → (Profile → C) → Type₀
factorsThrough {B} {C} q f = Σ[ g ∈ (B → C) ] ((p : Profile) → f p ≡ g (q p))

one-fiber-forces-constant :
  {B C : Type₀} (q : Profile → B) (f : Profile → C)
  → ((p p' : Profile) → q p ≡ q p')
  → factorsThrough q f
  → (p p' : Profile) → f p ≡ f p'
one-fiber-forces-constant q f q-const (g , fac) p p' =
  fac p ∙ cong g (q-const p p') ∙ sym (fac p')

-- The ONE fiber of W (§5.2) and the ONE fiber of pne (§5.3).
W-one-fiber : (p p' : Profile) → W p ≡ W p'
W-one-fiber (a , b) (a' , b') = welfare-const a b ∙ sym (welfare-const a' b')

pne-one-fiber : (p p' : Profile) → pne p ≡ pne p'
pne-one-fiber p p' = pne-const p ∙ sym (pne-const p')

-- The best-response composite β₂ ∘ π₁, and its TWO fibers.
β : Profile → Bool
β (a , b) = β₂ a

β-surjective : (v : Bool) → Σ[ p ∈ Profile ] β p ≡ v
β-surjective true  = (false , false) , refl
β-surjective false = (true  , true ) , refl

β-not-constant : ¬ ((p p' : Profile) → β p ≡ β p')
β-not-constant h = false≢true (h (true , true) (false , false))

-- Theorem 5.1.  Neither summary supports the best-response structure.
separator-W : ¬ (factorsThrough W β)
separator-W fac = β-not-constant (one-fiber-forces-constant W β W-one-fiber fac)

separator-pne : ¬ (factorsThrough pne β)
separator-pne fac =
  β-not-constant (one-fiber-forces-constant pne β pne-one-fiber fac)

-- Corollary 5.2, in the form the source note states it: any report,
-- score or reward that is a function of the welfare summary alone
-- cannot distinguish ANY two of the four profiles — while β does.  This
-- is `VERIFIER_BLIND_FIBER_REWARD` Theorem A's conclusion, reached here
-- through the strategic witness instead of the arithmetic one.
welfare-reward-is-blind :
  {C : Type₀} (r : Profile → C) → factorsThrough W r
  → (p p' : Profile) → r p ≡ r p'
welfare-reward-is-blind r = one-fiber-forces-constant W r W-one-fiber

pne-reward-is-blind :
  {C : Type₀} (r : Profile → C) → factorsThrough pne r
  → (p p' : Profile) → r p ≡ r p'
pne-reward-is-blind r = one-fiber-forces-constant pne r pne-one-fiber
