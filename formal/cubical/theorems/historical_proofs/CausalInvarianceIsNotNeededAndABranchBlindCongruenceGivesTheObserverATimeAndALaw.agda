{-# OPTIONS --cubical --safe #-}
--
-- Causal invariance is not needed.  A branch-blind congruence already gives
-- the observer a time and a law: different routes through the system must
-- come to one reading, and that follows from the congruence alone, with no
-- confluence premise anywhere in the statement.
--
--
-- WHAT THIS IS ABOUT.  A multiway rule — one state, many successors — is the
-- shape of a rewriting system, and the standard demand made of it is
-- CONFLUENCE: any two branches can be brought back together.  In the
-- computational-physics reading, confluence is what is called causal
-- invariance, and it is the hypothesis under which the observed history is
-- taken not to depend on the order in which updates were applied.  It is a
-- strong global property of the rule, and it usually fails.
--
-- THE FINDING.  It is not needed, and the thing that replaces it is a
-- property of the OBSERVER rather than of the rule:
--
--     if the observer's reading of a successor is determined by its reading
--     of the predecessor — the same reading in, the same reading out, NO
--     MATTER WHICH BRANCH IS TAKEN — then any two runs of the same length
--     from equally-read starts are equally read at every step.
--
-- The observer then has a deterministic law AND a well-defined time (the step
-- count), inside a rule that may branch without limit and need not be
-- confluent anywhere.  No confluence hypothesis appears in the proof, and
-- there is none to appear: `oneUtterance` below assumes only the congruence.
--
-- And the converse bite, as everywhere in this corpus: ONE pair of branches
-- the observer can tell apart destroys it — not the schedulers anyone tried,
-- every reading-level law at once.
--
-- This is the multiway face of `Anuvrtti_...`, which did the deterministic
-- case.  The step there was a function; here it is a relation, and the extra
-- content is exactly that the branch does not have to be chosen.
module CausalInvarianceIsNotNeededAndABranchBlindCongruenceGivesTheObserverATimeAndALaw where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using ()
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ {X : Type ℓ} (R : X → X → Type ℓ') where

  -- a run of exactly n steps, with the branches it took
  -- Defined by recursion on the length rather than as an indexed family: a
  -- run of zero steps IS an identification, and a run of n+1 steps is a first
  -- branch and a run of n.  Cubical Agda does not accept the doubly-indexed
  -- match this proof would otherwise need, and the recursive form is the
  -- better statement anyway -- the branch taken is right there in the data.
  route-n : ℕ → X → X → Type (ℓ-max ℓ ℓ')
  route-n zero x y = Lift {j = ℓ'} (x ≡ y)
  route-n (suc n) x z = Σ[ y ∈ X ] (R x y × route-n n y z)

  -- the observer cannot see WHICH branch was taken: equal readings in, equal
  -- readings out, for every choice of successor on either side.
  branchBlind : {V : Type ℓ''} → (X → V) → Type _
  branchBlind {V = V} o =
    {x y x' y' : X} → o x ≡ o y → R x x' → R y y' → o x' ≡ o y'

  -- ------------------------------------------------------------- the law
  -- Any two runs of the same length, from starts the observer cannot tell
  -- apart, end in states the observer cannot tell apart.  The branching is
  -- unrestricted and no confluence is assumed.
  oneUtterance : {V : Type ℓ''} (o : X → V) → branchBlind o
    → (n : ℕ) {x y u v : X}
    → route-n n x u → route-n n y v → o x ≡ o y → o u ≡ o v
  oneUtterance o blind zero (lift p) (lift q) e =
    cong o (sym p) ∙ e ∙ cong o q
  oneUtterance o blind (suc n) (_ , r , p) (_ , s , q) e =
    oneUtterance o blind n p q (blind e r s)

  -- ------------------------------------------------- and what breaks it
  -- A predictor at the level of readings: one function of the reading that
  -- gives the reading after any step, whichever branch.
  hasLaw : {V : Type ℓ''} → (X → V) → Type _
  hasLaw {V = V} o = Σ[ g ∈ (V → V) ] ({x x' : X} → R x x' → o x' ≡ g (o x))

  -- a predictor is branch-blind, so the two notions cannot come apart
  lawGivesBranchBlind : {V : Type ℓ''} (o : X → V) → hasLaw o → branchBlind o
  lawGivesBranchBlind o (g , p) e r s = p r ∙ cong g e ∙ sym (p s)

  -- ONE branching the observer can see refutes every reading-level law.
  -- Two successors of ONE state with different readings is the sharpest
  -- case: the start readings are equal by refl, so no g can send one value
  -- to two.
  noLaw : {V : Type ℓ''} (o : X → V) {x x' x'' : X}
    → R x x' → R x x'' → ¬ (o x' ≡ o x'')
    → ¬ (hasLaw o)
  noLaw o r s d h = d (lawGivesBranchBlind o h refl r s)

-- --------------------------------------------------------------- limits
--
-- WHAT IS CLAIMED, and it is the whole of it: the global hypothesis is
-- replaceable by a local one about the observer, and the replacement is not
-- an approximation.  `oneUtterance` has no confluence premise in its statement
-- or its proof.

  -- ------------------------------------------------------------ the tower
  -- A frame is not a number; it is a rung.  Given a branch-blind observer
  -- with its predictor g, ask which COARSENINGS of it are still branch-blind
  -- — every observer that throws away more but still sees one world.  The
  -- answer collapses the multiway question onto a deterministic one:
  --
  --     h ∘ o is branch-blind  ⟸  h is a congruence for g
  --
  -- and g is a FUNCTION.  So the tower of worlds a branching rule can present
  -- is the congruence structure of the single deterministic system living on
  -- its finest frame.  `machine/DrshtiJala_...` computes congruence lattices
  -- of deterministic systems; by this, the same machinery reaches multiway
  -- systems with nothing added.
  --
  -- The converse needs o to hit every value of V, which is a hypothesis
  -- about the observer and not about the rule.
  layer : {V : Type ℓ''} {W : Type ℓ''} (o : X → V) (h : V → W)
    → (b : hasLaw o)
    → ({a c : V} → h a ≡ h c → h (fst b a) ≡ h (fst b c))
    → branchBlind (λ x → h (o x))
  layer o h (g , p) hcong e r s =
    cong h (p r) ∙ hcong e ∙ cong h (sym (p s))
