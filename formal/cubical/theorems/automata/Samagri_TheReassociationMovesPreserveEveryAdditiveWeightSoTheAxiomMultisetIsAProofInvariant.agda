{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सामग्री — the complete apparatus.  Nyāya's name for the total collection
-- of causes that produces an effect; here, the multiset of AXIOMS a proof
-- path consumes.  runtime/propagate quotients proof paths by exactly this
-- (STATUS.md: "two paths are one proof when they consume the same multiset
-- of axiom justifications, i.e. when reassociating congruence/symmetry/
-- transitivity carries one to the other").  Proved here:
--
--   §2  EVERY reassociation move preserves EVERY additive weighting of
--       the axioms.  Universal linear invariance is multiset equality
--       (take the weight indicating one axiom), stated without decidable
--       equality: the smagr is a proof invariant, so propagate's
--       homotopy classes are well-defined.
--
--   §3  THE FENCE, and it is the content: CANCELLATION is not among the
--       moves and cannot be added.  tr p (sy p) ≈ rfl would force
--       2·w(a) ≡ 0 at a single axiom — refuted at weight 1.  The
--       quotient distinguishes a proof that cancels a detour from one
--       that never took it; erasing that distinction is exactly the
--       unreceipted compression this corpus forbids (the detour's
--       receipt: consumed twice, once forward, once back).
--
-- The path language mirrors the kernel's proof forest (kernel/egraph.py (absent from this repository)):
-- axiom leaves, refl, symmetry, transitivity, congruence context.
------------------------------------------------------------------------

module Samagri_TheReassociationMovesPreserveEveryAdditiveWeightSoTheAxiomMultisetIsAProofInvariant where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-assoc; +-comm; +-zero; snotz)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- §1 · proof paths: the shape of the proof forest's emitted explanations.
data P : Type where
  ax  : ℕ → P            -- an axiom justification, by id
  rfl : P                 -- the trivial path
  sy  : P → P             -- symmetry
  tr  : P → P → P         -- transitivity
  cg  : P → P             -- a congruence context around a subproof

-- an additive weighting of axioms, and the weight a path consumes.
count : (ℕ → ℕ) → P → ℕ
count w (ax a)   = w a
count w rfl      = 0
count w (sy p)   = count w p
count w (tr p q) = count w p + count w q
count w (cg p)   = count w p

------------------------------------------------------------------------
-- the reassociation moves — propagate's "one proof" relation: groupoid
-- reshuffling of trans/sym/refl and distribution of the congruence
-- context, closed under equivalence and the constructors.  NO cancellation.
data _≈_ : P → P → Type where
  assoc : ∀ p q r → tr (tr p q) r ≈ tr p (tr q r)
  unitl : ∀ p → tr rfl p ≈ p
  unitr : ∀ p → tr p rfl ≈ p
  syrfl : sy rfl ≈ rfl
  sysy  : ∀ p → sy (sy p) ≈ p
  sytr  : ∀ p q → sy (tr p q) ≈ tr (sy q) (sy p)
  cgrfl : cg rfl ≈ rfl
  cgtr  : ∀ p q → cg (tr p q) ≈ tr (cg p) (cg q)
  cgsy  : ∀ p → cg (sy p) ≈ sy (cg p)
  ≈rfl  : ∀ p → p ≈ p
  ≈sym  : ∀ {p q} → p ≈ q → q ≈ p
  ≈tr   : ∀ {p q r} → p ≈ q → q ≈ r → p ≈ r
  ≈sy   : ∀ {p q} → p ≈ q → sy p ≈ sy q
  ≈trl  : ∀ {p q} r → p ≈ q → tr p r ≈ tr q r
  ≈trr  : ∀ {p q} r → p ≈ q → tr r p ≈ tr r q
  ≈cg   : ∀ {p q} → p ≈ q → cg p ≈ cg q

------------------------------------------------------------------------
-- §2 · THE INVARIANT.  Every move preserves every additive weighting:
-- the smagr is well-defined on propagate's homotopy classes.
invariant : {p q : P} → p ≈ q → (w : ℕ → ℕ) → count w p ≡ count w q
invariant (assoc p q r) w = sym (+-assoc (count w p) (count w q) (count w r))
invariant (unitl p)     w = refl
invariant (unitr p)     w = +-zero (count w p)
invariant syrfl         w = refl
invariant (sysy p)      w = refl
invariant (sytr p q)    w = +-comm (count w p) (count w q)
invariant cgrfl         w = refl
invariant (cgtr p q)    w = refl
invariant (cgsy p)      w = refl
invariant (≈rfl p)      w = refl
invariant (≈sym e)      w = sym (invariant e w)
invariant (≈tr e f)     w = invariant e w ∙ invariant f w
invariant (≈sy e)       w = invariant e w
invariant (≈trl r e)    w = cong (_+ count w r) (invariant e w)
invariant (≈trr r e)    w = cong (count w r +_) (invariant e w)
invariant (≈cg e)       w = invariant e w

------------------------------------------------------------------------
-- §3 · THE FENCE: cancellation cannot be a move.  If tr (ax 0) (sy (ax 0))
-- were ≈ rfl, the invariant at the weight w ≡ 1 would give 2 ≡ 0.  So the
-- move set is maximal for this invariant on that side: a proof that walks
-- a detour and cancels it is NOT the proof that never left — the detour's
-- consumption is its receipt, and erasing it is unreceipted compression.
no-cancellation : ¬ (tr (ax 0) (sy (ax 0)) ≈ rfl)
no-cancellation cancel = snotz (invariant cancel (λ _ → 1))
