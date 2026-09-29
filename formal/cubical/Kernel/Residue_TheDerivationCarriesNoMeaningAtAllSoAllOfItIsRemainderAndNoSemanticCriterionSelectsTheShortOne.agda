{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Sesa_TheDerivationCarriesNoMeaningAtAll
--                     SoAllOfItIsRemainderAndNoSemanticCriterionSelectsTheShortOne
--
-- TERM.  शेष · śeṣa -- the remainder that is KEPT and made the material of
-- the next step, rather than discarded.  ryabhaa, *ryabhaya*,
-- Gaitapda 32-33 (499), as the kuaka's governing move.
--
-- What is borrowed is the kuaka's structural decision -- that the object
-- worth carrying forward is the residue, not the quotient -- and the claim
-- here is that this kernel's types force the same decision: §3 shows the
-- quotient (the meaning) has ZERO bits, so if anything at all is carried
-- forward it is the remainder or it is nothing.
--
------------------------------------------------------------------------
-- COMPANION TO `Vyapti_…`, AND THE SHARPER HALF.
--
-- `Vyapti_…` read `NativeOperation.control-sound` and found the kernel
-- cannot generalise.  This module reads the other soundness field --
-- `Kernel.RewriteCertificate.derivation-sound` -- and finds something that no
-- schema repairs, because it is not a defect:
--
--     derivation-sound : Derivation a b → (ρ : Env) → eval a ρ ≡ eval b ρ
--
-- `eval` lands in ℕ.  ℕ is a set.  So the codomain of that map is, at every
-- ρ, a PROPOSITION (§1).  A map into a proposition transmits at most one
-- bit, and here the bit is already fixed by the type's being inhabited.
--
--     THEREFORE A DERIVATION CARRIES NO SEMANTIC INFORMATION WHATSOEVER.
--     Every last bit of it is ea.
--
-- That is not a limitation of `eval`; §4 proves it of EVERY function of the
-- meaning.  And it is exactly the fact that makes the kernel's one
-- conservation law -- `Kernel.ControlledGrammar.advance-preserves-branch-count`,
-- multiplicity preserved with no dedupe, no sort, no quotient -- the load
-- bearing line it is.  What that law protects is precisely what the
-- semantics cannot see.
--
--   §1  meaning-is-a-proposition, soundness-factors-through-truncation
--       The soundness of a derivation depends only on ∥ Derivation a b ∥₁ --
--       on THAT one exists, never on WHICH.  The factoring is exhibited and
--       the triangle commutes by `refl`.
--
--   §2  derivations-are-not-a-proposition
--       And the truncation is strict, on the kernel's OWN pair: the direct
--       and detour histories of `GenerativeKernel` are distinct elements of
--       one `Derivation seed target₀`, separated by step count (2 against 4).
--       So the kernel's proof-relevance is real, not formal.
--
--   §3  cost-does-not-factor
--       `len` -- lghava, the step count -- does NOT factor through the
--       truncation.  A g on ∥·∥₁ agreeing with `len` would have to equate
--       2 and 4, because `squash₁` identifies the two histories upstairs.
--       So cost is not a function of meaning.  Sharp, on named terms.
--
--   §4  every-semantic-criterion-is-blind
--       The general form, and the reason §3 is not about `len` in
--       particular: for ANY C and ANY φ from the meaning to C, φ agrees on
--       the cheap and the expensive derivation.  No semantic criterion --
--       none, at any h-level, of any complexity -- selects the short proof.
--       Selection must be extra-semantic or it does not exist.
--
--   §5  step-sound-is-blind-too
--       One level down, so the statement is not an artefact of composition:
--       a single `Step`'s soundness is a proposition already.
--
-- WHY THIS IS THE LANGUAGE-MODEL STATEMENT, said once and not repeated.
-- `install` makes a proved theorem a next-move, so the operation library is
-- a learned policy and `EnabledFuture seed` is its forward pass.  §1-§4 say:
-- the correctness of an emission is one bit, and everything the kernel
-- actually maintains -- multiplicity, route, length -- lives in the fibre
-- over that bit.  A likelihood that is a function of correctness therefore
-- cannot rank branches at all, and the ranking that matters is a residual
-- quantity the semantics is provably blind to.  That is why `advance` may
-- not dedupe, why lghava is a SEPARATE order, and why search does not
-- reduce to checking.
------------------------------------------------------------------------

module Kernel.Residue_TheDerivationCarriesNoMeaningAtAllSoAllOfItIsRemainderAndNoSemanticCriterionSelectsTheShortOne where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; isSetℕ ; injSuc ; znots)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁ ; ∣_∣₁ ; squash₁ ; rec)

open import Kernel.RewriteCertificate
open import Kernel.GenerativeKernel
  using (seed ; target₀ ; direct-history ; detour-history)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1.  THE MEANING IS ONE BIT, AND SOUNDNESS FACTORS THROUGH ITS EXISTENCE.
------------------------------------------------------------------------

-- Because ℕ is a set, the type a derivation's soundness lands in is a
-- proposition.  Everything else in this module is downstream of this line.
meaning-is-a-proposition :
  (a b : Tm) (ρ : Env) → isProp (eval a ρ ≡ eval b ρ)
meaning-is-a-proposition a b ρ = isSetℕ (eval a ρ) (eval b ρ)

-- Two derivations with the same endpoints have EQUAL soundness proofs.  Not
-- "equally valid" -- equal, as terms, forced.
soundness-is-constant :
  {a b : Tm} (d e : Derivation a b) (ρ : Env)
  → derivation-sound d ρ ≡ derivation-sound e ρ
soundness-is-constant {a} {b} d e ρ =
  meaning-is-a-proposition a b ρ (derivation-sound d ρ) (derivation-sound e ρ)

-- So the semantics never needed the derivation, only its existence.
soundness-factors-through-truncation :
  {a b : Tm} (ρ : Env) → ∥ Derivation a b ∥₁ → eval a ρ ≡ eval b ρ
soundness-factors-through-truncation {a} {b} ρ =
  rec (meaning-is-a-proposition a b ρ) (λ d → derivation-sound d ρ)

-- and the triangle commutes on the nose.
the-factoring-triangle-commutes :
  {a b : Tm} (ρ : Env) (d : Derivation a b)
  → soundness-factors-through-truncation ρ ∣ d ∣₁ ≡ derivation-sound d ρ
the-factoring-triangle-commutes ρ d = refl

------------------------------------------------------------------------
-- §2.  AND THE TRUNCATION IS STRICT.  The kernel's own two histories.
------------------------------------------------------------------------

-- lghava: the number of steps actually taken.
len : {a b : Tm} → Derivation a b → ℕ
len (done _)        = ℕ.zero
len (then-step _ d) = ℕ.suc (len d)

len-direct : len direct-history ≡ ℕ.suc (ℕ.suc ℕ.zero)
len-direct = refl

len-detour : len detour-history ≡ ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)))
len-detour = refl

two≢four : ℕ.suc (ℕ.suc ℕ.zero) ≡ ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero))) → ⊥
two≢four p = znots (injSuc (injSuc p))

direct≢detour : direct-history ≡ detour-history → ⊥
direct≢detour p = two≢four (cong len p)

-- The kernel's proof-relevance is not a formality: this ONE type has two
-- provably different inhabitants, and §1 says the semantics identifies them.
derivations-are-not-a-proposition : isProp (Derivation seed target₀) → ⊥
derivations-are-not-a-proposition ip = direct≢detour (ip direct-history detour-history)

------------------------------------------------------------------------
-- §3.  COST IS NOT A FUNCTION OF MEANING.
--
-- `squash₁` identifies the two histories in the truncation, so anything
-- defined downstream of the truncation must give them the same cost.  `len`
-- gives 2 and 4.  Hence no such definition exists.
------------------------------------------------------------------------

cost-does-not-factor :
  Σ[ g ∈ (∥ Derivation seed target₀ ∥₁ → ℕ) ]
    ((d : Derivation seed target₀) → g ∣ d ∣₁ ≡ len d)
  → ⊥
cost-does-not-factor (g , agrees) =
  two≢four
    ( sym (agrees direct-history)
    ∙ cong g (squash₁ ∣ direct-history ∣₁ ∣ detour-history ∣₁)
    ∙ agrees detour-history )

------------------------------------------------------------------------
-- §4.  THE GENERAL NO-GO.  §3 is not about `len`, and not about ℕ.
--
-- Take ANY target type C and ANY function φ of the meaning.  φ cannot tell
-- the two derivations apart, because their meanings are literally the same
-- function.  There is no clever semantic criterion; there is no semantic
-- criterion.
------------------------------------------------------------------------

meanings-are-equal :
  {a b : Tm} (d e : Derivation a b)
  → derivation-sound d ≡ derivation-sound e
meanings-are-equal d e = funExt (soundness-is-constant d e)

every-semantic-criterion-is-blind :
  {a b : Tm} {C : Type ℓ}
  (φ : ((ρ : Env) → eval a ρ ≡ eval b ρ) → C)
  (d e : Derivation a b)
  → φ (derivation-sound d) ≡ φ (derivation-sound e)
every-semantic-criterion-is-blind φ d e = cong φ (meanings-are-equal d e)

-- Read at the kernel's own pair: whatever you score a derivation with, if
-- the score is computed from what the derivation MEANS, the detour scores
-- exactly what the direct route scores.
no-scorer-prefers-the-direct-route :
  {C : Type ℓ} (score : ((ρ : Env) → eval seed ρ ≡ eval target₀ ρ) → C)
  → score (derivation-sound direct-history) ≡ score (derivation-sound detour-history)
no-scorer-prefers-the-direct-route score =
  every-semantic-criterion-is-blind score direct-history detour-history

------------------------------------------------------------------------
-- §5.  ONE LEVEL DOWN, so §1 is not an artefact of composing steps.
------------------------------------------------------------------------

step-soundness-is-constant :
  {a b : Tm} (p q : Step a b) (ρ : Env)
  → step-sound p ρ ≡ step-sound q ρ
step-soundness-is-constant {a} {b} p q ρ =
  meaning-is-a-proposition a b ρ (step-sound p ρ) (step-sound q ρ)

-- In particular `reverse (reverse p)` and `p` are indistinguishable to the
-- semantics while remaining different data -- which is the whole mechanism
-- by which `detour-history` exists at all.
double-reverse-is-semantically-invisible :
  {a b : Tm} (p : Step a b) (ρ : Env)
  → step-sound (reverse (reverse p)) ρ ≡ step-sound p ρ
double-reverse-is-semantically-invisible p ρ =
  step-soundness-is-constant (reverse (reverse p)) p ρ
