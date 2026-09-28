{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheDeflationaryTestWasAlreadyRun
--
-- An audit of this thread's last several cycles against a module that
-- was in the corpus, and in the latch this thread typechecks every
-- cycle, the whole time.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT HAPPENED
--
-- "The deflationary test" has been a named live thread in every
-- heartbeat of this session.  `DeflationaryTest` has
-- been in `RootsThreadLatch` for longer than that.  It was never
-- opened.  Its §4 is
--
--     Π-stable, →-stable, ×-stable, ¬-always-stable
--
-- and its §5 instantiates them at the corpus's obstruction shapes.
-- That is `WhyTheSamePriceKeepsAppearing` §1 and §3, written again.
--
-- The failure is not that a lemma got proved twice.  It is that the
-- thread name and the module name were the same word for many cycles
-- and no one grepped one against the other.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED HERE
--
-- Not new mathematics.  §1 makes the duplication CHECKED rather than
-- asserted: each of this thread's closure lemmas is `refl`-equal to the
-- prior module's, because they are the same term.  A rediscovery that
-- typechecks as `refl` against its own prior art is not a matter of
-- opinion about who said what.
--
-- ────────────────────────────────────────────────────────────────────
-- THE LEDGER, EACH LINE READ FROM BOTH FILES
--
-- REDISCOVERED — prior art is `DeflationaryTest`:
--
--   `WhyTheSamePriceKeepsAppearing` §1  ←  its §4, term for term (§1
--       below).
--   `WhyTheSamePriceKeepsAppearing` §3  ←  its §5, which already
--       instantiates the closure lemmas at obstruction shapes.
--   `WhyTheSamePriceKeepsAppearing` §2  ←  its §4 heading and §8: it
--       already states stability does not pass through `⊎`.
--   `TheDomainThatIsAnAbsence`'s `¬¬Dec`  ←  its `no-barrier-claim`,
--       `¬ (BarrierClaim A)` with `BarrierClaim A = ¬ (Dec A)`.
--   `TheDeflationaryTestIsVacuous`'s central point  ←  its §7: "the
--       stabilisation level measures nothing".  My §4 there — that
--       `Stable ⊥` and `Stable Unit` both hold, so stability
--       discriminates nothing — is a sharper form of the same claim and
--       not an independent one.
--
-- NOT IN THE PRIOR MODULE, checked by reading its signature list:
--
--   `tripleNegation≃` as an EQUIVALENCE.  `DeflationaryTest` proves the
--       two implications as a product; the equivalence needs `isProp¬`
--       and is not there.
--   `noMiddleCollapse : ¬ ((¬ A) ≃ (¬ ¬ A))`.
--   `(A ≃ ¬ ¬ A) ⟺ Stable A` for propositions.
--   `Stable-↔`, stability along a bare logical equivalence.
--   the whole ground/exclusion/shadow development
--       (`ExclusionRecoversGroundAtAPrice`), which shares no statement
--       with it.
--   `A → isContr (¬ A → Y)` and `¬ A → ((¬ A → Y) ≃ Y)`.
--
-- CLOSELY RELATED, and I will not call it independent:
--   `¬ ¬ Stable A` (`TheUnstableGroundCannotBeExhibited` §1) follows
--   from its `no-barrier-claim` in two lines, since `Dec A → Stable A`.
--   It was proved here without noticing that.
--
-- AND WHAT THE PRIOR MODULE HAS THAT THIS THREAD NEVER REACHED, which
-- belongs in the same ledger:
--   its §8 — in a `--safe`, postulate-free development every inhabited
--   `⊎` is a decision, since there is no way to write a term of `A ⊎ B`
--   without producing `inl` or `inr`.  So the ⊎-sites close for a
--   reason about the SUBSTRATE, not about the types.  Nothing in this
--   thread's ⊎/Σ discussion gets near that.
--
-- ────────────────────────────────────────────────────────────────────
-- THE MECHANISM, PROPOSED AND NOT BUILT
--
-- This corpus's standing answer to a repeated violation is a mechanism
-- that fires at the moment of the act, not a paragraph.  The check that
-- would have caught this is one line and needs no judgement:
--
--     before writing a module for thread T, grep the latch's import
--     list for T's own name.
--
-- It is not added to `.claude/hooks/source-coverage.sh` (absent from this repository) here, because
-- hook changes are the owner's to approve and a previous design of mine
-- was rejected for being built before it was agreed.  It is written
-- down as a proposal, at the site where its absence cost something.
--
-- ────────────────────────────────────────────────────────────────────
-- ONE THING THIS IS NOT
--
-- Not a claim that the rediscovered modules should be deleted.  They
-- are marked, and the marks point here.  A record that deletes its own
-- errors is not a record — and the duplicated proofs are now the
-- evidence for §1, which is the only reason this file can prove
-- anything at all.
--
-- Nor is it a claim about which module is better.  There is no scale
-- here.  One was written earlier and one later, and the later one did
-- not read the earlier: that is a fact about the process, and the
-- process is what this file is about.
------------------------------------------------------------------------

module TheDeflationaryTestWasAlreadyRun where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; Stable)

open import DeflationaryTest
  using (¬-always-stable ; Π-stable ; →-stable ; ×-stable
        ; no-barrier-claim ; BarrierClaim)
open import WhyTheSamePriceKeepsAppearing
  using (stable¬ ; stableΠ ; stable→ ; stable×)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- 1.  The duplication, checked
--
-- Each pair is the same term.  `refl` is the whole proof, which is the
-- strongest available statement that nothing new was added.
------------------------------------------------------------------------

dup-¬ : {A : Type ℓ} → stable¬ {ℓ} {A} ≡ ¬-always-stable A
dup-¬ = refl

dup-Π : {A : Type ℓ} {B : A → Type ℓ'}
      → stableΠ {ℓ} {ℓ'} {A} {B} ≡ Π-stable {ℓ} {ℓ'} {A} {B}
dup-Π = refl

dup-→ : {A : Type ℓ} {B : Type ℓ'}
      → stable→ {ℓ} {ℓ'} {A} {B} ≡ →-stable {ℓ} {ℓ'} {A} {B}
dup-→ = refl

dup-× : {A : Type ℓ} {B : Type ℓ'}
      → stable× {ℓ} {ℓ'} {A} {B} ≡ ×-stable {ℓ} {ℓ'} {A} {B}
dup-× = refl

------------------------------------------------------------------------
-- 2.  And the one this thread proved without noticing it was a
--     two-line corollary of the prior module
--
-- `no-barrier-claim` says `¬ (¬ (Dec A))`.  Since a decision gives
-- stability, a refutation of stability refutes decidability, so
-- `¬ ¬ Stable A` follows.  `TheUnstableGroundCannotBeExhibited` §1
-- proves it directly instead; the direct proof is not wrong, it is
-- unaware.
------------------------------------------------------------------------

¬¬Stable-fromPriorArt :
  {A : Type ℓ} → (Dec A → Stable A) → ¬ ¬ Stable A
¬¬Stable-fromPriorArt {A = A} d→s ns =
  no-barrier-claim A (λ dec → ns (d→s dec))
