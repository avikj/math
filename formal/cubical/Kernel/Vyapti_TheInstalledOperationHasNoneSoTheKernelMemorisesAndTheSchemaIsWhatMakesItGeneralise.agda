{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Vyapti_TheInstalledOperationHasNoneSoTheKernelMemorises
--                       AndTheSchemaIsWhatMakesItGeneralise
--
-- TERM.  व्याप्ति · vyāpti -- pervasion: the invariable concomitance that
-- makes an inference carry from the case at hand to every case of the same
-- mark.  Root notion in Gautama, *Nyāyasūtra* (~2nd c. CE), under अनुमान;
-- the definitional apparatus (the vyāptivāda, and the उपाधि that defeats a
-- proposed pervasion) is Navya-Nyya, Gagea, *Tattvacintmai* (~1325).
--
-- What is borrowed is one
-- distinction they drew sharply and that this kernel's types do not: a
-- मार्क that licenses an inference ONLY in the instance where it was
-- observed is not a pervasion at all.  §1 shows the kernel's installed
-- operation is exactly such a mark, and the type forces it.
--
------------------------------------------------------------------------
-- WHAT THIS IS ABOUT
--
-- `ControlledGrammar.NativeOperation` is the kernel's unit of learned
-- behaviour, and `install : Derivation lhs rhs → NativeOperation` is how a
-- theorem the machine proved becomes a move the machine can make.  That is
-- the metacircular step: proofs become the generative library, so the
-- library at a context is a next-move distribution, kept without quotient
-- (`advance-preserves-branch-count`) and carrying its derivation.
--
-- The library IS the retrieval structure and `Control` IS the match.  So the
-- question "what does this kernel generalise over?" is answered by the type
-- of `control-sound`, and the answer is: NOTHING.
--
--   §1  fires-only-at-source, enabled-set-is-subsingleton, output-is-constant
--       Every installed operation fires at exactly one term, up to a path,
--       and emits a fixed target.  A NativeOperation is a single key/value
--       pair.  The kernel is a lookup table and `control-sound`'s type is
--       what makes it one -- this is not a property of the current library.
--
--   §2  covered-heights-are-library-heights, kernel-cannot-reach-a-tower
--       Consequently the coverage of a whole library is finite while `Tm` is
--       not: the heights of the terms a library can fire on are literally
--       the finitely many heights of its sources.  Exhibited on the kernel's
--       OWN library (`GenerativeKernel.run`'s two operations, whose common
--       source is `add var (suc zero)`): the term `suc (suc (suc zero))` has
--       no enabled future, so `form` returns [] there and the generative
--       loop has nothing to do.
--
--   §3  SchematicOperation, schematic-fires-at-every-instance,
--       one-schema-two-contexts, no-native-operation-does-this
--       The repair, and the point of the module: an operation whose control
--       carries a SUBSTITUTION WITNESS rather than an identification with a
--       fixed source.  Its soundness is not a new axiom and not a new proof
--       obligation -- `eval-subVar` and the schema's own meaning discharge
--       it, both already in `RewriteCertificate`.  So GENERALISATION IS FREE
--       IN THIS CALCULUS AND MEMORISATION IS WHAT COSTS: one schematic
--       operation covers a `Tm`-indexed family of contexts, and §3's last
--       theorem shows no NativeOperation whatsoever covers even two of them.
--
--   §4  every-substitution-is-enabled, all-collapse-to-one-output
--       The fibre reading, which is why the substitution witness may not be
--       thrown away.  `apply` reads `u` only through the right-hand side, so
--       when that side has no `var` the witness is unused.  For a schema whose
--       left-hand side contains no `var`, the enabled set at its one context
--       is a whole copy of `Tm` and every member emits the same output: the
--       fibre over an emission is infinite.  `GenerativeKernel.run-targets`
--       exhibits the two-element case of this (two histories, one target);
--       here it is unbounded.  Collapsing that fibre is the loss the carrier
--       law prices, and the reason `advance` refuses to dedupe.
------------------------------------------------------------------------

module Kernel.Vyapti_TheInstalledOperationHasNoneSoTheKernelMemorisesAndTheSchemaIsWhatMakesItGeneralise where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)

open import Kernel.RewriteCertificate
open import Kernel.ControlledGrammar
open import Kernel.GenerativeKernel
  using (direct-operation ; detour-operation)

------------------------------------------------------------------------
-- §0.  Discriminators.  Two terms are separated by a Bool-valued function
-- disagreeing on them; nothing here needs decidable equality on `Tm`.
------------------------------------------------------------------------

isAdd : Tm → Bool
isAdd (add _ _) = true
isAdd _         = false

leftIsZero : Tm → Bool
leftIsZero (add zero _) = true
leftIsZero _            = false

height : Tm → ℕ
height (suc t)   = ℕ.suc (height t)
height (add l r) = ℕ.suc (height l)
height _         = ℕ.zero

------------------------------------------------------------------------
-- §1.  THE MEMORISATION LAW.
--
-- `control-sound : {t : Tm} → Control t → t ≡ source` is the whole of it.
-- An operation's enabling evidence at t IS an identification of t with the
-- one term the operation was installed at, so the enabled set is a
-- subsingleton and the emission is a constant.  No library can be more
-- general than this, because every library is a list of these.
------------------------------------------------------------------------

fires-only-at-source :
  (op : NativeOperation) {t : Tm}
  → NativeOperation.Control op t → t ≡ NativeOperation.source op
fires-only-at-source op c = NativeOperation.control-sound op c

enabled-set-is-subsingleton :
  (op : NativeOperation) {s t : Tm}
  → NativeOperation.Control op s → NativeOperation.Control op t → s ≡ t
enabled-set-is-subsingleton op cs ct =
  NativeOperation.control-sound op cs ∙ sym (NativeOperation.control-sound op ct)

output-is-constant :
  (op : NativeOperation) {t : Tm} (c : NativeOperation.Control op t)
  → NativeOperation.apply op t c ≡ NativeOperation.target op
output-is-constant op c = refl

-- The same statement about the kernel's exported branch former: an
-- `EnabledFuture` is not a choice among contexts, it is a witness that the
-- context was already the operation's own source.
enabled-future-pins-the-seed :
  {seed : Tm} (f : EnabledFuture seed)
  → seed ≡ NativeOperation.source (EnabledFuture.operation f)
enabled-future-pins-the-seed f =
  NativeOperation.control-sound (EnabledFuture.operation f) (EnabledFuture.control f)

------------------------------------------------------------------------
-- §2.  FINITE COVERAGE OVER AN INFINITE LANGUAGE.
------------------------------------------------------------------------

SomeEnabled : List NativeOperation → Tm → Type₀
SomeEnabled []       t = ⊥
SomeEnabled (op ∷ L) t = NativeOperation.Control op t ⊎ SomeEnabled L t

sourceHeights : List NativeOperation → List ℕ
sourceHeights = map (λ op → height (NativeOperation.source op))

_∈ℕ_ : ℕ → List ℕ → Type₀
n ∈ℕ []       = ⊥
n ∈ℕ (m ∷ ms) = (n ≡ m) ⊎ (n ∈ℕ ms)

-- A library can only fire on terms whose height it already has on file.
-- This is the finiteness of the kernel's reach, and it needs no arithmetic:
-- it is §1 transported along `height`.
covered-heights-are-library-heights :
  (L : List NativeOperation) (t : Tm)
  → SomeEnabled L t → height t ∈ℕ sourceHeights L
covered-heights-are-library-heights []       t e       = e
covered-heights-are-library-heights (op ∷ L) t (inl c) =
  inl (cong height (NativeOperation.control-sound op c))
covered-heights-are-library-heights (op ∷ L) t (inr s) =
  inr (covered-heights-are-library-heights L t s)

tower : ℕ → Tm
tower ℕ.zero    = zero
tower (ℕ.suc n) = suc (tower n)

-- The kernel's own library, from GenerativeKernel: two operations with two
-- genuinely different derivations, installed at one and the same source.
kernel-library : List NativeOperation
kernel-library = direct-operation ∷ detour-operation ∷ []

-- And a term it cannot see.  `form` at this seed returns the empty list, so
-- the generative loop is not stuck here -- it has no branch to be stuck on.
kernel-cannot-reach-a-tower : SomeEnabled kernel-library (tower (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)))) → ⊥
kernel-cannot-reach-a-tower (inl p)       = true≢false (sym (cong isAdd p))
kernel-cannot-reach-a-tower (inr (inl p)) = true≢false (sym (cong isAdd p))

------------------------------------------------------------------------
-- §3.  THE SCHEMA.  Control carries a substitution witness instead of an
-- identification with a fixed source, and soundness is discharged by
-- lemmas that were already proved.
------------------------------------------------------------------------

record SchematicOperation : Type₀ where
  field
    lhs rhs : Tm
    meaning : (ρ : Env) → eval lhs ρ ≡ eval rhs ρ

  Control : Tm → Type₀
  Control t = Σ[ u ∈ Tm ] (t ≡ subVar u lhs)

  apply : (t : Tm) → Control t → Tm
  apply _ (u , _) = subVar u rhs

  -- THE PAYOFF.  Instantiation is sound for free: `eval-subVar` moves the
  -- substitution into the environment, the schema's own meaning holds at
  -- THAT environment because it holds at every one, and `eval-subVar` moves
  -- it back.  Nothing was assumed and nothing was searched for.
  apply-sound : (t : Tm) (c : Control t) (ρ : Env)
              → eval t ρ ≡ eval (apply t c) ρ
  apply-sound t (u , p) ρ =
      cong (λ q → eval q ρ) p
    ∙ eval-subVar u lhs ρ
    ∙ meaning (setX (eval u ρ) ρ)
    ∙ sym (eval-subVar u rhs ρ)

open SchematicOperation using (lhs ; rhs)

schematic-fires-at-every-instance :
  (op : SchematicOperation) (u : Tm)
  → SchematicOperation.Control op (subVar u (lhs op))
schematic-fires-at-every-instance op u = u , refl

-- The kernel's own accepted theorem, installed as a schema rather than as a
-- ground fact.  `accepted-sound` is RewriteCertificate's, unchanged.
plus-one : SchematicOperation
SchematicOperation.lhs     plus-one = add var (suc zero)
SchematicOperation.rhs     plus-one = suc var
SchematicOperation.meaning plus-one = accepted-sound

ctx₀ ctx₁ : Tm
ctx₀ = add zero (suc zero)
ctx₁ = add (suc zero) (suc zero)

ctx₀-enabled : SchematicOperation.Control plus-one ctx₀
ctx₀-enabled = zero , refl

ctx₁-enabled : SchematicOperation.Control plus-one ctx₁
ctx₁-enabled = suc zero , refl

ctx₀≢ctx₁ : ctx₀ ≡ ctx₁ → ⊥
ctx₀≢ctx₁ p = true≢false (cong leftIsZero p)

-- ONE SCHEMA, TWO CONTEXTS -- and no operation of the kernel's own kind can
-- do that for any two distinct contexts whatsoever.  This is the separation
-- the module exists to state: it is not that the current library is small,
-- it is that `NativeOperation` cannot express what `SchematicOperation`
-- expresses, and the obstruction is `control-sound`'s type.
no-native-operation-does-this :
  (op : NativeOperation)
  → NativeOperation.Control op ctx₀
  → NativeOperation.Control op ctx₁
  → ⊥
no-native-operation-does-this op c₀ c₁ =
  ctx₀≢ctx₁ (enabled-set-is-subsingleton op c₀ c₁)

------------------------------------------------------------------------
-- §4.  THE FIBRE.  When the right-hand side has no `var`, `apply` ignores
-- `u` (it computes `subVar u rhs` = rhs), so the enabled set maps
-- many-to-one onto emissions.  When the schema's left-hand side contains no
-- `var`, every substitution is enabled at one and the same context and all
-- of them emit the same term: the fibre over that emission is a whole copy
-- of `Tm`.  `GenerativeKernel.run-targets` is the two-element case of
-- exactly this, and it is why `advance` is forbidden to dedupe.
------------------------------------------------------------------------

constant-schema : SchematicOperation
SchematicOperation.lhs     constant-schema = add zero zero
SchematicOperation.rhs     constant-schema = zero
SchematicOperation.meaning constant-schema ρ = refl

every-substitution-is-enabled :
  (u : Tm) → SchematicOperation.Control constant-schema (add zero zero)
every-substitution-is-enabled u = u , refl

all-collapse-to-one-output :
  (u : Tm)
  → SchematicOperation.apply constant-schema (add zero zero)
      (every-substitution-is-enabled u)
  ≡ zero
all-collapse-to-one-output u = refl

-- Stated as the inference it licenses: knowing the emission tells you
-- nothing about which member of the enabled set produced it.
emission-does-not-determine-the-witness :
  SchematicOperation.apply constant-schema (add zero zero) (every-substitution-is-enabled zero)
  ≡ SchematicOperation.apply constant-schema (add zero zero) (every-substitution-is-enabled (suc zero))
emission-does-not-determine-the-witness = refl
