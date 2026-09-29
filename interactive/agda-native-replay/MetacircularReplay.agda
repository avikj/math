{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

-- Integration against the actual native kernel.
module MetacircularReplay where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as Nat
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)

open import Kernel.RewriteCertificate
open import Kernel.ControlledGrammar
import Kernel.GenerativeKernel as Example
import Kernel.Interaction_TheKernelIsAnInteractiveSystemAndTheSessionRetiresIntoOneOperation as Dialogue
import TheGenerativeLoopOnTheKernelsOwnTermsACertifiedNormalizerEmitsDerivationsSoLearnCallsInstall as Normalize

future : {a b : Tm} → Derivation a b → EnabledFuture a
EnabledFuture.operation (future d) = install d
EnabledFuture.control   (future d) = refl

receipt : {a b : Tm} → Derivation a b → CheckedFuture a
receipt d = execute (future d)

receipt-target : {a b : Tm} (d : Derivation a b)
  → CheckedFuture.target (receipt d) ≡ b
receipt-target d = refl

receipt-trace : {a b : Tm} (d : Derivation a b)
  → CheckedFuture.derivation (receipt d) ≡ d
receipt-trace {a} {b} d = substRefl {B = λ q → Derivation q b} d

learned : {a b : Tm} → Derivation a b → NativeOperation
learned d = Dialogue.learn (receipt d)

learned-trace : {a b : Tm} (d : Derivation a b)
  → NativeOperation.checked (learned d) ≡ d
learned-trace d = receipt-trace d

normalizing-future : (t : Tm) → EnabledFuture t
EnabledFuture.operation (normalizing-future t) = Normalize.learn t
EnabledFuture.control   (normalizing-future t) = refl

normalizing-session : Tm → Dialogue.Session
normalizing-session t =
  Dialogue.step (Dialogue.begin t) (normalizing-future t)

one-operation-learned : (t : Tm)
  → length (Dialogue.Session.library (normalizing-session t)) ≡ 1
one-operation-learned t = refl

session-target : (t : Tm)
  → Dialogue.Session.here (normalizing-session t) ≡ Normalize.normalForm t
session-target t = refl

retired-future : (S : Dialogue.Session)
  → EnabledFuture (Dialogue.Session.origin S)
EnabledFuture.operation (retired-future S) = Dialogue.retire S
EnabledFuture.control   (retired-future S) = refl

replay-session : (S : Dialogue.Session)
  → CheckedFuture (Dialogue.Session.origin S)
replay-session S = execute (retired-future S)

replay-session-target : (S : Dialogue.Session)
  → CheckedFuture.target (replay-session S) ≡ Dialogue.Session.here S
replay-session-target S = refl

replay-session-trace : (S : Dialogue.Session)
  → CheckedFuture.derivation (replay-session S) ≡ Dialogue.Session.trace S
replay-session-trace S =
  substRefl {B = λ q → Derivation q (Dialogue.Session.here S)} (Dialogue.Session.trace S)

base-step-count : {a b : Tm} → Derivation a b → ℕ
base-step-count (done _) = 0
base-step-count (then-step _ d) = Nat.suc (base-step-count d)

replay-preserves-base-step-count : (S : Dialogue.Session)
  → base-step-count (CheckedFuture.derivation (replay-session S))
    ≡ base-step-count (Dialogue.Session.trace S)
replay-preserves-base-step-count S =
  cong base-step-count (replay-session-trace S)

branches : List (EnabledFuture Example.seed)
branches = future Example.direct-history ∷ future Example.detour-history ∷ []

two-branches : length (advance branches) ≡ 2
two-branches = refl

direct-base-steps : base-step-count Example.direct-history ≡ 2
direct-base-steps = refl

detour-base-steps : base-step-count Example.detour-history ≡ 4
detour-base-steps = refl

sample : Tm
sample = add (add var (suc zero)) (suc (suc zero))

sample-target : Normalize.normalForm sample ≡ suc (suc (suc var))
sample-target = refl

sample-base-steps : base-step-count (Normalize.normalize sample) ≡ 5
sample-base-steps = refl

sample-sound : (ρ : Env)
  → eval sample ρ ≡ eval (suc (suc (suc var))) ρ
sample-sound = Normalize.normalize-sound sample
