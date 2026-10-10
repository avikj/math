{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Listening where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_ ; invEquiv)
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv)
open import Cubical.Data.Unit using (Unit ; isContrUnit)

private
  variable
    ℓ : Level

-- an interaction: each state poses a question — the signals it is
-- receptive to — and the action consumes the answer.
record Interaction (X : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Q : X → Type ℓ
    δ : (x : X) → Q x → X
open Interaction

module _ {X : Type ℓ} (I : Interaction X) where

  -- the run: a now, a receipt that now is the official state, the
  -- answer received, and the rest from the answered successor.  Total
  -- and guarded: an unbounded conversation is represented, never
  -- executed.
  record Run (x : X) : Type ℓ where
    coinductive
    field
      now  : X
      here : now ≡ x
      ans  : Q I x
      next : Run (δ I x ans)

  -- the environment's bare contribution: the signals, forever.
  record Signals (x : X) : Type ℓ where
    coinductive
    field
      ans  : Q I x
      more : Signals (δ I x ans)

  forgetStates : {x : X} → Run x → Signals x
  Signals.ans  (forgetStates e) = Run.ans e
  Signals.more (forgetStates e) = forgetStates (Run.next e)

  replay : (x : X) → Signals x → Run x
  Run.now  (replay x a) = x
  Run.here (replay x a) = refl
  Run.ans  (replay x a) = Signals.ans a
  Run.next (replay x a) = replay (δ I x (Signals.ans a)) (Signals.more a)

  replay-forget : {x : X} (e : Run x) → replay x (forgetStates e) ≡ e
  Run.now  (replay-forget e i) = Run.here e (~ i)
  Run.here (replay-forget e i) = λ j → Run.here e (~ i ∨ j)
  Run.ans  (replay-forget e i) = Run.ans e
  Run.next (replay-forget e i) = replay-forget (Run.next e) i

  forget-replay : {x : X} (a : Signals x) → forgetStates (replay x a) ≡ a
  Signals.ans  (forget-replay a i) = Signals.ans a
  Signals.more (forget-replay a i) = forget-replay (Signals.more a) i

  -- THE THEOREM.  The receptor's history is exactly the signals it
  -- received: the states are receipts, and receipts weigh nothing.
  runIsItsSignals : (x : X) → Run x ≃ Signals x
  runIsItsSignals x = isoToEquiv (iso forgetStates (replay x) forget-replay replay-forget)

  -- silence of questions is determinism: if there is nothing to be
  -- receptive to, there is one history.
  module _ (Qc : (x : X) → isContr (Q I x)) where

    mute : (x : X) → Signals x
    Signals.ans  (mute x) = fst (Qc x)
    Signals.more (mute x) = mute (δ I x (fst (Qc x)))

    signalsUnique : {x₀ x₁ : X} (p : x₀ ≡ x₁) (a₀ : Signals x₀) (a₁ : Signals x₁)
                  → PathP (λ i → Signals (p i)) a₀ a₁
    Signals.ans  (signalsUnique p a₀ a₁ i) =
      isProp→PathP (λ i → isContr→isProp (Qc (p i))) (Signals.ans a₀) (Signals.ans a₁) i
    Signals.more (signalsUnique p a₀ a₁ i) =
      signalsUnique
        (λ i → δ I (p i)
                 (isProp→PathP (λ i → isContr→isProp (Qc (p i)))
                               (Signals.ans a₀) (Signals.ans a₁) i))
        (Signals.more a₀) (Signals.more a₁) i

    oneSignalStream : (x : X) → isContr (Signals x)
    oneSignalStream x = mute x , signalsUnique refl (mute x)

    silenceIsDeterminism : (x : X) → isContr (Run x)
    silenceIsDeterminism x =
      isOfHLevelRespectEquiv 0 (invEquiv (runIsItsSignals x)) (oneSignalStream x)

-- the closed machine: the interaction with nothing to ask.
closed : {X : Type} → (X → X) → Interaction X
closed f .Q _   = Unit
closed f .δ x _ = f x

closedHasOneRun : {X : Type} (f : X → X) (x : X) → isContr (Run (closed f) x)
closedHasOneRun f = silenceIsDeterminism (closed f) (λ _ → isContrUnit)
