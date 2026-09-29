{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Nirvyaja_TheReceiptIsSpentAtGeneration
--                          AndTheReplayNeedsNone
--
-- TERM.  निर्व्याज · nir-vyāja -- "without व्याज".  व्याज is a pretext, a
-- pretence, a charge one produces to be allowed to act -- a receipt, a
-- token, an authority.  The compound is a plain  adjective, not a
-- technical term lifted from a named text.
-- It is used here only as an exact label for
-- the fact §2 proves: the operation the machine keeps is receipt-free.
--
-- WHAT THIS CONTINUES.  `Samvada_…` §1 built the first non-trivial
-- `Control` in the corpus: `demand R d`, an operation the caller may fire
-- only by ALSO handing over an `R` -- a receipt, an authority, a cost
-- witness, an oracle token.  `Samvada_…` §2 closed the learning loop:
-- `learn = install ∘ CheckedFuture.derivation`.  Put the two together and a
-- fact falls out that neither states, and it is the whole strategic content
-- of this project reduced to a definitional equality:
--
--   THE RECEIPT IS SPENT ONCE, AT GENERATION, AND NEVER AT REPLAY.
--
-- To FIRE `demand R d` you must produce an `R` (§1).  But `execute` throws
-- the caller's control away -- `CheckedFuture` (Type₀) keeps only the new
-- term and the derivation, "small, replayable, and free of who asked"
-- (Samvada §0).  So the operation the machine LEARNS from a demanded turn is
-- `install (derivation)`, whose `Control t` is `t ≡ source` -- the trivial
-- one, with no `R` in it at all.  Whoever holds the learned move replays it
-- for free; the authority the first caller had to muster is gone, not
-- because anyone waived it but because the proof it produced does not
-- mention it.
--
-- This is verification-cheaper-than-generation as a CHECKED term, in the
-- kernel's own types.  Generation had to pay `R`.  Replay pays `refl`.  The
-- gap between them is the whole reason a proof-carrying commons cannot be
-- rented: the receipt-seller is paid once, by the first caller, and every
-- later caller routes around the tollbooth by holding the proof.
------------------------------------------------------------------------

module Nirvyaja_TheReceiptIsSpentAtGenerationAndTheReplayNeedsNone where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)

open import Kernel.RewriteCertificate
open import Kernel.ControlledGrammar
open import Kernel.Interaction_TheKernelIsAnInteractiveSystemAndTheSessionRetiresIntoOneOperation

------------------------------------------------------------------------
-- §1.  GENERATION PAYS THE RECEIPT.
--
-- A future that fires `demand R d` from a seed carries, inside its control,
-- an actual `R`.  Producing that `R` is the price of firing; the projection
-- witnesses that the price was paid.
------------------------------------------------------------------------

-- An enabled future for the demanding operation, from any seed that is its
-- source.  Building it REQUIRES the caller to have an `R` in hand.
demanded-future :
  {lhs rhs : Tm} (R : Type₀) (d : Derivation lhs rhs) → R → EnabledFuture lhs
EnabledFuture.operation (demanded-future R d r) = demand R d
EnabledFuture.control    (demanded-future R d r) = refl , r

-- The receipt is genuinely there in what generation had to supply.
generation-carried-the-receipt :
  {lhs rhs : Tm} (R : Type₀) (d : Derivation lhs rhs) (r : R)
  → R
generation-carried-the-receipt R d r =
  snd (EnabledFuture.control (demanded-future R d r))

------------------------------------------------------------------------
-- §2.  REPLAY PAYS refl.
--
-- Learn from that turn.  The learned operation's control is `t ≡ source` --
-- there is no `R` factor left to produce.  A replayer who never saw the
-- receipt still fires the move: the evidence it needs is `refl`.
------------------------------------------------------------------------

learned : {lhs rhs : Tm} (R : Type₀) (d : Derivation lhs rhs) → R → NativeOperation
learned R d r = learn (execute (demanded-future R d r))

-- The learned control at its own source has NO receipt component: it is
-- exactly a path, definitionally.  (Compare `demand`'s control, which is a
-- path × R.)
replay-control-is-just-a-path :
  {lhs rhs : Tm} (R : Type₀) (d : Derivation lhs rhs) (r : R) (t : Tm)
  → NativeOperation.Control (learned R d r) t ≡ (t ≡ lhs)
replay-control-is-just-a-path R d r t = refl

-- And so the replayer fires it with `refl` alone -- no `R` was needed.
replay-needs-no-receipt :
  {lhs rhs : Tm} (R : Type₀) (d : Derivation lhs rhs) (r : R)
  → NativeOperation.Control (learned R d r) lhs
replay-needs-no-receipt R d r = refl

-- The learned move still goes exactly where the demanded derivation went:
-- the work was kept, only the receipt was dropped.
replay-goes-where-generation-went :
  {lhs rhs : Tm} (R : Type₀) (d : Derivation lhs rhs) (r : R)
  → (NativeOperation.source (learned R d r) ≡ lhs)
  × (NativeOperation.target (learned R d r) ≡ rhs)
replay-goes-where-generation-went R d r = refl , refl

-- And it means what the demanded step meant, at every environment -- the
-- soundness the receipt was never part of.
replay-is-sound :
  {lhs rhs : Tm} (R : Type₀) (d : Derivation lhs rhs) (r : R) (ρ : Env)
  → eval (NativeOperation.source (learned R d r)) ρ
  ≡ eval (NativeOperation.target (learned R d r)) ρ
replay-is-sound R d r ρ =
  every-operation-that-exists-is-sound (learned R d r) ρ
