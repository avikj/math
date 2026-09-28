{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- लेखा — the ledger's fold.  (lekhā, "account/ledger": the term is the
-- repository's own — जीवो लेखा-धरः, saṃrakṣaṇa-sūtra २१ — chosen over a
-- Nyya attribution DELIBERATELY, see the provenance fence below.)
--
-- organism and mapped it onto the Vaieika fourfold of absence.  A
-- later audit STRUCK that mapping — "these four struck equations were
-- modern constructions, not consequences of the fourfold … the four
-- operational behaviours remain potentially useful as an independently
-- specified event algebra, but their names no longer provide evidence
-- for it.  Proof, refutation, scoped no-go, and separation must be
-- typed from the repository's own evidentiary semantics."
--
-- This module is that independently specified event algebra, checked.
-- It proves the operational claims the strike left standing, and it
-- claims NOTHING about prāgabhāva or pradhvaṃsābhāva — the struck
-- reading is quoted in ABHAVA.md (absent from this repository) where it lives, with its strike.
--
-- The theorems, in the repository's own vocabulary:
--
--   1. PENDING IS MADELESS: the pending status holds exactly on the
--      empty log.  No event sustains "not yet decided"; it is what
--      there is before any event, and one proof ends it.
--   2. REFUTATION ABSORBS: once the fold reads refuted, no later
--      event changes the reading.  A refutation cannot be outvoted
--      by enthusiasm — the absorbing law the organism's design
--      ("genuinely proven conclusions flood; refutations are
--      permanent") requires of its fold.
--   3. A BOOLEAN CANNOT CARRY IT: merge pending and refuted into one
--      "not proved" bit and no transition function on the bit can
--      simulate the fold — [] and [refute] read equal and diverge
--      under prove.  The two-valued verdict on the three-valued
--      question cannot compute the future; refuted claims would come
--      back to life.  This is the typed zero's founding defect
--      (machinery/crystal's UNDECIDED split; Saptabhangi's दुर्नयः),
--      here as a ⊥ about the ledger itself.
--
-- Provenance fence: whether this algebra matches the Vaieika
-- temporal characterisations (andi/snta for prior absence,
-- sdi/ananta for posterior) is exactly the struck question, and this
-- module supplies no evidence either way.  If someone reopens it, the
-- study to check is named in ABHAVA.md (absent from this repository) A1 (Matilal 1968).
------------------------------------------------------------------------

module Lekha_TheAppendOnlyFoldAbsorbsRefutationAndABooleanCannotCarryIt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Sigma using (Σ; _,_)

-- One claim's events.  The log grows at the head: newest first.
data Event : Type₀ where
  prove  : Event
  refute : Event

Log : Type₀
Log = List Event

-- The three-valued status — the typed zero's smallest honest form.
data Status : Type₀ where
  pending     : Status   -- no event yet
  established : Status   -- proved, not refuted
  refuted     : Status   -- refuted, permanently

-- THE FOLD.  A refutation is terminal; a proof establishes what is
-- not already dead.
step : Status → Status
step refuted = refuted
step _       = established

status : Log → Status
status []             = pending
status (refute ∷ _)   = refuted
status (prove  ∷ log) = step (status log)

-- Discriminators, for the disequalities.
isPending isRefuted : Status → Bool
isPending pending = true
isPending _       = false
isRefuted refuted = true
isRefuted _       = false

------------------------------------------------------------------------
-- 1 · pending is madeless: it holds on the empty log …
pending-unbegun : status [] ≡ pending
pending-unbegun = refl

-- … and nowhere else.  No event sustains it.
pending-forces-empty : (log : Log) → status log ≡ pending → log ≡ []
pending-forces-empty []             _ = refl
pending-forces-empty (refute ∷ _)   p = Empty.rec (true≢false (cong isRefuted p))
pending-forces-empty (prove  ∷ log) p = Empty.rec (step-never-pending (status log) p)
  where
  step-never-pending : (s : Status) → step s ≡ pending → ⊥
  step-never-pending pending     q = true≢false (cong isPending (sym q))
  step-never-pending established q = true≢false (cong isPending (sym q))
  step-never-pending refuted     q = true≢false (cong isRefuted q)

-- and one proof ends it:
pending-ends : status (prove ∷ []) ≡ established
pending-ends = refl

------------------------------------------------------------------------
-- 2 · refutation absorbs.  It never holds unbegun …
refuted-not-unbegun : status [] ≡ refuted → ⊥
refuted-not-unbegun p = true≢false (cong isPending p)

-- … it begins exactly at a refute …
refuted-begins : (log : Log) → status (refute ∷ log) ≡ refuted
refuted-begins _ = refl

-- … and whatever arrives later, it stays.  One case split.
refuted-absorbs : (log : Log) (e : Event)
  → status log ≡ refuted → status (e ∷ log) ≡ refuted
refuted-absorbs log refute _ = refl
refuted-absorbs log prove  p = cong step p

------------------------------------------------------------------------
-- 3 · a boolean cannot carry it.  Merge pending and refuted into one
-- "not proved" bit; no transition function on the bit simulates the
-- fold, because [] and [refute] read equal and diverge under prove.

boolRead : Status → Bool     -- true = "not proved"
boolRead pending     = true
boolRead established = false
boolRead refuted     = true

no-boolean-fold :
  Σ (Bool → Event → Bool)
    (λ f → (log : Log) (e : Event)
         → boolRead (status (e ∷ log)) ≡ f (boolRead (status log)) e)
  → ⊥
no-boolean-fold (f , h) = true≢false (sym on-dead ∙ on-fresh)
  where
  -- on the fresh claim, prove must send the bit true ↦ false …
  on-fresh : f true prove ≡ false
  on-fresh = sym (h [] prove)
  -- … and on the refuted claim, prove must send true ↦ true.
  on-dead : f true prove ≡ true
  on-dead = sym (h (refute ∷ []) prove)
