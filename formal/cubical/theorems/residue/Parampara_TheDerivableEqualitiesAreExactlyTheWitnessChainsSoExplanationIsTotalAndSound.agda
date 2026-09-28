{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- परम्परा — the unbroken lineage of transmission.  The e-graph's proof
-- forest (runtime/kernel/egraph.py (absent from this repository), L2: "every union stores the
-- justification, so any derived equality can emit a checkable path") rests
-- on one theorem, declared there and proved here:
--
--     the EQUIVALENCE CLOSURE of the axiom set coincides exactly with
--     the ZIGZAG CHAINS of justified steps.
--
--   • COMPLETE (§2): every derivable equality — built from axioms by
--     refl, sym, trans, the operations the union-find performs — flattens
--     to a chain of steps, each one axiom used forward or backward.  This
--     is explain()'s totality: whatever the e-graph merged, a path can be
--     emitted.  sym is chain reversal, trans is concatenation: the proof
--     forest needs to store only the steps, because the derivation
--     structure above them is recoverable bureaucracy.
--
--   • SOUND (§1): every chain folds back into a derivation — an emitted
--     path certifies nothing but a derivable equality.
--
-- So "derived in the court" and "transmitted through an unbroken lineage
-- of witnessed steps" are one relation — paramparā: each link cites its
-- witness, forward or backward, and nothing else is needed.  Nothing here
-- is about hash-consing or find(): this is the invariant that LICENSES
-- storing a forest of justifications instead of whole derivations.
------------------------------------------------------------------------

module Parampara_TheDerivableEqualitiesAreExactlyTheWitnessChainsSoExplanationIsTotalAndSound where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; _,_)

private
  variable
    ℓ ℓ' : Level

module _ {A : Type ℓ} (R : A → A → Type ℓ') where

  -- what the e-graph DERIVES: the equivalence closure of the axioms.
  data Derives : A → A → Type (ℓ-max ℓ ℓ') where
    ax     : ∀ {x y} → R x y → Derives x y
    drfl   : ∀ {x} → Derives x x
    dsym   : ∀ {x y} → Derives x y → Derives y x
    dtrans : ∀ {x y z} → Derives x y → Derives y z → Derives x z

  -- what explain() EMITS: a chain of steps, each one axiom cited
  -- forward or backward, endpoints composing.
  data Chain : A → A → Type (ℓ-max ℓ ℓ') where
    nil : ∀ {x} → Chain x x
    fwd : ∀ {x y z} → R x y → Chain y z → Chain x z
    bwd : ∀ {x y z} → R y x → Chain y z → Chain x z

  ------------------------------------------------------------------
  -- chain algebra: concatenation and reversal.
  append : ∀ {x y z} → Chain x y → Chain y z → Chain x z
  append nil        c = c
  append (fwd r c₁) c = fwd r (append c₁ c)
  append (bwd r c₁) c = bwd r (append c₁ c)

  flip : ∀ {x y} → Chain x y → Chain y x
  flip nil        = nil
  flip (fwd r c) = append (flip c) (bwd r nil)
  flip (bwd r c) = append (flip c) (fwd r nil)

  ------------------------------------------------------------------
  -- §1 · SOUND: an emitted chain certifies a derivable equality.
  sound : ∀ {x y} → Chain x y → Derives x y
  sound nil        = drfl
  sound (fwd r c) = dtrans (ax r) (sound c)
  sound (bwd r c) = dtrans (dsym (ax r)) (sound c)

  ------------------------------------------------------------------
  -- §2 · COMPLETE: every derivation flattens to a chain — explain() is
  -- total.  sym becomes reversal, trans becomes concatenation: the
  -- forest keeps the steps, the derivation tree above them is free.
  complete : ∀ {x y} → Derives x y → Chain x y
  complete (ax r)        = fwd r nil
  complete drfl          = nil
  complete (dsym d)      = flip (complete d)
  complete (dtrans d e)  = append (complete d) (complete e)

  ------------------------------------------------------------------
  -- the two relations are one: derivable ⟺ transmitted through an
  -- unbroken witnessed lineage.
  parampara : ∀ {x y} → (Derives x y → Chain x y) × (Chain x y → Derives x y)
  parampara = complete , sound
