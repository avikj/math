{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अनिर्धारित — apavāda does not shed sthūla's provenance, and that is
-- the host's thesis, not its failure.  The identity
-- apavada (sthula t) ≡ t fails: sthula t = yoga (nyasa t) (mita 0)
-- — the coarse embedding that stamps a "+0" of provenance — and apavada
-- is structural: it carries the stamp through, landing at
-- yoga' t (mita' 0), never back at t.  The host proves the two
-- embeddings न्यास and स्थूल are observationally inseparable in value
-- (nyasa-sthula-avishesha) yet distinct in cost (mulya-bheda).
-- Road two, witness cara'.
------------------------------------------------------------------------

module Ratri.Anirdharita_Nirjara_ApavadaSthula where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Nirjara_SheddingAPrimitiveCostsLaghava
  using (Laghu; cara'; mita'; yoga'; apavada; sthula)

-- The composite keeps the provenance stamp:
composite-lands : apavada (sthula cara') ≡ yoga' cara' (mita' 0)
composite-lands = refl

-- and the stamped term is not the bare variable:
isCara' : Laghu → Bool
isCara' cara'       = true
isCara' (mita' _)   = false
isCara' (yoga' _ _) = false

stamped≢bare : yoga' cara' (mita' 0) ≡ cara' → ⊥
stamped≢bare p = true≢false (cong isCara' (sym p))

-- THE VERDICT.  Green here means the field is NOT determined:
-- apavada ∘ sthula is not the identity — shedding does not remove
-- provenance, it preserves it, which is the module's own theorem
-- held from the other side.
NOT-DETERMINED : apavada (sthula cara') ≡ cara' → ⊥
NOT-DETERMINED p = stamped≢bare (sym composite-lands ∙ p)
