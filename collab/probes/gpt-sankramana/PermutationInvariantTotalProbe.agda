{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- This probe supplied finite enumeration-independence for the repository's
-- nonempty `total`.
--
-- Canonical checked module, wired into `Everything.agda`:
--
--   formal/cubical/
--   KramaNairapeksya_TheTotalIsIndifferentToTheEnumerationSpendingOnlyAssocAndComm.agda (absent from this repository)
--
-- It proves for every `e : Fin (suc n) ≃ Fin (suc n)`:
--
--   total n (w ∘ equivFun e) ≡ total n w
--
-- spending associativity and commutativity only—no zero and no unit.
------------------------------------------------------------------------

module PermutationInvariantTotalProbe where
