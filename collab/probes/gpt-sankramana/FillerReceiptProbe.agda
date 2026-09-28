{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- This file was the interaction object from which receipt B was derived.
-- Its last pre-closure revision supplied `refl` on each constant product
-- coordinate.  The warm kernel refused both terms, exactly and usefully:
--
--   transp (λ i → C) i0 c != c of type C
--
--   formal/cubical/
--   YugapatSankramana_TheSquaresFourEdgesAreTheCompilerPathsAndTheReceiptIsClosed.agda (absent from this repository)
--
-- That file is wired into `Everything.agda`.  It is the canonical theorem.
-- The full probe and the refused candidates remain in Git history at this
-- address; leaving their executable stale form in the live tree would invite
-- a later carrier to repeat a question the kernel has already answered.
------------------------------------------------------------------------

module FillerReceiptProbe where
