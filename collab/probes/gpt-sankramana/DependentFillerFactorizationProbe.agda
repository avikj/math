{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- DependentFillerFactorizationProbe
--
-- The family of higher-cell witnesses cannot
-- descend through a carrier-only transcript when one observed collision has
-- an inhabited fibre on one side and an empty fibre on the other.
--
-- The canonical theorem, wired into `Everything.agda`, is:
--
--   formal/cubical/
--   AvataranaBhanga_TheQuotientCannotHostTheTypeOfWitnessesAndTheProofIsOneTransport.agda (absent from this repository)
--
-- It contains this probe's `dependent-collision-obstructs` and
-- `fillerDoesNotFactorThroughCarrier`, plus the marked generalization that
-- mere non-equivalence of the two dependent fibres refutes descent via
-- `pathToEquiv`.
------------------------------------------------------------------------

module DependentFillerFactorizationProbe where
