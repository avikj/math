{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- शेष-पूर्ति — the filling of a remainder the machine asked for itself.
--
-- interactive/sanghatta-report-latest.txt (absent from this repository) lists the non-joining critical
-- pairs of the installed rules, smallest first, and the top row is
--     x    max(x,0)
-- i.e. the rewriter cannot join x with max x 0.  This module is that pair
-- fed back as a term.
--
-- TERM.  शेष-पूर्ति, "filling of the remainder" — ordinary ,
-- compound built here.
-- The mathematics is one recursion clause of Cubical.Data.Nat.max.
------------------------------------------------------------------------

module ResiduePurti_TheMachinesTopNonJoiningPairFedBackThroughTheWarmConduit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; max)

पूर्तिः : (x : ℕ) → max x 0 ≡ x
पूर्तिः zero    = refl
पूर्तिः (suc x) = refl
