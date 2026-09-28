{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheLastCutHasOneRowWhenItsSeparatorIsInhabited
--
-- `interactive/SelfArchitecture.hs` (absent from this repository) §4 states "one order-independent exact
-- fact, checked here rather than assumed":
--
--   "every topological order ends at a module with no dependents, and at
--    the cut just before that final module m the separator is exactly
--    m's direct import set while EVERY row of the cut matrix equals {m}
--    — raw width |imports(m)|, deterministic semantic width 1 … no
--    choice of order avoids paying |imports(m)| raw for a cut whose
--    semantic content is a single mode."
--
-- It checks that by computing it on its own 385-vertex instance.  The
-- statement is order-independent AND instance-independent, and §2 proves
-- it for an arbitrary import relation: the last cut has a single column,
-- so every separator row is the same row.
--
-- ────────────────────────────────────────────────────────────────────
-- AND ONE EDGE CASE THE SENTENCE GLOSSES
--
-- "deterministic semantic width 1" holds when the separator is
-- INHABITED.  If the final module imports nothing, the separator is
-- empty and there are no rows at all — width 0, not 1.  §3 states the
-- hypothesis explicitly rather than leaving it to the instance, where it
-- happens to hold.  That is not a defect of the program, which computes
-- on a graph where the final module has imports; it is the difference
-- between a computed instance and a quantified statement.
------------------------------------------------------------------------

module TheLastCutHasOneRowWhenItsSeparatorIsInhabited where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  A module graph, its reachability matrix, and the one hypothesis
--     the argument needs
------------------------------------------------------------------------

module _
  (Module : Type)
  -- v imports d directly
  (imports : Module → Module → Type)
  -- the cut matrix: K s u is true iff u transitively imports s
  (K : Module → Module → Bool)
  -- the only thing needed of K: a direct import is reached
  (directIsReached : (u s : Module) → imports u s → K s u ≡ true)
  where

  -- the separator at the last cut, where the unchecked suffix is {m}:
  -- exactly the direct imports of m
  InSeparator : Module → Module → Type
  InSeparator m s = imports m s

  --------------------------------------------------------------------
  -- 2.  Every row of the last cut is the same row
  --
  -- The suffix is a single module, so a row is one Boolean, and for a
  -- separator element that Boolean is forced to `true`.
  --------------------------------------------------------------------

  everySeparatorRowIsTrue :
    (m s : Module) → InSeparator m s → K s m ≡ true
  everySeparatorRowIsTrue m s h = directIsReached m s h

  allSeparatorRowsAgree :
    (m s t : Module) → InSeparator m s → InSeparator m t → K s m ≡ K t m
  allSeparatorRowsAgree m s t hs ht =
    everySeparatorRowIsTrue m s hs ∙ sym (everySeparatorRowIsTrue m t ht)

  --------------------------------------------------------------------
  -- 3.  Hence exactly one distinct row — under the hypothesis the
  --     sentence leaves implicit
  --------------------------------------------------------------------

  -- inhabited separator: there is a single value every row takes
  oneRowWhenInhabited :
    (m : Module) → Σ[ s ∈ Module ] InSeparator m s
    → Σ[ b ∈ Bool ] ((t : Module) → InSeparator m t → K t m ≡ b)
  oneRowWhenInhabited m _ = true , everySeparatorRowIsTrue m

  -- empty separator: there are no rows to be distinct, so the count is
  -- 0 and not 1.  Stated, not assumed away.
  noRowsWhenEmpty :
    (m : Module) → ((s : Module) → ¬ InSeparator m s)
    → (s : Module) → ¬ (Σ[ _ ∈ Bool ] InSeparator m s)
  noRowsWhenEmpty m empty s (_ , h) = empty s h

------------------------------------------------------------------------
-- 4.  What this changes about the claim
--
-- The shelf calls §4 order-independent and verifies it by computation on
-- one 385-vertex graph.  §2 shows it is also GRAPH-independent, and that
-- the whole argument uses exactly one property of the cut matrix — that
-- a direct import is reached.  Acyclicity, the topological order, and
-- the rest of the width hierarchy are not needed for this cut and are
-- not assumed.
--
-- §3 is the sharpening: "deterministic semantic width 1" is conditional
-- on the separator being inhabited, i.e. on the final module importing
-- something.  On that graph it does; as a quantified statement it must
-- be said.  A computed instance and a quantified claim differ exactly
-- here.
------------------------------------------------------------------------
