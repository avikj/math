{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AbhavaAvacchedaka — Navya-Nyāya absence, with the limitor as a genuine
-- dependent binder (not an optional field).
--
-- SOURCE.  In Navya-Nyya (Gagea, Tattvacintmai, 14th c.; Raghuntha)
-- an absence (abhva) is not a property a thing lacks; it is a relational
-- entity with named slots:
--   pratiyogin  — the counterpositive: the thing that is absent;
--   anuyogin    — the locus: where it is absent;
--   avacchedaka — the LIMITOR: the mode/aspect under which the
--                 counterpositive is taken.
-- The operative doctrine (ABHAVA.md (absent from this repository) §1): CHANGE THE LIMITOR AND YOU CHANGE
-- THE ABSENCE.  "The absence of THIS pot" and "the absence of POTS AS SUCH"
-- are different absences with different truth conditions.
--
-- THE POINT, per this repository's own naming audit
-- (INDIC_FORMAL_TRADITIONS_MAP.md (absent from this repository) §3.3, §6.3): the tradition's own
-- formalizers — Ganeri, Bhattacharyya, and Panday–Ghosh (Cubical Type
-- Theoretic Navya-Nyāya) — establish that the avacchedaka delimiting a
-- pratiyogin is a TYPE-LEVEL BINDER, not a free variable, which is exactly
-- why higher-order logic cannot hold it and a dependent Π can.  The repo's
-- existing "index" lane runs the WEAK version (the limitor as an optional
-- field, its audit reporting zero live originating sites).  This file
-- supplies the core of the strong version in the declared substrate: the
-- limitor as a genuine dependent parameter, and the theorem that it is
-- LOAD-BEARING — the absence is a real function of the limitor, so any
-- account that drops it conflates distinct absences.
--
-- Contents (no postulates, no holes, --safe):
--
--   Absence          the abhva as a dependent record: an anuyogin (locus),
--                    a pratiyogin indexed by the avacchedaka (limitor), and
--                    the holding of the absence under a given limitor
--   holds            the absence-under-α: nothing in the locus bears the
--                    counterpositive under limitor α  ((x : ℓ) → ¬ P α x)
--   limitor-load-bearing
--                    a concrete abhva whose absence HOLDS under one limitor
--                    and FAILS under another — so the limitor cannot be
--                    dropped; "change the limitor, change the absence",
--                    exhibited, refuting the limitor-free reading
------------------------------------------------------------------------

module AbhavaAvacchedaka where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The abhva, with the avacchedaka as a genuine dependent binder.
------------------------------------------------------------------------

-- An absence structure: a locus (anuyogin), a set of limitors
-- (avacchedaka), and the counterpositive (pratiyogin) as a family DEPENDENT
-- on the limitor — "x bears the counterpositive, taken under limitor α".
record Abhava : Type₁ where
  field
    anuyogin    : Type                       -- the locus
    avacchedaka : Type                       -- the limitors (modes)
    pratiyogin  : avacchedaka → anuyogin → Type
                                             -- x bears the counterpositive
                                             -- UNDER limitor α  (dependent)

open Abhava public

-- the absence, taken under a given limitor: nothing in the locus bears the
-- counterpositive under α.  The limitor α is a real parameter here — a
-- dependent binder over the pratiyogin, not a discardable tag.
holds : (A : Abhava) → A .avacchedaka → Type
holds A α = (x : A .anuyogin) → ¬ (A .pratiyogin α x)

------------------------------------------------------------------------
-- The limitor is load-bearing.  A concrete abhva on the two-point locus
-- with two limitors, where the SAME locus and SAME counterpositive-family
-- give an absence that HOLDS under one limitor and FAILS under the other.
-- So the absence is a genuine function of the avacchedaka: drop it and you
-- conflate two distinct absences.  This is "change the limitor, change the
-- absence", as a theorem — and the exact thing a limitor-free ¬ cannot see.
------------------------------------------------------------------------

-- locus = Bool, limitors = Bool.  Counterpositive under α at x: holds iff
-- α is `true` and x is `true`.  So under limitor `false` nothing bears it
-- (absence holds); under limitor `true` the point `true` bears it (absence
-- fails).
example : Abhava
example .anuyogin    = Bool
example .avacchedaka = Bool
example .pratiyogin α x = (α ≡ true) × (x ≡ true)

limitor-load-bearing :
    (holds example false)              -- absence HOLDS under limitor `false`
  × (¬ (holds example true))           -- absence FAILS under limitor `true`
limitor-load-bearing =
    (λ x aα → true≢false (sym (aα .fst)))   -- α≡true is false when α=false
  , (λ h → h true (refl , refl))            -- at α=true, x=true bears it

------------------------------------------------------------------------
-- This record delimits the pratiyogin and leaves the anuyogin bare.
-- `INDIC_FORMAL_TRADITIONS_MAP.md` (absent from this repository) §3.3 names that as half of a gap: in
-- Navya-Nyya the pratiyogit and the anuyogit carry DISTINCT
-- avacchedakas.  The second slot is added, and proved not derivable from
-- the first, in
-- `TheAnuyogitaAvacchedakaIsADistinctSlot`, whose
-- `reduct : Abhava₂ → Abhava` lands exactly in this record.
--
-- That module's `oneSlot→twoSlot` shows `holds` here implies the
-- two-slot verdict at every locus limitor, with no hypothesis; the
-- converse needs the locus limitor to be total, i.e. inert.  So this
-- module's `holds` is not a weaker notion — it is the stronger demand,
-- and what it lacks is the ability to state the delimited one.
------------------------------------------------------------------------
