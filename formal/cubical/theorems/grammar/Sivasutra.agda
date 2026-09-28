{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Sivasutra — Pāṇini's pratyāhāra as an interval, checked.
--
-- SOURCE.  The Adhyy opens with the fourteen Mhevara / iva-stras:
-- the sounds of  laid out in ONE linear order, each stra ending in
-- an anubandha (it-marker).  A pratyhra names a class of sounds as the
-- INTERVAL from a starting sound up to (and excluding) a marker: e.g. `a`
-- = a i u; `aK` = a i u  ; `aC` = all the vowels.  This is the device
-- that lets any needed phonological class be named by two letters, and it
-- is why INDIC_FORMAL_TRADITIONS_MAP.md (absent from this repository) §1.1 records the iva-stra
-- ordering as an interval representation of an intersection-closed family
-- (Petersen's optimality theorem is that deeper object).
--
-- The first four stras, with their it-markers  K  C:
--   1.  a  i  u  
--   2.      K
--   3.  e  o  
--   4.  ai au C
-- (These four give the entire vowel system; the consonant sūtras 5–14 are
-- not encoded here.)
--
-- WHAT IS CHECKED.  The interval mechanism itself, on the vowel prefix:
-- `upto m` collects the sounds from the front up to marker m, skipping any
-- intervening markers.  The pratyhras a, aK, aC then compute to exactly
-- the traditional classes, by refl; and no it-marker ever appears in a
-- pratyhra (the anubandha is a boundary, not a member).
--
-- Contents (no postulates, no holes, --safe):
--   Sym, isMarker, sivasutra   the vowel prefix as a linear order
--   upto                       the pratyhra extractor (interval to marker)
--   a, aK, aC                 the three vowel pratyhras, each ≡ its
--                              traditional class by refl
--   marker-free                no pratyhra contains an it-marker
------------------------------------------------------------------------

module Sivasutra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_ ; true≢false)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- The sounds and it-markers of the first four stras, in iva-stra order.
------------------------------------------------------------------------

data Sym : Type where
  -- vowels (the sounds)
  a i u ṛ ḷ e o ai au : Sym
  -- it-markers (anubandhas)
  Ṇ K Ṅ C : Sym

isMarker : Sym → Bool
isMarker Ṇ = true
isMarker K = true
isMarker Ṅ = true
isMarker C = true
isMarker _ = false

-- decidable equality, as a boolean, for the stop test
eqSym : Sym → Sym → Bool
eqSym a a = true
eqSym i i = true
eqSym u u = true
eqSym ṛ ṛ = true
eqSym ḷ ḷ = true
eqSym e e = true
eqSym o o = true
eqSym ai ai = true
eqSym au au = true
eqSym Ṇ Ṇ = true
eqSym K K = true
eqSym Ṅ Ṅ = true
eqSym C C = true
eqSym _ _ = false

-- the linear order of the first four stras
sivasutra : List Sym
sivasutra = a ∷ i ∷ u ∷ Ṇ ∷ ṛ ∷ ḷ ∷ K ∷ e ∷ o ∷ Ṅ ∷ ai ∷ au ∷ C ∷ []

------------------------------------------------------------------------
-- The pratyhra extractor.  From the front, collect sounds up to (not
-- including) the marker m; any OTHER marker along the way is a boundary of
-- an earlier stra and is skipped, never emitted.  (All pratyhras here
-- begin at `a`, the head, so no start-search is needed.)
------------------------------------------------------------------------

upto : Sym → List Sym → List Sym
upto m [] = []
upto m (x ∷ xs) =
  if eqSym x m
  then []
  else (if isMarker x then upto m xs else x ∷ upto m xs)

------------------------------------------------------------------------
-- The three vowel pratyhras, each equal to its traditional class BY REFL
-- (the extractor computes).
------------------------------------------------------------------------

-- a : the sounds a i u
aṆ : upto Ṇ sivasutra ≡ a ∷ i ∷ u ∷ []
aṆ = refl

-- aK : the simple vowels a i u  
aK : upto K sivasutra ≡ a ∷ i ∷ u ∷ ṛ ∷ ḷ ∷ []
aK = refl

-- aC : ALL the vowels a i u   e o ai au
aC : upto C sivasutra ≡ a ∷ i ∷ u ∷ ṛ ∷ ḷ ∷ e ∷ o ∷ ai ∷ au ∷ []
aC = refl

-- The three nest as intervals of the one order: aṆ ⊂ aK ⊂ aC, each a
-- prefix of the next (visible directly in the refls above — the shorter
-- class is a prefix of the longer, since they share the same left endpoint
-- `a` and only the right marker moves outward).  That the class is named by
-- moving ONE endpoint along ONE linear order is the iva-stra device.

------------------------------------------------------------------------
-- EXTENSION.
-- `NonInitialPratyaharasAndOneIntersectionInstance` adds
-- the start-search this module says it does not need — "All pratyāhāras
-- here begin at `a`, the head, so no start-search is needed" — and with
-- it the two-endpoint extractor `between`.  It checks `iK`, `e`, `aiC`,
-- `iC` by refl, verifies `between a C ≡ upto C` so the extension agrees
-- with `upto` at the head, and gives one intersection instance:
-- `aK ∩ iC ≡ iK`, a named class again.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- EXTENSION: A LOWER BOUND ON THE MARKER COUNT.
-- `PratyaharaLaghava_TheMarkerCountIsForcedByTheAntichain.agda` proves, for
-- ANY linear order of the sounds and ANY placement of markers, that two
-- classes ending at the same anubandha are ⊆-comparable — so the classes
-- carried by one marker are a chain, and a ⊆-ANTICHAIN of classes forces that
-- many distinct markers.  a, iK, e, aiC are pairwise incomparable as sets,
-- hence four markers are forced; the iva-stra order names all four with
--  K  C and has no fifth, so four is the minimum and this order attains it.
--
-- What is proved is a lower bound and its attainment on the vowel subfamily.
-- `interactive/Pratyahara_TheIntervalDecisionProcedure.hs` (absent from this repository) decides nameability
-- against the line (no table) and computes the bound over all fourteen
-- stras: width 14 over the 294 classes the line can name, width 11 over the
-- ~30 the grammar uses.
------------------------------------------------------------------------
