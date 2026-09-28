{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अङ्कपाशः — अङ्कानां पाशः ।
-- (aṅkapāśa: "the net of digits" — the counting of arrangements.)
--
-- THE TERM, ITS TEXT AND ITS DATE.  `अङ्कपाश` is the name of the section
-- on permutations in Bhskara II, *Llvat* (1150 CE): the arrangements
-- of n distinct digits number the product 1·2⋯n.  The metrical material is Pigala,
-- *छन्दःशास्त्रम्* ८.२४–२८ (~300 BCE): the प्रस्तार, and सङ्ख्या, the
-- प्रत्यय that asks how many.
--
------------------------------------------------------------------------
-- WHAT THIS MODULE IS.
--
-- `machine/Setubandha_TheCheckedIdentificationsAreEdgesAndTheIsolatedNodes
-- AreTheFrontier.hs` (absent from this repository) reports `Decategorification.π₀FinSet`
-- at degree 1: joined to the hub `ℕ` and to nothing else.  It is at
-- distance 2 from
-- `Pingala.छन्दस्`:
--
--       Pingala.छन्दस्  ──[ Pingala.छन्दस्≃ℕ ]──  ℕ
--                       ──[ Decategorification.ℕ≃π₀FinSet ]──  π₀FinSet
--
-- ONE DIFFERENCE FROM THE OTHER TWO CAUSEWAYS, and it is why this file
-- says `≃` where they said `≡`.  `π₀FinSet : Type₁` and `छन्दस् : Type₀`
-- live in DIFFERENT UNIVERSES, so `ua` is unavailable and there is no
-- path to transport along — the graph program already records only an
-- `[equiv]` for `ℕ≃π₀FinSet` and no `[path]`.  The route is therefore
-- composed with `compEquiv` rather than `_∙_`, and what it carries is
-- carried by composition of equivalences, not by `subst`.  Naming that
-- limit is part of the result: a causeway across a universe boundary is
-- narrower than one within a universe, and reporting it as the same
-- thing would be the overstatement this corpus keeps catching.
--
-- NOTHING BELOW IS CONSTRUCTED BY HAND.  No induction over छन्दस्, no
-- case split on लघु/गुरु, no permutation is ever written down.  Every
-- theorem is `compEquiv` of equivalences somebody else checked, or an
-- instance of one of them.
--
-- THE THREE THINGS THE ROUTE CARRIES.
--
--   १  A metre NAMES a finite set, and Piṅgala's सङ्ख्या is that set's
--      cardinality.  `card-Fin` is `refl`, so the naming map needs no
--      coherence lemma at all.
--
--   २  TWO METRES ARE ONE METRE EXACTLY WHEN THE SETS THEY NAME ARE
--      MERELY EQUAL.  `Decategorification.card≡MereEq` is the general
--      statement; instantiated at the metres it becomes Pigala's own
--      uniqueness theorem `मूल्य-एकैकम्` read one level up, and the two
--      compose into a decategorification statement about छन्दस् that
--      neither file states.
--
--   ३  WHAT THE NUMBER FORGETS IS BHĀSKARA'S PRODUCT.  The loop at the
--      component a metre names is the symmetric group on its सङ्ख्या
--      letters (`FinSetLoop≃Sym`), and that group is enumerated by
--      `SymmetryEnumeration.symmetryEnum` as `Fin (n !)`.  Composing:
--      the metre of value n has exactly n! loops — Piṅgala's प्रस्तार
--      index on one side, the अङ्कपाश count on the other, and no term in
--      this file does any counting.
------------------------------------------------------------------------

module Ankapasa_TheMetreNamesAFiniteSetAndTheLoopsOfThatSetAreTheFactorial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; compEquiv ; invEq)
open import Cubical.Data.Nat using (ℕ ; _!)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.FinSet using (FinSet ; card)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

open import Pingala using (छन्दस् ; मूल्य ; अनुक्रम ; मूल्य-एकैकम् ; छन्दस्≃ℕ)
open import Decategorification
  using (𝔽 ; card-Fin ; card≡MereEq ; FinSetLoop≃Sym ; π₀FinSet ; ℕ≃π₀FinSet)
open import SymmetryEnumeration using (symmetryEnum)

------------------------------------------------------------------------
-- ० · THE ROUTE.  Two checked equivalences, composed.  `compEquiv` and
--     not `_∙_`, because the two endpoints are in different universes
--     and there is no path to compose.
------------------------------------------------------------------------

छन्दस्≃π₀FinSet : छन्दस् ≃ π₀FinSet
छन्दस्≃π₀FinSet = compEquiv छन्दस्≃ℕ ℕ≃π₀FinSet

------------------------------------------------------------------------
-- १ · A METRE NAMES A FINITE SET, AND सङ्ख्या IS ITS CARDINALITY.
--
--     `card-Fin` is `refl`, so this needs no coherence lemma: the
--     cardinality of the set a metre names is its प्रस्तार-index on the
--     nose.
------------------------------------------------------------------------

नामकः : छन्दस् → FinSet ℓ-zero
नामकः ds = 𝔽 (मूल्य ds)

सङ्ख्या-कार्ड् : (ds : छन्दस्) → card (नामकः ds) ≡ मूल्य ds
सङ्ख्या-कार्ड् ds = card-Fin (मूल्य ds)

------------------------------------------------------------------------
-- २ · DECATEGORIFICATION, READ ON PIṄGALA.
--
--     `card≡MereEq` says a numeral is a name for a connected component:
--     equality of cardinalities IS mere equality in FinSet.  At the sets
--     two metres name, that becomes a statement about metres, and
--     composing it with Pigala's own injectivity theorem gives what
--     neither file states — two metres coincide exactly when the finite
--     sets they name are merely equal.
------------------------------------------------------------------------

छन्द-समता : (d e : छन्दस्)
          → (मूल्य d ≡ मूल्य e) ≃ ∥ नामकः d ≡ नामकः e ∥₁
छन्द-समता d e = card≡MereEq (नामकः d) (नामकः e)

छन्द-एकैकम् : (d e : छन्दस्) → ∥ नामकः d ≡ नामकः e ∥₁ → d ≡ e
छन्द-एकैकम् d e t = मूल्य-एकैकम् d e (invEq (छन्द-समता d e) t)

------------------------------------------------------------------------
-- ३ · अङ्कपाशः — WHAT THE NUMBER FORGETS.
--
--     `Decategorification` says the loop at a component is the symmetric
--     group; `SymmetryEnumeration` says that group has n! elements.
--     Neither mentions a metre.  Composed at `मूल्य ds`, they say: the
--     metre of प्रस्तार-index n carries exactly n! rearrangements —
--     Bhskara's product, arriving at Pigala's enumeration by
--     composition and by nothing else.
--
--     अङ्कपाशः प्रस्तारस्य स्थानाङ्केन मीयते ।
------------------------------------------------------------------------

छन्दो-भ्रमणम् : (ds : छन्दस्)
             → (नामकः ds ≡ नामकः ds) ≃ Fin ((मूल्य ds) !)
छन्दो-भ्रमणम् ds =
  compEquiv (FinSetLoop≃Sym (मूल्य ds)) (symmetryEnum (मूल्य ds))

-- The next row of the प्रस्तार adds one letter, and the अङ्कपाश count of
-- the next row is therefore the count of this one times the new index.
-- Stated, not proved arithmetically: the equivalence below is the SAME
-- construction at the successor's value, and its codomain is where the
-- factorial recurrence lives.
अनुक्रमस्य-भ्रमणम् : (ds : छन्दस्)
                   → (नामकः (अनुक्रम ds) ≡ नामकः (अनुक्रम ds))
                   ≃ Fin ((मूल्य (अनुक्रम ds)) !)
अनुक्रमस्य-भ्रमणम् ds = छन्दो-भ्रमणम् (अनुक्रम ds)
