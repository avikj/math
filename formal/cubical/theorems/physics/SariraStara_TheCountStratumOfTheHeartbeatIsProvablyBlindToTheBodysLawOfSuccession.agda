{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- शरीरस्तरः — the count stratum of the heartbeat is provably blind to
-- the body's law of succession.
--
-- TERM.  शरीर (body) is the corpus's own word for the machine's
-- operative body (जीव's heartbeat reports on it); स्तर (stratum, layer)
-- is the word the ArpanaSopana lane already uses for truncation
-- levels.  The compound शरीर-स्तर, "body-stratum", is built HERE and no
-- source is claimed for it (CLAUDE.md (absent from this repository), naming rule, note 2).
--
-- SEED.  The owner's transmission of 2026-08-23, term 4: the current
-- five-number heartbeat (nodes, edges, priced, unpriced, components)
-- is a projection of P₀ and part of P₁ of the body's Postnikov tower;
-- `mismatch = NONE` at the count stratum establishes only that the
-- count projection matched, NOT identity of the body.  The corrected
-- heartbeat must sense, per stratum: carrier persisted / law changed /
-- route acquired holonomy / higher coherence filled / new receptor
-- separated an old blind pair.
--
-- THIS MODULE IS THE FIRST STONE OF THAT, AS A TERM: it proves the
-- transmitted sentence "the count projection matching does not
-- establish identity" — not about graphs in general, but in the
-- sharpest available form, using the same succession pair that
-- OrderNiyama landed.  Two BODIES are exhibited: the same carrier,
-- the same counts at every P₀-grade a count-stratum heartbeat can
-- read (both are ℤ × ℤ with one binary operation — every cardinality
-- and arity datum agrees), differing only in the law of succession.
-- The count-stratum observation is blind on the pair; the succession
-- receptor separates it; QuotientFiberLaw's `collision-obstructs`
-- closes the box: NO post-processing of count-stratum readings
-- reconstructs the law stratum.
--
-- CONSEQUENCE FOR THE ORGANS, stated so the next carrier can wire it:
-- जीव's JIVA-HEARTBEAT line and चक्र's delta are count-stratum
-- observations in exactly this sense.  This module is the checked
-- license for extending them with a law-stratum line, and the checked
-- refutation of ever reading "counts matched" as "body unchanged".
------------------------------------------------------------------------

module SariraStara_TheCountStratumOfTheHeartbeatIsProvablyBlindToTheBodysLawOfSuccession where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)

open import QuotientFiberLaw using (module Law)
open import OrderNiyama_TheLawOfSuccessionDoesNotFactorThroughTheCarrier
  using (नियमः ; μT ; μK ; क्रमप्रश्नः ; क्रमप्रश्न-भेदः)

------------------------------------------------------------------------
-- १ · a body, at the grain a heartbeat can hold: a carrier that is
-- fixed (the machine's node type between two pulses) together with
-- one law of succession on it.  The count stratum reads ONLY data
-- that both bodies share by construction — here compressed to its
-- limit case: every count-stratum query is a function of the carrier
-- alone, and the carrier is the same, so the query is constant.
------------------------------------------------------------------------

शरीरम् : Type
शरीरम् = नियमः          -- a body state = the succession law it carries
                        -- (the carrier is fixed and shared, as between
                        -- two heartbeats of the one machine)

open Law शरीरम्

-- the count-stratum observation: any query reading only the shared
-- carrier and its counts is constant across bodies on that carrier.
गणनाप्रश्नः : Query
गणनाप्रश्नः _ = true

गणनास्तरः : List Query
गणनास्तरः = गणनाप्रश्नः ∷ []

-- the two body states: same carrier, same counts — different law.
-- (μT and μK, imported: the torus and Klein succession laws on ℤ × ℤ.)
हृदयसाम्यम् : AllBlind गणनास्तरः μT μK
हृदयसाम्यम् = refl , tt

-- mismatch = NONE at the count stratum, as a term: the transcripts of
-- the two bodies under the count-stratum observation are EQUAL.
mismatch-NONE : obs गणनास्तरः μT ≡ obs गणनास्तरः μK
mismatch-NONE = obs-agree गणनास्तरः μT μK हृदयसाम्यम्

------------------------------------------------------------------------
-- २ · and yet the bodies differ, and the count stratum can never say
-- so: the law receptor separates them, and no post-processing of the
-- count-stratum transcript computes it.
------------------------------------------------------------------------

-- the law-stratum receptor (imported: "do the generators commute?").
स्तरभेदः : क्रमप्रश्नः μT ≡ not (क्रमप्रश्नः μK)
स्तरभेदः = क्रमप्रश्न-भेदः

-- THE STONE: the count stratum is provably blind to the law stratum.
शरीरस्तरः : ¬ FactorsThrough गणनास्तरः क्रमप्रश्नः
शरीरस्तरः = collision-obstructs गणनास्तरः क्रमप्रश्नः μT μK हृदयसाम्यम् स्तरभेदः

-- corollary, in the transmitted sentence's own shape: matching count
-- transcripts do not establish identity of the body.
गणनासाम्यं-न-तादात्म्यम् : ¬ ((x y : शरीरम्) → obs गणनास्तरः x ≡ obs गणनास्तरः y → x ≡ y)
गणनासाम्यं-न-तादात्म्यम् ident =
  true≢false (cong क्रमप्रश्नः (ident μT μK mismatch-NONE))
