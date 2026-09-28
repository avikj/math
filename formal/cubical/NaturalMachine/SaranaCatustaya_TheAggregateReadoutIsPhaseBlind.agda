{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सारणाचतुष्टय — the aggregate readout is phase-blind; the labelled one is not
--
-- Handle: cf-tessera-e-0.
--
-- SOURCE, WITH TEXT AND DATE.
--
--   Bharata, *Nāṭyaśāstra* ch. 28 (c. 200 BCE – 200 CE).  The 22 śrutis of
--   the octave are established by the *sra* procedure: two vs tuned
--   identically, one of them (the *cal*, moving) displaced by one ruti at
--   a time while the other (the *dhruv*, fixed) is held, and the
--   coincidences between the two instruments observed.  The fourfold form,
--   *sra-catuaya*, is set out in Abhinavagupta's *Abhinavabhrat*
--   (c. 1000 CE) at N 28.26.  rgadeva, *Sagtaratnkara* I
--   (c. 1210–1247 CE), tabulates the resulting 4-3-2-4-4-3-2 division of
--   the 22.  Matanga, *Bṛhaddeśī* (c. 6th–8th c. CE), carries the same
--   gamut into the de repertoire.
--
--   The technical fact this file takes from the procedure, and only this:
--   the experiment is run with TWO instruments.  A single v, however
--   long it is played, cannot report its own displacement; what reports it
--   is a second instrument holding the un-displaced state, read position
--   by position.  The theorems below are that statement, made exact.
--
-- WHAT IS CLAIMED OF THE SOURCE.
--   That the *Nyastra*'s procedure requires a second, held instrument
--   and a per-position comparison, and that the text records the counts of
--   coincidences rather than an aggregate.
--
-- PRIOR ART IN THIS REPOSITORY:
--   `NaturalMachine.ApavadaVisaya_TheLineWorldCorollaryPinsItsObservableUpToScalar`
--   and collab/messages/2041 (cf-tessera-2) already carry the *Nyastra*,
--   the *Sagtaratnkara* and the sra under the **gcd law**: which
--   chains of a fixed interval close early and which exhaust the cycle.
--   That is the ORBIT question.  This file is the VISIT-COUNT question,
--   which is disjoint from it: how often each position is struck in `n`
--   steps, and what a readout of that data does and does not determine.
--   `notes/SEED78_THE_CYCLOTOMIC_COMMA.md` (absent from this repository) carries the Pythagorean comma as
--   an exact lattice residue; nothing here touches it.
--
-- THE CORPUS OBJECT BEING CHECKED.
--
--   `collab/upstream/raw/2026-08-16-packages/EGB_COMPREHENSIVE_INDEX_V3_PACKAGE/`
--   `EGB_REPETITION_STRUCTURE_REVERIFY_V3.json` (absent from this repository) reports, of the artifact
--   `ETERNAL_GOLDEN_BRAID_100K_FIELD_BOOK_DELTA_36_2026-08-14.md` (absent from this repository)
--   (312254 bytes, 7242 lines, 450 numbered diamonds):
--
--       template_cycle_length : 24
--       template_counts       : 1..18 ↦ 19,  19..24 ↦ 18
--
--   with the note "Every byte reparsed in V3".  `readout-phase-0` below is
--   that count vector, obtained by walking a 24-position cycle 450 times.
--   The same file reports of the sibling artifact (5731414 bytes, 169202
--   lines, 1200 numbered stanzas) `unique_normalized_body_count : 1`.
--
-- THE TWO METHOD LENSES, AND WHICH ONE THIS FILE DECIDES FOR.
--
--   Darwin — variation plus selection plus time explains the appearance of
--   design.  Ashby — a regulator must have at least as much variety as
--   what it regulates.  On the drawn material the two disagree, and the
--   disagreement is sharp on `machine/race-variants.sh` (absent from this repository), whose own footer
--   prints "PRIMARY METRIC DID NOT SEPARATE THE VARIANTS" and, separately,
--   that the kernel gate "certifies by `refl` over {0, s, +, *} only".
--   Darwin's lens reads a flat table as a shortage of variation or of
--   time, and prescribes more variants and more rounds.  Ashby's lens says
--   the prescription cannot work: the SELECTOR's output has variety one
--   (every arm scores known=0), and a one-valued readout regulates nothing
--   however rich the thing being read.  `sarana-total` is that objection
--   made into a theorem — the aggregate is invariant under the
--   displacement FOR EVERY `n`, so no budget of steps makes it informative
--   — and `readout-separates` is the matching positive half: the labelled,
--   per-position readout does see the displacement.  Ashby wins here.
------------------------------------------------------------------------

module NaturalMachine.SaranaCatustaya_TheAggregateReadoutIsPhaseBlind where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; snotz)
open import Cubical.Data.Nat.Properties using (+-zero ; +-suc ; +-comm ; +-assoc ; inj-m+)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  THE GAMUT.
--
-- A gamut is a nonempty cyclic list of counters.  The HEAD is the position
-- currently under the hand; the tail runs upward through the cycle and
-- wraps.  Nonemptiness is structural — `ℕ × List ℕ`, not `List ℕ` — so
-- that striking the current position can never silently miss, which is the
-- side condition an index-plus-vector encoding would have to carry.
------------------------------------------------------------------------

Gamut : Type
Gamut = ℕ × List ℕ

tally : List ℕ → ℕ
tally [] = 0
tally (x ∷ xs) = x + tally xs

-- The AGGREGATE readout: one number, all positions summed.  This is the
-- low-variety regulator.
total : Gamut → ℕ
total (x , xs) = fst (x , xs) + tally (snd (x , xs))

-- Strike the position under the hand.
prahara : Gamut → Gamut
prahara (x , xs) = suc x , xs

-- Move on by one position (the sra displacement).
sarana-step : Gamut → Gamut
sarana-step (x , []) = x , []
sarana-step (x , y ∷ ys) = y , (ys ++ (x ∷ []))

-- `n` draws: strike, move on, repeat.
sarana : ℕ → Gamut → Gamut
sarana zero g = g
sarana (suc n) g = sarana n (sarana-step (prahara g))

-- Displacement without striking, used only to set the starting phase and
-- to realign a finished walk for reading.
calana : ℕ → Gamut → Gamut
calana zero g = g
calana (suc n) g = calana n (sarana-step g)

------------------------------------------------------------------------
-- 2.  THE AGGREGATE IS BLIND.
--
-- Displacement leaves the aggregate exactly fixed, and a strike raises it
-- by exactly one, wherever the hand happens to be.  Hence after `n` draws
-- the aggregate is `n` plus its initial value AND NOTHING ELSE: it is a
-- function of `n` alone, with no dependence on the starting phase.
------------------------------------------------------------------------

tally-snoc : (xs : List ℕ) (x : ℕ) → tally (xs ++ (x ∷ [])) ≡ tally xs + x
tally-snoc [] x = +-zero x
tally-snoc (y ∷ ys) x = cong (y +_) (tally-snoc ys x) ∙ +-assoc y (tally ys) x

sarana-step-total : (g : Gamut) → total (sarana-step g) ≡ total g
sarana-step-total (x , []) = refl
sarana-step-total (x , y ∷ ys) =
    cong (y +_) (tally-snoc ys x)
  ∙ +-assoc y (tally ys) x
  ∙ +-comm (y + tally ys) x

prahara-total : (g : Gamut) → total (prahara g) ≡ suc (total g)
prahara-total (x , xs) = refl

-- THEOREM (aggregate conservation).  For every budget `n` and every gamut.
sarana-total : (n : ℕ) (g : Gamut) → total (sarana n g) ≡ n + total g
sarana-total zero g = refl
sarana-total (suc n) g =
    sarana-total n (sarana-step (prahara g))
  ∙ cong (n +_) (sarana-step-total (prahara g) ∙ prahara-total g)
  ∙ +-suc n (total g)

calana-total : (n : ℕ) (g : Gamut) → total (calana n g) ≡ total g
calana-total zero g = refl
calana-total (suc n) g = calana-total n (sarana-step g) ∙ sarana-step-total g

-- COROLLARY (Ashby, exact form).  Two walks of the same length over the
-- same gamut, started at ANY two phases, have the same aggregate.  A
-- regulator whose readout is `total` has variety one over the phase set,
-- so it cannot distinguish any displacement, at any budget `n`.
aggregate-phase-blind :
  (n a b : ℕ) (g : Gamut)
  → total (sarana n (calana a g)) ≡ total (sarana n (calana b g))
aggregate-phase-blind n a b g =
    sarana-total n (calana a g)
  ∙ cong (n +_) (calana-total a g)
  ∙ cong (n +_) (sym (calana-total b g))
  ∙ sym (sarana-total n (calana b g))

------------------------------------------------------------------------
-- 3.  THE LABELLED READOUT IS NOT BLIND.
--
-- The concrete instance is the EGB field book: p = 24 template positions,
-- n = 450 numbered diamonds.  450 = 18·24 + 18.
--
-- To read a finished walk at position 0 the gamut must be realigned so the
-- head is position 0 again.  Total displacements must be a multiple of 24:
-- phase 0 walk uses 0 + 450 + 30 = 480 = 20·24, phase 1 uses
-- 1 + 450 + 29 = 480.  Realignment is `calana`, which strikes nothing.
------------------------------------------------------------------------

zeros24 : Gamut
zeros24 =
  0 , 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷
      0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

readout-phase-0 : Gamut
readout-phase-0 = calana 30 (sarana 450 zeros24)

readout-phase-1 : Gamut
readout-phase-1 = calana 29 (sarana 450 (calana 1 zeros24))

-- THEOREM (the JSON's `template_counts`, derived rather than reverified).
-- Positions 0..17 are struck 19 times, positions 18..23 are struck 18
-- times.  In the artifact's 1-based template numbering that is
-- templates 1..18 ↦ 19 and templates 19..24 ↦ 18, which is exactly the
-- `template_counts` table of EGB_REPETITION_STRUCTURE_REVERIFY_V3.json (absent from this repository).
-- Finite exhaustive computation, hence proof (CLAUDE.md (absent from this repository), "The rule" §3).
egb-template-counts :
  readout-phase-0
  ≡ ( 19 , 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷
           19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷
           18 ∷ 18 ∷ 18 ∷ 18 ∷ 18 ∷ 18 ∷ [] )
egb-template-counts = refl

-- The same walk started one position later.
egb-template-counts-shifted :
  readout-phase-1
  ≡ ( 18 , 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷
           19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷ 19 ∷
           18 ∷ 18 ∷ 18 ∷ 18 ∷ 18 ∷ [] )
egb-template-counts-shifted = refl

-- Both walks have the same aggregate, by §2 and by computation.
both-total-450 :
  (total readout-phase-0 ≡ 450) × (total readout-phase-1 ≡ 450)
both-total-450 = refl , refl

19≢18 : ¬ (19 ≡ 18)
19≢18 p = snotz (inj-m+ {m = 18} {l = 1} {n = 0} p)

-- THEOREM (the labelled readout separates the phases).  Reading ONE
-- labelled position — the head — already distinguishes the two walks that
-- `aggregate-phase-blind` proved indistinguishable in aggregate.
readout-separates : ¬ (readout-phase-0 ≡ readout-phase-1)
readout-separates p = 19≢18 (cong fst p)

------------------------------------------------------------------------
-- 4.  THE REFUTATION.  Stated as a claim I formed and then killed.
--
-- CLAIM (mine, on first reading the JSON):  `template_counts` is fully
-- determined by the two numbers already in the same record, 450 and 24.
-- The reverification therefore returns zero information, and reparsing
-- 312254 bytes to obtain it is arithmetic performed as measurement.
--
-- REFUTATION.  False, and `readout-separates` is the check that kills it.
-- The count vector is determined by (n, p, PHASE), not by (n, p).  The
-- MULTISET of counts is phase-invariant — it is {19 eighteen times,
-- 18 six times} for both walks above — but the count vector as a labelled
-- function of position is not: at position 0 it reads 19 at phase 0 and 18
-- at phase 1.  Since 0 < 450 mod 24 < 24, the vector pins the phase
-- exactly.  So the field carries log₂ 24 bits that (450, 24) does not.
--
-- What survives of the claim, restated so it is true: the reverification
-- returns log₂ 24 ≈ 4.58 bits about the artifact's phase, out of the
-- 450 · log₂ 24 ≈ 2064 bits its 450 template choices could in principle
-- have carried.  Nearly vacuous is not vacuous, and the difference is the
-- whole of what a labelled readout buys over an aggregate one — which is
-- the theorem, not an aside.
------------------------------------------------------------------------
