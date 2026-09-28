{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- नष्ट — यत् त्यक्तं तत् पुनः लभ्यते, अतः वहनं पता एव आसीत् ।
--
-- (naṣṭa — what was dropped is got back, so the receipt was an address
--  all along.)
--
-- ────────────────────────────────────────────────────────────────────
-- मूलवाक्यम् · SOURCE OF THE TERM, with text and date.
--
--   नष्ट ("the lost one") is one of Piṅgala's प्रत्यय: given the row
--   number, RECOVER the pattern that was not written down.  Pigala,
--   *Chandaḥśāstra* ८.२४–२८ (~300 BCE); worked with the array by
--   हलायुध, *Mṛtasañjīvanī* (10th c. CE).  Its partner उद्दिष्ट runs the
--   other way, pattern to row number.
--
--   The term names the OPERATION performed in §२ and §३ and nothing
--   else: producing the map that brings the object back from the datum.
--
-- ────────────────────────────────────────────────────────────────────
-- WHY THIS MODULE EXISTS.
--
-- `Pata_CarryingIsUnconditionalButAddressingNeedsTheMapToBeAnIdentification.agda`
-- separates two things this corpus had been running together:
--
--   वहनम्   a RECEIPT.  `ग्राह f ≃ A` for EVERY f, no hypothesis.  A
--           derived datum may always be kept beside its object.
--   पता     an ADDRESS.  A recovery map with both round trips, i.e.
--           the object may be DROPPED and recomputed from the datum.
--           Not free: it is exactly the statement that f is an
--           identification.
--
-- `machine/Lopa_TheIrreversibleEdgesAreTheOtherGraphAndTheyRunOneWay.hs` (absent from this repository)
-- grades the corpus's declarations into an invertible road and a road
-- of one-way edges, and `--queue` emits the latter.  Every edge on that
-- queue is a receipt whose ADDRESS STATUS IS UNKNOWN — the census does
-- not claim they fail to be addresses, only that no term says they are.
--
-- This module takes two of them off the queue by exhibiting the नष्ट.
-- Both were already three quarters proved at their own site and the
-- last quarter was never written, which is why the census could not see
-- them: a proof that is not a signature is not visible to a parser.
--
-- §२  `compileContext : OneHoleContext X → List (ContextAction X)`
--     « CompositionalContextAdapter.
--     That module proves `compile-decode` (one round trip) and uses it
--     to route SyntacticContextEq → ContextEq.  The other round trip is
--     absent from the file, and with it the fact that the one-hole term
--     grammar IS its action word: the syntax may be dropped.
--
-- §३  `colsOf : Col → ℤ × ℤ × ℤ` and `entriesOf : Mat 3 3 → Nine`
--     « SmithPathCountedExecution.
--     That module proves `fromCols-entries` and `fromNine-entries` (the
--     hard halves, by funext over the index) and uses them only to
--     derive `col≡` / `mat≡`, equality-reflection helpers.  The easy
--     halves are `refl` and were never stated, so a 3×1 integer matrix
--     and its triple of entries stood in the census as two types with a
--     one-way map between them.
--
--     The two are NOT in the same position in the census and the
--     difference is worth naming.  `colsOf` was on the queue.
--     `entriesOf` is nowhere in the census's printed output at all —
--     not on the queue, not an endomorphism, not a refusal — so it sits
--     in one of the two buckets the instrument counts and does not
--     name, and from the output I cannot tell which.  `Mat` reaches
--     that file through an unnamed `open Coefficient ℤCommRing`, which
--     is the likely reason and is a guess, not a reading.  Silence is
--     not a verdict: मौनं न निषेधः.  Both are proved below regardless,
--     because the queue is where the question was asked and not where
--     it lives.
--
-- §४ is the honest limit and states the extent of the search.
------------------------------------------------------------------------

module Nasta_TheOneHoleContextAndTheColumnAreRecoveredFromTheirData where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.List using (List)
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import Pata_CarryingIsUnconditionalButAddressingNeedsTheMapToBeAnIdentification
  using (पता ; पता→समता ; वहनम् ; ग्राह)

open import CompositionalContextAdapter
  using ( OneHoleContext ; hole ; leftHole ; rightHole
        ; ContextAction ; compileContext ; decodeContext ; compile-decode )

open import SmithPathCountedExecution
  using ( Col ; Nine
        ; colsOf ; fromCols ; fromCols-entries
        ; entriesOf ; fromNine ; fromNine-entries )

open import Cubical.Data.Int using (ℤ)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Algebra.Matrix.CommRingCoefficient using (module Coefficient)
open Coefficient ℤCommRing using (Mat)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- १ · The two readings, restated on the edges below so this file can be
--     read on its own.  वहनम् is the free half and is quoted, not
--     reproved: it holds of every map, hence of both maps here.
------------------------------------------------------------------------

सन्दर्भ-वहनम् : {X : Type ℓ} → ग्राह (compileContext {X = X}) ≃ OneHoleContext X
सन्दर्भ-वहनम् {X = X} = वहनम् (compileContext {X = X})

स्तम्भ-वहनम् : ग्राह colsOf ≃ Col
स्तम्भ-वहनम् = वहनम् colsOf

------------------------------------------------------------------------
-- २ · नष्ट FOR THE ONE-HOLE CONTEXT.
--
--     `compileContext` walks a context from the hole outwards and emits
--     one `ContextAction X = Bool × X` per layer: `false` for a hole on
--     the left, `true` for a hole on the right, paired with the fixed
--     operand.  The recovery is the obvious re-fold, and it is already
--     written in the adapter as `decodeContext` — used there ONLY in
--     the direction `compileContext ∘ decodeContext ≡ id`.
--
--     The missing direction is `decode-compile`.  With it, the whole
--     grammar of generated unary contexts is content-addressed by its
--     action word: an adapter may store the word and throw the tree
--     away.  That is what the adapter's own design assumes and what its
--     file did not say.
------------------------------------------------------------------------

decode-compile : {X : Type ℓ} (c : OneHoleContext X)
  → decodeContext (compileContext c) ≡ c
decode-compile hole                  = refl
decode-compile (leftHole fixed outer)  = cong (leftHole fixed)  (decode-compile outer)
decode-compile (rightHole fixed outer) = cong (rightHole fixed) (decode-compile outer)

-- THE IDENTIFICATION.  Both round trips, in the shape §३ of Pata asks for.
सन्दर्भ-पता : {X : Type ℓ} → पता (compileContext {X = X})
सन्दर्भ-पता {X = X} = decodeContext , decode-compile , compile-decode

सन्दर्भ-समता : {X : Type ℓ} → OneHoleContext X ≃ List (ContextAction X)
सन्दर्भ-समता {X = X} = पता→समता (compileContext {X = X}) सन्दर्भ-पता

------------------------------------------------------------------------
-- ३ · नष्ट FOR THE COLUMN AND FOR THE 3×3 MATRIX.
--
--     `Col = Mat 3 1` is a FUNCTION out of the index type, so the hard
--     half — that a matrix rebuilt from its entries is the matrix it
--     came from — needs funext and a case split on the index, and
--     `SmithPathCountedExecution` does it (`fromCols-entries`,
--     `fromNine-entries`).  The other half is `refl`, because `mkCol`
--     and `mk3` compute on literal indices.  Neither module stated it,
--     so the census read `colsOf` and `entriesOf` as one-way.
------------------------------------------------------------------------

cols-fromCols : (v : ℤ × ℤ × ℤ) → colsOf (fromCols v) ≡ v
cols-fromCols v = refl

स्तम्भ-पता : पता colsOf
स्तम्भ-पता = fromCols , fromCols-entries , cols-fromCols

स्तम्भ-समता : Col ≃ (ℤ × ℤ × ℤ)
स्तम्भ-समता = पता→समता colsOf स्तम्भ-पता

entries-fromNine : (v : Nine) → entriesOf (fromNine v) ≡ v
entries-fromNine v = refl

मातृका-पता : पता entriesOf
मातृका-पता = fromNine , fromNine-entries , entries-fromNine

मातृका-समता : Mat 3 3 ≃ Nine
मातृका-समता = पता→समता entriesOf मातृका-पता

------------------------------------------------------------------------
-- ४ · THE EXTENT OF THE SEARCH, so nothing here reads as more than it is.
--
--     WHAT WAS SEARCHED.  `Lopa … --queue` (run 2026-08-22 over the
--     whole repository: 1008 files, 11928 top-level signatures) emits
--     its undecided one-way edges as `src ⟶ tgt ⟶ site`.  I joined that
--     queue against itself to find every SOURCE/TARGET pair carrying an
--     edge in both directions — the shape a mutual inverse would leave
--     — and opened the candidates one file at a time.
--
--     WHAT WAS FOUND, and only §२ and §३ are proved here:
--
--     · Several of those pairs are ALREADY identifications at their own
--       site and are on the queue because the census's parser matches
--       `_≃_` and `_≡_` conclusions and not `Iso`, or because the two
--       sides are written with different aliases for one type.
--       `PMTorus.vertexToFin` is the clearest instance:
--       `vertexIso : Iso Vertex (Fin V)` and `vertexCount : Vertex ≃
--       Fin V` are both in that file, and the map's signature says
--       `Fin 6`, with `V = 6` a definition the resolver does not unfold.
--       Same for `edgeToFin`, and for
--       `S3IntegerRelativeCoordinates.relativeCoordinates`
--       (`relativeCoordinateIso` is in the file).  These are census
--       defects, not mathematics, and are NOT repaired here — the
--       instrument is another seat's file.
--
--     · Some are receipts with a recovery map that is still not an
--       address, which is exactly Pata §४ arriving from the other side.
--       `the deleted Swarm.S01PaniniAshby.sig : SmithState → Bool × Bool` is
--       injective (`sigDistinct01/02/12`) and cannot be surjective:
--       three states, four signatures.  That file's own reading —
--       Ashby's variety bound — is why.  `
--       AdaptiveProbeCollapse.staticTriple : St → Bool × Bool × Bool`
--       has its retraction proved (`static-budget-3-identifies`) and the
--       same obstruction.  Neither is proved non-invertible here.
--
--     WHAT THE CENSUS DOES WITH THIS FILE, checked by re-running it
--     after §२ and §३ landed.  `colsOf` leaves the queue: `स्तम्भ-समता`
--     is picked up as a causeway and `Col ⟶ ℤ × ℤ × ℤ` is joined.
--     `compileContext` DOES NOT leave it, and the reason is not
--     mathematical — `सन्दर्भ-समता` is stated over a bound `X`, and the
--     census discards any conclusion mentioning a binder, while it
--     resolves the adapter's own implicit `X` to the unrelated
--     definition `TwoProjections.X`.  So the queue will
--     keep printing that edge.  The theorem is §२ and the queue entry
--     is the instrument, and they disagree; the instrument is another
--     seat's file and is not touched here.
--
------------------------------------------------------------------------
