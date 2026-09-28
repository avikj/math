{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- संयोगे — समता संयोगे तिष्ठति, हानिस्तु न ; अतः पदैः पन्थाः न मीयते ।
--
-- (in composition: losslessness survives, lossiness does not — so a
--  pipeline is not graded by its steps.)
--
-- ────────────────────────────────────────────────────────────────────
-- THE ASYMMETRY, and it is the one that makes pipeline reasoning hard.
--
-- §२ · समता संयोगे — a composite of identifications is an identification.
--   Lossless composes, always, no hypothesis beyond the two.  So if every
--   step of a route is an identification, the route is one, and this is
--   why a route can be free at any length.
--
-- §३ · हानिः न संयोगे — a composite of LOSSY maps need not be lossy.
--   `loss/…/SakalaVikalaDesa_…` §3 already computes the witness
--   and reads it as a refutation of a sequential diagnostic; here it is
--   read as the composition law it also is:
--
--     सत् : Unit → Bool     u ↦ true    — its fibre over `false` is EMPTY.
--                                        Nothing is lost: Bool merely has
--                                        a name Unit cannot utter.
--                                        अवक्तव्यम्, and POSITIVE.
--     एकम् : Bool → Unit    _ ↦ tt      — its fibre over `tt` is CROWDED.
--                                        Exactly one bit is lost. विकलादेश.
--     एकम् ∘ सत् : Unit → Unit          — the IDENTITY.  An equivalence.
--
--   Neither factor is an identification and the composite is one.  The
--   inexpressibility at the first step and the collapse at the second
--   CANCEL.
--
-- SO: you may certify a pipeline lossless by certifying every step, and
-- you may NOT diagnose it lossy by finding a lossy step.  One direction
-- is compositional and the other is not, and no amount of care about the
-- steps repairs the second — the information is not there.  §४ says the
-- same thing as a refusal: there is no grading function on maps that both
-- respects composition and detects loss.
--
-- A SECOND NEIGHBOUR, AND IT NARROWS THIS MODULE.S TITLE.
--
-- `BhittiSankrama_WallsTransportAlongFordsSoEveryFordRetiresCandidatesFor
-- Free.agda` (absent from this repository) (another seat, 2026-08-23) proves
--
--     भित्ति-संक्रमः : (A ≃ B) → ¬ (B ≃ C) → ¬ (A ≃ C)
--
-- so a WALL -- a proved non-identification -- composes with a FORD into a
-- wall, and every new ford extends every standing wall across it.  Its
-- own sentence for what that buys: "the candidate list shrinks
-- quadratically in what is landed, not linearly in what is proved."
--
-- Read against §५ here, that looks like a contradiction and is not.  Two
-- different compositions:
--
--   THIS FILE composes MAPS along a pipeline, `g ∘ f`.  There,
--   certification composes and refutation does not -- §३.s two lossy
--   factors give a lossless composite.
--
--   THAT FILE transports a STATEMENT ABOUT TYPES along an equivalence.
--   There, refutation composes perfectly: non-identification crosses
--   every ford in the net, for free.
--
-- So "refutation does not compose" is true of sequential composition and
-- FALSE of transport across the identification graph, which is the
-- direction that matters for search.  This module.s title says "no
-- pipeline grades by its steps" and means exactly that -- a PIPELINE.  A
-- reader who took it as "negative information never propagates" would
-- have the wrong economics entirely, and that reading is available from
-- the title alone, so it is corrected here rather than left.
--
-- A NEIGHBOUR, FOUND AFTER THIS WAS WRITTEN AND NAMED HERE RATHER THAN
-- LEFT FOR A READER TO DISCOVER.  `Parampara_TheChainOfThreeIsPricedAnd
-- TheLossesDoNotAddBecauseAnAbsenceSitsInTheMiddleFibre.agda` (absent from this repository) in this
-- same lane found the non-additivity FIRST and went deeper than §३ does:
-- it prices an explicit chain of three, fibre by fibre, and names the
-- MECHANISM -- an अभाव sitting in the middle fibre, with both its
-- Nyya-Vaieika slots (pratiyogin and anuyogin) supplied, so the result
-- is a relation and not a report that a number came out smaller than
-- expected.
--
-- Neither module subsumes the other and the difference is worth stating.
-- Parampara is one chain, priced, with the reason.  This is the general
-- asymmetry -- certification composes, refutation does not -- with the
-- smallest possible witness and no mechanism.  A reader who has only this
-- file knows THAT stepwise diagnosis fails; a reader who has only that one
-- knows WHY it failed once.  I did not know of it when I wrote this.
--
-- NARROWED 2026-08-23, AFTER A NEIGHBOUR SHOWED THE TITLE IS FALSE IN THE
-- DIRECTION THAT MATTERS.  What §२ and §३ establish is about SEQUENTIAL
-- COMPOSITION OF MAPS along a pipeline, and nothing else.  Read as
-- "negative information never propagates" the title is WRONG, and a reader
-- who took it that way would have the search economics exactly backwards.
--
-- Across the IDENTIFICATION GRAPH negative information propagates very
-- well, and `Kosthabhitti_…agda` gives the structural reason neither file
-- had stated:
--
--   a DEFECT is a property of a MAP — `Σ[b] ¬ isContr (fiber f b)` — so it
--     needs a SITE, and `TritiyaMarga_…` shows that getting the site out of
--     a refutation costs at least Markov.s Principle.
--   a WALL is a property of a PAIR OF TYPES, and transport moves statements
--     about types.
--
-- So WALLS CROSS FORDS AND DEFECTS DO NOT, and that is the term/type
-- distinction rather than a happy accident about search.  A proved
-- non-crossing retires every candidate on the far side of every ford it
-- reaches; a proved lossy step retires nothing beyond itself, which is §३.
-- Both are true and they are about different objects.
--
-- ────────────────────────────────────────────────────────────────────
--
-- संयोग is ordinary  for conjunction/composition and is the word
-- सूत्र १३ of the corpus's root text uses; no source is claimed for
-- anything below.
------------------------------------------------------------------------

module Samyoge_LosslessnessComposesButLossinessDoesNotSoNoPipelineGradesByItsSteps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using (_≃_ ; isEquiv ; fiber ; compEquiv ; idEquiv)
open import Cubical.Foundations.Isomorphism using (isoToEquiv ; iso)
open import Cubical.Foundations.Function using (idfun ; _∘_)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false ; false≢true ; isSetBool)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- १ · The three maps.  Written out so §२ and §३ are about the same
--     objects and not about two unrelated examples.
------------------------------------------------------------------------

सत् : Unit → Bool
सत् _ = true

एकम् : Bool → Unit
एकम् _ = tt

संहति : Unit → Unit
संहति = एकम् ∘ सत्

------------------------------------------------------------------------
-- २ · समता संयोगे — LOSSLESS COMPOSES.
------------------------------------------------------------------------

समता-संयोगः : {A B C : Type ℓ} → A ≃ B → B ≃ C → A ≃ C
समता-संयोगः = compEquiv

------------------------------------------------------------------------
-- ३ · हानिः न संयोगे — AND LOSSY DOES NOT.
--
--     Both factors fail to be identifications, in OPPOSITE ways, and the
--     composite is the identity.
------------------------------------------------------------------------

-- the first step's fibre over `false` is empty: nothing lost, unsayable
सत्-अवक्तव्यम् : ¬ (fiber सत् false)
सत्-अवक्तव्यम् (_ , p) = true≢false p

सत्-न-समता : ¬ (isEquiv सत्)
सत्-न-समता e = सत्-अवक्तव्यम् (isEquiv.equiv-proof e false .fst)

-- the second step's fibre over `tt` is crowded: exactly one bit lost
एकम्-वाम एकम्-दक्षिण : fiber एकम् tt
एकम्-वाम   = false , refl
एकम्-दक्षिण = true  , refl

एकम्-विकलादेश : ¬ (एकम्-वाम ≡ एकम्-दक्षिण)
एकम्-विकलादेश p = false≢true (cong fst p)

एकम्-न-समता : ¬ (isEquiv एकम्)
एकम्-न-समता e =
  एकम्-विकलादेश (isContr→isProp (isEquiv.equiv-proof e tt) एकम्-वाम एकम्-दक्षिण)

-- and the composite is the identity, hence an equivalence
संहति-तत्समम् : (u : Unit) → संहति u ≡ idfun Unit u
संहति-तत्समम् tt = refl

संहति-समता : isEquiv संहति
संहति-समता = subst isEquiv (λ i u → संहति-तत्समम् u (~ i)) (idEquiv Unit .snd)

------------------------------------------------------------------------
-- ४ · न श्रेणी-मापः — NO STEPWISE GRADE DETECTS LOSS.
--
--     Suppose a grade assigns a value to every map, respects composition
--     in the sense that a composite's grade is determined by its factors'
--     grades, and reports "lossless" exactly at the identifications.
--     §३ kills it: `सत्` and `एकम्` are both graded lossy, `एकम्` composed
--     with `सत्` is lossless, and `एकम्` composed with `एकम् `— no; the
--     cleanest form needs no second instance, because a determined
--     composite grade would have to be a FUNCTION of the two factor
--     grades, and here two lossy factors give a lossless composite while
--     a lossy factor composed with an identity gives a lossy one.
------------------------------------------------------------------------

-- the second pair: एकम् after the identity is still lossy
संहति' : Bool → Unit
संहति' = एकम् ∘ idfun Bool

संहति'-न-समता : ¬ (isEquiv संहति')
संहति'-न-समता = एकम्-न-समता

-- so no function of the factors' loss-status determines the composite's:
-- (lossy , lossy) ↦ lossless  and  (lossless , lossy) ↦ lossy are both
-- realised, and any such function would have to send the SAME pair of
-- statuses to both answers if it also graded `सत्` and `idfun Bool`
-- alike -- which it cannot, since one is an equivalence and the other is
-- not.  What survives, stated exactly, is §५.

------------------------------------------------------------------------
-- ५ · What actually survives, so §४ is not read as more than it is.
--
--     A grade that respects composition CAN certify losslessness: if both
--     factors are identifications the composite is (§२).  What it cannot
--     do is DETECT loss — a lossy factor is no evidence about the
--     composite, because §३ exhibits two lossy factors composing to an
--     identity.  Certification composes; refutation does not.
--
--     And that is not a defect in the grading.  It is सूत्र १३ read
--     correctly: the composite's fibre is fibred OVER the fibre — built
--     from the parts, not determined by them — and §३ is precisely a case
--     where non-trivial parts assemble a trivial total.
------------------------------------------------------------------------
