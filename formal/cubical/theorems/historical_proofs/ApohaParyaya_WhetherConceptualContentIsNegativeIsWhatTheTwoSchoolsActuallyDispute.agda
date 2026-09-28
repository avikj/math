{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ApohaParyaya_WhetherConceptualContentIsNegativeIsWhatTheTwoSchoolsActuallyDispute
--
-- THE DISPUTE, AND WHY IT IS THE OBJECT RATHER THAN THE OBSTACLE.
--
-- The Bauddha logicians and the Jaina logicians rejected each other's
-- accounts of what a standpoint IS, for centuries, in print, and neither
-- conceded.  Every modern treatment I am aware of resolves this by
-- blending them into one "Indic" toolkit -- which discards the dispute,
-- and the dispute is the content.  CLAUDE.md (absent from this repository) names that as the mining
-- move one level up: not extracting results from a tradition, but
-- extracting vocabulary from several and flattening them into a register
-- none of them would recognise.
--
-- This module does the opposite.  It makes the Bauddha argue, against a
-- Jaina construction already in this corpus, and it exhibits the
-- incompatibility as a checked object WITHOUT resolving it.  Prose has to
-- pick a side or blend.  A type theory does not.
--
-- ────────────────────────────────────────────────────────────────────
-- SOURCES, WITH THE GRADE OF EACH STATED.
--
-- Bauddha side.  Dignga, *Pramasamuccaya* (c. 480-540), for apoha:
-- conceptual content as *anya-apoha*, exclusion-of-the-other -- a general
-- term does not pick out a shared positive feature, it excludes what the
-- term is not.  Dharmakrti, *Pramavrttika* (c. 600-660), develops it
-- and attacks the Jaina position.  ntarakita, *Tattvasagraha*
-- (c. 750), with Kamalala's *Pajik*, carries an examination of the
-- Jaina doctrine of many-sidedness.
--
-- Jaina side.  Umsvti, *Tattvrthastra* 5.29
-- (*utpdavyayadhrauvyayukta sat* -- what is, is joined with
-- origination, cessation and persistence) and 5.31
-- (*arpitnarpitasiddhe* -- established through the emphasised and the
-- unemphasised), for dravya persisting through paryya.  Akalaka
-- (c. 720-780); Vidynanda, *Aasahasr* (c. 850); Prabhcandra,
-- *Prameyakamalamrtaa* (c. 1000), for the replies to the Bauddha
-- charge.
--
-- GRADE, stated because a provenance you did not check is the same class
-- of error as a fitted constant: I have these at the level of author,
-- work and approximate date, and at the level of the doctrine each work
-- is known for.  I have NOT verified chapter or verse numbering against
-- an edition -- this container has no route to a text.  Where a number
-- appears above (5.29, 5.31) it is one I can state; no others are given.
--
-- THE MODELLING STEP THAT IS EASIEST TO MISS, FLAGGED HERE RATHER THAN
-- LEFT IN THE PROOFS.
--
-- Apoha is a theory of how a GENERAL TERM gets its content.  A naya is a
-- STANDPOINT on an object.  Treating the second as individuated the way
-- the first is, is a step, it is mine, and neither school took it in
-- these words.  Everything below is conditional on it, and a Jaina would
-- very likely reject the step before reaching §3 at all -- which would be
-- a third position this module does not construct.
--
-- What makes the step defensible rather than convenient: a naya is
-- articulated, and on the Bauddha's own division the articulated is
-- conceptual -- pratyaka grasps the svalakaa non-conceptually, and
-- everything a standpoint can SAY has already passed through
-- conceptualisation.  So on the Bauddha's own account a naya falls under
-- apoha.  That is why the step is available to him.  It is not thereby
-- available to his opponent, and §6 does not pretend otherwise.
--
-- `Durnaya_TheProhibitionHasContentOnlyOffThePropositional-
-- World` (cf-archivist, 2026-08-20) proves that the aneknta prohibition
-- has content only where the fibres are not propositions, and that any
-- separating family must be non-propositional.  Every theorem there takes
-- `isProp (P s)` AS A HYPOTHESIS.  Nothing in this corpus asks where
-- propositionality would COME from.
--
-- The answer is that one of the two disputants derives it.  §2: an
-- exclusion is proposition-valued, necessarily, on both readings of
-- apoha.  §3: therefore a family of Bauddha standpoints satisfies that
-- hypothesis automatically, and the deflation is not an assumption the
-- Bauddha smuggles in -- it is forced by his own theory of concepts.
-- §4: and so no apoha-family can EVER separate, which is Dharmakrti's
-- charge made exact and made structural rather than polemical.
--
-- §5 is the Jaina reply, and it is not a refutation: a paryya is a
-- positive determination of a persisting dravya, not an exclusion, and a
-- positive family CAN separate -- the corpus's own `Mixed` does it.
--
-- §6 is the point of the module.  Neither argument touches the other.
-- The proposition actually in dispute is *whether conceptual content is
-- negative*, and nothing above decides it.
------------------------------------------------------------------------

module ApohaParyaya_WhetherConceptualContentIsNegativeIsWhatTheTwoSchoolsActuallyDispute where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary using (¬_ ; isProp¬)

open import Durnaya_CollapseIffEveryNayaAgrees
  using (AllNayasAgree ; Mixed ; Mixed-not-agree)
open import Durnaya_TheProhibitionHasContentOnlyOffThePropositionalWorld
  using (MutuallyEntail ; entail→agree-onProps ; separator-is-not-proposition-valued
        ; Mixed-entails)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- 1.  THE MODELLING, STATED BEFORE IT IS USED.
--
-- A standpoint assigns, to each respect `s`, a type `P s` -- the content
-- the standpoint has AT that respect.  That much both schools' positions
-- can be written in; it is the corpus's existing `Naya`.
--
-- The Bauddha commitment being modelled: conceptual content is
-- *anya-apoha*, exclusion.  What a term contributes is the ruling-out of
-- what it is not, and never a positive feature shared by particulars.
-- Modelled: the content at a respect is an exclusion of some `A s`.
--
-- TWO READINGS, and the result does not depend on choosing between them.
-- The texts are standardly read either as simple exclusion or as
-- exclusion-of-the-exclusion ("cow" as not-non-cow).  Both are given, and
-- §2 covers both, precisely so that no objection of the form "you picked
-- the convenient reading" survives.  That is the only reason the second
-- one is here.
------------------------------------------------------------------------

Apoha : {S : Type ℓ} → (S → Type ℓ') → S → Type ℓ'
Apoha A s = ¬ (A s)

DviApoha : {S : Type ℓ} → (S → Type ℓ') → S → Type ℓ'
DviApoha A s = ¬ (¬ (A s))

------------------------------------------------------------------------
-- 2.  AN EXCLUSION IS PROPOSITION-VALUED.  Necessarily, on either
--     reading, with no hypothesis whatsoever.
--
-- This is the whole engine and it is three lines.  `¬ A` is `A → ⊥`; a
-- Π into a proposition is a proposition; ⊥ is a proposition.
------------------------------------------------------------------------

apoha-isProp : {S : Type ℓ} (A : S → Type ℓ') (s : S) → isProp (Apoha A s)
apoha-isProp A s = isProp¬ (A s)

dviApoha-isProp : {S : Type ℓ} (A : S → Type ℓ') (s : S) → isProp (DviApoha A s)
dviApoha-isProp A s = isProp¬ (¬ (A s))

------------------------------------------------------------------------
-- 3.  SO THE BAUDDHA DOES NOT ASSUME THE DEFLATION.  HE DERIVES IT.
--
-- cf-archivist's `entail→agree-onProps` needs `(s : S) → isProp (P s)`.
-- For an apoha-family that hypothesis is discharged by §2, from nothing.
-- Hence: among Bauddha standpoints, mutual entailment already IS full
-- agreement, and the aneknta prohibition says nothing a biconditional
-- would not.
--
-- That is Dharmakrti's trivialisation charge, and the finding is that it
-- is not question-begging.  It follows from apoha.
------------------------------------------------------------------------

apoha-entail→agree :
  {S : Type ℓ} (A : S → Type ℓ') →
  MutuallyEntail (Apoha A) → AllNayasAgree (Apoha A)
apoha-entail→agree A = entail→agree-onProps (Apoha A) (apoha-isProp A)

dviApoha-entail→agree :
  {S : Type ℓ} (A : S → Type ℓ') →
  MutuallyEntail (DviApoha A) → AllNayasAgree (DviApoha A)
dviApoha-entail→agree A = entail→agree-onProps (DviApoha A) (dviApoha-isProp A)

------------------------------------------------------------------------
-- 4.  AND THEREFORE NO APOHA-FAMILY CAN SEPARATE -- NOT AS A FAILURE TO
--     FIND ONE, BUT AS A NON-EXISTENCE.
--
-- §3 already gives this pointwise.  Stated as the non-existence it is,
-- because that is the form the charge actually takes: within the
-- Bauddha's vocabulary a separating standpoint is not unattested, it is
-- unconstructible.
--
-- Which is stronger than "aneknta is incoherent" and also kinder to the
-- Jaina than the polemic was: the doctrine is INEXPRESSIBLE in apoha.
-- That is why, from inside that vocabulary, the Jaina looks like a man
-- asserting a contradiction.  He is not.  He is speaking a vocabulary in
-- which the sentence has a referent.
--
------------------------------------------------------------------------

no-apoha-family-separates :
  ¬ (Σ[ A ∈ (Bool → Type₀) ]
       (MutuallyEntail (Apoha A) × (¬ (AllNayasAgree (Apoha A)))))
no-apoha-family-separates (A , e , ¬a) = ¬a (apoha-entail→agree A e)

-- and the same for the double-exclusion reading, so the non-existence
-- does not depend on which reading of apoha is taken.
no-dviApoha-family-separates :
  ¬ (Σ[ A ∈ (Bool → Type₀) ]
       (MutuallyEntail (DviApoha A) × (¬ (AllNayasAgree (DviApoha A)))))
no-dviApoha-family-separates (A , e , ¬a) = ¬a (dviApoha-entail→agree A e)

------------------------------------------------------------------------
-- 5.  THE JAINA REPLY, WHICH IS NOT A REFUTATION.
--
-- Umsvti 5.29: what IS, is joined with origination, cessation and
-- persistence -- simultaneously.  A paryya is a positive determination
-- of a dravya that persists through it, not an exclusion of something
-- else.  Modelled: the fibres are free to be any type.
--
-- And a positive family can separate.  The corpus already carries the
-- witness -- `Mixed`, with fibres Unit and Bool: mutually entailing,
-- because both inhabited, and not agreeing, because Unit and Bool are not
-- equivalent.
--
-- Note what this does and does not do.  It does NOT show the Bauddha
-- wrong.  It shows that the Jaina is not asserting a contradiction; he is
-- refusing the modelling of a standpoint as an exclusion.
------------------------------------------------------------------------

paryaya-can-separate :
  Σ[ P ∈ (Bool → Type₀) ] (MutuallyEntail P × (¬ (AllNayasAgree P)))
paryaya-can-separate = Mixed , Mixed-entails , Mixed-not-agree

------------------------------------------------------------------------
-- 6.  WHERE THE DISPUTE ACTUALLY IS, AND THAT NOTHING ABOVE SETTLES IT.
--
-- §3/§4:  IF content is exclusion, aneknta is inexpressible.
-- §5:     IF content can be positive, aneknta has a witness.
--
-- Both are theorems.  Neither contradicts the other, because their
-- hypotheses are different, and the hypotheses are the two ontologies.
-- What is refuted is only this: that the logic settles the question.  It
-- does not.  The disputed proposition is
--
--       IS CONCEPTUAL CONTENT NEGATIVE?
--
-- and it is prior to everything above.
--
-- The asymmetry worth recording, because it explains the shape the
-- dispute took historically rather than merely restating it: the Bauddha
-- CANNOT SEE HIS OWN COMMITMENT, because propositionality reaches him as
-- a consequence of apoha and never as an axiom about standpoints.  From
-- inside, the Jaina is asserting P and ¬P of one thing.  From the Jaina
-- side the Bauddha has assumed the answer in his semantics.  Both
-- experiences are accurate given the commitments, which is why centuries
-- of the exchange produced no concession from either.
--
-- I am not adjudicating it and I do not think this corpus should.  §1
-- of `Anekanta.agda` records the instruction: hold every view, grasp
-- none; the collision specifies a missing distinction and IS the
-- valuable object.  The missing distinction is named above.
------------------------------------------------------------------------

-- The two conditionals, side by side, as one checked object.
vivādaḥ :
  ( {S : Type₀} (A : S → Type₀) →
      MutuallyEntail (Apoha A) → AllNayasAgree (Apoha A) )
  × ( Σ[ P ∈ (Bool → Type₀) ] (MutuallyEntail P × (¬ (AllNayasAgree P))) )
vivādaḥ = (λ A → apoha-entail→agree A) , paryaya-can-separate
