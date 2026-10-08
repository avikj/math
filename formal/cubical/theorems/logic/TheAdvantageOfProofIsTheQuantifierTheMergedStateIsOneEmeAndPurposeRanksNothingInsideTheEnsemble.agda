{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheAdvantageOfProofIsTheQuantifierTheMergedStateIsOneEmeAndPurposeRanksNothingInsideTheEnsemble
--
-- The 2025–2026 ruliology corpus, held to terms.  This module continues
-- Coordinatization… over the SAME multiway system (two updating events on
-- unary strings) and answers three sentences from Wolfram's 2025–2026
-- writings, each quoted verbatim:
--
--   W5. "We don't get any fundamental advantage by trying to make a
--       proof rather than just running the Turing machine — in both
--       cases we have to expend a potentially unbounded amount of
--       computational effort."
--       (Towards a Theory of Bugs: The Ruliology of the Unexpected,
--        July 2026)
--   W6. "Equivalent states are in fact merged."  And the emes: "atoms
--       of existence" whose "only property is distinctness".
--       (What Ultimately Is There? Metaphysics and the Ruliad,
--        February 2026)
--   W7. The rulial ensemble is "an ensemble of possible rules ...
--       selected to 'achieve the purpose'", and life is patches of
--       irreducibility "fitted together to achieve that purpose"
--       through bulk orchestration.
--       (What's Special about Life?, November 2025)
--
-- W5: THE ADVANTAGE OF PROOF IS THE QUANTIFIER (§1).  The sentence is
-- exactly right about each single instance and exactly wrong about
-- their totality, and both halves are terms.  Running the system
-- reaches one endpoint per run; the term `sarva-prapti` reaches EVERY
-- endpoint at once — a function (n : ℕ) → Evolve zero n, built by one
-- induction through the snoc lemma — and no amount of running produces
-- a universally quantified statement, because a run is one point of
-- the family and the term is the family.  The corpus already holds the
-- machine-scale form (abstract 25: the composition theorem certifies
-- incr ⨟ incr for every n with no induction over the compound); this
-- is the same fact at the smallest scale, stated against W5's exact
-- sentence: the effort of proof is bounded by the induction, the
-- effort of running is unbounded over the family, and that asymmetry
-- IS the fundamental advantage.
--
-- W6: THE MERGED STATE IS ONE EME (§2).  Coordinatization… merged the
-- branches with a propositional truncation — existence kept, identity
-- withheld.  Wolfram's February 2026 sentence is stronger: merged IN
-- THE OBJECT.  That is the set quotient, and it is also checked: under
-- the co-terminality relation, the branches become EQUAL as data
-- (`ekibhava`, by eq/), the whole quotient contracts to a single point
-- (`eka-eme`) — an object with no property but its own distinctness,
-- which is Wolfram's eme, constructed rather than posited — and the
-- stronger merge still has no section (`punaruddhara-nasti-eva`): the
-- collision that refuted reconstruction from the thread refutes it
-- from the quotient, by the same two congs.  So the two merges the
-- 2021 and 2026 sentences name — treat-as-equivalent and
-- merged-in-fact — are BOTH real, both lossy, and the loss is the same
-- computed object either way.
--
-- W7: PURPOSE RANKS NOTHING INSIDE THE ENSEMBLE (§3).  Take the
-- purpose to be arrival — reach state 3 from state 0 — so that the
-- ensemble "selected to achieve the purpose" is exactly the fibre of
-- the endpoint, populated here by the two interchanged orders.  Any
-- assessor that reads only purpose-achievement — any function out of
-- the merged outcome, prop-valued fitness included — answers equally
-- on all ensemble members (`niyojana-anankana`, the quotient form of
-- Coordinatization…'s baddha-drashta): selection BY the purpose cannot
-- rank WITHIN the ensemble that achieves it, which is abstract 12's
-- theorem (no scoring function of the outcome ranks the route) arrived
-- at from Wolfram's November 2025 vocabulary.  The orchestration half
-- of W7 — the step whose visible part consults its hidden part, the
-- checkable ingredient of "patches fitted together" — is already a
-- checked term as Entanglement…'s living step, cited not re-proved.
--
-- RELATION TO THE CORPUS.  Abstract 25's
-- composition theorem is W5 at machine scale; abstract 12 is W7's
-- non-ranking in general; Entanglement… holds W7's orchestration ingredient;
-- Coordinatization… holds the truncation half of W6 and the branch pair
-- this module's quotient merges.  The set-quotient construction
-- parallels abstract 25's Beh = Code/SameRun, one level down: there
-- codes were quotiented by behaviour, here runs are quotiented by
-- co-terminality, and in both the quotient is the observer's object
-- while the fibre is the ruliology.
------------------------------------------------------------------------

module TheAdvantageOfProofIsTheQuantifierTheMergedStateIsOneEmeAndPurposeRanksNothingInsideTheEnsemble where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.SetQuotients using (_/_ ; [_] ; eq/ ; squash/ ; elimProp)

open import CoordinatizationIsAPathTheMergeIsATruncationWithNoSectionAndTheBoundedObserverSeparatesNoCoTerminalRuns
  using (Evolve ; halt ; ev₁ ; ev₂ ; route₁ ; route₂ ; routesDistinct)

------------------------------------------------------------------------
-- 1 · W5: the advantage of proof is the quantifier.
------------------------------------------------------------------------

-- appending one updating event at the END of an evolution.
extendByOne : {m n : ℕ} → Evolve m n → Evolve m (suc n)
extendByOne (halt n) = ev₁ (halt (suc n))
extendByOne (ev₁ r)  = ev₁ (extendByOne r)
extendByOne (ev₂ r)  = ev₂ (extendByOne r)

-- THE TERM RUNNING CANNOT PRODUCE: every state is reached from zero,
-- all of them by one induction.  A run exhibits one endpoint; this
-- function is the whole family at once.
reachesEvery : (n : ℕ) → Evolve zero n
reachesEvery zero    = halt zero
reachesEvery (suc n) = extendByOne (reachesEvery n)

------------------------------------------------------------------------
-- 2 · W6: the merged state is one eme, and still has no section.
------------------------------------------------------------------------

-- co-terminality: the relation that holds between any two evolutions
-- sharing both endpoints (they already do, by the index).
coTerminal : {a b : ℕ} → Evolve a b → Evolve a b → Type
coTerminal _ _ = Unit

-- the object-level merge: runs 0 → 3, quotiented.
mergedStates : Type
mergedStates = Evolve zero (suc (suc (suc zero))) / coTerminal

-- "equivalent states are in fact merged": the branches are EQUAL as
-- data in the quotient, not merely jointly present in a truncation.
equalAsData : Path mergedStates [ route₁ ] [ route₂ ]
equalAsData = eq/ route₁ route₂ tt

-- the merged object is one eme: a point with no property beyond its
-- own distinctness — the whole quotient contracts onto it.
oneEme : isContr mergedStates
oneEme = [ route₁ ] , elimProp (λ x → squash/ [ route₁ ] x)
                                (λ r → eq/ route₁ r tt)

-- and the stronger merge still has no section: reading a run back out
-- of the merged object collides with the branch distinction.
noSectionEither :
  ¬ (Σ[ sel ∈ (mergedStates → Evolve zero (suc (suc (suc zero)))) ]
       ((r : Evolve zero (suc (suc (suc zero)))) → sel [ r ] ≡ r))
noSectionEither (sel , h) =
  routesDistinct (sym (h route₁) ∙ cong sel equalAsData ∙ h route₂)

------------------------------------------------------------------------
-- 3 · W7: purpose ranks nothing inside the ensemble.
------------------------------------------------------------------------

-- the ensemble selected by the purpose "arrive at 3 from 0" is the
-- run type itself (the fibre of arrival); any assessor reading only
-- the merged achievement answers equally on all members — prop-valued
-- fitness functions included, since they factor through functions.
purposeRanksNothing : {ℓ : Level} {X : Type ℓ} (g : mergedStates → X)
              → g [ route₁ ] ≡ g [ route₂ ]
purposeRanksNothing g = cong g equalAsData
