{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- पुद्गल — matter: atoms and aggregates.  The FORM changes by combination
-- and division; the ATOM-COUNT persists.  utpda-vyaya-dhrauvya, for the
-- one substance that has extension.
--
-- SOURCE.  Umāsvāti, *Tattvārthasūtra*, adhyāya 5 (~2nd–5th c. CE):
--   5.23  spara-rasa-gandha-varavanta pudgal
--         — matter has touch, taste, smell, colour (it is corporeal, rūpī,
--           unlike dharma/adharma/ka/kla; `DharmaAdharma.agda` (absent from this repository)).
--   5.25  aṇavaḥ skandhāś ca — pudgala exists as ATOMS (paramāṇu) and as
--         AGGREGATES (skandha).
--   5.26  saṅghāta-bhedebhya utpadyante — aggregates arise from combination
--         (saghta) and division (bheda).
--   5.27  bhedāt aṇuḥ — and the atom (aṇu/paramāṇu) arises by division;
--         it is itself partless, the limit of bheda.
--
-- The doctrine, exactly: a skandha is a plurality of paramus held
-- together; saghta joins two skandhas, bheda splits one; through all of
-- it the paramus themselves are neither created nor destroyed (dravya is
-- nitya, 5.3-4 — substance is permanent through its modes).  So the
-- aggregate's FORM is paryya (it originates and ceases, utpda-vyaya),
-- while the paramu-count is dhrauvya (it persists).  This is exactly the
-- three-fold real `Anekanta.ध्रौव्यम्`/`जन्मन्` (Tattvārthasūtra 5.29),
-- now for matter: change of form over conservation of substance.
--
-- WHAT IS PROVED (a skandha is a finite plurality of atoms; combination is
-- their joining; count is the number of atoms):
--
--   §2  संघातः-योगः — combination adds the counts:
--         गणना (saṅghāta a b) ≡ गणना a + गणना b.
--       Matter-count is a monoid homomorphism (Skandha, saṅghāta, aṇu⁰) →
--       (ℕ, +, 0) — the free-monoid fold of `MalaSetu` at (ℕ,+,0), here
--       the LAW OF CONSERVED MASS UNDER COMBINATION.
--   §3  भेद-संरक्षणम् — division conserves: for ANY split of s into a,b
--         (saṅghāta a b ≡ s), गणना a + गणना b ≡ गणना s.  No atom is lost
--       or made in bheda; only the form is cut.
--   §4  द्रव्य-नित्यम् — combine then divide however you like: the total
--       count is invariant.  utpda-vyaya of the FORM, dhrauvya of the
--       COUNT — stated as a round trip saṅghāta→bheda that returns the
--       count unchanged.
--   §5  अणुः-अविभाज्यः — the paramāṇu is partless: a single-atom skandha
--         admits no division into two nonempty parts (5.27's limit of
--       bheda).  The atom is where cutting stops.
--
-- No postulates, no holes, --safe.
------------------------------------------------------------------------

module Pudgala_MatterIsAtomsAndAggregatesTheFormChangesByCombinationAndDivisionButTheAtomCountPersists where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; snotz ; injSuc)
open import Cubical.Data.Nat.Properties using (+-assoc ; +-zero ; +-suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd ; _×_)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Data.Unit using (Unit)
open import Cubical.Foundations.Prelude using (Lift)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level

module _ (Paramanu : Type ℓ) where

  ------------------------------------------------------------------------
  -- §1  The atom, the aggregate, combination, division, count.
  ------------------------------------------------------------------------

  -- a skandha is a finite plurality of atoms (multiplicity via List)
  Skandha : Type ℓ
  Skandha = List Paramanu

  अणु⁰ : Skandha                       -- the empty aggregate (no atoms)
  अणु⁰ = []

  अणु : Paramanu → Skandha             -- a single atom as a skandha
  अणु p = p ∷ []

  संघातः : Skandha → Skandha → Skandha  -- combination (saṅghāta)
  संघातः = _++_

  गणना : Skandha → ℕ                    -- the atom-count
  गणना = length

  ------------------------------------------------------------------------
  -- §2  संघातः-योगः — combination adds counts (conserved mass, forward).
  ------------------------------------------------------------------------

  संघातः-योगः : (a b : Skandha) → गणना (संघातः a b) ≡ गणना a + गणना b
  संघातः-योगः []       b = refl
  संघातः-योगः (p ∷ a) b = cong suc (संघातः-योगः a b)

  -- the empty aggregate is the unit: combining with अणु⁰ changes nothing
  संघातः-रिक्तम् : (a : Skandha) → संघातः a अणु⁰ ≡ a
  संघातः-रिक्तम् []       = refl
  संघातः-रिक्तम् (p ∷ a) = cong (p ∷_) (संघातः-रिक्तम् a)

  ------------------------------------------------------------------------
  -- §3  भेद-संरक्षणम् — a division of s is a way to write it as a
  --     combination; and every division conserves the count.
  ------------------------------------------------------------------------

  भेदः : Skandha → Type ℓ
  भेदः s = Σ Skandha (λ a → Σ Skandha (λ b → संघातः a b ≡ s))

  भेद-संरक्षणम् : (s : Skandha) (d : भेदः s)
              → गणना (fst d) + गणना (fst (snd d)) ≡ गणना s
  भेद-संरक्षणम् s (a , b , e) = sym (संघातः-योगः a b) ∙ cong गणना e

  ------------------------------------------------------------------------
  -- §4  द्रव्य-नित्यम् — combine then divide: the total count returns.
  --     The FORM may be recut arbitrarily; the COUNT is dhrauvya.
  ------------------------------------------------------------------------

  द्रव्य-नित्यम् : (a b : Skandha) (d : भेदः (संघातः a b))
              → गणना (fst d) + गणना (fst (snd d)) ≡ गणना a + गणना b
  द्रव्य-नित्यम् a b d = भेद-संरक्षणम् (संघातः a b) d ∙ संघातः-योगः a b

  ------------------------------------------------------------------------
  -- §5  अणुः-अविभाज्यः — the paramāṇu is partless: a single atom cannot be
  --     split into two NONEMPTY aggregates.  bheda stops at the atom.
  ------------------------------------------------------------------------

  -- "is nonempty": has at least one atom
  _नरिक्तः : Skandha → Type ℓ
  [] नरिक्तः      = Lift ⊥
  (_ ∷ _) नरिक्तः = Lift Unit
  अणुः-अविभाज्यः : (p : Paramanu) (a b : Skandha)
              → संघातः a b ≡ अणु p
              → a नरिक्तः → b नरिक्तः → ⊥
  अणुः-अविभाज्यः p (x ∷ a) (y ∷ b) e _ _ =
    snotz (injSuc (sym (lenLaw) ∙ cong length e))
    where
    lenLaw : length ((x ∷ a) ++ (y ∷ b)) ≡ suc (suc (length a + length b))
    lenLaw = cong suc (संघातः-योगः a (y ∷ b)) ∙ cong suc (+-suc (length a) (length b))
