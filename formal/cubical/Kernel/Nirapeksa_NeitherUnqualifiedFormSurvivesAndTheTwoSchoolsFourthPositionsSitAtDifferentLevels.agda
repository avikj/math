{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Kernel.Nirapeksa_NeitherUnqualifiedFormSurvives
--                  AndTheTwoSchoolsFourthPositionsSitAtDifferentLevels
--
-- TWO SCHOOLS APPEAR IN THIS FILE.  THEY REJECT EACH OTHER'S CATEGORIES
-- AND THEY ARE NOT MERGED INTO ONE TOOLKIT.  §1 is Jaina, §2 is Bauddha,
-- and §3 states a claim ABOUT THE TWO FORMALISATIONS -- not about what
-- either tradition really means.
--
-- TERM (JAINA).  निरपेक्ष · nirapekṣa -- without reference, absolute, said
-- of an assertion made with no upādhi; against सापेक्ष · sāpekṣa, made with
-- one.  The Jaina rule is that a नय · naya asserted nirapekṣa becomes a
-- दुर्नय · durnaya.  Siddhasena Divākara, *Sanmatitarka*; developed by
-- Akalaka (~8th c.).
--
-- §1 exhibits bhagas ONE and TWO
-- (syd-asti, syd-nsti) and the KRAMA reading of the THIRD -- both, in
-- succession.  The fourth arises from
--  · yugapat, simultaneous assertion, and is not what is proved here.
--
-- TERM (BAUDDHA).  चतुष्कोटि · catuṣkoṭi -- the four corners, standard in
-- Ngrjuna's *Mlamadhyamakakrik* (~2nd c. CE).  §2 formalises the
-- FOURTH corner as ¬ (A ⊎ ¬ A) with प्रसज्यप्रतिषेध · prasajya-pratiṣedha,
-- the non-implicative negation -- the reading on which the negation
-- asserts nothing positive, which is `A → ⊥`.  The distinction from
-- पर्युदास · paryudāsa, the implicative negation, is drawn by Westerhoff in
-- the modern literature.  UNDER
-- PARYUDSA THE FOURTH CORNER IS A DIFFERENT FORMULA AND §2 DOES NOT
-- APPLY TO IT.
--
------------------------------------------------------------------------
-- PRIOR ART.
--
-- Formal treatments of both exist and are contested.  Priest and Ganeri
-- read the saptabhag as supporting a non-classical (many-valued/modal)
-- system; Balcerowicz contests that reading.  Priest and Garfield read the
-- catukoi paraconsistently, via FDE and a plurivalent extension, and
-- WOULD NOT ACCEPT §2's flat refutation of the fourth corner -- on their
-- reading it is assertable.  Schang treats the saptabhag and the
-- catukoi within ONE common framework.
--
-- §3 DISAGREES WITH SCHANG, and the disagreement is the file's point: the
-- two fourth positions are not two settings of one dial.  What would
-- refute §3 is a single formal setting in which the Jaina fourth and the
-- Bauddha fourth are the same construction.
--
------------------------------------------------------------------------
-- WHAT IS PROVED.
--
--   §1  asti, nasti, and then BOTH unqualified forms refuted:
--         no-unqualified-assertion, no-unqualified-denial.
--       So the qualified forms are not a weakening of an available
--       absolute one.  There is no absolute one, in either direction.
--       AND THIS IS NOT A CONTRADICTION: it is the ordinary condition of
--       a family over `Env` whose fibres disagree.  Contingent on the
--       pair, and false for pairs the calculus does derive.
--
--   §2  no-fourth-corner : ¬ (¬ (A ⊎ ¬ A)), for EVERY A, at every level,
--       depending on nothing.  A theorem of logic, not a fact about an
--       object.
--
--   §3  THE CONTRAST, which is the claim.  §1 is contingent, about one
--       family, and consistent.  §2 is universal, about no family, and a
--       refutation.  A doctrine whose fourth position is §1's shape and a
--       doctrine whose fourth position is §2's shape are not variants of
--       one logic: the first lives in the dependency of a type on an
--       index, the second in the propositional structure of negation.
------------------------------------------------------------------------

module Kernel.Nirapeksa_NeitherUnqualifiedFormSurvivesAndTheTwoSchoolsFourthPositionsSitAtDifferentLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (znots)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; Σ-syntax)
import Cubical.Data.Empty as E

open import Kernel.RewriteCertificate

private
  variable
    ℓ : Level

infix 3 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → E.⊥

------------------------------------------------------------------------
-- §1.  JAINA.  One pair, two respects, and no absolute form either way.
------------------------------------------------------------------------

diagonal off-diagonal : Env
diagonal     = env 0 0 0 0 0 0
off-diagonal = env 0 1 0 0 0 0

-- syd-asti: in the respect where the coordinates agree, it is.
asti : eval var diagonal ≡ eval yvar diagonal
asti = refl

-- syd-nsti: in the respect where they differ, it is not.
nasti : ¬ (eval var off-diagonal ≡ eval yvar off-diagonal)
nasti = znots

-- and NEITHER absolute form is available.  The qualifier is not a hedge
-- on an assertion one could otherwise make; there is nothing to hedge.
no-unqualified-assertion : ¬ ((ρ : Env) → eval var ρ ≡ eval yvar ρ)
no-unqualified-assertion f = nasti (f off-diagonal)

no-unqualified-denial : ¬ ((ρ : Env) → ¬ (eval var ρ ≡ eval yvar ρ))
no-unqualified-denial g = g diagonal asti

------------------------------------------------------------------------
-- §2.  BAUDDHA.  The fourth corner under prasajya negation, refuted for
--      every A, at every level, on no hypothesis at all.
------------------------------------------------------------------------

no-fourth-corner : {A : Type ℓ} → ¬ (¬ (A ⊎ (¬ A)))
no-fourth-corner k = k (inr (λ a → k (inl a)))

------------------------------------------------------------------------
-- §3.  THE CONTRAST, STATED AS THE TYPES SHOW IT.
--
--   §1  ¬ ((ρ : Env) → P ρ)   and   ¬ ((ρ : Env) → ¬ P ρ)
--       A Π over an index is refuted in both directions.  The content is
--       that P is NOT CONSTANT.  Contingent, consistent, and about a
--       family.  For a pair the calculus derives, both statements fail.
--
--   §2  ¬ (¬ (A ⊎ ¬ A))
--       No index, no family, no hypothesis.  The content is the
--       propositional structure of negation itself.
--
-- One is about DEPENDENCY, the other about NEGATION.  They are not two
-- values of one parameter, and a framework that renders them as such has
-- flattened the difference rather than explained it.
------------------------------------------------------------------------

-- The Jaina configuration, as one object, so §3 is read off the types and not the prose.
saptabhangi-shape :
  (¬ ((ρ : Env) → eval var ρ ≡ eval yvar ρ))
  × (¬ ((ρ : Env) → ¬ (eval var ρ ≡ eval yvar ρ)))
saptabhangi-shape = no-unqualified-assertion , no-unqualified-denial

-- and the same configuration WITH its witnesses, so the packaged object
-- does not drop what §1 exhibits: a respect where it holds and a respect
-- where it fails, each named.  Constructively this is strictly stronger
-- than `saptabhangi-shape`, which records only the two refutations.
saptabhangi-witnessed :
  (Σ[ ρ ∈ Env ] (eval var ρ ≡ eval yvar ρ))
  × (Σ[ ρ ∈ Env ] (¬ (eval var ρ ≡ eval yvar ρ)))
saptabhangi-witnessed = (diagonal , asti) , (off-diagonal , nasti)

