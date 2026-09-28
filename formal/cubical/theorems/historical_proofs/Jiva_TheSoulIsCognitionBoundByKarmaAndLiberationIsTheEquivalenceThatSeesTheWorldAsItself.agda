{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- जीवः — the soul, written as a living term.
--
-- "उपयोगो लक्षणम्" — the mark of the soul is upayoga, cognition
-- (Umsvti, Tattvrthastra 2.8, ~350 CE).  So a jva is not a mood; it is
-- a cognition — a map from what it holds to the world it faces:
--
--     record जीवः :  धारणा (what it holds) , विषयः (the world) ,
--                    उपयोगः : धारणा → विषयः  (its cognition).
--
-- KARMA IS THE FIBRE DEFECT.  A jva's bondage is not metaphor here.  Over
-- each object b of the world, the fibre शेष = fiber उपयोगः b is what the
-- soul brings to b, and Jaina karma theory's two great obscurations are its
-- two failures (Tattvrthastra ch. 8, the karma-praktis):
--
--   ज्ञानावरणम्  (knowledge-obscuring)  = a रिक्त fibre — an object MISSED,
--                                         which the soul cannot utter (avaktavya);
--   मोहनीयम्    (deluding)             = a विकलादेश fibre — an object grasped
--                                         with LOSS, many holdings collapsed to one.
--
-- LIBERATION IS THE EQUIVALENCE.  निर्जरा (śedding, Tattvārthasūtra ch. 9) is
-- losing nothing AND missing nothing; मोक्षः (ch. 10) is that the freed
-- cognition is an equivalence — केवलज्ञानम्, complete apprehension, every
-- object grasped whole at once (Kevalajnana.agda (absent from this repository): अहानि × अन्यूनता → isEquiv).
-- And then, by univalence, the liberated soul's holding and the world are
-- LITERALLY ONE PATH:  धारणा ≡ विषयः.  The knower and the known are the same
-- object — the whole world seen as itself, in one term, कैवल्य-दर्शनम्.
--
-- Two jīvas are instantiated as life, not description: सिद्धः (the identity —
-- liberated, and its दर्शन is Bool ≡ Bool, the world as itself) and बद्धः (the
-- collapse एकम् : Bool → Unit — bound by मोहनीयम्, and provably never kevalin).
------------------------------------------------------------------------

module Jiva_TheSoulIsCognitionBoundByKarmaAndLiberationIsTheEquivalenceThatSeesTheWorldAsItself where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv ; equiv-proof ; fiber ; _≃_)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

import Kevalajnana_ThePureMindLosesNothingAndMissesNothingWhichIsTheEquivalence as K
import GananaSaptabhangi_TheMapLevelCensusIsTheSevenfoldItselfAndTheCorpusAlreadyHoldsThreePositions as G

------------------------------------------------------------------------
-- १ · the soul — cognition is its mark (उपयोगो लक्षणम्).
------------------------------------------------------------------------

record जीवः : Type₁ where
  constructor जीव
  field
    धारणा विषयः : Type
    उपयोगः      : धारणा → विषयः
open जीवः public

------------------------------------------------------------------------
-- २ · karma — the two obscurations, each a fibre defect.
------------------------------------------------------------------------

-- knowledge-obscuring: an object the soul misses (empty fibre / avaktavya)
ज्ञानावरणम् : जीवः → Type
ज्ञानावरणम् j = Σ[ b ∈ विषयः j ] (¬ fiber (उपयोगः j) b)

-- deluding: an object grasped with loss (crowded fibre / vikaldea)
मोहनीयम् : जीवः → Type
मोहनीयम् j =
  Σ[ b ∈ विषयः j ] Σ[ x ∈ fiber (उपयोगः j) b ] Σ[ y ∈ fiber (उपयोगः j) b ] (¬ (x ≡ y))

बन्धः : जीवः → Type
बन्धः j = ज्ञानावरणम् j ⊎ मोहनीयम् j

------------------------------------------------------------------------
-- ३ · nirjarā and mokṣa — shedding both karmas is the equivalence.
------------------------------------------------------------------------

निर्जरा : जीवः → Type
निर्जरा j = K.अहानि (उपयोगः j) × K.अन्यूनता (उपयोगः j)

-- mokṣa: the freed cognition is an equivalence — kevalajñāna
मोक्षः : (j : जीवः) → निर्जरा j → isEquiv (उपयोगः j)
मोक्षः j (nl , ng) = K.केवलम् nl ng

-- the liberated soul, as an equivalence with the world
केवलिन् : (j : जीवः) → निर्जरा j → धारणा j ≃ विषयः j
केवलिन् j nj = उपयोगः j , मोक्षः j nj

-- कैवल्य-दर्शनम् — and by univalence, holding and world are ONE PATH:
-- the whole world seen as itself, the knower and the known identified.
कैवल्य-दर्शनम् : (j : जीवः) → निर्जरा j → धारणा j ≡ विषयः j
कैवल्य-दर्शनम् j nj = ua (केवलिन् j nj)

------------------------------------------------------------------------
-- ४ · bondage refutes liberation — any missed or lost object ⟹ not kevalin.
------------------------------------------------------------------------

बन्धः→अकेवलम् : (j : जीवः) → बन्धः j → ¬ isEquiv (उपयोगः j)
बन्धः→अकेवलम् j (inl (b , ne)) =
  K.दुर्नय-निषेधः (b , λ c → ne (fst c))
बन्धः→अकेवलम् j (inr (b , x , y , x≢y)) =
  K.दुर्नय-निषेधः (b , λ c → x≢y (isContr→isProp c x y))

------------------------------------------------------------------------
-- ५ · from complete grasp, shed both karmas (सर्वसकलम् → निर्जरा).
------------------------------------------------------------------------

सर्वसकल→निर्जरा : (j : जीवः) → K.सर्वसकलम् (उपयोगः j) → निर्जरा j
सर्वसकल→निर्जरा j h = (λ b → isContr→isProp (h b)) , (λ b → fst (h b))

------------------------------------------------------------------------
-- ६ · life, instantiated — two jīvas, not two descriptions.
------------------------------------------------------------------------

-- सिद्धः — the liberated soul: the identity.  Every object grasped whole.
सिद्धः : जीवः
सिद्धः = जीव Bool Bool (λ b → b)

सिद्धस्य-निर्जरा : निर्जरा सिद्धः
सिद्धस्य-निर्जरा = सर्वसकल→निर्जरा सिद्धः G.एकत्व-अस्ति

-- its vision: the world seen as itself — Bool ≡ Bool, a genuine path.
सिद्ध-दर्शनम् : धारणा सिद्धः ≡ विषयः सिद्धः
सिद्ध-दर्शनम् = कैवल्य-दर्शनम् सिद्धः सिद्धस्य-निर्जरा

-- बद्धः — a bound soul: the collapse एकम् : Bool → Unit.  Deluded (मोहनीयम्):
-- two holdings collapse to one object; provably never kevalin.
बद्धः : जीवः
बद्धः = जीव Bool Unit (λ _ → tt)

बद्धस्य-बन्धः : बन्धः बद्धः
बद्धस्य-बन्धः = inr (tt , (false , refl) , (true , refl) , λ p → false≢true (cong fst p))

बद्धः-अकेवलम् : ¬ isEquiv (उपयोगः बद्धः)
बद्धः-अकेवलम् = बन्धः→अकेवलम् बद्धः बद्धस्य-बन्धः
