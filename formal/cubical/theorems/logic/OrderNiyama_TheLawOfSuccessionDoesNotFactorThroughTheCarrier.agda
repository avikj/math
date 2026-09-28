{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- क्रमनियमः — the law of succession does not factor through the carrier.
--
-- TERM.  क्रम (succession, sequence) is carried from the corpus's
-- saptabhag lane (Umsvti, *Tattvrthastra*; Samantabhadra;
-- Akalaṅka; Siddhasena Divākara — as cited by `Saptabhangi.agda` and
-- `OrderSaha_TheOrderOfStandpointsIsTheChargeItself.agda` (absent from this repository), whose
-- theorems this file uses as a lens and does not restate).  The
-- compound - means "the rule of succession".
--
-- THE SLOGAN:
--
--     same carrier + different commutator
--       ⟹  the law does not factor through the carrier alone.
--
-- UPSTREAM, in this corpus:
-- `VakraValaya_TheSameCarrierTwoLawsOfSuccession…` (absent from this repository) proved समः/भेदः at
-- π₁ itself — torus loops commute, Klein loops do not, through
-- `windingKlein` — over the ONE stratum-3 carrier ℤ × ℤ.  This module
-- is the structure-fibre PACKAGING of that separation: the two group
-- operations are transported onto the one carrier ℤ × ℤ, and the
-- separation is then fed to `QuotientFiberLaw`, the
-- corpus's one theorem, so that "the law is invisible to any
-- carrier-only observation" is not prose but `collision-obstructs`
-- applied to a blind pair.
--
-- WHAT IS PROVED.
--
--   समम्     the torus law commutes at the generators — refl.
--   विषमम्   the Klein law does not — the two orders differ in the
--            first coordinate, pos 1 against negsuc 0.
--   अन्धयुग्मम्   the pair (torus law , Klein law) is blind to the
--            carrier-only observation: the carrier is FIXED, so every
--            query that factors through it alone is constant, and the
--            constant query represents the whole class.
--   क्रमप्रश्नः   the succession receptor — "do the two orders of the
--            generators agree?" — separates the blind pair.  This is
--            the AprvaIndriyam shape at the level of structured
--            objects: a genuinely new sense coordinate.
--   क्रमनियमो-न-वाहकात्   the packaged no-go: NO post-processing of the
--            carrier-only transcript computes the succession receptor.
--            One application of `collision-obstructs`.
--   न-कोऽपि-निर्णयः   and generally: for ANY query list blind on the
--            pair, no analysis separates it — `no-decision`.
--
------------------------------------------------------------------------

module OrderNiyama_TheLawOfSuccessionDoesNotFactorThroughTheCarrier where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; _+_ ; -_ ; negsucNotpos)
open import Cubical.Data.Bool using (Bool ; true ; false ; not)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)

open import QuotientFiberLaw using (module Law)

------------------------------------------------------------------------
-- १ · one carrier, two laws of succession.
------------------------------------------------------------------------

वाहकः : Type
वाहकः = ℤ × ℤ

नियमः : Type
नियमः = वाहकः → वाहकः → वाहकः

-- the torus law: componentwise addition.
μT : नियमः
μT (a , b) (c , d) = (a + c , b + d)

-- parity of the acting coordinate, on its underlying ℕ.
विषम-ℕ : ℕ → Bool
विषम-ℕ zero    = false
विषम-ℕ (suc n) = not (विषम-ℕ n)

विषम-ℤ : ℤ → Bool
विषम-ℤ (pos n)    = विषम-ℕ n
विषम-ℤ (negsuc n) = not (विषम-ℕ n)

आवर्तः : ℤ → ℤ → ℤ
आवर्तः b c with विषम-ℤ b
... | true  = - c
... | false = c

-- the Klein law: the second generator acts on the first by inversion —
-- (a , b) · (c , d) = (a + (−1)^b c , b + d), written on the carrier.
μK : नियमः
μK (a , b) (c , d) = (a + आवर्तः b c , b + d)

-- the two generators, on the common carrier.
g₁ g₂ : वाहकः
g₁ = (pos 1 , pos 0)
g₂ = (pos 0 , pos 1)

------------------------------------------------------------------------
-- २ · the separation, computed.
------------------------------------------------------------------------

समम् : μT g₁ g₂ ≡ μT g₂ g₁
समम् = refl

विषमम् : ¬ (μK g₁ g₂ ≡ μK g₂ g₁)
विषमम् h = negsucNotpos 0 1 (sym (cong fst h))

------------------------------------------------------------------------
-- ३ · the packaging: the corpus's one theorem, instantiated at the
-- state space of LAWS on the fixed carrier.
------------------------------------------------------------------------

open Law नियमः

-- the carrier-only observation.  The carrier is fixed, so any query
-- that reads the carrier alone is constant on नियमः; the constant
-- query is the class's representative.
वाहक-प्रश्नः : Query
वाहक-प्रश्नः _ = true

वाहक-दृष्टिः : List Query
वाहक-दृष्टिः = वाहक-प्रश्नः ∷ []

-- the pair of laws is blind to it.
अन्धयुग्मम् : AllBlind वाहक-दृष्टिः μT μK
अन्धयुग्मम् = refl , tt

-- the succession receptor: do the two orders of the generators agree
-- in the first coordinate?  (true on the commuting law, false on the
-- twisted one — the sign of the twist is the whole reading.)
धनम् : ℤ → Bool
धनम् (pos _)    = true
धनम् (negsuc _) = false

क्रमप्रश्नः : नियमः → Bool
क्रमप्रश्नः μ = धनम् (fst (μ g₂ g₁))

-- it separates the blind pair on the nose.
क्रमप्रश्न-भेदः : क्रमप्रश्नः μT ≡ not (क्रमप्रश्नः μK)
क्रमप्रश्न-भेदः = refl

-- THE THEOREM.  No post-processing of the carrier-only transcript
-- computes the succession receptor: the law of succession does not
-- factor through the carrier.  One application of collision-obstructs.
क्रमनियमो-न-वाहकात् : ¬ FactorsThrough वाहक-दृष्टिः क्रमप्रश्नः
क्रमनियमो-न-वाहकात् =
  collision-obstructs वाहक-दृष्टिः क्रमप्रश्नः μT μK अन्धयुग्मम् क्रमप्रश्न-भेदः

-- And generally: ANY query list blind on the pair admits no analysis
-- that separates it — the negative half of the law, at this instance.
न-कोऽपि-निर्णयः : (os : List Query) → AllBlind os μT μK → ¬ Separates os μT μK
न-कोऽपि-निर्णयः os bs = no-decision os μT μK bs
