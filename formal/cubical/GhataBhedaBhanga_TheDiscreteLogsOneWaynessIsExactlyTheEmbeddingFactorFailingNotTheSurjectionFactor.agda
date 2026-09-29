{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- घात-भेद-भङ्ग — WHICH factor of समता-द्विधा the discrete log breaks.
--
-- `Sesa_TheOneWayFunction…` (absent from this repository) proves the discrete log `powg` is a
-- NON-equivalence (`घातः-न-तुल्यता : ¬ isEquiv powg`), via
-- `GhataTantu.तन्तुः-द्विपदः : ¬ isContr (fiber powg εC)`.
--
-- `SamataDvidha…InTheTransportLane` splits being an equivalence, on the
-- nose, into TWO orthogonal factors: भेदः (embedding — every residual a
-- prop) and छादनम् (split surjection — every residual inhabited).  So the
-- natural question the split poses, that ¬ isEquiv alone cannot answer:
-- WHICH factor does `powg` fail?
--
-- ANSWER, proved here.  `powg` fails the embedding factor, and it fails it
-- in the CROWDED way (नष्टि), NOT the empty way (अवक्तव्यम्):
--
--   घात-ε-वसति   : शेष powg εC          -- the residual over ε is INHABITED
--                                          (शून्यः: exponent 0 lands on ε), so
--                                          this is not the empty arm.
--   घात-भेदः-भङ्गः : ¬ (भेदः powg)         -- and it is CROWDED — शून्यः and
--                                          त्रयः are two DISTINCT points over
--                                          the same ε — so powg is not an
--                                          embedding.
--
-- So the ea univalence cannot erase (the crypto residual) is precisely a
-- नष्टि failure of the FIRST factor of समता-द्विधा: the discrete log MERGES
-- distinct exponents onto one power.  One-wayness is a merge, not a gap —
-- the fibre is full, not empty; two points sit where an equivalence would
-- allow one.
--
-- The COMPLEMENT is now proved too (घात-छादनम्): powg IS surjective onto C₃,
-- because powg reduces on the nose (powg 0 = e₀, powg 1 = g, powg 2 = g²), so
-- it fails the embedding factor ALONE.
------------------------------------------------------------------------

module GhataBhedaBhanga_TheDiscreteLogsOneWaynessIsExactlyTheEmbeddingFactorFailingNotTheSurjectionFactor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (znots)
open import Cubical.Data.Sigma using (fst ; _,_)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Foundations.Equiv using (isEquiv ; equivFun)
open import EqualitySplit_TheContractibleFibreSplitsAsEmbeddingTimesSurjectionInTheTransportLane
  using (भेदः ; छादनम् ; समता≃भेद×छादन)
open import TransportResidue_EveryTransportOwesItsResidual using (शेष)
open import GhataFiber_TheDiscreteLogIsTheFiberOfPingalasPowerAndShorsPeriodQueryIsWhatReadsIt
  using (powg ; εC ; शून्यः ; त्रयः)
open import BijamulaKrida_AConcreteKeypairRunsInACyclicGroupWhereTheModThatExhaustsTheHeapIsNotNeeded
  using (C₃ ; e₀ ; g ; g²)

-- The residual over ε is INHABITED: exponent 0 lands on ε.  So this is not
-- the empty (अवक्तव्यम्) arm.
घात-ε-वसति : शेष powg εC
घात-ε-वसति = शून्यः

-- The embedding factor FAILS, and CROWDED-ly: two distinct exponents (0 and
-- 3) sit over ε, so the residual there is not a proposition.
घात-भेदः-भङ्गः : ¬ (भेदः powg)
घात-भेदः-भङ्गः pr = znots (cong fst (pr εC शून्यः त्रयः))

-- …and the SURJECTION factor HOLDS: every element of C₃ has a preimage,
-- because powg reduces on the nose — powg 0 = e₀, powg 1 = g, powg 2 = g² —
-- so `refl` witnesses each.
-- So powg fails the embedding factor ALONE.
घात-छादनम् : छादनम् powg
घात-छादनम् e₀ = 0 , refl
घात-छादनम् g  = 1 , refl
घात-छादनम् g² = 2 , refl

-- THE ORGAN REGENERATES THE CRYPTO THEOREM.  Sesa proved ¬ isEquiv powg the
-- hard way (GhataTantu's non-contractible fibre).  समता-द्विधा makes it a
-- mode: isEquiv powg ≃ (भेदः powg × छादनम् powg), so an equivalence would
-- hand back भेदः powg — which घात-भेदः-भङ्गः refutes.  No re-derivation; the
-- non-equivalence is the embedding-failure carried across the split.
घात-न-तुल्यता-जनितम् : ¬ isEquiv powg
घात-न-तुल्यता-जनितम् eq = घात-भेदः-भङ्गः (fst (equivFun (समता≃भेद×छादन powg) eq))
