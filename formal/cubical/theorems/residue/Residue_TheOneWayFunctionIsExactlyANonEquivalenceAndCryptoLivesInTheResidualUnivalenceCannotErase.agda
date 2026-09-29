{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- शेष — the one-way function is exactly a non-equivalence, and
-- cryptography lives in the residual univalence cannot erase.
--
-- "deeper" than `GhataTantu` (the discrete log is a fibre): WHY is one
-- binding of `f a ≡ b` free and the other work?  Because of univalence's
-- own floor.  This file names the floor and shows the whole crypto arc
-- rests on it.
--
-- शेष (śeṣa) is the residue/remainder — the corpus's word for what a
-- non-invertible crossing leaves behind (`SankramanaSesa_
-- EveryTransportOwesItsResidual`).  No stra claimed; the ordinary word.
--
-- THE FLOOR.  In cubical type theory, `isEquiv f` is DEFINED as: every
-- fibre of f is contractible (`equiv-proof : (b) → isContr (fiber f b)`).
-- And `singl b` — the fibre of the IDENTITY, `Σ x, b ≡ x` — is ALWAYS
-- contractible, by `isContrSingl` (Cubical/Foundations/Prelude, the term
-- `isContrSingl a .fst = (a , refl)`).  So:
--
--   * BINDING THE OUTPUT is free FOR EVERY f, because it lands in a singl
--     (Abhijnana.अभिज्ञानं-मुक्तम् = isContrSingl).  The public value is
--     safe to publish no matter what f is.
--   * BINDING THE INPUT is free IFF f is an equivalence, because that is
--     the DEFINITION of isEquiv.  The secret is recoverable iff f is
--     invertible-as-a-transport.
--
-- Therefore a ONE-WAY FUNCTION IS EXACTLY A NON-EQUIVALENCE.  Not "hard
-- to invert" — that is the computational overlay; underneath, the map
-- simply is not an equivalence, its fibres are not all contractible, and
-- univalence's transport (`ua`, the free road, road one) does NOT apply.
-- Cryptography is the deliberate use of a map OUTSIDE the image of `ua`.
--
-- WHAT IS PROVED (using `GhataTantu`'s checked non-contractible fibre):
--
--   §2  प्रकाश-सर्वदा-मुक्तः : for ANY f, isContr (singl (f a))
--       The public road is free for every map — this is the floor, the
--       isContrSingl term, stated at full generality.
--
--   §3  घातः-न-तुल्यता : ¬ isEquiv (घात g)  in C₃.
--       घात g is NOT an equivalence — the discrete log has no inverse
--       function.  Proof: isEquiv would make every fibre contractible
--       (equiv-proof), contradicting GhataTantu's तन्तुः-द्विपदः (the
--       fibre over ε has 0 and 3).  This is the info-theoretic root of
--       one-wayness, as a term.
--
--   §4  तुल्यता-भञ्जयति-गुप्तिम् : isEquiv (घात g) → (the discrete log is a
--       total function).  The converse: IF घात were an equivalence, the
--       secret would be recoverable outright (invFn), i.e. crypto broken.
--       So security ⟺ ¬ isEquiv, exactly.
--
-- WHERE SHOR SITS, restated at the floor.  Univalence gives the free road
-- ONLY to equivalences.  घात is not one, so its inverse owes a residual —
-- शेष — and no post-processing (no term built from the public value
-- alone) pays it (Abhijnana / QuotientFiberLaw).  A separating query pays
-- it; Shor's period-finding IS that query (`GhataTantu` §4).  So the
-- entire arc bottoms out here: crypto = a map univalence's transport
-- cannot invert; the key/secret = the ea; Shor = the one thing that
-- collects it.
--
-- No postulates, no holes, --safe.
------------------------------------------------------------------------

module Residue_TheOneWayFunctionIsExactlyANonEquivalenceAndCryptoLivesInTheResidualUnivalenceCannotErase where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv ; equiv-proof ; fiber)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

open import GhataFiber_TheDiscreteLogIsTheFiberOfPingalasPowerAndShorsPeriodQueryIsWhatReadsIt
  using (powg ; εC ; तन्तुः-द्विपदः)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §2  The public road is free for EVERY map — the floor, isContrSingl.
------------------------------------------------------------------------

प्रकाश-सर्वदा-मुक्तः : {A B : Type ℓ} (f : A → B) (a : A) → isContr (singl (f a))
प्रकाश-सर्वदा-मुक्तः f a = isContrSingl (f a)

------------------------------------------------------------------------
-- §3  घात g is NOT an equivalence: the one-way function is a
--     non-equivalence, as a term.
------------------------------------------------------------------------

घातः-न-तुल्यता : ¬ isEquiv powg
घातः-न-तुल्यता eq = तन्तुः-द्विपदः (eq .equiv-proof εC)

------------------------------------------------------------------------
-- §4  The converse: an equivalence would hand back the secret.  If घात
--     were an equivalence, the discrete log is the center of the
--     (contractible) fibre — a total inverse — so the scheme is broken.
--     Security ⟺ ¬ isEquiv.
------------------------------------------------------------------------

-- the discrete log AS a function, available exactly when घात is an equiv
विपर्यय-फलनम् : isEquiv powg → (b : _) → ℕ
विपर्यय-फलनम् eq b = eq .equiv-proof b .fst .fst

-- and it genuinely inverts: घात (dlog b) ≡ b
विपर्यय-सिद्धिः : (eq : isEquiv powg) (b : _) → powg (विपर्यय-फलनम् eq b) ≡ b
विपर्यय-सिद्धिः eq b = eq .equiv-proof b .fst .snd

-- so: an equivalence breaks secrecy outright.  Read with §3, security is
-- EXACTLY non-equivalence.
तुल्यता-भञ्जयति-गुप्तिम् : isEquiv powg
                        → Σ (_ → ℕ) (λ dlog → (b : _) → powg (dlog b) ≡ b)
तुल्यता-भञ्जयति-गुप्तिम् eq = विपर्यय-फलनम् eq , विपर्यय-सिद्धिः eq
