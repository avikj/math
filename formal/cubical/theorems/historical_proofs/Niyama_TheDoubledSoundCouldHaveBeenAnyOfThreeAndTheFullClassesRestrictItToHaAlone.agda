{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Niyama — the doubled sound could have been any of three, and the full
-- classes restrict it to ha alone.
--
-- SOURCE for the term.  *Niyama* is the stric category of the
-- restricting rule: where more than one course is open, a niyama cuts
-- the options to one.  The vidhi / niyama / pratiedha triad is operated
-- throughout Patajali's *Mahbhya* (~150 BCE) and is a load-bearing
-- category of Mms.
-- The term names the SHAPE of this file's result.
--
-- WHERE THIS STANDS.  `Vyavaya_TheAttestedTrioForcesATwiceRecitedSound-
-- AndPaninisChoiceIsHa.agda` (absent from this repository) proved: no line reciting h, y,  once each
-- names three classes restricting to the {h y }-cycle; so ONE OF the
-- three must be said twice.  That the
-- repeated one is ha is Pini's choice.  This file examines the choice
-- and finds it was not one.
--
-- WHAT IS PROVED.  The same trio of attested classes restricts to a
-- 3-cycle on TWO MORE triples of sounds, computed by refl from the
-- stretches Vyavya extracted from the real line:
--
--     on {h v ś} :  aṬ↾ = {h v}   śaL↾ = {ś h}   yaR↾ = {v ś}
--     on {h y ṣ} :  aṬ↾ = {h y}   śaL↾ = {ṣ h}   yaR↾ = {y ṣ}
--
-- and the impossibility theorem is proved ONCE, parametrically over any
-- triple of sounds (त्रिकोणे-त्रयम्-असाध्यम्): for any t₁ t₂ t₃, any
-- line whose {t₁ t₂ t₃}-subsequence is one of the six permutations
-- admits no three classes restricting to {t₁t₂}, {t₁t₃}, {t₂t₃}.  The
-- six seat-denial checks arrive as arguments and are discharged by refl
-- at each instantiation; Vyavya's own theorem is re-derived as the
-- third instance, as a coherence check.
--
-- THE NIYAMA, read off the three instances together.  Let a line name
-- the full attested trio and recite AT MOST ONE sound twice.  Markers
-- are unconstrained throughout — every theorem here quantifies over
-- arbitrary marker placement, so no marker arrangement escapes.  Case on
-- the doubled sound d:
--
--   d ∉ {h y ś}      : h, y, ś stand once each — Vyavāya's instance
--                      (re-derived here) refutes the line.
--   d = y            : h, v, ś stand once each — the {h v ś} instance
--                      refutes it.  (y is not in that triple; doubling
--                      it buys nothing there.)
--   d = ś            : h, y, ṣ stand once each — the {h y ṣ} instance
--                      refutes it.
--   d = h            : survives — and the real line attains it
--                      (`रेखा`, repetition count exactly one, Vyavāya §8).
--
-- So among single-doubling lines, ha is the ONLY admissible choice.  The
-- reason is visible in the intersections: aṬ ∩ śaL = {h} exactly — ha is
-- the sole articulation point of the triangle, the one sound whose
-- doubling dismantles every 3-cycle the trio generates.  Doubling y or 
-- breaks one cycle and leaves another standing; doubling h leaves none.
-- Pini's "choice" of ha is forced by the classes themselves.
--
-- No postulates, no holes, --safe.  The generic machinery, the alphabet,
-- the line and the three stretches are imported from Vyavya; the
-- parametric theorem is proved here; every concrete discharge is refl.
------------------------------------------------------------------------

module Niyama_TheDoubledSoundCouldHaveBeenAnyOfThreeAndTheFullClassesRestrictItToHaAlone where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; _or_ ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)

open import Vyavaya_TheAttestedTrioForcesATwiceRecitedSoundAndPaninisChoiceIsHa
open Kartana Varṇa eqV

------------------------------------------------------------------------
-- §1  The triple-parametric membership predicate and content summary.
------------------------------------------------------------------------

tOn : Varṇa → Varṇa → Varṇa → Varṇa → Bool
tOn t₁ t₂ t₃ x₀ = eqV x₀ t₁ or (eqV x₀ t₂ or eqV x₀ t₃)

sigOn : Varṇa → Varṇa → Varṇa → List Varṇa → Sig₃
sigOn t₁ t₂ t₃ xs = sg₃ (occV t₁ xs) (occV t₂ xs) (occV t₃ xs)

षट्कम् : Varṇa → Varṇa → Varṇa → List (List Varṇa)
षट्कम् t₁ t₂ t₃ = (t₁ ∷ t₂ ∷ t₃ ∷ []) ∷ (t₁ ∷ t₃ ∷ t₂ ∷ [])
                ∷ (t₂ ∷ t₁ ∷ t₃ ∷ []) ∷ (t₂ ∷ t₃ ∷ t₁ ∷ [])
                ∷ (t₃ ∷ t₁ ∷ t₂ ∷ []) ∷ (t₃ ∷ t₂ ∷ t₁ ∷ []) ∷ []

------------------------------------------------------------------------
-- §2  Seat denial, parametric in the summary.  Identical in structure to
--     Vyavāya's एकासनम्; restated because that one fixes tHYŚ and sig₃.
------------------------------------------------------------------------

वारणम् : (tP : Varṇa → Bool) (sigP : List Varṇa → Sig₃)
         (Pm : List Varṇa) (pr : Sig₃)
       → eqSig₃ pr pr ≡ true
       → allL (λ tr → not (eqSig₃ (sigP (fst (snd tr))) pr)) (allSplits Pm) ≡ true
       → (ℓ₀ q₀ : List Varṇa) (st mk : Varṇa)
       → keep tP ℓ₀ ≡ Pm
       → klassL st mk ℓ₀ ≡ just q₀
       → sigP (keep tP q₀) ≡ pr
       → ⊥
वारणम् tP sigP Pm pr prSelf noOuter ℓ₀ q₀ st mk pP kEq sEq =
  let fac = klassL-factor st mk ℓ₀ q₀ kEq
      us = fst fac
      ws = fst (snd fac)
      kp : keep tP ℓ₀ ≡ keep tP us ++ keep tP q₀ ++ keep tP ws
      kp = cong (keep tP) (snd (snd fac)) ∙ keep-++₃ tP us q₀ ws
      mm : (keep tP us , (keep tP q₀ , keep tP ws)) ∈ᴸ allSplits Pm
      mm = subst (λ zs → (keep tP us , (keep tP q₀ , keep tP ws)) ∈ᴸ allSplits zs)
                 (sym kp ∙ pP)
                 (allSplits-complete (keep tP us) (keep tP q₀) (keep tP ws))
      lk : not (eqSig₃ (sigP (keep tP q₀)) pr) ≡ true
      lk = ∈ᴸ-lookup (λ tr → not (eqSig₃ (sigP (fst (snd tr))) pr)) (allSplits Pm) mm noOuter
      fl : not (eqSig₃ (sigP (keep tP q₀)) pr) ≡ false
      fl = cong (λ zs → not (eqSig₃ zs pr)) sEq ∙ cong not prSelf
  in ⊥rec (true≢false (sym lk ∙ fl))

------------------------------------------------------------------------
-- §3  The theorem, once, for every triple.  The six noOuter checks are
--     arguments; at a concrete triple each is refl.
------------------------------------------------------------------------

private
  NoOuter : Varṇa → Varṇa → Varṇa → List Varṇa → Sig₃ → Type
  NoOuter t₁ t₂ t₃ Pm pr =
    allL (λ tr → not (eqSig₃ (sigOn t₁ t₂ t₃ (fst (snd tr))) pr)) (allSplits Pm) ≡ true

त्रिकोणे-त्रयम्-असाध्यम् :
    (t₁ t₂ t₃ : Varṇa)
  → NoOuter t₁ t₂ t₃ (t₁ ∷ t₂ ∷ t₃ ∷ []) (sg₃ true false true)
  → NoOuter t₁ t₂ t₃ (t₁ ∷ t₃ ∷ t₂ ∷ []) (sg₃ true true false)
  → NoOuter t₁ t₂ t₃ (t₂ ∷ t₁ ∷ t₃ ∷ []) (sg₃ false true true)
  → NoOuter t₁ t₂ t₃ (t₂ ∷ t₃ ∷ t₁ ∷ []) (sg₃ true true false)
  → NoOuter t₁ t₂ t₃ (t₃ ∷ t₁ ∷ t₂ ∷ []) (sg₃ false true true)
  → NoOuter t₁ t₂ t₃ (t₃ ∷ t₂ ∷ t₁ ∷ []) (sg₃ true false true)
  → (ℓ₀ : List Varṇa)
  → keep (tOn t₁ t₂ t₃) ℓ₀ ∈ᴸ षट्कम् t₁ t₂ t₃
  → (st₁ mk₁ st₂ mk₂ st₃ mk₃ : Varṇa) (q₁ q₂ q₃ : List Varṇa)
  → klassL st₁ mk₁ ℓ₀ ≡ just q₁ → sigOn t₁ t₂ t₃ (keep (tOn t₁ t₂ t₃) q₁) ≡ sg₃ true true false
  → klassL st₂ mk₂ ℓ₀ ≡ just q₂ → sigOn t₁ t₂ t₃ (keep (tOn t₁ t₂ t₃) q₂) ≡ sg₃ true false true
  → klassL st₃ mk₃ ℓ₀ ≡ just q₃ → sigOn t₁ t₂ t₃ (keep (tOn t₁ t₂ t₃) q₃) ≡ sg₃ false true true
  → ⊥
त्रिकोणे-त्रयम्-असाध्यम् t₁ t₂ t₃ n₁ n₂ n₃ n₄ n₅ n₆ ℓ₀ (inl pP) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  वारणम् (tOn t₁ t₂ t₃) (sigOn t₁ t₂ t₃) (t₁ ∷ t₂ ∷ t₃ ∷ []) (sg₃ true false true) refl n₁ ℓ₀ q₂ st₂ mk₂ pP k₂ g₂
त्रिकोणे-त्रयम्-असाध्यम् t₁ t₂ t₃ n₁ n₂ n₃ n₄ n₅ n₆ ℓ₀ (inr (inl pP)) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  वारणम् (tOn t₁ t₂ t₃) (sigOn t₁ t₂ t₃) (t₁ ∷ t₃ ∷ t₂ ∷ []) (sg₃ true true false) refl n₂ ℓ₀ q₁ st₁ mk₁ pP k₁ g₁
त्रिकोणे-त्रयम्-असाध्यम् t₁ t₂ t₃ n₁ n₂ n₃ n₄ n₅ n₆ ℓ₀ (inr (inr (inl pP))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  वारणम् (tOn t₁ t₂ t₃) (sigOn t₁ t₂ t₃) (t₂ ∷ t₁ ∷ t₃ ∷ []) (sg₃ false true true) refl n₃ ℓ₀ q₃ st₃ mk₃ pP k₃ g₃
त्रिकोणे-त्रयम्-असाध्यम् t₁ t₂ t₃ n₁ n₂ n₃ n₄ n₅ n₆ ℓ₀ (inr (inr (inr (inl pP)))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  वारणम् (tOn t₁ t₂ t₃) (sigOn t₁ t₂ t₃) (t₂ ∷ t₃ ∷ t₁ ∷ []) (sg₃ true true false) refl n₄ ℓ₀ q₁ st₁ mk₁ pP k₁ g₁
त्रिकोणे-त्रयम्-असाध्यम् t₁ t₂ t₃ n₁ n₂ n₃ n₄ n₅ n₆ ℓ₀ (inr (inr (inr (inr (inl pP))))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  वारणम् (tOn t₁ t₂ t₃) (sigOn t₁ t₂ t₃) (t₃ ∷ t₁ ∷ t₂ ∷ []) (sg₃ false true true) refl n₅ ℓ₀ q₃ st₃ mk₃ pP k₃ g₃
त्रिकोणे-त्रयम्-असाध्यम् t₁ t₂ t₃ n₁ n₂ n₃ n₄ n₅ n₆ ℓ₀ (inr (inr (inr (inr (inr (inl pP)))))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  वारणम् (tOn t₁ t₂ t₃) (sigOn t₁ t₂ t₃) (t₃ ∷ t₂ ∷ t₁ ∷ []) (sg₃ true false true) refl n₆ ℓ₀ q₂ st₂ mk₂ pP k₂ g₂
त्रिकोणे-त्रयम्-असाध्यम् t₁ t₂ t₃ n₁ n₂ n₃ n₄ n₅ n₆ ℓ₀ (inr (inr (inr (inr (inr (inr ())))))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃

------------------------------------------------------------------------
-- §4  The three instances.  Every seat-denial check is refl.
--
--     ya doubled  ⟹  h v ś once each  ⟹  refuted:
------------------------------------------------------------------------

हवशेषु-त्रयम्-असाध्यम् :
    (ℓ₀ : List Varṇa) → keep (tOn h v ś) ℓ₀ ∈ᴸ षट्कम् h v ś
  → (st₁ mk₁ st₂ mk₂ st₃ mk₃ : Varṇa) (q₁ q₂ q₃ : List Varṇa)
  → klassL st₁ mk₁ ℓ₀ ≡ just q₁ → sigOn h v ś (keep (tOn h v ś) q₁) ≡ sg₃ true true false
  → klassL st₂ mk₂ ℓ₀ ≡ just q₂ → sigOn h v ś (keep (tOn h v ś) q₂) ≡ sg₃ true false true
  → klassL st₃ mk₃ ℓ₀ ≡ just q₃ → sigOn h v ś (keep (tOn h v ś) q₃) ≡ sg₃ false true true
  → ⊥
हवशेषु-त्रयम्-असाध्यम् = त्रिकोणे-त्रयम्-असाध्यम् h v ś refl refl refl refl refl refl

--     śa doubled  ⟹  h y ṣ once each  ⟹  refuted:

हयषेषु-त्रयम्-असाध्यम् :
    (ℓ₀ : List Varṇa) → keep (tOn h y ṣ) ℓ₀ ∈ᴸ षट्कम् h y ṣ
  → (st₁ mk₁ st₂ mk₂ st₃ mk₃ : Varṇa) (q₁ q₂ q₃ : List Varṇa)
  → klassL st₁ mk₁ ℓ₀ ≡ just q₁ → sigOn h y ṣ (keep (tOn h y ṣ) q₁) ≡ sg₃ true true false
  → klassL st₂ mk₂ ℓ₀ ≡ just q₂ → sigOn h y ṣ (keep (tOn h y ṣ) q₂) ≡ sg₃ true false true
  → klassL st₃ mk₃ ℓ₀ ≡ just q₃ → sigOn h y ṣ (keep (tOn h y ṣ) q₃) ≡ sg₃ false true true
  → ⊥
हयषेषु-त्रयम्-असाध्यम् = त्रिकोणे-त्रयम्-असाध्यम् h y ṣ refl refl refl refl refl refl

--     and any other doubling leaves h y ś once each — the predecessor's
--     instance, re-derived through the parametric theorem as coherence:

हयशेषु-पुनः : (ℓ₀ : List Varṇa) → keep (tOn h y ś) ℓ₀ ∈ᴸ षट्कम् h y ś
  → (st₁ mk₁ st₂ mk₂ st₃ mk₃ : Varṇa) (q₁ q₂ q₃ : List Varṇa)
  → klassL st₁ mk₁ ℓ₀ ≡ just q₁ → sigOn h y ś (keep (tOn h y ś) q₁) ≡ sg₃ true true false
  → klassL st₂ mk₂ ℓ₀ ≡ just q₂ → sigOn h y ś (keep (tOn h y ś) q₂) ≡ sg₃ true false true
  → klassL st₃ mk₃ ℓ₀ ≡ just q₃ → sigOn h y ś (keep (tOn h y ś) q₃) ≡ sg₃ false true true
  → ⊥
हयशेषु-पुनः = त्रिकोणे-त्रयम्-असाध्यम् h y ś refl refl refl refl refl refl

------------------------------------------------------------------------
-- §5  The attested stretches satisfy the hypotheses of BOTH new
--     instances — computed from the real line's own extracts, by refl.
--     So the refutations bite exactly the trio Pini names.
------------------------------------------------------------------------

अट्-हवशेषु : sigOn h v ś (keep (tOn h v ś) अट्-आयामः) ≡ sg₃ true true false
अट्-हवशेषु = refl

शल्-हवशेषु : sigOn h v ś (keep (tOn h v ś) शल्-आयामः) ≡ sg₃ true false true
शल्-हवशेषु = refl

यर्-हवशेषु : sigOn h v ś (keep (tOn h v ś) यर्-आयामः) ≡ sg₃ false true true
यर्-हवशेषु = refl

अट्-हयषेषु : sigOn h y ṣ (keep (tOn h y ṣ) अट्-आयामः) ≡ sg₃ true true false
अट्-हयषेषु = refl

शल्-हयषेषु : sigOn h y ṣ (keep (tOn h y ṣ) शल्-आयामः) ≡ sg₃ true false true
शल्-हयषेषु = refl

यर्-हयषेषु : sigOn h y ṣ (keep (tOn h y ṣ) यर्-आयामः) ≡ sg₃ false true true
यर्-हयषेषु = refl

-- and ha is the triangle's sole articulation point: a ∩ aL = {h}
-- exactly, visible in one computation over the whole inventory
एकसन्धिः-हकारः :
  allL (λ v₀ → not (occV v₀ अट्-आयामः and occV v₀ शल्-आयामः) or eqV v₀ h) वर्णाः
  ≡ true
एकसन्धिः-हकारः = refl
