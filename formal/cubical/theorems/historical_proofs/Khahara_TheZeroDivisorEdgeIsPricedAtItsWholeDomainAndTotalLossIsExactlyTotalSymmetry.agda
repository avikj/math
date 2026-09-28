{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- खहरः — शून्य-हर-राशेः तन्तुः कृत्स्नं क्षेत्रम्, सर्व-नाशः सर्व-गतिश्च एकम् ।
--
-- (khahara — the fibre of the zero-divisor map is the whole domain, and
--  total loss is exactly total symmetry.)
--
-- ────────────────────────────────────────────────────────────────────
-- TERM, TEXT, DATE.  खहर · khahara, "having the void for divisor": a
-- quantity divided by nya, carried as an object rather than refused.
-- भास्कर द्वितीय, *बीजगणितम्* २० (Bhāskara II, Bījagaṇita 20, 1150 CE):
--
--     अस्मिन् विकारः खहरे न राशावपि प्रविष्टेष्वपि निःसृतेषु ।
--     बहुष्वपि स्याल्लयसृष्टिकाले ऽनन्ते ऽच्युते भूतगणेषु यद्वत् ॥
--
--   "In this khahara quantity there is no change, though quantities
--    enter it and issue from it, however many — as in the infinite and
--    unfallen (अच्युत) at the time of dissolution and creation, though
--    hosts of beings enter and go out."
--
-- The arithmetic rule is *लीलावती* ४५–४७, whose verse 47 worked example
-- (63 → 14) cannot be solved without it.  The preceding statement is
-- ब्रह्मगुप्त, *ब्राह्मस्फुटसिद्धान्त* १८.३४–३५ (628).  Citation as given
-- in `.claude/hooks/MulaVakya_SourceStatementsForTheTermsInOurFileNames.txt` (absent from this repository)
-- line 190, including its LIMIT: Bhskara does not distinguish n0 from
-- 00, and read as an arithmetic on a field the rule fails.  No
-- manuscript was opened here either.
--
-- §२–§४ are not attributed to him.  The word अच्युत is his simile's
-- referent, not a technical term for a maximally lossy observation; the
-- application of it to that is this corpus's and is not in the text.
-- The substrate is cubical type theory (Voevodsky), this repository's
-- one admitted non-Indian frame.
--
-- ────────────────────────────────────────────────────────────────────
-- WHY THIS FILE EXISTS.  `machine/Lopa_…hs`, run 2026-08-22 against the
-- tree at this commit, prints
--
--     1062  UNDECIDED       16  बहु       4  रिक्तम्
--
-- and one of the 1062 is `[map] ⟨lib⟩.ℤ ⟶ Khahara.खहर « Khahara.शून्य-हरः`.
-- Its four deciding rules R1–R4 key on the TARGET being `Unit`, `⊥`, or a
-- propositional truncation, and on the SOURCE being `⊥`.  None fires
-- here, because `खहर` is none of those.  The rules therefore miss the
-- most lossy map that can exist: a CONSTANT one, whose target happens to
-- have two constructors.  §१–§२ price that edge, and §६ states the
-- census rule that would have caught it.
--
-- A receipt is an IDENTIFICATION of the fibre with a standard type,
-- never a bound (README, "the receipt economy").  §१ gives one:
-- `fiber शून्य-हरः अनन्त ≃ ℤ`, on the nose, the whole domain.  Nothing
-- crosses this edge.  It is the far end of the scale whose near end is
-- `Dhruva_…agda` §२ (`isEquiv f → संरक्षणम् → Φ ≡ id`: zero loss, zero
-- symmetry) and whose middle is `Lopa_TheSumsFibreIsExactlyNPlusOne…`
-- (`fiber (_+_) n ≃ Fin (suc n)`: finite loss).
--
-- ────────────────────────────────────────────────────────────────────
-- THE THEOREM THIS FILE IS FOR (§३).  Dhruva proved NO LOSS ⟹ NO
-- SYMMETRY.  The other end is an EQUIVALENCE and not merely an
-- implication:
--
--     every endomorphism of A conserves f   ⟺   f is constant
--
-- (the ⟸ direction free, the ⟹ direction needing only that A is
-- inhabited, by taking Φ to be a constant map).  So the size of the
-- conserving monoid is not merely correlated with the loss — at the two
-- ends it is DETERMINED by it, trivial monoid at zero loss and the full
-- endomorphism monoid at total loss.  §४ shows the two ends meet only
-- on a proposition: a map that is both an equivalence and constant
-- forces its domain to have at most one point.
------------------------------------------------------------------------

module Khahara_TheZeroDivisorEdgeIsPricedAtItsWholeDomainAndTotalLossIsExactlyTotalSymmetry where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sum.Properties using (isSet⊎)
open import Cubical.Data.Int using (ℤ ; pos ; isSetℤ) renaming (_+_ to _+ℤ_)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Relation.Nullary using (¬_)

open import Khahara using (खहर ; ससीम ; अनन्त ; शून्य-हरः ; अनन्त-न-ससीमः)

private variable ℓ ℓ' : Level

------------------------------------------------------------------------
-- ० · खहर is a set.  Needed because a fibre is a Σ over a PATH type, and
--     `Σ[ a ∈ ℤ ] (अनन्त ≡ अनन्त)` is ℤ only if that loop space is
--     contractible.  Two constructors, no path constructors, so the
--     forgetful Iso to `ℤ ⊎ Unit` is definitional in all four clauses.
------------------------------------------------------------------------

खहर→⊎ : खहर → ℤ ⊎ Unit
खहर→⊎ (ससीम a) = inl a
खहर→⊎ अनन्त     = inr tt

⊎→खहर : ℤ ⊎ Unit → खहर
⊎→खहर (inl a) = ससीम a
⊎→खहर (inr _) = अनन्त

खहर-Iso : Iso खहर (ℤ ⊎ Unit)
Iso.fun      खहर-Iso           = खहर→⊎
Iso.inv      खहर-Iso           = ⊎→खहर
Iso.rightInv खहर-Iso (inl a)   = refl
Iso.rightInv खहर-Iso (inr tt)  = refl
Iso.leftInv  खहर-Iso (ससीम a)  = refl
Iso.leftInv  खहर-Iso अनन्त      = refl

isSetखहर : isSet खहर
isSetखहर = isOfHLevelRetractFromIso 2 खहर-Iso (isSet⊎ isSetℤ isSetUnit)

------------------------------------------------------------------------
-- १ · अभिज्ञानम् — THE RECEIPT.  The fibre over अनन्त is ℤ itself.
--
--     fiber शून्य-हरः अनन्त  ≃  ℤ
--
-- Not a bound.  An identification with a standard type, which is what
-- the corpus's rule demands of a receipt.  Read it as the price: the
-- edge `ℤ ⟶ खहर` costs its entire domain, and the verdict is बहु with
-- the amount named.
------------------------------------------------------------------------

अभिज्ञान-Iso : Iso (fiber शून्य-हरः अनन्त) ℤ
Iso.fun      अभिज्ञान-Iso (a , _) = a
Iso.inv      अभिज्ञान-Iso a       = a , refl
Iso.rightInv अभिज्ञान-Iso a       = refl
Iso.leftInv  अभिज्ञान-Iso (a , p) =
  ΣPathP (refl , isSetखहर अनन्त अनन्त refl p)

अभिज्ञानम् : fiber शून्य-हरः अनन्त ≃ ℤ
अभिज्ञानम् = isoToEquiv अभिज्ञान-Iso

------------------------------------------------------------------------
-- २ · रिक्तम् — and every OTHER fibre is empty.  So the image is a
--     single point and the three verdicts of `Avaccheda_…agda` are both
--     realised by this one map: बहु at अनन्त, रिक्तम् at every ससीम a.
--     `एकम्` — contractible — occurs nowhere, which is the statement
--     that no information whatsoever crosses.
------------------------------------------------------------------------

रिक्तम्-ससीमे : (a : ℤ) → ¬ (fiber शून्य-हरः (ससीम a))
रिक्तम्-ससीमे a (_ , p) = अनन्त-न-ससीमः a p

------------------------------------------------------------------------
-- ३ · सर्व-नाशः सर्व-गतिश्च — TOTAL LOSS IS EXACTLY TOTAL SYMMETRY.
--
-- `Dhruva_…agda` defines संरक्षणम् f Φ = (a : A) → f (Φ a) ≡ f a, and
-- proves that zero loss forces Φ = id.  Here is the other end, stated
-- for an arbitrary map between arbitrary types, no hypotheses beyond
-- inhabitedness where it is genuinely needed.
------------------------------------------------------------------------

module _ {A : Type ℓ} {B : Type ℓ'} (f : A → B) where

  -- EVERY endomorphism of the domain conserves the observable.
  सर्व-संरक्षणम् : Type (ℓ-max ℓ ℓ')
  सर्व-संरक्षणम् = (Φ : A → A) (a : A) → f (Φ a) ≡ f a

  -- The observable sees nothing at all.
  सर्व-नाशः : Type (ℓ-max ℓ ℓ')
  सर्व-नाशः = (x y : A) → f x ≡ f y

  -- ⟸ : a constant observable is conserved by everything.  Free.
  नाशात्-गतिः : सर्व-नाशः → सर्व-संरक्षणम्
  नाशात्-गतिः c Φ a = c (Φ a) a

  -- ⟹ : if everything conserves it, it is constant.  The witness is the
  -- constant flow: `Φ = λ _ → x` moves a chosen basepoint to x, and
  -- conservation says the observable did not notice.  Inhabitedness of A
  -- is the whole hypothesis, and it is necessary: over A = ⊥ every map
  -- is vacuously conserved by everything and `सर्व-नाशः` is vacuous too,
  -- so nothing is lost there either — the statement is not about the
  -- empty domain and does not pretend to be.
  गतेः-नाशः : A → सर्व-संरक्षणम् → सर्व-नाशः
  गतेः-नाशः a₀ s x y = s (λ _ → x) a₀ ∙ sym (s (λ _ → y) a₀)

------------------------------------------------------------------------
-- ४ · The two ends meet only on a proposition.
--
-- Dhruva's hypothesis (isEquiv f — nothing hidden) and this file's
-- (सर्व-नाशः — everything hidden) are not merely different: holding both
-- collapses the domain.  So the scale really has two ends, and a map
-- sitting at both is a map on an object with at most one point.
------------------------------------------------------------------------

  उभयान्ते-प्रमाणम् : isEquiv f → सर्व-नाशः → (x y : A) → x ≡ y
  उभयान्ते-प्रमाणम् e c x y =
    cong fst (sym (ctr .snd (x , refl)) ∙ ctr .snd (y , c y x))
    where
      ctr : isContr (fiber f (f x))
      ctr = e .equiv-proof (f x)

  -- Contrapositive, in the form that is actually used: a domain with two
  -- provably distinct points admits no constant equivalence.
  न-समता : सर्व-नाशः → (x y : A) → ¬ (x ≡ y) → ¬ (isEquiv f)
  न-समता c x y sep e = sep (उभयान्ते-प्रमाणम् e c x y)

------------------------------------------------------------------------
-- ५ · The instance: Bhāskara's map sits at the far end.
------------------------------------------------------------------------

खहर-सर्व-नाशः : सर्व-नाशः शून्य-हरः
खहर-सर्व-नाशः _ _ = refl

खहर-सर्व-संरक्षणम् : सर्व-संरक्षणम् शून्य-हरः
खहर-सर्व-संरक्षणम् = नाशात्-गतिः शून्य-हरः खहर-सर्व-नाशः

-- The verse, as the special case Φ = (_+ℤ k).  BG 20 states it of the
-- RESULT — the khahara is unaltered when quantities enter and leave it —
-- and `Khahara.खहरे-न-विकारः-योगे` is that reading, already checked in
-- the file this one imports.  This is the DOMAIN reading, which is the
-- one the fibre law is about: the numerator may be moved arbitrarily and
-- the observation does not change.  Both are refl; that they are two
-- readings and not one is the point of writing the second.
भास्कर-प्रवाहः : (k n : ℤ) → शून्य-हरः (n +ℤ k) ≡ शून्य-हरः n
भास्कर-प्रवाहः k n = refl

-- And the fibre statement of the same verse: every insertion stays inside
-- the one fibre, because the fibre is everything.  Stated through the
-- receipt so it is the identification that is doing the work.
प्रविष्टं-तन्तौ-तिष्ठति : (k : ℤ) → fiber शून्य-हरः अनन्त → fiber शून्य-हरः अनन्त
प्रविष्टं-तन्तौ-तिष्ठति k (n , p) = (n +ℤ k) , p

------------------------------------------------------------------------
-- ६ · शेषः — what this opens, and one thing it hands to another lane.
--
-- (a) A CENSUS RULE, offered to `machine/Lopa_…hs` and not applied here,
--     because that file is another lane's and an audit that rewrites its
--     subject is not an audit:
--
--       R5  a top-level definition whose every clause returns the SAME
--           closed term, with no occurrence of any pattern variable,
--           is CONSTANT.  Verdict बहु at that value with fibre = the
--           whole source, and रिक्तम् at every other value of the target
--           IF the target is a set with decidable equality.
--
--     R1 is the special case target = Unit.  R5 subsumes it and would
--     have decided this edge.  How many of the 1062 UNDECIDED it decides
--     is NOT estimated here — a count without a run is the fitted
--     constant CLAUDE.md (absent from this repository) opens with.
--
--     The companion move is
--     `Chandomudra_ThePratyayasFibresWereWrittenInProseAndTheCensusCalledThemUndecided`,
--     which prices undecided edges whose fibres the corpus ALREADY had,
--     defined by name fifteen lines below the map.  This one is the
--     other case: no fibre existed for this edge anywhere, and the
--     reason the census could not name it is not that it failed to look
--     up an answer but that its rule set has no rule for constancy.
--     Two different defects, and the second is not repaired by the first
--     one's remedy ("look it up before constructing").  Chandomudra
--     reports 1045 UNDECIDED and this file reports 1062 from a run on
--     2026-08-22; the census is a moving number and neither figure is
--     the corpus's, only that day's parse of it.
--
-- (b) NOT DONE.  The scale between the two ends is not a scale yet.
--     Dhruva's end and this one are both characterised; what is missing
--     is the statement that the conserving monoid `Σ[ Φ ] संरक्षणम् f Φ`
--     is MONOTONE in the fibres — that a coarser f admits more flows.
--     "Coarser" needs an order on maps out of A (the quotient order),
--     and this file does not have one.  Naming it as absent rather than
--     gesturing at it.
--
-- (c) The 00 case is untouched.  Khahara.agda's CORRECTED block of
--     2026-08-19 separates it from अवक्तव्यम् as a UNIQUENESS failure,
--     and `NonUniquenessAndInexpressibilityAreIndependent`
--     checks the independence.  Nothing here bears on that dispute; the
--     map priced above is the n÷0 branch only, and it is total on ℤ
--     precisely because `Khahara.शून्य-हरः` ignores its argument — which
--     is the very degeneracy §१ is the receipt for, and is also the
--     LIMIT the source ledger's row states.
------------------------------------------------------------------------
