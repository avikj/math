{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AnuktaAvaktavya — अनुक्तम् is not अवक्तव्यम्, and the difference is a
-- swapped quantifier.
--
-- `Satyayantra.agda` opens by describing its third position:
--
--     अनुक्तं न मिथ्या, न ⊥ — तृतीयं पदम् (avaktavyam), बूलियन्-रहितम् ।
--     "the un-said is not false, not ⊥ — a third position (avaktavyam),
--      boolean-free."
--
-- Everything in that line is right except the parenthesis.  The un-said of
-- the honest machine is a genuine third position, it is not falsity and not
-- ⊥, and there is no boolean anywhere.  But it is NOT the fourth bhaṅga of
-- the saptabhaṅgī, and `SaptabhangiNaya.agda` — sitting in the same
-- directory, also checked, also --safe — proves the opposite modality.
--
-- THE TWO MODULES SAY, IN THEIR OWN WORDS:
--
--   Purnata.agda:  अनुक्तं सामयिकम् एव, न अन्तः ।
--                  सत्यं न त्यक्तम्, केवलम् अद्यापि अनुक्तम् — अनुदानेन प्रकाश्यम् ।
--                  "the un-said is only ever TEMPORARY, never a dead end.
--                   Truth was never abandoned, only not-yet-said —
--                   uncovered by grant."
--
--   SaptabhangiNaya.agda §5:  no single utterance denotes the joint
--                  content, exhaustively over all six atoms of the
--                  language, each with its own separating profile.  The
--                  remedy is not more of anything.  It is a SECOND
--                  utterance, taken in succession (krama).
--
-- So one third position is removed by giving the machine more, and the
-- other is not removed by giving anything more.  Same word, opposite
-- modality: "not yet" against "not ever, in one breath".
--
-- THE SEPARATION IS EXACT AND IT IS A QUANTIFIER.  Both facts already
-- exist as theorems; what was missing is that they have the same shape
-- with ∃ and ∀ exchanged, which is why one word could cover both and
-- hide it.
--
--     सामयिक  bad : I → R → Type      (i : I) → Σ[ r ] ¬ bad i r
--              for EVERY instance there is SOME remedy that removes it
--
--     नित्य    bad : I → R → Type      (r : R) → Σ[ i ] bad i r
--              for EVERY remedy there is SOME instance that survives it
--
-- `Purnata.पूर्णता` gives the first for the kuṭṭaka's un-said, with the
-- remedy being the grant.  `SaptabhangiNaya.no-single-vacana` IS the
-- second, with the remedy being a single utterance.  Neither theorem is
-- reproved here; this module only exhibits that they instantiate the two
-- shapes, which is the content of the distinction.
--
-- WHY IT MATTERS RATHER THAN BEING A LABELLING QUIBBLE.  A machine that
-- reports its third position has to tell a caller what to DO about it, and
-- the two answers are incompatible: spend more, or speak again.  Calling
-- both avaktavyam tells the caller to do nothing, twice.  Nyya keeps them
-- apart too — a hetu that is asiddha (unestablished) is a defect of the
-- MEANS, repaired by establishing it; avaktavyam in the Jain scheme is a
-- positive predication about the ARTHA, and there is nothing to repair.
--
-- SOURCES.  Bhagavat Stra (pre-CE strata, redacted c. 5th c.); Umsvti,
-- Tattvārthasūtra 5.31 arpitānarpitasiddheḥ (c. 2nd–5th c.); Siddhasena
-- Divkara, Sanmatitarka 1.21 (c. 5th c.); Akalaka, Laghyastraya
-- (c. 720–780) for kramārpaṇa against sahārpaṇa — succession against
-- simultaneity, which is precisely the ∃/∀ difference below; Mallisena,
-- Sydvdamajar (1292) for sakaldea against vikaldea.  The kuaka
-- itself is Āryabhaṭa, Āryabhaṭīya, Gaṇitapāda 32–33 (499 CE).
------------------------------------------------------------------------

module Mula.AnuktaAvaktavya where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; suc ; _+_)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Gati using (फलम् ; गुरुः ; अनुक्तफलम् ; फल ; गति)
open import Purnata using (पूर्णता)
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; false≢true)
open import Cubical.Data.Nat using (zero)
open import Cubical.Data.Int using (ℤ ; pos ; discreteℤ) renaming (_·_ to _·ℤ_)
open import Cubical.Relation.Nullary using (yes ; no)
open import Mula.SaptabhangiNaya
  using ( Vacana ; Profile ; denotes ; joint ; no-single-vacana
        ; krama-expresses ; asti-from ; nasti-from ; rewriter ; kernel-refl )

------------------------------------------------------------------------
-- 1.  The two shapes.
--
-- `bad i r` reads: instance i is STILL in the third position when remedy r
-- has been applied.
------------------------------------------------------------------------

सामयिक : {I R : Type} → (I → R → Type) → Type
सामयिक {I} {R} bad = (i : I) → Σ[ r ∈ R ] (¬ bad i r)

नित्य : {I R : Type} → (I → R → Type) → Type
नित्य {I} {R} bad = (r : R) → Σ[ i ∈ I ] (bad i r)

------------------------------------------------------------------------
-- 2.  अनुक्तम् is सामयिक.  The remedy is the grant, and it always exists.
------------------------------------------------------------------------

-- "the result is still un-said"
अनुक्तमस्ति : फलम् → Type
अनुक्तमस्ति (गुरुः _)       = ⊥
अनुक्तमस्ति (अनुक्तफलम् _)  = Unit

बद्धम् : (ℕ × ℕ) → ℕ → Type
बद्धम् (a , b) n = अनुक्तमस्ति (फल (गति n a b))

अनुक्तम्-सामयिकम् : सामयिक बद्धम्
अनुक्तम्-सामयिकम् (a , b) =
  suc (a + b) , λ h → subst अनुक्तमस्ति (snd (पूर्णता a b)) h

------------------------------------------------------------------------
-- 3.  अवक्तव्यम् is नित्य.  For every single utterance there is a profile
-- that survives it — which is `no-single-vacana`, exactly, with nothing
-- added.
------------------------------------------------------------------------

असमर्थम् : Profile → Vacana → Type
असमर्थम् φ v = ¬ (denotes v φ ≡ joint φ)

अवक्तव्यम्-नित्यम् : नित्य असमर्थम्
अवक्तव्यम्-नित्यम् = no-single-vacana

------------------------------------------------------------------------
-- 4.  So the two words name different shapes, and one word cannot carry
--     both.
--
-- Stated as a type rather than a sentence: a predicate that is सामयिक
-- gives, at every instance, a remedy under which it fails; a predicate
-- that is नित्य gives, at every remedy, an instance under which it holds.
-- Nothing below asserts that no predicate can be both — for an empty
-- instance type or an empty remedy type the shapes degenerate, and that
-- is a separate statement I am not making.  What is exhibited is only
-- this: the two theorems already in this repository realise the two
-- shapes, and `Satyayantra.agda`'s parenthetical puts one under the other's name.
------------------------------------------------------------------------

-- the un-said, at the pole it actually occupies
अनुक्त-पदम् : सामयिक बद्धम्
अनुक्त-पदम् = अनुक्तम्-सामयिकम्

-- the fourth bhaga, at the other one
अवक्तव्य-पदम् : नित्य असमर्थम्
अवक्तव्य-पदम् = अवक्तव्यम्-नित्यम्

------------------------------------------------------------------------
-- 5.  THE SHARPER DIFFERENCE: WHERE THE REMEDY LIVES.
--
-- The quantifier is the surface of it.  Underneath, the two shapes differ
-- in whether the remedy can stay in its own type.
--
--   सामयिक.  The remedy is an element of R, and remedies COMBINE inside R.
--   `SatyayantraSamyoga.संयोग` proves this for the honest machine: the
--   composite of two machines is a machine, and its परिपूर्णता field is
--   constructed at grant  g२ + g१  — the two grants aligned by stability
--   and then added.  So chaining honest machines keeps the un-said
--   temporary, and the cost is additive.  You never leave ℕ.
--
--   नित्य.  No element of R works — that is exactly `no-single-vacana`,
--   exhaustively.  What works is an ordered PAIR, `krama-expresses`.  The
--   remedy is not a bigger element of R; it is an element of R × R.  You
--   must leave the type.
--
-- That is Akalaka's kramrpaa against sahrpaa in its operational form
-- (Laghīyastraya, c. 720–780): succession is not more simultaneity, and no
-- amount of one becomes the other.  Both halves below are already theorems
-- elsewhere in this repository; what is new here is that they are the two
-- clauses of one statement, which is what makes the pair a SEPARATION and
-- not two remarks.
------------------------------------------------------------------------

युग्मेन-साध्यम् :
    ((v : Vacana) → Σ[ φ ∈ Profile ] (¬ (denotes v φ ≡ joint φ)))
  × (Σ[ vw ∈ (Vacana × Vacana) ]
      ((φ : Profile) → joint φ ≡ (denotes (fst vw) φ and denotes (snd vw) φ)))
युग्मेन-साध्यम् =
    no-single-vacana
  , ((asti-from rewriter , nasti-from kernel-refl) , krama-expresses)

------------------------------------------------------------------------
-- 6.  A THIRD USE OF THE WORD, AND IT FAILS THE SAME TEST FROM THE OTHER
--     SIDE.
--
-- `Khahara.agda` and `Shunya.agda` both identify 00 with avaktavyam:
--
--   Khahara:  0÷0 = अवक्तव्यम् (अनिश्चितम्, सप्तभङ्ग्याः ४र्थं पदम्)
--   Shunya:   0÷0 न एकं मूल्यम्, किन्तु अनिश्चितम् — अवक्तव्यम्
--             (सप्तभङ्ग्याः चतुर्थं पदम्), न शून्यम्
--
-- Both are right that Brahmagupta's `00 = 0` (Brhmasphuasiddhnta, 628)
-- is a durnaya — a definite verdict where none is available — and right
-- that Bhskara II's khahara (Llvat, 1150) is a genuinely different
-- non-finite result from it.  Those are the load-bearing claims of both
-- modules and nothing here touches them.
--
-- The identification with the fourth bhaga is what fails, and it fails
-- INTERNALLY: by `SaptabhangiNaya`'s own criterion, not by an outside
-- standard.  §5 there defines avaktavyam as the case where NO SINGLE
-- UTTERANCE denotes the content, proved exhaustively over the six atoms.
--
-- But 00's situation is denotable in one utterance, and the utterance is
-- the type of `शून्यहरः-सर्वत्र` below: every x whatsoever satisfies the
-- defining condition.  That is one statement, it is complete, and it says
-- exactly what is wrong.  Nothing is inexpressible.
--
-- So the two defects are opposite:
--
--   avaktavyam  the content is DETERMINATE (`joint` is total into Bool with
--               both values realised) and the MEDIUM cannot say it in one
--               go.  An expressibility failure.
--   00         the content is perfectly EXPRESSIBLE and the SOLUTION SET
--               is not a singleton.  A uniqueness failure.
--
-- Determinate-but-unsayable against sayable-but-underdetermined.  Calling
-- both by the fourth bhaga's name is the boolean collapse this corpus
-- exists to fight, committed one level up: a single third position used as
-- a catch-all for "not a clean single answer".  Three modules now do it —
-- Satyayantra (§1 above), Khahara and Shunya — with three different things
-- underneath.
--
------------------------------------------------------------------------

-- Brahmagupta's own reason, as a term: every x satisfies it.  Over cubical
-- ℤ this is `refl`, because `pos zero · m` reduces to `pos zero` on the
-- nose — the multiplication recurses on its first argument.
शून्यहरः-सर्वत्र : (x : ℤ) → (pos 0) ·ℤ x ≡ pos 0
शून्यहरः-सर्वत्र _ = refl

एकम्? : ℤ → Bool
एकम्? (pos (suc zero)) = true
एकम्? _                = false

शून्य≢एकम् : ¬ (pos 0 ≡ pos 1)
शून्य≢एकम् p = false≢true (cong एकम्? p)

-- Two distinct values both satisfy it, so the fibre is not a singleton.
-- THIS is the defect at 00, and it is not the defect at avaktavyam.
शून्यहरः-अनेकम् :
  Σ[ x ∈ ℤ ] Σ[ y ∈ ℤ ]
    ((¬ (x ≡ y)) × (((pos 0) ·ℤ x ≡ pos 0) × ((pos 0) ·ℤ y ≡ pos 0)))
शून्यहरः-अनेकम् = pos 0 , pos 1 , शून्य≢एकम् , refl , refl

------------------------------------------------------------------------
-- `NaturalMachine.SamayikaAndNityaAreIndependent` adds what kind of difference the swapped
-- quantifier is: an INDEPENDENT one.
--
--   bothHold              matching i r = (i ≡ r) on Bool satisfies
--                         सामयिक AND नित्य simultaneously
--   samayikaWithoutNitya  bad = ⊥
--   nityaWithoutSamayika  bad = Unit
--
-- So neither implies the other and neither implies the other's negation.
-- What each does refute is the other's STRONG failure —
-- नित्य refutes a universal remedy, सामयिक refutes an invincible
-- instance — and those two cannot both hold, which is why the fourth
-- corner has no strong witness.
--
-- That module says nothing about the WORDS अनुक्तम् and अवक्तव्यम्, about
-- the saptabhag, or about which module here uses which.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 7.  WHAT WAS ALREADY HERE, AND THE DISTINCTION THAT RESOLVES IT.
--
-- CREDIT FIRST, because §5 and §6 above were written without it.  Two
-- modules in this repository had already gone further than they do:
--
--   `NaturalMachine/AvaktavyaDoesNotFactor.agda` proves
--   `avaktavya-decidable`, so avaktavyam is neither a truth-value gap nor
--   an undecidability, and identifies its shape as a FAILURE TO FACTOR,
--   ¬ Σ[ decoder ] ((x : _) → decoder (coarse x) ≡ fine x) -- the same
--   shape as Pini's lghava criterion and as the analytic lane's open
--   barrier problem.  My §6 called this an "expressibility failure" as
--   though it were an observation; it was already a term, and sharper.
--   (That file's header credits `Saptabhangi.no-single-vacana`; the
--   theorem is in `SaptabhangiNaya`, which is what it actually imports.)
--
--   `Saptabhangi.agda` proves `क्रम-सह-भेदः`: the bhaṅga reached by
--   krama-arpaṇa is not the bhaṅga reached by saha-arpaṇa.  And `दुर्नयः`:
--   ANY two-valued verdict on the sevenfold identifies two of the three
--   seeds, by pigeonhole -- the boolean collapse, proved rather than
--   deplored.
--
-- THE APPARENT TENSION.  `SaptabhangiNaya.krama-expresses` says a PAIR of
-- utterances denotes the joint content exactly.  `Saptabhangi.क्रम-सह-भेदः`
-- says the sequential position is not the simultaneous one.  Read
-- carelessly these disagree about whether succession reaches avaktavyam.
--
-- THEY DO NOT, AND THE REASON IS A DISTINCTION NEITHER FILE DRAWS:
-- they quantify over different objects.
--
--   CONTENT   a predicate on profiles.  Reachable by a pair: the joint
--             content IS the conjunction of two denotations.
--   POSITION  a bhaga, a speech act.  NOT reachable by sequencing: the
--             third bhaga and the fourth are distinct inhabitants.
--
-- So expressing-the-content and occupying-the-position come apart.  A pair
-- of successive utterances says what avaktavyam is about, and is still not
-- avaktavyam.  That is exactly Akalaka's point in putting kramrpaa and
-- sahrpaa side by side rather than ordering them, and it is why the
-- scheme needs a fourth member instead of stopping at three.
--
-- AND MY OWN FINDING IS AN INSTANCE OF दुर्नयः, ONE LEVEL UP.  §1 and §6
-- found three distinct structures in this repository all called
-- avaktavyam -- Satyayantra's un-said (सामयिक), 0÷0 (underdetermined), and
-- the fourth bhaṅga (नित्य, non-factoring).  `दुर्नयः` proves that mapping
-- three distinct seeds into two values must identify two of them.  Mapping
-- three distinct structures onto ONE name is the same pigeonhole with a
-- smaller codomain, and it collapses all three.  The corpus escaped Bool
-- and then made its escape hatch into a Bool of one element.
------------------------------------------------------------------------

open import Saptabhangi
  using (सप्तभङ्गी ; अर्पणम् ; उभयम् ; क्रमः ; सहः ; क्रम-सह-भेदः)

-- POSITION: succession does not reach the fourth bhaga.  (Saptabhangi's,
-- re-exported here so the two levels stand in one place.)
स्थान-भेदः : ¬ (अर्पणम् उभयम् क्रमः ≡ अर्पणम् उभयम् सहः)
स्थान-भेदः = क्रम-सह-भेदः

-- CONTENT: and yet the pair denotes the joint content exactly.  (§5's
-- second clause.)  Both hold; they are about different things.
अर्थ-साम्यम् : (φ : Profile)
             → joint φ ≡ (denotes (asti-from rewriter) φ
                          and denotes (nasti-from kernel-refl) φ)
अर्थ-साम्यम् = krama-expresses

------------------------------------------------------------------------
-- 8.  THE THREE-WAY SEPARATION, COMPLETED.
--
-- §1 and §6 asserted three distinct structures wearing one name, and
-- proved two of the three separations.  A pattern over n instances is a
-- pattern over n instances until something downstream of it is computed,
-- so here is the third, and it changes the shape of the claim.
--
-- 0÷0 is नित्य: for EVERY candidate value there is a competing value
-- satisfying the same defining condition (`शून्यहरः-नित्यम्` below).  That
-- does NOT show it is not सामयिक — the two properties are independent
-- (`SamayikaAndNityaAreIndependent.bothHold`) — so on the सामयिक column 0÷0
-- is NOT SHOWN either way.  What separates 0÷0 from the fourth bhaṅga is
-- the other axis, the one §6 exhibited: 0÷0's whole situation is denotable
-- in a single utterance (`शून्यहरः-सर्वत्र`), and avaktavyam's is not
-- (`no-single-vacana`).  The table, with only what is proved:
--
--                        सामयिक?     sayable in one utterance?
--   अनुक्तम् (Satyayantra)   yes             --
--   0÷0                    not shown       yes
--   अवक्तव्यम् (4th bhaṅga)  no              no
------------------------------------------------------------------------

शून्यहरः-नित्यम् :
  (r : ℤ) → Σ[ i ∈ ℤ ] ((¬ (i ≡ r)) × ((pos 0) ·ℤ i ≡ pos 0))
शून्यहरः-नित्यम् r with discreteℤ r (pos 0)
... | yes p = pos 1 , (λ q → शून्य≢एकम् (sym (q ∙ p))) , refl
... | no ¬p = pos 0 , (λ q → ¬p (sym q)) , refl

------------------------------------------------------------------------
-- `NaturalMachine.NonUniquenessAndInexpressibilityAreIndependent` checks
-- that the two defects §6 and §8 separate — a UNIQUENESS failure (0÷0)
-- and an EXPRESSIBILITY failure (avaktavyam) — are independent, over
-- four realised corners, so neither implies the other and neither
-- implies the other's negation.  The types locate the asymmetry:
-- non-uniqueness is a property of the CONTENT alone, inexpressibility of
-- the content AND the MEDIUM.
--
-- It deliberately does NOT put अनुक्तम् on that carrier, for the reason
-- d909db0d gives: the remedies live in different types, and forcing all
-- three onto one carrier would be the collapse being diagnosed.  Two are
-- compared because two are comparable.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 9.  "DUAL" AND "POLES" ARE WRONG, AND ANOTHER IDENTITY PROVED IT.
--
-- This module says "dual shapes" (§4, §1), "the two poles" (§4, §5) and
-- "the same pole as avaktavyam" (§8).  All of that treats सामयिक and नित्य
-- as opposites, and treats non-uniqueness and inexpressibility the same
-- way.  Both are wrong, and both were refuted by reading this file rather
-- than by me:
--
--   `NaturalMachine/SamayikaAndNityaAreIndependent.agda` — the swap of ∃
--   and ∀ is NOT a negation.  `bothHold` exhibits a single `bad` that is
--   सामयिक AND नित्य at once; `samayikaWithoutNitya` and
--   `nityaWithoutSamayika` give the other two corners.  Neither predicate
--   implies the other and neither implies the other's negation.  What each
--   DOES refute is the other's STRONG failure, which is a different and
--   weaker relation than duality.
--
--   `NaturalMachine/NonUniquenessAndInexpressibilityAreIndependent.agda` —
--   the same, over four realised corners, for §6's other axis.  So the two
--   defects are not two readings of one thing at any strength.
--
-- WHAT SURVIVES.  The three-way separation of §1, §6 and §8 stands: the
-- three structures ARE distinct, and each pair is separated by at least
-- one of the two properties.  What does not survive is the geometry I put
-- on it.  "Poles" implies a line with two ends and a thing at one end not
-- at the other.  The truth is a square with at least three corners
-- occupied, and reading a square as a line is how a classification loses
-- exactly the case that matters — which is this module's own complaint
-- about one word over three structures, committed by me one level up
-- while making it.
------------------------------------------------------------------------

open import NaturalMachine.NonUniquenessAndInexpressibilityAreIndependent
  using ( corner-nonUnique-expressible ; corner-unique-inexpressible
        ; corner-both ; corner-neither )

-- The corner that kills "dual" on §6's axis: one content is BOTH
-- non-unique and inexpressible at once, so they are not two ends of
-- anything.
न-द्वैतम् : _
न-द्वैतम् = corner-both

-- and the corner that kills "poles" in the other direction: a content
-- with NEITHER defect.  A line with two ends has no such point; a square
-- has four, and all four are inhabited here.
न-ध्रुवौ : _
न-ध्रुवौ = corner-neither
-- The other two corners, named rather than tupled.  A four-way tuple with
-- an inferred type leaves Agda unable to solve which Σ it is (the same
-- ambiguity §5 of `BhavanaKrida` hit), and an anonymous meta is not a
-- checked claim.  Four names, four checks.
पृथक्-अनेकम् : _
पृथक्-अनेकम् = corner-nonUnique-expressible

पृथक्-अवाच्यम् : _
पृथक्-अवाच्यम् = corner-unique-inexpressible
