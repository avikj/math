{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अवक्तव्य-गर्भः — चतुर्थं स्थानं जिह्वाभेदस्य बहु-तन्तुः, तस्य शेषः च
-- यत् सह उक्तम् आसीत् तदेव ।
--
-- (the fourth position is the crowded fibre of the tongue-break, and its
--  residual is exactly what was said at once.)
--
-- ON THE NAME.  गर्भ is taken from AvaktavyaPrasava's own quotation of
-- `notes/AHIMSA_SUTRA_VISTARA.md` (absent from this repository) §३ — अवक्तव्ये शेषो वसति । शेषो गर्भः, न
-- विफलता — "in the avaktavya the residue dwells; the residue is a WOMB,
-- not a failure."  This module is that sentence read as a fibre, which is
-- what it already was.
--
------------------------------------------------------------------------
-- WHAT IS SEEN HERE, AND IT IS ONE THING SAID THREE WAYS.
--
-- `SaptabhangiSamyoga` gives the sevenfold two composition laws: krama
-- (profile join — associative, commutative, idempotent, a semilattice)
-- and saha (join, then `जिह्वाभेदः`, which on a profile carrying BOTH asti
-- and nsti destroys the two seed markings and writes avaktavya alone).
-- It proves saha non-associative by exhibiting two groupings, and its
-- header says why: *"जिह्वाभेदः destroys the two seed markings, so the
-- fourth position does not record which pair produced it."*
--
-- That sentence is a fibre census on जिह्वाभेदः, and nobody had taken it as
-- one.  Doing so collapses three things that were three:
--
--   §1  THE FOURTH POSITION IS A CROWDED FIBRE.  `जिह्वाभेदः` is a map
--       समावेश → समावेश.  Over the fourth profile (न , न , आम्) its fibre has
--       THREE points and is computed exactly (§1.4): it is
--
--           शेष-जिह्वा  ≃  Unit ⊎ उपस्थिति
--
--       — the fixed point (न,न,आम्) itself, plus ONE BIT, and that bit is
--       the third slot of the profile that broke: whether avaktavya was
--       already present when the tongue broke.  So `विकलादेश` at (न,न,आम्),
--       and by `Sesa`/`देश` this is the second cell, नष्टि, exhibited —
--       the loss is a TYPE and it is holdable.
--
--   §2  THE NON-ASSOCIATIVITY IS THAT CROWDING, DERIVED.  §2.1 proves the
--       implication nobody had stated: IF `जिह्वाभेदः` were the identity —
--       i.e. if the tongue-break destroyed nothing — THEN saha would be
--       associative, because it would BE krama.  So the corpus's existing
--       counterexample stops being a curiosity and becomes a proof:
--       `सङ्क्षेपः-अस्ति` (§2.2) derives ¬((t : समावेश) → जिह्वाभेदः t ≡ t)
--       FROM `सह-असङ्गतिः`.  Collapse is not observed; it is entailed.
--
--       What is proved is ONE direction: no collapse ⇒ associative, so
--       non-associative ⇒ some collapse.  The converse is false:
--       `Arpitanarpita` §८ shows सहार्पणम् is non-associative on records
--       that retain both seeds, where nothing is collapsed.  Non-
--       associativity is not the same fact as a crowded fibre.
--
--   §3  AND THE RESIDUAL IS WHAT WAS SAID AT ONCE.  §3.1 characterises the
--       fibre without the equivalence: a profile lands on the fourth
--       position iff it IS the fourth position, or it carries both asti and
--       nāsti.  Which is the doctrine's own content of अवक्तव्यम् — not the
--       unknown, not the undetermined, not the empty, but the positive
--       fourth position holding what two simultaneous assertions were.
--       Umāsvāti's arpita/anarpita (Tattvārthasūtra 5.31, c. 2nd–5th c.):
--       the pair is UNASSERTED in the utterance and PRESENT in the residual.
--
-- WHAT THIS BUYS DOWNSTREAM, and it is why the module is worth its lines.
-- `AvaktavyaPrasava` (machine/) can only exist because `Vipratisedha`'s
-- Avaktavya carries a `Sesa` as a VALUE rather than a rendering — and it
-- calls what it does from that residue a BIRTH.  §1.4 says what a birth is:
-- choosing a point of a non-contractible fibre, i.e. a SECTION.  Which is
-- exactly why prasava cannot be automatic (a canonical choice is what
-- contractibility WOULD have given, and §1.3 refutes it) and why the
-- operation must be supplied and then gated.  `Vivada`'s refusal — no rule
-- born where the contenders do not join — is the same non-contractibility
-- one level up.
--
-- AND WHY THE FOURTH POSITION IS NOT A PRIMITIVE OF THE SCHEME.  It is the
-- image of a crowded fibre.  `Saptabhangi.क्रम-सह-भेदः` proves it is not
-- reachable by succession, and `SaptabhangiSamyoga.अवक्तव्यम्-न-क्रमजम्`
-- proves the krama-closure of the first three never touches it.  §1 says
-- what it IS instead: where जिह्वाभेदः is not injective.  The two facts are
-- the same fact — a point with a crowded fibre is a point no injection
-- reaches from its preimages, and the seed-free fragment is precisely the
-- part of समावेश on which जिह्वाभेदः IS the identity (§2.3).
------------------------------------------------------------------------

module Avaktavyagarbha_TheFourthPositionIsTheCrowdedFibreOfTheTongueBreakAndItsResidualIsExactlyWhatWasSaidAtOnce where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso ; iso)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Relation.Nullary using (¬_ ; Discrete ; yes ; no ; Discrete→isSet)

open import Saptabhangi
  using ( सप्तभङ्गी
        ; स्यात्-अस्ति ; स्यात्-नास्ति ; स्यात्-अस्ति-नास्ति ; स्यात्-अवक्तव्यम्
        ; उपस्थिति ; आम् ; न ; समावेश ; अन्तर्भाव ; प्रत्यन्तर्भाव )

open import SaptabhangiSamyoga_TheCompositionOfVerdicts
  using ( जिह्वाभेदः ; सह-योग ; क्रम-योग ; क्रम-सङ्गतिः ; सह-असङ्गतिः
        ; संयोग ; आम्≢न ; नास्त्यंशः )

------------------------------------------------------------------------
-- ०ः  समावेशः समुच्चयः — the profiles are a set.
--
-- Needed only for §1.4's leftInv: two proofs that a profile lands on the
-- fourth position are equal, so the fibre has no path structure beyond
-- its points.  Discreteness by cases; nothing subtle.
------------------------------------------------------------------------

विवेक-उपस्थिति : Discrete उपस्थिति
विवेक-उपस्थिति आम् आम् = yes refl
विवेक-उपस्थिति आम् न   = no आम्≢न
विवेक-उपस्थिति न   आम् = no (λ e → आम्≢न (sym e))
विवेक-उपस्थिति न   न   = yes refl

समुच्चय-उपस्थिति : isSet उपस्थिति
समुच्चय-उपस्थिति = Discrete→isSet विवेक-उपस्थिति

विवेक-समावेश : Discrete समावेश
विवेक-समावेश (a₁ , n₁ , v₁) (a₂ , n₂ , v₂)
  with विवेक-उपस्थिति a₁ a₂ | विवेक-उपस्थिति n₁ n₂ | विवेक-उपस्थिति v₁ v₂
... | no ¬p | _      | _      = no (λ e → ¬p (cong fst e))
... | yes _ | no ¬q  | _      = no (λ e → ¬q (cong (λ t → fst (snd t)) e))
... | yes _ | yes _  | no ¬r  = no (λ e → ¬r (cong (λ t → snd (snd t)) e))
... | yes p | yes q  | yes r  = yes (λ i → p i , q i , r i)

समुच्चय-समावेश : isSet समावेश
समुच्चय-समावेश = Discrete→isSet विवेक-समावेश

------------------------------------------------------------------------
-- १ · चतुर्थ-तन्तुः — THE FIBRE OF THE TONGUE-BREAK OVER THE FOURTH
--     POSITION.
------------------------------------------------------------------------

-- the fourth position's profile
चतुर्थम् : समावेश
चतुर्थम् = न , न , आम्

चतुर्थम्-अन्तर्भावः : अन्तर्भाव स्यात्-अवक्तव्यम् ≡ चतुर्थम्
चतुर्थम्-अन्तर्भावः = refl

-- शेष, at this map and this point.  Punaragamana.Sesa's `शेष f b` is
-- Σ[ a ] (f a ≡ b); that library cannot be imported from this lane (two
-- .agda-libs, two pins), so the Σ is written out.  It is the same Σ.
शेष-जिह्वा : Type
शेष-जिह्वा = Σ[ t ∈ समावेश ] (जिह्वाभेदः t ≡ चतुर्थम्)

-- १.१  three points of it, each a term.
स्वयम्-बिन्दुः : शेष-जिह्वा                -- the fixed point
स्वयम्-बिन्दुः = (न , न , आम्) , refl

उभय-रिक्तः : शेष-जिह्वा                    -- both seeds, avaktavya absent
उभय-रिक्तः = (आम् , आम् , न) , refl

उभय-सहितः : शेष-जिह्वा                     -- both seeds, avaktavya present
उभय-सहितः = (आम् , आम् , आम्) , refl

-- १.२  they are pairwise distinct — विकलादेश, exhibited, not asserted.
अभेद-प्रथमः : ¬ (स्वयम्-बिन्दुः ≡ उभय-रिक्तः)
अभेद-प्रथमः e = आम्≢न (sym (cong (λ u → fst (fst u)) e))

अभेद-द्वितीयः : ¬ (उभय-रिक्तः ≡ उभय-सहितः)
अभेद-द्वितीयः e = आम्≢न (sym (cong (λ u → snd (snd (fst u))) e))

-- १.३  hence the fibre is NOT contractible.  This is the whole of §2's
--      reason, standing on its own before §2 uses it.
चतुर्थः-न-सकलः : ¬ (isContr शेष-जिह्वा)
चतुर्थः-न-सकलः c = अभेद-प्रथमः (isContr→isProp c स्वयम्-बिन्दुः उभय-रिक्तः)

-- १.४  and the fibre COMPUTED: a fixed point plus exactly one bit, and the
--      bit is the third slot of the profile that broke.
चतुर्थ-तन्तु-गणना : Iso शेष-जिह्वा (Unit ⊎ उपस्थिति)
चतुर्थ-तन्तु-गणना = iso आगमः प्रत्यागमः दक्षिणम् वामम्
  where
    आगमः : शेष-जिह्वा → Unit ⊎ उपस्थिति
    आगमः ((आम् , आम् , v)  , _) = inr v
    आगमः ((न   , न   , आम्) , _) = inl tt
    आगमः ((आम् , न   , _)  , p) = ⊥-rec (आम्≢न (cong fst p))
    आगमः ((न   , आम् , _)  , p) = ⊥-rec (आम्≢न (cong (λ t → fst (snd t)) p))
    आगमः ((न   , न   , न)  , p) = ⊥-rec (आम्≢न (sym (cong (λ t → snd (snd t)) p)))

    प्रत्यागमः : Unit ⊎ उपस्थिति → शेष-जिह्वा
    प्रत्यागमः (inl _) = (न , न , आम्) , refl
    प्रत्यागमः (inr v) = (आम् , आम् , v) , refl

    दक्षिणम् : (u : Unit ⊎ उपस्थिति) → आगमः (प्रत्यागमः u) ≡ u
    दक्षिणम् (inl _)   = refl
    दक्षिणम् (inr आम्) = refl
    दक्षिणम् (inr न)   = refl

    -- the second component is a path in a set, hence unique
    समः : (t : समावेश) (p q : जिह्वाभेदः t ≡ चतुर्थम्) → p ≡ q
    समः t = समुच्चय-समावेश (जिह्वाभेदः t) चतुर्थम्

    वामम् : (u : शेष-जिह्वा) → प्रत्यागमः (आगमः u) ≡ u
    वामम् ((आम् , आम् , v)  , p) = ΣPathP (refl , समः (आम् , आम् , v) refl p)
    वामम् ((न   , न   , आम्) , p) = ΣPathP (refl , समः (न , न , आम्) refl p)
    वामम् ((आम् , न   , _)  , p) = ⊥-rec (आम्≢न (cong fst p))
    वामम् ((न   , आम् , _)  , p) = ⊥-rec (आम्≢न (cong (λ t → fst (snd t)) p))
    वामम् ((न   , न   , न)  , p) = ⊥-rec (आम्≢न (sym (cong (λ t → snd (snd t)) p)))

------------------------------------------------------------------------
-- २ · असङ्गतिः सङ्क्षेपः एव — NON-ASSOCIATIVITY IS THE COLLAPSE, DERIVED.
------------------------------------------------------------------------

-- २.१  IF the tongue-break destroyed nothing, saha WOULD be krama…
अलोपे-सह-क्रमः : ((t : समावेश) → जिह्वाभेदः t ≡ t)
               → (x y : सप्तभङ्गी) → सह-योग x y ≡ क्रम-योग x y
अलोपे-सह-क्रमः h x y =
  cong प्रत्यन्तर्भाव (h (संयोग (अन्तर्भाव x) (अन्तर्भाव y)))

-- …and therefore associative, since krama is.
अलोपे-सङ्गतिः : ((t : समावेश) → जिह्वाभेदः t ≡ t)
              → (x y z : सप्तभङ्गी)
              → सह-योग (सह-योग x y) z ≡ सह-योग x (सह-योग y z)
अलोपे-सङ्गतिः h x y z =
    अलोपे-सह-क्रमः h (सह-योग x y) z
  ∙ cong (λ t → क्रम-योग t z) (अलोपे-सह-क्रमः h x y)
  ∙ क्रम-सङ्गतिः x y z
  ∙ cong (क्रम-योग x) (sym (अलोपे-सह-क्रमः h y z))
  ∙ sym (अलोपे-सह-क्रमः h x (सह-योग y z))

-- २.२  THE DERIVATION.  The corpus's counterexample now proves that the
--      tongue-break genuinely destroys — collapse is entailed by the
--      failure of the law, not separately observed.
सङ्क्षेपः-अस्ति : ¬ ((t : समावेश) → जिह्वाभेदः t ≡ t)
सङ्क्षेपः-अस्ति h =
  सह-असङ्गतिः (अलोपे-सङ्गतिः h स्यात्-अस्ति-नास्ति स्यात्-अस्ति स्यात्-नास्ति)

-- २.३  and WHERE it destroys is exactly §1's fibre: off the both-seeds
--      profiles जिह्वाभेदः is the identity, and on them it is not.
अन्यत्र-अलोपः : (a n₀ v : उपस्थिति)
              → ¬ ((a ≡ आम्) × (n₀ ≡ आम्))
              → जिह्वाभेदः (a , n₀ , v) ≡ (a , n₀ , v)
अन्यत्र-अलोपः आम् आम् v ¬both = ⊥-rec (¬both (refl , refl))
अन्यत्र-अलोपः आम् न   v _     = refl
अन्यत्र-अलोपः न   आम् v _     = refl
अन्यत्र-अलोपः न   न   v _     = refl

उभयत्र-लोपः : ¬ (जिह्वाभेदः (आम् , आम् , न) ≡ (आम् , आम् , न))
उभयत्र-लोपः e = आम्≢न (sym (cong fst e))

------------------------------------------------------------------------
-- ३ · गर्भः — THE RESIDUAL IS WHAT WAS SAID AT ONCE.
------------------------------------------------------------------------

-- ३.१  the census without the equivalence: a profile reaches the fourth
--      position iff it IS the fourth position, or it carries BOTH seeds.
--      That disjunction is the content of अवक्तव्यम्.
गर्भ-लक्षणम् : (t : समावेश) → जिह्वाभेदः t ≡ चतुर्थम्
             → (t ≡ चतुर्थम्) ⊎ ((fst t ≡ आम्) × (fst (snd t) ≡ आम्))
गर्भ-लक्षणम् (आम् , आम् , _)  _ = inr (refl , refl)
गर्भ-लक्षणम् (न   , न   , आम्) _ = inl refl
गर्भ-लक्षणम् (आम् , न   , _)  p = ⊥-rec (आम्≢न (cong fst p))
गर्भ-लक्षणम् (न   , आम् , _)  p = ⊥-rec (आम्≢न (cong (λ t → fst (snd t)) p))
गर्भ-लक्षणम् (न   , न   , न)  p = ⊥-rec (आम्≢न (sym (cong (λ t → snd (snd t)) p)))

-- ३.२  the two seeds are recoverable FROM THE RESIDUAL and from nothing
--      else: the utterance स्यात्-अवक्तव्यम् has नास्त्यंशः न, while the profile
--      that produced it had आम्.  So the pair is not in the word and is in
--      the womb — arpita/anarpita, as a pair of terms.
वाचि-न-विद्यते : नास्त्यंशः स्यात्-अवक्तव्यम् ≡ न
वाचि-न-विद्यते = refl

गर्भे-विद्यते : fst (snd (fst उभय-रिक्तः)) ≡ आम्
गर्भे-विद्यते = refl
