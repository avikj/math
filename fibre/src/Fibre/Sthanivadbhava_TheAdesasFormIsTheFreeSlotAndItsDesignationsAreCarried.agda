{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- स्थानिवद्भावः — रूपम् एव स्वतन्त्रं, स्थानी सञ्ज्ञा च वाह्ये ।
-- (sthnivadbhva: the form is the only free slot; the sthnin and the
--  designation ride in the carried datum.)
--
-- THE STRAS, in the vulgate text and numbering.  Pini, *Adhyy*,
-- ~500 BCE; Ktyyana's vrttikas ~250 BCE; Patajali's *Mahbhya*
-- ~150 BCE.
--
--   1.1.56  स्थानिवदादेशोऽनल्विधौ   sthānivad ādeśo 'nalvidhau
--           A substitute (आदेश) is like the original it stands for
--           (स्थानिन्) — except in an अल्विधि, an operation conditioned on
--           the sounds themselves (अल् is the pratyāhāra of the whole
--           inventory).
--   1.1.60  अदर्शनं लोपः            adarśanaṃ lopaḥ — elision is
--           NON-APPEARANCE.
--   1.1.62  प्रत्ययलोपे प्रत्ययलक्षणम्  pratyayalope pratyayalakṣaṇam — when
--           an affix is elided, the operations conditioned by that affix
--           still apply.
--   1.3.9   तस्य लोपः               tasya lopaḥ — the it-marker is elided,
--           having already done its marking.
--   1.1.5   क्ङिति च                 kṅiti ca — no guṇa/vṛddhi after an
--           affix marked k or , a marking 1.3.9 has already erased.
--
-- CLAIMED OF THE SOURCE: form, sthnin and designation are the
-- three distinctions 1.1.56 turns on, and its अल्/अनल् exception splits
-- one of the three off from the other two.
--
------------------------------------------------------------------------
-- WHICH SLOTS ARE BASE AND WHICH ARE CARRIED — answered by the
-- mathematics rather than by preference.
--
-- FIRST ANSWER, and it is negative.  A bare वर्ण — a record of रूपम् /
-- स्थानी / सञ्ज्ञा — is NOT a Carrier.  None of its three fields is a
-- function of the other two, and that is three theorems below
-- (`रूपम्-न-निर्धारितम्`, `स्थानी-न-निर्धारितः`, `सञ्ज्ञा-न-निर्धारिता`),
-- each exhibiting two वर्ण agreeing on two fields, disagreeing on the
-- third, and provably distinct.  This is the same shape as the three
-- slots of the कुट्टक in this library and has the same consequence:
-- there is no Carrier whose base is two fields of a वर्ण and whose
-- carried datum is the third.  The fibre of any such forgetful map has
-- two points that are not joined, so it is not contractible and `Σ-law`
-- has nothing to consume.
--
-- SECOND ANSWER, and it is the instance.  What is determined is not a
-- field of a वर्ण; it is a field of the OUTPUT of the आदेश OPERATION.
-- Take as base the pair
--
--     आधार  =  वर्ण × वर्णरूप      (the varṇa operated on, and the form
--                                    to be put in its place)
--
-- and read off what 1.1.56 says the substitute inherits:
--
--     निर्धारितम् (v , f)  =  (रूपम् v , सञ्ज्ञा v)  :  वर्णरूप × वर्णसञ्ज्ञा
--     स्थानिवत्           =  Carrier निर्धारितम्
--
-- The output's स्थानी IS the input's रूपम्, and the output's सञ्ज्ञा IS
-- the input's सञ्ज्ञा.  Both are functions of the base.  The substituted
-- form f is a function of nothing and sits in the base as a free slot.
-- The fibre Σ[ p ] (निर्धारितम् x ≡ p) = singl (निर्धारितम् x) is
-- contractible, so आधार ≃ स्थानिवत् and, by univalence, आधार ≡ स्थानिवत्.
--
-- WHY THE PAIR AND NOT THE स्थानिन् ALONE.  The candidate this module was
-- asked to check was `f (v , r) = रूपम् v`, carrying the स्थानी by itself.
-- That is correct and it is not the whole of what is determined: सञ्ज्ञा
-- is determined by the base in exactly the same way, and it is the
-- quantity 1.1.56 is actually about — the substitute inherits the
-- DESIGNATIONS.  Carrying the स्थानी while leaving the सञ्ज्ञा in the base
-- would put a determined quantity in the free part, which is the error
-- the law exists to prevent.  So the carried datum is the pair and the
-- free slot is the form alone.  That IS 1.1.56, read as an arity count.
--
-- THE अल्/अनल् SPLIT IS THE BASE/CARRIED SPLIT.  This is the point of the
-- module.  A rule reading only सञ्ज्ञा factors through the carried datum,
-- and the carried datum does not mention the free slot — so such a rule
-- cannot see which form was substituted, and it cannot see it BY refl
-- (`वाहक-अन्धः`).  A rule reading the form is reading the free slot, and
-- there is provably no function of the carried datum agreeing with it
-- (`एच्-न-वाह्यम्`).  1.1.56's exception clause is not a hedge; it names
-- the slot the law had to leave free.
--
------------------------------------------------------------------------
-- WHAT THE ORBIT THEOREM ESTABLISHES ABOUT 1.1.62.
--
-- 1.1.62 is the reason single-step preservation is not enough: an
-- operation conditioned by an elided affix applies LATER, so whatever
-- 1.1.56 secures must survive the rest of the derivation and not one
-- rewrite.  Here a derivation is `unfold पदम्` — the whole infinite
-- trajectory as one object — and the statements about it are proved as
-- BISIMULATIONS, corecursively, one head at a time, because equality of
-- coinductive objects is not implied by agreement on any finite prefix.
--
--   `सञ्ज्ञा-अनुवृत्तिः`: along the entire orbit of an
--   ARBITRARY rule नियम, the designation read off the carried datum is
--   constant and equal to the designation of the starting varṇa — not
--   "for every n" but as a single path between two coinductive objects.
--   And `स्थानि-शृङ्खला`: at every position, the स्थानी carried at step
--   n+1 is the रूपम् standing at step n, so the chain back to the
--   original is unbroken at arbitrary depth.
--
--   What the orbit theorem establishes is
--   the weaker, prior statement 1.1.62 PRESUPPOSES: that the designation
--   a later rule wants to read is still there to be read at arbitrary
--   derivational depth.  1.1.62 asserts that this holds even when the
--   bearer has disappeared from the surface.
--
------------------------------------------------------------------------
-- REMARKS.
--
-- 1. `आदेश` IS NOT LITERALLY `descend`, and cannot be — different
--    codomains.  `descend निर्धारितम् : आधार → स्थानिवत्`, while
--    `आदेश : वर्णरूप → वर्ण → वर्ण`.  They differ by exactly one map,
--    `पुनर्रचना : स्थानिवत् → वर्ण`, which reassembles a varṇa from the free
--    slot and the two carried components, and the factorisation is
--    DEFINITIONAL: `आदेश-अवतरणम्` is `refl`.  So the honest statement is
--    `पुनर्रचना (अवतरण (v , f)) ≡ आदेश f v` by refl, not `आदेश ≡ descend`.
--    Conversely `वहनम्-आदेशः`, also refl, says the carried datum is the
--    pair (स्थानी , सञ्ज्ञा) of the ādeśa's own output.  The two records
--    hold the same information; neither is the other.
--
-- 2. `आदेश-अन्धः` — the parent module's `anal-blind` — DID HAVE TO BE
--    REPROVED, and the reason is worth more than the theorem.  What the
--    Carrier gives for free is `वाहक-अन्धः`: two bases differing ONLY in
--    the free slot have equal carried data, hence equal verdicts from any
--    carried-reading rule, BY refl, with no factorisation lemma and no
--    case analysis.  That is the stronger and cleaner statement.  It does
--    NOT entail `anal-blind`, because `anal-blind` compares the dea
--    with the स्थानिन् VARṆA v, and v is not in the image of
--    `पुनर्रचना ∘ अवतरण` unless स्थानी v ≡ रूपम् v.  The two points being
--    compared do not lie in one fibre of निर्धारितम्, so the contraction
--    has nothing to say about them and the `h _ ∙ sym (h _)` survives.
--    Stated as a finding: THE LAW DERIVES 1.1.56's BLINDNESS ACROSS
--    SUBSTITUTIONS DEFINITIONALLY AND DOES NOT DERIVE ITS BLINDNESS
--    BETWEEN A SUBSTITUTE AND ITS ORIGINAL.  `आदेश-स्वस्थानी` and
--    `आदेश-अन्धः-वाहकात्` below isolate the exact extra hypothesis
--    (स्थानी v ≡ रूपम् v) that closes the gap, so the missing ingredient
--    is named rather than described.
--
-- 3. THE RULE IS A FUNCTION वर्ण → वर्णरूप.  Real sūtras read a word, an
--    environment, and the त्रिपादी's असिद्धत्व stratification (§४६ of
--    notes/AHIMSA_SUTRA_VISTARA.md (absent from this repository): what is asiddha is not seen; the
--    later rule's result is invisible to the earlier).  A one-vara rule
--    has no environment and no stratum, so the orbit below is the
--    trajectory of ONE site under ONE rule and not a derivation of the
--    *Adhyy*.  Calling it a derivation would be a false
--    advertisement; the step is called पदम् and प्रक्रिया occurs as a type
--    abbreviation and in this header, never as a claim.
--
-- 4. THREE FORMS AND NO MORE — ī, its guṇa substitute e, and the a that
--    6.1.78 would produce from e: the ones the derivation of नयन passes
--    through, taken from the parent-repository module.
--
-- 5. Nothing here imports outside `Punaragamana`: the vocabulary वर्ण /
--    आदेश / AnalVidhi is redefined rather than imported from
--    `formal/cubical`, so the library stays standalone and `check.sh` (absent from this repository)
--    keeps checking what it says it checks.  That duplication is
--    deliberate, and it is the same trade the कुट्टक module records.
------------------------------------------------------------------------

module Fibre.Sthanivadbhava_TheAdesasFormIsTheFreeSlotAndItsDesignationsAreCarried where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (Σ; _×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)

open import Fibre.Carrier
open import Fibre.Orbit
open import Fibre.Nucleus

private
  ¬_ : Type → Type
  ¬ A = A → ⊥

------------------------------------------------------------------------
-- १ · वर्णरूप and वर्णसञ्ज्ञा, with their distinctness.
--
-- The types are named as compounds (the forms of a vara, the
-- designations of a vara) because the record fields below take the
-- bare terms रूपम् / सञ्ज्ञा, which is what a sūtra reads.
------------------------------------------------------------------------

data वर्णरूप : Type where
  ई ए अ : वर्णरूप

data वर्णसञ्ज्ञा : Type where
  अङ्ग प्रत्यय कित् : वर्णसञ्ज्ञा

रूप-कोड : वर्णरूप → Type
रूप-कोड ई = Unit
रूप-कोड ए = ⊥
रूप-कोड अ = ⊥

ई≢ए : ¬ (ई ≡ ए)
ई≢ए p = subst रूप-कोड p tt

सञ्ज्ञा-कोड : वर्णसञ्ज्ञा → Type
सञ्ज्ञा-कोड अङ्ग   = Unit
सञ्ज्ञा-कोड प्रत्यय = ⊥
सञ्ज्ञा-कोड कित्   = ⊥

अङ्ग≢कित् : ¬ (अङ्ग ≡ कित्)
अङ्ग≢कित् p = subst सञ्ज्ञा-कोड p tt

------------------------------------------------------------------------
-- २ · वर्ण — the three slots, one record.  रूपम् is the representation,
-- स्थानी is what it stands in place of (itself, when nothing), सञ्ज्ञा is
-- the interface.
------------------------------------------------------------------------

record वर्ण : Type where
  constructor वर्णः
  field
    रूपम्  : वर्णरूप
    स्थानी : वर्णरूप
    सञ्ज्ञा : वर्णसञ्ज्ञा

open वर्ण public

------------------------------------------------------------------------
-- ३ · NO FIELD OF A वर्ण IS A FUNCTION OF THE OTHER TWO.
--
-- Three theorems, in the shape of `पक्षः-न-निर्धारितः` in this library's
-- कुट्टक module: two records agreeing on two coordinates by refl,
-- disagreeing on the third, provably distinct.  वर्ण is therefore not a
-- Carrier of any forgetful map out of a two-field base.
------------------------------------------------------------------------

रूपम्-न-निर्धारितम् :
    (स्थानी (वर्णः ई ई अङ्ग) ≡ स्थानी (वर्णः ए ई अङ्ग))
  × ((सञ्ज्ञा (वर्णः ई ई अङ्ग) ≡ सञ्ज्ञा (वर्णः ए ई अङ्ग))
  × (¬ (वर्णः ई ई अङ्ग ≡ वर्णः ए ई अङ्ग)))
रूपम्-न-निर्धारितम् = refl , (refl , λ p → ई≢ए (cong रूपम् p))

स्थानी-न-निर्धारितः :
    (रूपम् (वर्णः ई ई अङ्ग) ≡ रूपम् (वर्णः ई ए अङ्ग))
  × ((सञ्ज्ञा (वर्णः ई ई अङ्ग) ≡ सञ्ज्ञा (वर्णः ई ए अङ्ग))
  × (¬ (वर्णः ई ई अङ्ग ≡ वर्णः ई ए अङ्ग)))
स्थानी-न-निर्धारितः = refl , (refl , λ p → ई≢ए (cong स्थानी p))

सञ्ज्ञा-न-निर्धारिता :
    (रूपम् (वर्णः ई ई अङ्ग) ≡ रूपम् (वर्णः ई ई कित्))
  × ((स्थानी (वर्णः ई ई अङ्ग) ≡ स्थानी (वर्णः ई ई कित्))
  × (¬ (वर्णः ई ई अङ्ग ≡ वर्णः ई ई कित्)))
सञ्ज्ञा-न-निर्धारिता = refl , (refl , λ p → अङ्ग≢कित् (cong सञ्ज्ञा p))

------------------------------------------------------------------------
-- ४ · आदेश — 1.1.56 as an operation.  A new form; the old form kept as
-- the sthnin; the designation inherited.
------------------------------------------------------------------------

आदेश : वर्णरूप → वर्ण → वर्ण
आदेश f v = वर्णः f (रूपम् v) (सञ्ज्ञा v)

आदेश-सञ्ज्ञा : (f : वर्णरूप) (v : वर्ण) → सञ्ज्ञा (आदेश f v) ≡ सञ्ज्ञा v
आदेश-सञ्ज्ञा f v = refl

आदेश-रूपम् : (f : वर्णरूप) (v : वर्ण) → रूपम् (आदेश f v) ≡ f
आदेश-रूपम् f v = refl

आदेश-स्थानी : (f : वर्णरूप) (v : वर्ण) → स्थानी (आदेश f v) ≡ रूपम् v
आदेश-स्थानी f v = refl

-- when a vara already stands for its own form, replacing it by that
-- same form changes nothing.  This is the hypothesis Remark 2 isolates.
आदेश-स्वस्थानी : (v : वर्ण) → स्थानी v ≡ रूपम् v → आदेश (रूपम् v) v ≡ v
आदेश-स्वस्थानी v p i = वर्णः (रूपम् v) (p (~ i)) (सञ्ज्ञा v)

------------------------------------------------------------------------
-- ५ · THE INSTANCE.  Base = (the varṇa operated on , the form put in its
-- place).  Carried = what the output inherits, which is a function of the
-- base and does not mention the substituted form at all.
--
-- No pattern match on the pair: Σ has eta, and keeping the projections is
-- what makes the square close for an opaque variable.
------------------------------------------------------------------------

आधार : Type
आधार = वर्ण × वर्णरूप

निर्धारितम् : आधार → वर्णरूप × वर्णसञ्ज्ञा
निर्धारितम् x = रूपम् (fst x) , सञ्ज्ञा (fst x)

स्थानिवत् : Type
स्थानिवत् = Carrier निर्धारितम्

-- the four coordinates: two from the base, two carried.  The carried
-- pair is read as the स्थानी and the सञ्ज्ञा OF THE OUTPUT of the pending
-- substitution, which is what `पुनर्रचना` below assembles.
स्थानिवत्-वर्णः : स्थानिवत् → वर्ण
स्थानिवत्-वर्णः c = fst (base c)

स्थानिवत्-रूपम् : स्थानिवत् → वर्णरूप
स्थानिवत्-रूपम् c = snd (base c)          -- THE FREE SLOT

स्थानिवत्-स्थानी : स्थानिवत् → वर्णरूप
स्थानिवत्-स्थानी c = fst (carried c)

स्थानिवत्-सञ्ज्ञा : स्थानिवत् → वर्णसञ्ज्ञा
स्थानिवत्-सञ्ज्ञा c = snd (carried c)

स्थानिवत्-प्रमाण : (c : स्थानिवत्) → निर्धारितम् (base c) ≡ carried c
स्थानिवत्-प्रमाण c = witness c

-- the fibre is singl, hence contractible; hence the equivalence and the path
स्थानिवत्-क्षेत्र-सम्पूर्ण : (x : आधार) → isContr (fibre निर्धारितम् x)
स्थानिवत्-क्षेत्र-सम्पूर्ण = fibre-isContr निर्धारितम्

आधार-Iso-स्थानिवत् : Iso आधार स्थानिवत्
आधार-Iso-स्थानिवत् = Carrier-Iso निर्धारितम्

आधार≃स्थानिवत् : आधार ≃ स्थानिवत्
आधार≃स्थानिवत् = Carrier≃ निर्धारितम्

आधार≡स्थानिवत् : आधार ≡ स्थानिवत्
आधार≡स्थानिवत् = Carrier≡ निर्धारितम्

अवतरण : आधार → स्थानिवत्
अवतरण = descend निर्धारितम्

आरोहः : स्थानिवत् → आधार
आरोहः = ascend निर्धारितम्

परिवहन : आधार → स्थानिवत्
परिवहन = carry-transport निर्धारितम्

परिवहन-अवतरण : (x : आधार) → परिवहन x ≡ अवतरण x
परिवहन-अवतरण = carry-transport-descend निर्धारितम्

------------------------------------------------------------------------
-- ६ · IS आदेश THE descend?  Not literally — different codomains.  It is
-- descend composed with one reassembly map, and the factorisation is
-- definitional in both directions.  See Remark 1.
------------------------------------------------------------------------

पुनर्रचना : स्थानिवत् → वर्ण
पुनर्रचना c = वर्णः (स्थानिवत्-रूपम् c) (स्थानिवत्-स्थानी c) (स्थानिवत्-सञ्ज्ञा c)

-- descend, reassembled, IS the dea
आदेश-अवतरणम् : (v : वर्ण) (f : वर्णरूप) → पुनर्रचना (अवतरण (v , f)) ≡ आदेश f v
आदेश-अवतरणम् v f = refl

-- and the carried datum IS the pair (sthnin , designation) of the
-- dea's own output
वहनम्-आदेशः : (v : वर्ण) (f : वर्णरूप)
            → carried (अवतरण (v , f)) ≡ (स्थानी (आदेश f v) , सञ्ज्ञा (आदेश f v))
वहनम्-आदेशः v f = refl

-- the same along the univalent transport rather than along descend.  This
-- one is NOT refl: transport along ua does not reduce on a neutral
-- variable, so it goes through uaβ.  (§६ द्वौ मार्गौ — the transport
-- carries the structure and nothing is lost.)
आदेश-परिवहनम् : (v : वर्ण) (f : वर्णरूप) → पुनर्रचना (परिवहन (v , f)) ≡ आदेश f v
आदेश-परिवहनम् v f = cong पुनर्रचना (परिवहन-अवतरण (v , f))

------------------------------------------------------------------------
-- ७ · THE अल्/अनल् SPLIT IS THE BASE/CARRIED SPLIT.
--
-- अनल्विधि: a rule that factors through the designation.  The definition
-- is the parent module's, restated here so this library imports nothing
-- outside itself.
------------------------------------------------------------------------

AnalVidhi : (A : Type) → (वर्ण → A) → Type
AnalVidhi A r = Σ (वर्णसञ्ज्ञा → A) (λ g → (v : वर्ण) → r v ≡ g (सञ्ज्ञा v))

-- WHAT THE CARRIER GIVES FOR FREE.  A rule reading only the carried
-- datum cannot see the free slot — BY refl, for opaque arguments, with no
-- factorisation lemma and no case analysis.  Which form was substituted
-- is invisible to it.
वाहक-अन्धः : {A : Type} (g : वर्णरूप × वर्णसञ्ज्ञा → A) (v : वर्ण) (f f' : वर्णरूप)
           → g (carried (अवतरण (v , f))) ≡ g (carried (अवतरण (v , f')))
वाहक-अन्धः g v f f' = refl

-- An anal-vidhi IS such a rule: it factors through the carried datum,
-- because the designation of the output is the carried datum's second
-- projection.
अनल्विधिः-वाहकेन : {A : Type} (r : वर्ण → A) → AnalVidhi A r
                → Σ (वर्णरूप × वर्णसञ्ज्ञा → A)
                    (λ g → (x : आधार) → r (पुनर्रचना (अवतरण x)) ≡ g (carried (अवतरण x)))
अनल्विधिः-वाहकेन r (g , h) = (λ p → g (snd p)) , (λ x → h (पुनर्रचना (अवतरण x)))

-- and so it answers the same whatever form was substituted: 1.1.56's
-- blindness ACROSS SUBSTITUTIONS, which is the half the law derives.
अनल्विधिः-अन्धः : {A : Type} (r : वर्ण → A) → AnalVidhi A r
                → (v : वर्ण) (f f' : वर्णरूप) → r (आदेश f v) ≡ r (आदेश f' v)
अनल्विधिः-अन्धः {A} r av v f f' =
  k (v , f) ∙ वाहक-अन्धः g' v f f' ∙ sym (k (v , f'))
  where
    g' : वर्णरूप × वर्णसञ्ज्ञा → A
    g' = fst (अनल्विधिः-वाहकेन r av)

    k : (x : आधार) → r (पुनर्रचना (अवतरण x)) ≡ g' (carried (अवतरण x))
    k = snd (अनल्विधिः-वाहकेन r av)

-- THE PARENT MODULE'S STATEMENT, reproved from the factorisation.  See
-- Remark 2: the two points compared do not lie in one fibre of
-- निर्धारितम्, so the contraction has nothing to say about them.
आदेश-अन्धः : {A : Type} (r : वर्ण → A) → AnalVidhi A r
           → (f : वर्णरूप) (v : वर्ण) → r (आदेश f v) ≡ r v
आदेश-अन्धः r (g , h) f v = h (आदेश f v) ∙ sym (h v)

-- …and the exact extra hypothesis under which it DOES follow from the
-- carrier half: when v already stands for its own form, v is in the image
-- of पुनर्रचना ∘ अवतरण and the two points share a fibre.
आदेश-अन्धः-वाहकात् : {A : Type} (r : वर्ण → A) (av : AnalVidhi A r)
                   → (v : वर्ण) → स्थानी v ≡ रूपम् v
                   → (f : वर्णरूप) → r (आदेश f v) ≡ r v
आदेश-अन्धः-वाहकात् r av v p f =
  अनल्विधिः-अन्धः r av v f (रूपम् v) ∙ cong r (आदेश-स्वस्थानी v p)

-- THE OTHER HALF, AND IT MUST FAIL.  6.1.78 एचोऽयवायावः operates on एच्;
-- asking whether a sound is in एच् is asking about the sound.  There is
-- no function of the CARRIED datum that agrees with it — two bases with
-- identical carried data, opposite verdicts.  The अल्विधि reads the free
-- slot, which is what 1.1.56's exception clause names.
एचः-अयवायावः : वर्ण → वर्णरूप
एचः-अयवायावः v = रूपम् v

CarriedVidhi : (A : Type) → (आधार → A) → Type
CarriedVidhi A r = Σ (वर्णरूप × वर्णसञ्ज्ञा → A) (λ g → (x : आधार) → r x ≡ g (निर्धारितम् x))

ई-अङ्ग : वर्ण
ई-अङ्ग = वर्णः ई ई अङ्ग

एच्-न-वाह्यम् : ¬ (CarriedVidhi वर्णरूप (λ x → एचः-अयवायावः (पुनर्रचना (अवतरण x))))
एच्-न-वाह्यम् (g , h) = ई≢ए (h (ई-अङ्ग , ई) ∙ sym (h (ई-अङ्ग , ए)))

-- concretely: the same input vara, two substitutions, two verdicts
पठनम्-भिन्नम् : ¬ (एचः-अयवायावः (आदेश ए ई-अङ्ग) ≡ एचः-अयवायावः (आदेश ई ई-अङ्ग))
पठनम्-भिन्नम् p = ई≢ए (sym p)

------------------------------------------------------------------------
-- ८ · पदम् — THE STEP, as a Φ on the base.
--
-- A rule नियम : वर्ण → वर्णरूप says what form to put in the current
-- vara's place.  One step performs the pending substitution and asks the
-- rule for the next form.
------------------------------------------------------------------------

पदम् : (वर्ण → वर्णरूप) → आधार → आधार
पदम् नियम x = आदेश (snd x) (fst x) , नियम (आदेश (snd x) (fst x))

------------------------------------------------------------------------
-- ९ · THE LIFT, AND THE SQUARE.  Neither is proved here — both are
-- instances of the law, and `Φ-square` closes DEFINITIONALLY, by refl,
-- for an opaque variable.
------------------------------------------------------------------------

module _ (नियम : वर्ण → वर्णरूप) where

  पदम्-स्थानिवत् : स्थानिवत् → स्थानिवत्
  पदम्-स्थानिवत् = Φ-carrier निर्धारितम् (पदम् नियम)

  पदम्-वर्गः : (x : आधार) → पदम्-स्थानिवत् (अवतरण x) ≡ अवतरण (पदम् नियम x)
  पदम्-वर्गः = Φ-square निर्धारितम् (पदम् नियम)

  पदम्-आरोहः : (c : स्थानिवत्) → आरोहः (पदम्-स्थानिवत् c) ≡ पदम् नियम (आरोहः c)
  पदम्-आरोहः = Φ-ascend निर्धारितम् (पदम् नियम)

  पदम्-परिवहन : (x : आधार) → परिवहन (पदम् नियम x) ≡ अवतरण (पदम् नियम x)
  पदम्-परिवहन = Φ-transport निर्धारितम् (पदम् नियम)

  -- the carried datum is recomputed at every step, never stale: after one
  -- step the sthnin is the form that was just substituted, and the
  -- designation is the one the input had
  पदम्-वहनम् : (x : आधार)
             → carried (पदम्-स्थानिवत् (अवतरण x)) ≡ (snd x , सञ्ज्ञा (fst x))
  पदम्-वहनम् x = refl

------------------------------------------------------------------------
-- १० · THE ORBIT — the whole run as one object, and the payoff.
--
-- `Nucleus` says carrier and orbit commute over the WHOLE infinite
-- trajectory.  The two theorems after those instances are the ones 1.1.62
-- makes necessary and which a single-step square cannot supply.
------------------------------------------------------------------------

module _ (नियम : वर्ण → वर्णरूप) where

  प्रक्रिया : Type
  प्रक्रिया = Orbit स्थानिवत्

  बुन : आधार → प्रक्रिया
  बुन x = unfold (पदम्-स्थानिवत् नियम) (अवतरण x)

  -- descending pointwise along the base orbit IS the carrier orbit:
  -- instances, proved corecursively in Nucleus, not reproved here
  बुन-अवतरणम् : (x : आधार) → mapO अवतरण (unfold (पदम् नियम) x) ≡ बुन x
  बुन-अवतरणम् = descend-orbit निर्धारितम् (पदम् नियम)

  बुन-आरोहः : (x : आधार) → mapO आरोहः (बुन x) ≡ unfold (पदम् नियम) x
  बुन-आरोहः = ascend-orbit निर्धारितम् (पदम् नियम)

  बुन-परिवहन : (x : आधार) → mapO परिवहन (unfold (पदम् नियम) x) ≡ बुन x
  बुन-परिवहन = transport-orbit निर्धारितम् (पदम् नियम)

  ------------------------------------------------------------------
  -- THE DESIGNATION SURVIVES THE WHOLE DERIVATION — not "for every n",
  -- but as a single path between two coinductive objects, proved by
  -- bisimulation, because agreement on every finite prefix is not what
  -- equality of orbits is.
  ------------------------------------------------------------------

  स्थिर : वर्णसञ्ज्ञा → Orbit वर्णसञ्ज्ञा
  here (स्थिर s) = s
  next (स्थिर s) = स्थिर s

  सञ्ज्ञा-अनुवृत्तिः≈ : (x : आधार)
                    → mapO स्थानिवत्-सञ्ज्ञा (बुन x) ≈ स्थिर (सञ्ज्ञा (fst x))
  ≈here (सञ्ज्ञा-अनुवृत्तिः≈ x) = refl
  ≈next (सञ्ज्ञा-अनुवृत्तिः≈ x) = सञ्ज्ञा-अनुवृत्तिः≈ (पदम् नियम x)

  सञ्ज्ञा-अनुवृत्तिः : (x : आधार)
                   → mapO स्थानिवत्-सञ्ज्ञा (बुन x) ≡ स्थिर (सञ्ज्ञा (fst x))
  सञ्ज्ञा-अनुवृत्तिः x = bisim (सञ्ज्ञा-अनुवृत्तिः≈ x)

  -- the finite reading of the same fact, position by position
  सञ्ज्ञा-पदे : (x : आधार) (n : ℕ)
             → स्थानिवत्-सञ्ज्ञा (lookup (बुन x) n) ≡ सञ्ज्ञा (fst x)
  सञ्ज्ञा-पदे x zero    = refl
  सञ्ज्ञा-पदे x (suc n) = सञ्ज्ञा-पदे (पदम् नियम x) n

  ------------------------------------------------------------------
  -- THE CHAIN BACK TO THE ORIGINAL IS UNBROKEN AT EVERY DEPTH: the
  -- sthnin carried at position n+1 is the form standing at position n.
  ------------------------------------------------------------------

  स्थानि-शृङ्खला : (x : आधार) (n : ℕ)
                → स्थानिवत्-स्थानी (lookup (बुन x) (suc n))
                ≡ स्थानिवत्-रूपम् (lookup (बुन x) n)
  स्थानि-शृङ्खला x zero    = refl
  स्थानि-शृङ्खला x (suc n) = स्थानि-शृङ्खला (पदम् नियम x) n

  -- and each position is the descent of the n-th iterate: an instance of
  -- `orbit-lookup`, so the finite view and the coinductive one are one
  -- object read two ways
  पद-स्थानम् : (x : आधार) (n : ℕ)
             → lookup (बुन x) n ≡ अवतरण (iterate (पदम् नियम) n x)
  पद-स्थानम् = orbit-lookup निर्धारितम् (पदम् नियम)

------------------------------------------------------------------------
-- ११ · IT RUNS.  नी + ल्युट् → नयन, at the aṅga's final position: 7.3.84
-- puts ए in place of ई (guṇa), and 6.1.78 एचोऽयवायावः then operates on
-- that ए, because it is an अल्विधि and reads the substitute.  Each line
-- holds by refl, so Agda must execute the steps.
--
-- The rule below is a caricature: one site, no environment, no
-- stratification (Remark 3).  What the numbers show is only that the
-- carried datum tracks the chain — ए stands for ई, अ stands for ए — and
-- that the designation अङ्ग is never lost.
------------------------------------------------------------------------

अग्रिम-रूप : वर्णरूप → वर्णरूप
अग्रिम-रूप ई = ए
अग्रिम-रूप ए = अ
अग्रिम-रूप अ = अ

अग्रिम : वर्ण → वर्णरूप
अग्रिम v = अग्रिम-रूप (रूपम् v)

आरम्भः : आधार
आरम्भः = ई-अङ्ग , ए              -- ī, with 7.3.84's e pending

गणना-प्रथमम् : पदम् अग्रिम आरम्भः ≡ (वर्णः ए ई अङ्ग , अ)
गणना-प्रथमम् = refl

गणना-द्वितीयम् : iterate (पदम् अग्रिम) 2 आरम्भः ≡ (वर्णः अ ए अङ्ग , अ)
गणना-द्वितीयम् = refl

गणना-वहनम् : carried (lookup (बुन अग्रिम आरम्भः) 2) ≡ (अ , अङ्ग)
गणना-वहनम् = refl

गणना-स्थानी : स्थानिवत्-स्थानी (lookup (बुन अग्रिम आरम्भः) 1) ≡ ए
गणना-स्थानी = refl

गणना-सञ्ज्ञा : स्थानिवत्-सञ्ज्ञा (lookup (बुन अग्रिम आरम्भः) 20) ≡ अङ्ग
गणना-सञ्ज्ञा = refl

गणना-स्थिरम् : iterate (पदम् अग्रिम) 20 आरम्भः ≡ (वर्णः अ अ अङ्ग , अ)
गणना-स्थिरम् = refl

-- the अल्विधि reads the substitute and the अनल्विधि does not: after one
-- step the form is ए and the designation is still अङ्ग
गणना-अल् : एचः-अयवायावः (fst (iterate (पदम् अग्रिम) 1 आरम्भः)) ≡ ए
गणना-अल् = refl

गणना-अनल् : सञ्ज्ञा (fst (iterate (पदम् अग्रिम) 1 आरम्भः)) ≡ अङ्ग
गणना-अनल् = refl
