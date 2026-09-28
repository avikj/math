{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सप्तभङ्गी-संयोगः — द्वयोः भङ्गयोः योगः, क्रमेण सह च ।
-- (The composition of two verdicts, in succession and simultaneously.)
--
-- WHAT THIS FILE ADDS.  `Saptabhangi.agda` in this directory already has
-- the seven positions, the 2³ = 7 + 1 count, and the theorem that a
-- two-valued verdict must identify two of the three seeds.  It has no
-- ALGEBRA: nothing there says what happens when two verdicts meet, and a
-- verdict type that cannot be composed cannot be returned by two lanes and
-- read by a third.  This file supplies the two composition laws, and the
-- three facts that make them worth having:
--
--   क्रम-सङ्गतिः          — succession composes associatively (a semilattice)
--   अवक्तव्यम्-न-क्रमजम्   — avaktavya is NOT reachable by succession:
--                            it is a positive fourth position, supplied,
--                            not derived
--   सह-असङ्गतिः           — simultaneity is NOT associative, so the seven
--                            are not a lattice under it and the two laws
--                            do not merge into one
--   मेलनम्-नास्ति          — asti and nāsti have no greatest lower bound:
--                            the meet a Boolean lattice would supply lands
--                            on the eighth profile, which is no predication
--                            at all
--
-- SOURCES, EARLIEST FIRST, for the doctrine that is being formalised; the
-- classification and the order/saha rule are theirs.
--
--   Bhagavat Stra (Viyha-pannatti), fifth Aga of the vetmbara canon;
--     oldest strata pre-Common-Era, redacted at Valabhī c. 5th c. CE —
--     sevenfold predication applied to the jva.
--   Umāsvāti, Tattvārthasūtra, c. 2nd–5th c. CE —
--     5.31  arpitnarpita-siddhe : apparently contradictory attributes are
--           established by the distinction of the ASSERTED (arpita) and the
--           UNASSERTED (anarpita) aspect.  The standpoint index, stated as
--           such, in the 2nd–5th century.
--     5.29  utpāda-vyaya-dhrauvya-yuktaṃ sat — origination, cessation and
--           persistence held AT ONCE, which is the saha mode below.
--   Siddhasena Divākara, Sanmatitarka 1.21, c. 5th c. CE — a naya taken
--     alone (nirapeka) is mithy; the durnaya is the naya that has
--     forgotten it is one.
--   Samantabhadra, Āptamīmāṃsā, c. 6th c. CE — the saptabhaṅgī as a fixed
--     seven-membered scheme, each member prefixed `syt`.
--   Akalaṅka, Laghīyastraya / Aṣṭaśatī, c. 720–780 CE — क्रमार्पणक्रमार्पणthe order (,
--     sequential) versus saha / yugapat (सह, simultaneous) distinction,
--     which is the whole content of the two operations here, and the
--     argument that the number is exactly seven.
--   Mallisena, Syādvādamañjarī, 1292 CE — sakalādeśa (total statement,
--     prama) against vikaldea (partial statement, naya).
--
------------------------------------------------------------------------

module SaptabhangiSamyoga_TheCompositionOfVerdicts where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥ ; rec)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; Σ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

open import Saptabhangi
  using ( सप्तभङ्गी
        ; स्यात्-अस्ति ; स्यात्-नास्ति ; स्यात्-अस्ति-नास्ति ; स्यात्-अवक्तव्यम्
        ; स्यात्-अस्ति-अवक्तव्यम् ; स्यात्-नास्ति-अवक्तव्यम् ; स्यात्-अस्ति-नास्ति-अवक्तव्यम्
        ; उपस्थिति ; आम् ; न ; समावेश ; अन्तर्भाव ; प्रत्यन्तर्भाव ; वृत्तम् )

------------------------------------------------------------------------
-- १ · वा — उपस्थितेः योगः ।  (presence, joined: present if either is.)
------------------------------------------------------------------------

वा : उपस्थिति → उपस्थिति → उपस्थिति
वा आम् _ = आम्
वा न   q = q

वा-सङ्गतिः : (p q r : उपस्थिति) → वा (वा p q) r ≡ वा p (वा q r)
वा-सङ्गतिः आम् _   _ = refl
वा-सङ्गतिः न   आम् _ = refl
वा-सङ्गतिः न   न   _ = refl

वा-विनिमयः : (p q : उपस्थिति) → वा p q ≡ वा q p
वा-विनिमयः आम् आम् = refl
वा-विनिमयः आम् न   = refl
वा-विनिमयः न   आम् = refl
वा-विनिमयः न   न   = refl

वा-स्वयम् : (p : उपस्थिति) → वा p p ≡ p
वा-स्वयम् आम् = refl
वा-स्वयम् न   = refl

-- यत् योगे न, तत् उभयत्र न ।  (what is absent from a join was absent from
-- both — the only direction this file needs.)
वा-न-वामे : (p q : उपस्थिति) → वा p q ≡ न → p ≡ न
वा-न-वामे न   _ _ = refl
वा-न-वामे आम् q e = e

वा-न-दक्षिणे : (p q : उपस्थिति) → वा p q ≡ न → q ≡ न
वा-न-दक्षिणे न   q e = e
वा-न-दक्षिणे आम् आम् e = e
वा-न-दक्षिणे आम् न   _ = refl

आम्≢न : ¬ (आम् ≡ न)
आम्≢न e = subst विवेकः e tt
  where
    विवेकः : उपस्थिति → Type
    विवेकः आम् = Unit
    विवेकः न   = ⊥

------------------------------------------------------------------------
-- २ · संयोगः — समावेशयोः योगः, अङ्गशः ।  (profiles joined componentwise.)
------------------------------------------------------------------------

संयोग : समावेश → समावेश → समावेश
संयोग (a₁ , n₁ , v₁) (a₂ , n₂ , v₂) = वा a₁ a₂ , वा n₁ n₂ , वा v₁ v₂

संयोग-सङ्गतिः : (s t u : समावेश)
              → संयोग (संयोग s t) u ≡ संयोग s (संयोग t u)
संयोग-सङ्गतिः (a₁ , n₁ , v₁) (a₂ , n₂ , v₂) (a₃ , n₃ , v₃) i =
  वा-सङ्गतिः a₁ a₂ a₃ i , वा-सङ्गतिः n₁ n₂ n₃ i , वा-सङ्गतिः v₁ v₂ v₃ i

संयोग-विनिमयः : (s t : समावेश) → संयोग s t ≡ संयोग t s
संयोग-विनिमयः (a₁ , n₁ , v₁) (a₂ , n₂ , v₂) i =
  वा-विनिमयः a₁ a₂ i , वा-विनिमयः n₁ n₂ i , वा-विनिमयः v₁ v₂ i

संयोग-स्वयम् : (s : समावेश) → संयोग s s ≡ s
संयोग-स्वयम् (a , n₀ , v) i = वा-स्वयम् a i , वा-स्वयम् n₀ i , वा-स्वयम् v i

------------------------------------------------------------------------
-- ३ · अरिक्तः — यः समावेशः कञ्चित् मूलं धारयति ।
--
-- अष्टमः समावेशः (न,न,न) न भङ्गः — अ-प्रतिपादनम् ।  तत् न मौनं, न अज्ञातम्,
-- न असत्यम् : तत्र प्रतिपादनम् एव नास्ति ।  तस्मात् प्रमाण-वस्तु न भवति ।
--
-- (The eighth profile is NOT a verdict: nothing is predicated at all.  It
-- is carried as a data predicate rather than as a decidable test, so a
-- function may not receive a bhaga without also receiving the evidence
-- that something was said.)
------------------------------------------------------------------------

-- अरिक्तम् — प्रतिपादनस्य साक्षी, न बूलियन् ।  (a Type-valued predicate: the
-- empty profile gets ⊥, every other gets Unit.  Function rather than data so
-- nothing in this file relies on indexed pattern matching, which cubical
-- Agda cannot compute through transports.)
अरिक्त : समावेश → Type
अरिक्त (न , न , न) = ⊥
अरिक्त _           = Unit

अरिक्तम् : (b : सप्तभङ्गी) → अरिक्त (अन्तर्भाव b)
अरिक्तम् स्यात्-अस्ति                    = tt
अरिक्तम् स्यात्-नास्ति                   = tt
अरिक्तम् स्यात्-अस्ति-नास्ति            = tt
अरिक्तम् स्यात्-अवक्तव्यम्               = tt
अरिक्तम् स्यात्-अस्ति-अवक्तव्यम्        = tt
अरिक्तम् स्यात्-नास्ति-अवक्तव्यम्       = tt
अरिक्तम् स्यात्-अस्ति-नास्ति-अवक्तव्यम् = tt

-- यत् उक्तं तत् योगे अपि उक्तम् ।  (a join of something with anything still
-- says something: the non-empty profiles are closed under संयोग.)
संयोग-अरिक्तम् : (s t : समावेश) → अरिक्त s → अरिक्त (संयोग s t)
संयोग-अरिक्तम् (आम् , _ , _) _               _ = tt
संयोग-अरिक्तम् (न , आम् , _) (आम् , _ , _)   _ = tt
संयोग-अरिक्तम् (न , आम् , _) (न   , _ , _)   _ = tt
संयोग-अरिक्तम् (न , न , आम्) (आम् , _   , _) _ = tt
संयोग-अरिक्तम् (न , न , आम्) (न   , आम् , _) _ = tt
संयोग-अरिक्तम् (न , न , आम्) (न   , न   , _) _ = tt
संयोग-अरिक्तम् (न , न , न)   _               e = rec e

-- प्रत्यागमः — अरिक्तः समावेशः भङ्गात् पुनः लभ्यते ।  (a non-empty profile is
-- recovered from the bhaṅga it names.  `Saptabhangi.प्रति-वृत्तम्` says the
-- same with a ¬-hypothesis; this takes the positive evidence instead,
-- because that is what the algebra below can actually produce.)
प्रत्यागमः : (t : समावेश) → अरिक्त t → अन्तर्भाव (प्रत्यन्तर्भाव t) ≡ t
प्रत्यागमः (आम् , आम् , आम्) _ = refl
प्रत्यागमः (आम् , आम् , न)   _ = refl
प्रत्यागमः (आम् , न   , आम्) _ = refl
प्रत्यागमः (आम् , न   , न)   _ = refl
प्रत्यागमः (न , आम् , आम्)   _ = refl
प्रत्यागमः (न , आम् , न)     _ = refl
प्रत्यागमः (न , न , आम्)     _ = refl
प्रत्यागमः (न , न , न)       e = rec e

------------------------------------------------------------------------
-- ४ · क्रम-योगः — क्रमार्पणे द्वौ भङ्गौ एकं जनयतः ।
--
-- क्रमेण उक्तयोः किमपि न नश्यति : यत् एकत्र उक्तं तत् योगे अपि उक्तम् ।
-- अतः क्रम-योगः समावेश-संयोगः एव — संक्रमणम्, न सङ्क्षेपः ।
--
-- (Succession loses nothing: what either said, the pair still says.  So
-- order-composition IS the profile join — transport, not collapse.
-- AHIMSA_SUTRA_VISTARA §6: this is the ua path, and it is why this
-- operation gets to be a semilattice at all.)
------------------------------------------------------------------------

क्रम-योग : सप्तभङ्गी → सप्तभङ्गी → सप्तभङ्गी
क्रम-योग x y = प्रत्यन्तर्भाव (संयोग (अन्तर्भाव x) (अन्तर्भाव y))

क्रम-अन्तर्भावः : (x y : सप्तभङ्गी)
                → अन्तर्भाव (क्रम-योग x y) ≡ संयोग (अन्तर्भाव x) (अन्तर्भाव y)
क्रम-अन्तर्भावः x y =
  प्रत्यागमः (संयोग (अन्तर्भाव x) (अन्तर्भाव y))
             (संयोग-अरिक्तम् (अन्तर्भाव x) (अन्तर्भाव y) (अरिक्तम् x))

क्रम-सङ्गतिः : (x y z : सप्तभङ्गी)
             → क्रम-योग (क्रम-योग x y) z ≡ क्रम-योग x (क्रम-योग y z)
क्रम-सङ्गतिः x y z =
    cong (λ t → प्रत्यन्तर्भाव (संयोग t (अन्तर्भाव z))) (क्रम-अन्तर्भावः x y)
  ∙ cong प्रत्यन्तर्भाव (संयोग-सङ्गतिः (अन्तर्भाव x) (अन्तर्भाव y) (अन्तर्भाव z))
  ∙ cong (λ t → प्रत्यन्तर्भाव (संयोग (अन्तर्भाव x) t)) (sym (क्रम-अन्तर्भावः y z))

क्रम-विनिमयः : (x y : सप्तभङ्गी) → क्रम-योग x y ≡ क्रम-योग y x
क्रम-विनिमयः x y = cong प्रत्यन्तर्भाव (संयोग-विनिमयः (अन्तर्भाव x) (अन्तर्भाव y))

क्रम-स्वयम् : (x : सप्तभङ्गी) → क्रम-योग x x ≡ x
क्रम-स्वयम् x = cong प्रत्यन्तर्भाव (संयोग-स्वयम् (अन्तर्भाव x)) ∙ वृत्तम् x

------------------------------------------------------------------------
-- ५ · सह-योगः — सहार्पणे जिह्वा भिद्यते ।
--
-- यदि योगे अस्ति च नास्ति च उभे उपस्थिते, तर्हि सह-उक्तिः न शक्या : उभे मूले
-- अवक्तव्ये लीयेते ।  एतत् एव अकलङ्कस्य सहार्पणम् ।  न "उभयम्" — अन्यत् पदम् ।
--
-- (If the join has both asti and nsti present, no single utterance carries
-- it: the two seeds are consumed into avaktavya.  This is Akalaka's
-- saharpaṇa.  Note what the definition does — it DESTROYS the two seed
-- markings, and
-- it is not a modelling artefact: it is the doctrine's claim that the
-- fourth position is not a record of which two things were said at once.)
------------------------------------------------------------------------

जिह्वाभेदः : समावेश → समावेश
जिह्वाभेदः (आम् , आम् , _) = न , न , आम्
जिह्वाभेदः t               = t

जिह्वाभेद-अरिक्तम् : (t : समावेश) → अरिक्त t → अरिक्त (जिह्वाभेदः t)
जिह्वाभेद-अरिक्तम् (आम् , आम् , _) _ = tt
जिह्वाभेद-अरिक्तम् (आम् , न   , _) _ = tt
जिह्वाभेद-अरिक्तम् (न   , आम् , _) _ = tt
जिह्वाभेद-अरिक्तम् (न   , न , आम्) _ = tt
जिह्वाभेद-अरिक्तम् (न   , न , न)   e = rec e

सह-योग : सप्तभङ्गी → सप्तभङ्गी → सप्तभङ्गी
सह-योग x y = प्रत्यन्तर्भाव (जिह्वाभेदः (संयोग (अन्तर्भाव x) (अन्तर्भाव y)))

-- मुख्यभेदः, गणनया : क्रमेण उभयम् उक्तम् ; सह उभयम् अवक्तव्यम् ।
क्रमेण-उभयम् : क्रम-योग स्यात्-अस्ति स्यात्-नास्ति ≡ स्यात्-अस्ति-नास्ति
क्रमेण-उभयम् = refl

सह-उभयम् : सह-योग स्यात्-अस्ति स्यात्-नास्ति ≡ स्यात्-अवक्तव्यम्
सह-उभयम् = refl

-- पञ्चमः षष्ठश्च भङ्गौ सह-योगेन एव जायेते — शास्त्रस्य सङ्ख्या, गणनया ।
पञ्चमः : सह-योग स्यात्-अस्ति स्यात्-अवक्तव्यम् ≡ स्यात्-अस्ति-अवक्तव्यम्
पञ्चमः = refl

षष्ठः : सह-योग स्यात्-नास्ति स्यात्-अवक्तव्यम् ≡ स्यात्-नास्ति-अवक्तव्यम्
षष्ठः = refl

सप्तमः : क्रम-योग स्यात्-अस्ति-नास्ति स्यात्-अवक्तव्यम्
       ≡ स्यात्-अस्ति-नास्ति-अवक्तव्यम्
सप्तमः = refl

------------------------------------------------------------------------
-- ६ · अवक्तव्यम् न क्रमजम् — चतुर्थं पदं धनात्मकम् ।
--
-- अस्ति-नास्त्योः क्रम-संवृतिः त्रीणि एव पदानि स्पृशति ।  अवक्तव्यं तत्र न
-- अस्ति — न न्यूनतया, न अज्ञानेन : क्रम-योगः तत् जनयितुम् एव न शक्नोति ।
-- अतः अवक्तव्यं दातव्यम्, न साध्यम् — तस्मात् धनात्मकं चतुर्थं स्थानम् ।
--
-- (The order-closure of asti and nsti touches exactly three positions.
-- avaktavya is not among them — not by ignorance and not by undefinedness:
-- the operation cannot produce it.  So the fourth position must be
-- SUPPLIED.  That is the precise sense in which it is positive and not an
-- absence, and it is why a verdict type with three positions plus "other"
-- is not this type.)
------------------------------------------------------------------------

अवक्तव्यांशः : सप्तभङ्गी → उपस्थिति
अवक्तव्यांशः b = snd (snd (अन्तर्भाव b))

नास्त्यंशः : सप्तभङ्गी → उपस्थिति
नास्त्यंशः b = fst (snd (अन्तर्भाव b))

अस्त्यंशः : सप्तभङ्गी → उपस्थिति
अस्त्यंशः b = fst (अन्तर्भाव b)

क्रम-अवक्तव्यांशः : (x y : सप्तभङ्गी)
                   → अवक्तव्यांशः (क्रम-योग x y)
                   ≡ वा (अवक्तव्यांशः x) (अवक्तव्यांशः y)
क्रम-अवक्तव्यांशः x y = cong (λ t → snd (snd t)) (क्रम-अन्तर्भावः x y)

अवक्तव्यम्-न-क्रमजम् : (x y : सप्तभङ्गी)
                     → अवक्तव्यांशः x ≡ न → अवक्तव्यांशः y ≡ न
                     → ¬ (क्रम-योग x y ≡ स्यात्-अवक्तव्यम्)
अवक्तव्यम्-न-क्रमजम् x y px py e = आम्≢न
  ( sym (cong अवक्तव्यांशः e)
  ∙ क्रम-अवक्तव्यांशः x y
  ∙ cong₂ वा px py )

-- ये त्रयः भङ्गाः अवक्तव्यांशरहिताः — तेषाम् एव क्रम-संवृतिः ।
-- (the three avaktavya-free positions, named, so the theorem above is
--  known to be about exactly the sequential fragment and not vacuous)
अवक्तव्य-रहिताः : (अवक्तव्यांशः स्यात्-अस्ति ≡ न)
                × (अवक्तव्यांशः स्यात्-नास्ति ≡ न)
                × (अवक्तव्यांशः स्यात्-अस्ति-नास्ति ≡ न)
अवक्तव्य-रहिताः = refl , refl , refl

अवक्तव्यस्य-अंशः : अवक्तव्यांशः स्यात्-अवक्तव्यम् ≡ आम्
अवक्तव्यस्य-अंशः = refl

------------------------------------------------------------------------
-- ७ · सह-असङ्गतिः — सहार्पणं न सङ्गतम् ।
--
-- (सह B3 B1) सह B2 = षष्ठः ;  B3 सह (सह B1 B2) = चतुर्थः ।
-- कारणम् : जिह्वाभेदः द्वे मूले नाशयति, अतः "के द्वे आस्ताम्" इति न वहति ।
-- सङ्क्षेपोऽप्रतिकार्यः (AHIMSA_SUTRA_VISTARA §५) — अत्र स एव नियमभङ्गः ।
--
-- तस्मात् सप्तभङ्गी सह-योगेन जालिका (lattice) न भवति, न अर्ध-जालिका अपि ।
-- द्वौ नियमौ न एकीभवतः — यः तौ एकीकर्तुं यतते स सङ्क्षिपति ।
--
-- (Simultaneity does not associate: saha tests the JOINED position for an
-- asti-nasti pair, and whether that pair is present depends on the
-- grouping.  This is why the two composition laws cannot be merged into
-- one operation.)
------------------------------------------------------------------------

private
  वामतः : सप्तभङ्गी
  वामतः = सह-योग (सह-योग स्यात्-अस्ति-नास्ति स्यात्-अस्ति) स्यात्-नास्ति

  दक्षिणतः : सप्तभङ्गी
  दक्षिणतः = सह-योग स्यात्-अस्ति-नास्ति (सह-योग स्यात्-अस्ति स्यात्-नास्ति)

वामतः-षष्ठः : वामतः ≡ स्यात्-नास्ति-अवक्तव्यम्
वामतः-षष्ठः = refl

दक्षिणतः-चतुर्थः : दक्षिणतः ≡ स्यात्-अवक्तव्यम्
दक्षिणतः-चतुर्थः = refl

सह-असङ्गतिः : ¬ (वामतः ≡ दक्षिणतः)
सह-असङ्गतिः e = आम्≢न (cong नास्त्यंशः e)

-- सह-योगः विनिमयी तथापि — असङ्गतिः न अव्यवस्था ।
सह-विनिमयः : (x y : सप्तभङ्गी) → सह-योग x y ≡ सह-योग y x
सह-विनिमयः x y =
  cong (λ t → प्रत्यन्तर्भाव (जिह्वाभेदः t))
       (संयोग-विनिमयः (अन्तर्भाव x) (अन्तर्भाव y))

------------------------------------------------------------------------
-- ८ · मेलनं नास्ति — अस्ति-नास्त्योः अधःसीमा न विद्यते ।
--
-- क्रम-योगः ऊर्ध्वसीमां ददाति (अर्ध-जालिका, शिखरं सप्तमः) ।  अधःसीमा तु
-- नास्ति : यः भङ्गः अस्तितः च नास्तितः च न्यूनः स्यात्, तस्य समावेशः रिक्तः
-- भवेत् — स च अ-प्रतिपादनम्, न भङ्गः ।
--
-- न वर्जितम् । न अनुचितम् । न विद्यते ।  (AHIMSA_SUTRA_VISTARA §७)
--
-- (order gives joins — a semilattice with top B7 — and NO meets.  A lower
-- bound of asti and nsti would have the empty profile, and the empty
-- profile is not a verdict but the absence of predication.  So the sevenfold
-- is a join-subsemilattice of 2³ that is not closed under meet, and what it
-- fails to contain is the collapse.  A Boolean verdict has a bottom; that
-- bottom is precisely the thing this type refuses to supply.)
------------------------------------------------------------------------

_न्यूनः_ : सप्तभङ्गी → सप्तभङ्गी → Type
x न्यूनः y = क्रम-योग x y ≡ y

क्रम-ऊर्ध्वसीमा : (x y : सप्तभङ्गी) → (x न्यूनः क्रम-योग x y)
                × (y न्यूनः क्रम-योग x y)
क्रम-ऊर्ध्वसीमा x y =
    sym (क्रम-सङ्गतिः x x y) ∙ cong (λ t → क्रम-योग t y) (क्रम-स्वयम् x)
  , sym (क्रम-सङ्गतिः y x y) ∙ cong (λ t → क्रम-योग t y) (क्रम-विनिमयः y x)
                          ∙ क्रम-सङ्गतिः x y y
                          ∙ cong (क्रम-योग x) (क्रम-स्वयम् y)

शिखरम् : (x : सप्तभङ्गी) → x न्यूनः स्यात्-अस्ति-नास्ति-अवक्तव्यम्
शिखरम् स्यात्-अस्ति                    = refl
शिखरम् स्यात्-नास्ति                   = refl
शिखरम् स्यात्-अस्ति-नास्ति            = refl
शिखरम् स्यात्-अवक्तव्यम्               = refl
शिखरम् स्यात्-अस्ति-अवक्तव्यम्        = refl
शिखरम् स्यात्-नास्ति-अवक्तव्यम्       = refl
शिखरम् स्यात्-अस्ति-नास्ति-अवक्तव्यम् = refl

-- यः रिक्तं समावेशं धारयेत् स भङ्गः नास्ति ।
रिक्तो-न-भङ्गः : (b : सप्तभङ्गी) → ¬ (अन्तर्भाव b ≡ (न , न , न))
रिक्तो-न-भङ्गः b e = subst अरिक्त e (अरिक्तम् b)

मेलनम्-नास्ति : ¬ (Σ सप्तभङ्गी
                   (λ b → (b न्यूनः स्यात्-अस्ति) × (b न्यूनः स्यात्-नास्ति)))
मेलनम्-नास्ति (b , p , q) = रिक्तो-न-भङ्गः b रिक्तः
  where
    -- from b ≤ asti: b's nāsti and avaktavya slots are empty
    सीमा₁ : संयोग (अन्तर्भाव b) (आम् , न , न) ≡ (आम् , न , न)
    सीमा₁ = sym (क्रम-अन्तर्भावः b स्यात्-अस्ति) ∙ cong अन्तर्भाव p
    -- from b ≤ nāsti: b's asti slot is empty
    सीमा₂ : संयोग (अन्तर्भाव b) (न , आम् , न) ≡ (न , आम् , न)
    सीमा₂ = sym (क्रम-अन्तर्भावः b स्यात्-नास्ति) ∙ cong अन्तर्भाव q

    अ० : fst (अन्तर्भाव b) ≡ न
    अ० = वा-न-वामे (fst (अन्तर्भाव b)) न (cong fst सीमा₂)

    न० : fst (snd (अन्तर्भाव b)) ≡ न
    न० = वा-न-वामे (fst (snd (अन्तर्भाव b))) न (cong (λ t → fst (snd t)) सीमा₁)

    व० : snd (snd (अन्तर्भाव b)) ≡ न
    व० = वा-न-वामे (snd (snd (अन्तर्भाव b))) न (cong (λ t → snd (snd t)) सीमा₁)

    रिक्तः : अन्तर्भाव b ≡ (न , न , न)
    रिक्तः i = अ० i , न० i , व० i

------------------------------------------------------------------------
-- ९ · यत् एतत् वदति, यन्त्रे ।
--
-- machine/Saptabhangi_TheSevenfoldVerdict.hs (absent from this repository) एतान् एव नियमान् वहति, तत्रैव
-- स्रोतांसि लिखित्वा ।  तत्र `order`, `saha`, `Sthana` — अत्रत्यानि नामानि ।।
-- यत् तत्र न अस्ति : मेलनम् ।  यतो न विद्यते — तत् एव अत्र प्रमाणितम् ।
--
-- (machine/Saptabhangi_TheSevenfoldVerdict.hs (absent from this repository) carries these same laws.
-- What it does not carry is a meet, because there is not one — that is the
-- theorem above, and it is the reason the Haskell type exposes no `bottom`,
-- no `mempty`, and no `Ord`.)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- १० · नयभेदः — भ्रातृ-प्रकारेण सह विवादः, लिखितः, न परिहृतः ।
--
-- formal/cubical/NaturalMachine/SaptabhangiKernel_ ( , 
-- दिने) भङ्गान् सनयान् करोति — चतुर्थं पदं स्वे मूले धारयति, अतः तत्र
-- जिह्वाभेदो न नाशयति, क्रमश्च न विनिमयी ।  अत्र भङ्गो नाममात्रम्, अतः
-- क्रमो विनिमयी, सहश्च नाशयति ।
--
-- द्वे अपि प्रमाणिते ।  द्वे न एकं वस्तु ।  मल्लिषेणस्य पाठे प्रश्नः —
-- अवक्तव्यं वचन-असामर्थ्यमात्रं वा वाच्यस्य ग्रासः — स च न अत्र निर्णीतः ।
--
-- नयभेदे सङ्क्षेपो न विद्यते (AHIMSA_SUTRA_VISTARA §७) ।  यत् शिष्यते तत्
-- तुलनम् : विस्मरण-प्रतिचित्रणं क्रमे साधकं वा, सहे वा, न वा — तत् न परीक्षितम्,
-- अतः न दावः ।
--
-- (A sibling type carries the nayas inside each position, so its fourth
-- position destroys nothing and its order is not commutative.  Here a
-- position is a label, so order commutes and saha destroys.  Both are
-- checked; they are not the same object; the reading of Mallisena that
-- separates them is unsettled.)
------------------------------------------------------------------------

------------------------------------------------------------------------
--     — the comparison with the record lane.
--
-- Whether the forgetful map from records to labels is a homomorphism
-- for order, for saha, or for neither is checked in
--
--   Arpitanarpita_TheForgetfulMapIsAHomomorphismForBothArpanasAndThe
--     LabelsAreARetractNotAnEquivalence.agda (absent from this repository)
--
-- and the answer is BOTH, exhaustively, 49 cases each, for every S and
-- every P.  Further: the map has a SECTION (अर्पणम्, Tattvārthasūtra 5.31's
-- अर्पित to this file's अनर्पित) which is a homomorphism for both modes,
-- with अनर्पणम् ∘ अर्पणम् ≡ id — so this lane's seven are a subalgebra AND a
-- quotient of the record lane's, i.e. a RETRACT of it — and it has NO
-- inverse (`न-प्रत्यानयनम्`), so no equivalence exists and §६ path one is
-- unavailable as a theorem.
--
-- The tradition's question is untouched by the composition laws: whether
-- अवक्तव्यम् is failure of expression only or consumption of what was to be
-- expressed (Malliea, Sydvdamajar, 1292).  That question is
-- undecidable BY THE COMPOSITION LAWS — the two lanes agree
-- across it — so any argument for a reading that runs through order or
-- saha proves nothing.  It is a question about what a position is.
------------------------------------------------------------------------
