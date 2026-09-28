{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- मूलवाक्यम् · PROVENANCE OF THE NAME, AND A WARNING ABOUT IT.
--
-- **The mathematics in this module originates in cubical type theory, not in
-- an Indian source, and the name should not be read as claiming otherwise.**
-- `transport`, `ua` and `uaβ` are Voevodsky's univalence as realised in
-- cubical type theory — the substrate this repository is checked in, and the
-- one exception CLAUDE.md (absent from this repository) grants ("all respects paid to Indians only, plus
-- Voevodsky").  Nothing below is a theorem of any  text.
--
-- संक्रमण · saṃṃorder IS a technical term, and it does not mean this.  In
-- Jaina karma theory it is the transition of one karma-prakti into another
-- — *Ṣaṭkhaṇḍāgama* with Vīrasena's *Dhavalā* (~816 CE); Śivaśarmasūri,
-- *Karmaprakti*.  In jyotia, sakrnti is the sun's passage into a sign.
-- **Neither is what this module proves**, and welding the Jaina term onto a
-- path-transport would be the error CLAUDE.md (absent from this repository)'s second naming condition
-- names: "a fabricated term is the mirror image of the scrubbing this rule
-- corrects: it asserts a provenance nobody checked."
--
-- What the name legitimately carries is the READING, from
-- नश्यति — which is this repository's own gloss of two paths and no third,
-- and which is what the module makes precise.  A reading is not a citation.
--
------------------------------------------------------------------------
-- संक्रमणम् — transport as the machine's ONLY identification primitive.
--
-- अहिंसा-सूत्र-विस्तारः § ६ (द्वौ मार्गौ) एतत् वदति :
--     संक्रमणे संरचना वहति । संक्रमणे न किञ्चिन् नश्यति ।
--     अन्यो मार्गो दोषलेखः । तृतीयो मार्गो न विद्यते ।
-- तत्र संक्रमणम् उक्तम्, न साधितम् ।  अत्र साध्यते ।
--
-- (The stra states, in §6, that in transport the structure is carried and
-- nothing perishes; that the only other move is to WRITE THE DEFECT; and
-- that there is no third road.  §6 wrote down `संक्रमणम् e = transport (ua e)`
-- and `अलोपः = uaβ` and stopped there.  Those two lines are the DEFINITION
-- and its COMPUTATION RULE.  Neither of them is the claim.  This module
-- proves the claim.)
--
-- WHAT WAS ACTUALLY MISSING, and why the gap was invisible
--
-- `uaβ e a : transport (ua e) a ≡ equivFun e a` says that transporting a
-- POINT computes.  It says nothing whatever about STRUCTURE — about what
-- happens to an operation, a predicate, a law, when it is carried across.
-- A reader who has `uaβ` in hand and reads "संक्रमणे संरचना वहति" will believe
-- the sentence is discharged.  It is not: uaβ is a statement about
-- elements of A, and "the structure is carried" is a statement about
-- elements of S A for arbitrary S.  The gap is one quantifier wide and it
-- is exactly the gap between a definition and a theorem.
--
-- WHAT IS PROVED HERE
--
--  १ · संक्रमणम् is an equivalence, and the return trip is exhibited.
--       Not "invertible in principle": the inverse is a term, and
--       प्रत्यानयनम् computes the round trip to `refl`-level identity.
--
--  २ · संरचना वहति — THE THEOREM.  For an operation of any arity, the
--       carried operation is the conjugate, and `e` is a HOMOMORPHISM for
--       it.  For a predicate, the carried predicate at `e a` is `P a`.
--       This is what "nothing is lost" means when said about structure
--       rather than about points, and it is the form the machine cites:
--       an identification licenses moving the WHOLE object, laws included.
--
--  ३ · The contrast with ∥_∥₁, as ONE statement rather than two.
--       ∣_∣₁ IS an identification — is a संक्रमणम् — EXACTLY WHEN `A` is a
--       proposition, i.e. exactly when there was nothing to lose.  So
--       transport and truncation are not two unrelated moves: truncation
--       is what transport degenerates to at the one h-level where the
--       question "which?" has no answer to destroy.  Everywhere else
--       (¬ isProp A) the retraction does not merely fail to be found —
--       it does not exist.
--
--       Asked as `isEquiv ∣_∣₁`, NOT as `hasRetract ∣_∣₁`.  The retraction
--       form, at every h-level n and with the retraction type shown
--       contractible, is another lane's and is strictly stronger:
--       `Apratikaryatva_TheRetractionTypeIsTheHLevelHypothesis.agda`.
--       My first draft of §3 proved the n = 1 retraction case; on finding
--       theirs I CUT MINE rather than ship a weaker twin, and §3 below
--       records the cut.  `SetTruncationDescentBoundary.agda` is the
--       ∥_∥₂/isSet member of the same family.  Three lanes, one fact,
--       indexed by h-level.
--
--  ४ · अतृतीयः — there is no third road, in the one form that is a
--       theorem rather than a syntactic remark about a datatype: ANY map
--       that is lossless in both directions IS a transport, and its
--       equivalence is produced AS DATA.  So a lossless move cannot
--       decline to exhibit its identification; if it is lossless the
--       identification is recoverable from it, constructively.
--       The machine cites this one to justify demanding evidence: the
--       demand costs the caller nothing it did not already have.
--
-- स्रोतांसि :
--   उमास्वाति, तत्त्वार्थसूत्र ७.८ / ७.१३ (c. 2nd–5th c. CE) — प्रमत्तयोगात्
--     प्राणव्यपरोपणं हिंसा ; परस्परोपग्रहो जीवानाम् ।  हिंसा is analysed there as
--     an act on a जीव, and the सूत्र-विस्तार's move is to read सङ्क्षेप — the
--     collapse of many determinations into one — as that act.  The reading
--     is the सूत्र-विस्तार's; the सूत्र is Umāsvāti's.
--   सिद्धसेन दिवाकर, सन्मतितर्क (c. 5th c. CE) — नयवाद : a नय which asserts
--     itself whole becomes दुर्नय.  This is the reason the DEFECT LOG is a
--     legitimate move and silence is not.
--   Vladimir Voevodsky, univalence (2009–2013); `ua`, `uaβ`, `uaη`,
--     `transportUAop₁/₂` as in agda/cubical v0.9 — CITED, NOT RE-DERIVED.
--     The corpus rule is that re-deriving what the library has is the
--     failure mode; every library lemma used below is used by name.
--   Nasti_ShabdeJivahVartante.agda — §४, §५, §६ of the सूत्र-विस्तार.
--   Apratikaryatva_TheRetractionTypeIsTheHLevelHypothesis.agda and
--     SetTruncationDescentBoundary.agda — the retraction-form and the
--     ∥_∥₂/isSet members of the family §3 belongs to.  Concurrent lanes,
--     read before §3 was cut down; see §3.
--   machine/Uttara_SamordernaOrDosalekhaNeverABareBoolean.hs (absent from this repository) — the
--     operational lane, another agent's, which §5 is the Agda side of.
------------------------------------------------------------------------

module Samkramana_TransportCarriesStructureAndTruncationIsTransportExactlyWhenNothingWasThereToLose where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using (_≃_ ; equivFun ; invEq ; retEq ; secEq ; invEquiv ; isEquiv
        ; isPropIsEquiv)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Univalence
  using (ua ; uaβ ; ua→ ; isEquivTransport ; transportUAop₁ ; transportUAop₂)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁ ; ∣_∣₁ ; squash₁ ; rec)
open import Cubical.Relation.Nullary using (¬_)

open import Nasti_ShabdeJivahVartante
  using (संक्रमणम् ; संक्रमणम्-अलोपः)

private variable
  ℓ ℓ′ : Level
  A B : Type ℓ

------------------------------------------------------------------------
-- १ · प्रत्यानयनम् — the return.  न किञ्चिन् नश्यति, साधितम् ।
--
-- संक्रमणम् is an equivalence for EVERY e, with no hypothesis on A or B,
-- and the round trip is a term one can run, not an existence claim.
------------------------------------------------------------------------

-- संक्रमणम् is an equivalence.  (isEquivTransport, cited.)
संक्रमणम्-तुल्यता : (e : A ≃ B) → isEquiv (संक्रमणम् e)
संक्रमणम्-तुल्यता e = isEquivTransport (ua e)

-- The return trip, forwards then back, is the identity — pointwise,
-- computed through uaβ at both steps.
प्रत्यानयनम् : (e : A ≃ B) (a : A) → संक्रमणम् (invEquiv e) (संक्रमणम् e a) ≡ a
प्रत्यानयनम् e a =
    संक्रमणम्-अलोपः (invEquiv e) (संक्रमणम् e a)
  ∙ cong (invEq e) (संक्रमणम्-अलोपः e a)
  ∙ retEq e a

-- …and back then forwards.  Both sides, because a retraction alone is
-- half of losslessness and the सूत्र claims the whole of it.
प्रत्यानयनम्′ : (e : A ≃ B) (b : B) → संक्रमणम् e (संक्रमणम् (invEquiv e) b) ≡ b
प्रत्यानयनम्′ e b =
    संक्रमणम्-अलोपः e (संक्रमणम् (invEquiv e) b)
  ∙ cong (equivFun e) (संक्रमणम्-अलोपः (invEquiv e) b)
  ∙ secEq e b

-- The form the machine cites: every संक्रमणम् comes with its retraction,
-- as data, unconditionally.  Compare नास्ति-प्रत्यानयनम् in §५.
संक्रमणम्-सप्रत्यानयनम्
  : (e : A ≃ B) → Σ[ g ∈ (B → A) ] ((a : A) → g (संक्रमणम् e a) ≡ a)
संक्रमणम्-सप्रत्यानयनम् e = संक्रमणम् (invEquiv e) , प्रत्यानयनम् e

------------------------------------------------------------------------
-- २ · संरचना वहति — the structure is carried.
--
-- वहनम् S e carries an S-structure across the identification.  The
-- theorems below say WHAT it carries it to: the conjugate, with `e` a
-- homomorphism.  That is the whole content of "nothing is lost", said
-- about structure instead of about points.
------------------------------------------------------------------------

वहनम् : (S : Type ℓ → Type ℓ′) (e : A ≃ B) → S A → S B
वहनम् S e = subst S (ua e)

-- Unary operations.  e is a homomorphism from (A, f) to (B, वहनम् f).
संरचना-वहति₁
  : (e : A ≃ B) (f : A → A) (a : A)
  → equivFun e (f a) ≡ वहनम् (λ X → X → X) e f (equivFun e a)
संरचना-वहति₁ e f a =
  sym ( transportUAop₁ e f (equivFun e a)
      ∙ cong (λ x → equivFun e (f x)) (retEq e a) )

-- Binary operations — the composition-law case, which is the one the
-- machine actually meets (a vocabulary carries an operation, and an
-- identification of vocabularies must carry the operation with it).
संरचना-वहति₂
  : {A B : Type ℓ} (e : A ≃ B) (op : A → A → A) (a a′ : A)
  → equivFun e (op a a′)
    ≡ वहनम् (λ X → X → X → X) e op (equivFun e a) (equivFun e a′)
संरचना-वहति₂ e op a a′ =
  sym ( transportUAop₂ e op (equivFun e a) (equivFun e a′)
      ∙ cong₂ (λ x y → equivFun e (op x y)) (retEq e a) (retEq e a′) )

-- Predicates.  A property of A becomes a property of B, and it is the
-- SAME property: reading the carried predicate at `e a` returns `P a`
-- on the nose (up to a path that is itself exhibited).
--
-- This is the case the machine needs most and the one uaβ says least
-- about: "these two objects are identified" must license transferring
-- every PROPERTY, not merely relabelling points.
धर्म-वहति
  : (e : A ≃ B) (P : A → Type ℓ′)
  → PathP (λ i → ua e i → Type ℓ′) P (λ b → P (invEq e b))
धर्म-वहति e P = ua→ (λ a → cong P (sym (retEq e a)))

धर्म-अलोपः
  : (e : A ≃ B) (P : A → Type ℓ′) (a : A)
  → transport (λ i → ua e i → Type ℓ′) P (equivFun e a) ≡ P a
धर्म-अलोपः e P a =
    funExt⁻ (fromPathP (धर्म-वहति e P)) (equivFun e a)
  ∙ cong P (retEq e a)

------------------------------------------------------------------------
-- ३ · नष्टिः — the other side, and it is the same statement.
--
-- ┌──────────────────────────────────────────────────────────────────┐
-- │ DUPLICATION FOUND AND CUT, 2026-08-20, same day, same repository.│
-- └──────────────────────────────────────────────────────────────────┘
--
-- This section as first written defined `प्रत्यानयन₁ A` (the type of ways
-- back from ∥ A ∥₁), proved `प्रत्यानयन₁ A → isProp A` and its converse,
-- and derived "no retraction where there is a difference".  All of that
-- is SUBSUMED — and at strictly greater generality — by
--
--     Apratikaryatva_TheRetractionTypeIsTheHLevelHypothesis.agda §3–§4
--
-- written concurrently in another lane, which proves
-- `प्रत्यानयनम् n A ≃ isOfHLevel n A` for EVERY h-level n, shows the
-- retraction type is CONTRACTIBLE when A is an n-type (so nothing is
-- chosen), and recovers the stra's Bool statement as a corollary.  n = 1
-- is my case.  I deleted mine rather than keep a weaker twin: the corpus
-- names re-derivation as its most frequent failure, and a second proof of
-- a special case is that failure even when both are green.
--
-- WHAT IS KEPT is the one statement of the pair that is NOT theirs, and
-- it is not theirs because it is asked in the transport lane's vocabulary
-- rather than the retraction lane's:
--
--     they ask  — does ∣_∣₁ have a way BACK?          (hasRetract)
--     this asks — is ∣_∣₁ ITSELF a संक्रमणम्?           (isEquiv)
--
-- These are different questions with the same answer, and having both
-- answers is the point: it says the transport/truncation contrast is not
-- an opposition between two moves at all.  ∣_∣₁ is a transport EXACTLY
-- when A is a proposition — so truncation is what transport degenerates
-- to at the one h-level where the question "which?" has no answer left to
-- destroy, and everywhere else it is the other road entirely.
--
-- SetTruncationDescentBoundary.agda is the ∥_∥₂ / isSet member of the
-- same family, written earlier by a third lane.  Three modules, one fact,
-- indexed by h-level; recorded here so a reader meets it as a family and
-- not as three coincidences.
------------------------------------------------------------------------

-- THE CONTRAST, as one biimplication.  ∣_∣₁ is an equivalence — that is,
-- the truncation move IS an identification, and so a संक्रमणम् via ua —
-- exactly when A is a proposition.
--
-- अवशेषो नास्ति यदा नष्टं किमपि नास्ति ।
तादात्म्यम्↔निर्धर्मता : isEquiv (∣_∣₁ {A = A}) → isProp A
तादात्म्यम्↔निर्धर्मता {A = A} ie x y =
    sym (retEq (∣_∣₁ , ie) x)
  ∙ cong (invEq (∣_∣₁ , ie)) (squash₁ ∣ x ∣₁ ∣ y ∣₁)
  ∙ retEq (∣_∣₁ , ie) y

निर्धर्मता↔तादात्म्यम् : isProp A → isEquiv (∣_∣₁ {A = A})
निर्धर्मता↔तादात्म्यम् {A = A} p =
  snd (isoToEquiv (iso ∣_∣₁ (rec p (λ a → a))
                       (λ t → squash₁ ∣ rec p (λ a → a) t ∣₁ t)
                       (λ _ → refl)))

-- Both sides are propositions, so the biimplication is an equivalence and
-- not merely a pair of maps: the two facts are literally one datum.
नष्टिः≃निर्धर्मता : (isEquiv (∣_∣₁ {A = A})) ≃ (isProp A)
नष्टिः≃निर्धर्मता {A = A} =
  isoToEquiv (iso तादात्म्यम्↔निर्धर्मता निर्धर्मता↔तादात्म्यम्
                  (λ q → isPropIsProp _ q)
                  (λ q → isPropIsEquiv ∣_∣₁ _ q))

-- The consequence, in the transport lane's own terms: where there IS a
-- difference, ∣_∣₁ is not an identification at all, so §६'s first road is
-- CLOSED and only the defect log remains.  नष्टिरप्रतिकार्या ।
-- (The corresponding statement about retractions is
--  Apratikaryatva…§4 `नास्ति-प्रत्यानयनम्-सामान्यम्`; not restated here.)
भेदे-न-संक्रमणम् : ¬ (isProp A) → ¬ (isEquiv (∣_∣₁ {A = A}))
भेदे-न-संक्रमणम् ¬p ie = ¬p (तादात्म्यम्↔निर्धर्मता ie)

------------------------------------------------------------------------
-- ४ · अतृतीयः — no third road, in its provable form.
--
-- The sūtra says तृतीयो मार्गो न विद्यते.  Read as a claim about datatypes
-- that is unprovable and uninteresting.  Read as a claim about LOSSLESS
-- moves it is a theorem: a map lossless in both directions cannot be
-- anything but a transport, and its identification is extracted from it
-- constructively.  So "exhibit your equivalence" is never an extra
-- burden — the caller who was lossless already had it.
--
-- THE OTHER HALF, and it is another lane's, written the same day:
--   TritiyaMarga_TheNoThirdPathClaimIsExcludedMiddle.agda (absent from this repository)
-- proves that the DISJUNCTIVE reading of तृतीयो मार्गो न विद्यते — every map
-- is either an identification or has a nameable defect — is exactly
-- excluded middle, i.e. classical, not constructive.
--
-- The two results are not in tension and the pair is worth more than
-- either.  Theirs bounds what the sentence can mean: you may not
-- CLASSIFY an arbitrary map into two roads without assuming LEM.  Mine
-- says what survives that bound: you never needed to classify.  A move
-- that IS lossless hands you its identification whether or not anyone can
-- decide, for an arbitrary move, which road it took.  So the machine's
-- discipline — "produce your equivalence or write your defect" — is
-- constructively legitimate as an OBLIGATION ON THE ACTOR, and would be
-- classical only if imposed as a VERDICT ON A STRANGER.
-- स्याद् अस्ति च नास्ति च : both, under different अर्पण.
------------------------------------------------------------------------

अतृतीयः
  : (f : A → B) (g : B → A)
  → (ret : (a : A) → g (f a) ≡ a)
  → (sec : (b : B) → f (g b) ≡ b)
  → Σ[ e ∈ A ≃ B ] ((a : A) → संक्रमणम् e a ≡ f a)
अतृतीयः f g ret sec =
    isoToEquiv (iso f g sec ret)
  , λ a → संक्रमणम्-अलोपः (isoToEquiv (iso f g sec ret)) a

------------------------------------------------------------------------
-- ५ · गति — the machine's move, as a type.
--
-- Two constructors.  This is a datatype declaration, NOT a theorem that
-- the world has two moves; see "SYĀT — THE CLAIM, EXACTLY" above.  What it buys
-- is that a move cannot be performed without producing one of two things:
-- an equivalence, or a written defect.  Silence is not a constructor.
--
-- दोषलेख carries the map AND the proof that it is not an identification.
-- लिखितो दोषो जीवति । अलिखितो दोषो हिंसा ।
--
-- THIS IS THE CHECKED COUNTERPART OF A HASKELL TYPE ANOTHER LANE IS
-- BUILDING RIGHT NOW: `machine/Uttara_SamordernaOrDosalekhaNeverABareBoolean.hs` (absent from this repository),
-- whose `Uttara` has these same two constructors, whose `Tulyata` is the
-- exhibited identification, and whose `uVahita` is the carried structure.
-- §2 above is the theorem that record is entitled to cite: given the
-- equivalence, the carried operations ARE the conjugates and the
-- identification IS a homomorphism, so `uVahita` is not a claim about
-- what travelled — it is determined.  I am NOT reimplementing that
-- module; the operational lane is theirs and this is the Agda side of it.
------------------------------------------------------------------------

data गति (A B : Type ℓ) : Type (ℓ-suc ℓ) where
  संक्रमण-गतिः : (e : A ≃ B) → गति A B
  दोषलेख-गतिः  : (f : A → B) (दोषः : ¬ (isEquiv f)) → गति A B

-- Every move denotes a function; the defect log does not block the work,
-- it accompanies it.  (§६: the second road is a road, not a refusal.)
चालनम् : गति A B → (A → B)
चालनम् (संक्रमण-गतिः e) = संक्रमणम् e
चालनम् (दोषलेख-गतिः f _) = f

-- …and only the first road has a return.
गति-प्रत्यानयनम्
  : (e : A ≃ B) → Σ[ g ∈ (B → A) ] ((a : A) → g (चालनम् (संक्रमण-गतिः e) a) ≡ a)
गति-प्रत्यानयनम् e = संक्रमणम्-सप्रत्यानयनम् e

------------------------------------------------------------------------
-- अहिंसा ।  संक्रमणे न किञ्चिन् नश्यति — इदानीं साधितम्, न उक्तमात्रम् ।
------------------------------------------------------------------------
