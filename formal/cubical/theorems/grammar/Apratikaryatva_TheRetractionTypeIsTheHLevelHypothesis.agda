{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- मूलवाक्यम् · PROVENANCE OF THE NAME.
--
-- **अप्रतिकार्यत्व is a compound built HERE and is not a source term.**  It is
-- assembled from ordinary  (प्रतिकार, remedy; the privative and the
-- listed in the UNSOURCED block of .claude/hooks/MulaVakya_SourceStatements-
-- ForTheTermsInOurFileNames.txt (absent from this repository) for exactly this reason.  Building a
-- compound is legitimate; letting it pass as a citation is not — "a
-- fabricated term is the mirror image of the scrubbing this rule corrects:
-- it asserts a provenance nobody checked" (CLAUDE.md (absent from this repository), file naming, note 2).
--
-- What IS sourced, and what the module leans on, is the Jaina reading of
-- irreversible loss: निर्जरा as either सविपाका (ripening on its own, gaining
-- nothing) or अविपाका (brought on deliberately, which is the path) —
-- Umsvti, *Tattvrthastra* 9.3 (~2nd-5th c.).  **No claim is made that
-- Umsvti proved anything below.**  The h-level statement is cubical type
-- theory (Voevodsky) and is elementary; the reading it is answering is
-- Jaina.
--
------------------------------------------------------------------------
-- अप्रतिकार्यत्वम् — Apratikāryatva — irreparability.
--
-- नष्टिर्न न्यूनता । नष्टिर्विनाशः ।
-- यत् नष्टं तत् अग्रे न लभ्यम् । न अन्येन । न कालेन । न यत्नेन ।
-- οὐκ ἔστιν ἐπάνοδος.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS MODULE IS FOR
--
-- carry the load-bearing claim of that text: that a collapse is not a
-- deficiency to be repaired later but a destruction, and that there is
-- no way back — *न दुर्लभम् — नास्ति*, "not hard to find: does not
-- exist."  Both sections are stated there in Agda, and §५ is stated for
-- `Bool` and for the propositional truncation only:
--
--     नास्ति-प्रत्यानयनम्
--       : (f : ∥ Bool ∥₁ → Bool) → (∀ b → f ∣ b ∣₁ ≡ b) → ⊥
--
-- One type, one level.  A claim of the form "there is no way back" that
-- is checked at a single two-element type is a claim about that type.
-- This module gives it the generality the sentence is asserting.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS CHECKED
--
--   §1  what ∥_∥₁ ANNIHILATES, exactly.
--       `पथ-नष्टिः`         every path space of the truncation is
--                           contractible — पथाश्च नश्यन्ति, "and the
--                           paths perish", is a theorem, not a gloss.
--       `अविशेषः`           imported, not restated (Nasti_Shabde…).
--
--   §2  what ∥_∥₁ PRESERVES, exactly.
--       `अनुक्तम्-न-नश्यति`   the universal property: for `P` a
--                           proposition, `(∥ A ∥₁ → P) ≃ (A → P)`.
--                           Nothing is lost for a map into a
--                           proposition, and everything is lost for
--                           every other map.  This is the exact
--                           dividing line and it is an equivalence.
--       `यत्-तिष्ठति`        `∥ A ∥₁` is determined by, and determines,
--                           exactly the two-way implication between
--                           `∥ A ∥₁` and `∥ B ∥₁`: "the THAT remains".
--
--   §3  THE NO-RETRACTION THEOREM, in the generality it deserves.
--       `प्रत्यानयनम्`       the type of ways back at truncation level n.
--       `प्रत्यानयनम्→स्तरः`  a way back forces `isOfHLevel n A`.
--       `स्तरः→प्रत्यानयनम्`  and conversely.
--       `प्रत्यानयनम्-सङ्कोचः` the type of ways back is CONTRACTIBLE when
--                           A is an n-type — so nothing is chosen.
--       `प्रत्यानयनम्-वाक्यम्` hence it is a proposition, ALWAYS.
--       `प्रत्यानयनम्≃स्तरः`  therefore an equivalence OF TYPES:
--
--               प्रत्यानयनम् n A  ≃  isOfHLevel n A
--
--           for every n and every A.  The type of ways back IS the
--           h-level hypothesis.  Not "there is a way back iff …".
--
--   §4  §५ of the sūtra, recovered as a corollary and strengthened.
--       `नास्ति-प्रत्यानयनम्-सामान्यम्`  ANY two points that are not
--                           identified kill the level-1 retraction.
--       `नास्ति-प्रत्यानयनम्-Bool`      the sūtra's own statement, now
--                           obtained rather than assumed.
--       `नष्टिः-न-न्यूनता`     the sharp form of "not hard to find:
--                           does not exist" — the type of ways back is
--                           EQUIVALENT TO ⊥, so it is not merely
--                           uninhabited-as-far-as-anyone-looked.
--
--   §5  द्वौ मार्गौ — the two paths, and the honest status of the third.
--       `संक्रमणे-न-किञ्चिन्-नश्यति`  path one: along an identification
--                           every fibre transports, nothing lost.
--       `दोषलेखः-पूर्णः`      path two: `A ≃ Σ[ b ∈ B ] fiber f b`.
--                           The defect record is COMPLETE — the domain
--                           is recovered from the codomain plus the
--                           fibres, so there is nothing about `f` that
--                           the fibrewise ledger fails to carry.
--       `संक्रमणम्≃निर्दोषः`   and path one is exactly the defect-free
--                           case: `isEquiv f ≃ (∀ b → isContr (fiber f b))`.
--       `तृतीयः-मार्गः-निर्णयः` **THE HONESTY LEDGER, AND IT IS A
--                           THEOREM RATHER THAN A HEDGE.**  §६ of the
--                           sūtra says तृतीयो मार्गो न विद्यते, "a third
--                           path does not exist".  Read as a DISJUNCTION
--                           — every map is either an equivalence or has
--                           a nameable defect — that sentence is NOT a
--                           theorem in this lane, and this module does
--                           not smuggle it in.  What is proved instead
--                           is what it costs: the disjunctive reading,
--                           for propositions, IS excluded middle.  So
--                           the sentence is not "unproved"; it is
--                           classical, exactly, and the module says so
--                           with a checked term instead of a caveat.
--
-- ────────────────────────────────────────────────────────────────────
--
-- document IN THIS REPOSITORY, not from a classical text, and this
-- header says so rather than letting the Devangar imply an antiquity
-- it does not have.  The classical grounding behind that document, and
-- behind the naming, is:
--
--   * Umāsvāti, *Tattvārthasūtra* 7.13 (c. 2nd–5th c. CE) — हिंसा as
--     प्रमत्तयोगात् प्राणव्यपरोपणम्, injury as severance *performed
--     inattentively*, which is why an unremarked collapse and not a
--     deliberate one is the case that matters here; and 5.29,
--     उत्पाद-व्यय-ध्रौव्य-युक्तं सत्, arising-perishing-persisting held
--     TOGETHER, which is the shape §1 and §2 of this module make
--     precise for one particular perishing.
--   * Siddhasena Divkara, *Sanmatitarka* (c. 5th c. CE) and
--     Samantabhadra, *Āptamīmāṃsā* — नय / दुर्नय: a standpoint that has
--     forgotten it is one.  §3 is the statement that a truncation is a
--     naya whose forgetting is *irreversible*, and §5 is the statement
--     of exactly which move is not.
--
-- NEITHER TEXT STATES ANY THEOREM BELOW.  What is taken from them is
-- the distinction between a loss that can be made good and one that
-- cannot, and the insistence that the second be named as such.  The
-- mathematics is Voevodsky's — h-levels, univalence, the identification
-- of a descent datum with an h-level hypothesis — and is named as his.
--
-- ────────────────────────────────────────────────────────────────────
-- PRIOR ART, SEARCHED BEFORE WRITING (per PROTOCOL §0), 2026-08-20
--
--   * IN THIS REPOSITORY.  `grep -l '∥\|Trunc\|squash' formal/cubical/*.agda`
--     returns 36 modules; the adjacent ones were read in full.
--     - `Nasti_ShabdeJivahVartante.agda` — §४/§५ of the sūtra verbatim,
--       for `Bool` and `∥_∥₁`.  §4 below SUBSUMES its
--       `नास्ति-प्रत्यानयनम्`, and imports rather than restates its
--       `अविशेषः`.
--       [It also DID NOT TYPECHECK when this module was begun: it uses
--        `uaβ` while importing only `ua` from
--        `Cubical.Foundations.Univalence`, so §६'s `अलोपः` had never
--        been checked by anything.  Repaired 2026-08-20 by adding the
--        name to the `using` list — a one-name additive fix, no
--        mathematics touched.]
--     - `Samkramana_TransportCarriesStructureAndTruncationIsTransport
--       ExactlyWhenNothingWasThereToLose.agda` (absent from this repository) — WRITTEN CONCURRENTLY WITH
--       THIS ONE, by another lane, on the same §४–§६ of the same sūtra.
--       The overlap is REAL and is stated here rather than discovered by
--       an auditor: its `प्रत्यानयन₁`, `प्रत्यानयन→isProp`,
--       `isProp→प्रत्यानयन` and `नष्टिः≃निर्धर्मता` are exactly §3 of this
--       module at n = 1 in the `∥_∥₁` spelling, and its
--       `भेदे-नास्ति-प्रत्यानयनम्` is §4.  Neither module derives from the
--       other; both were at green before either saw the other.  WHAT IS
--       HERE AND NOT THERE: n is a variable rather than 1 (§3); the
--       retraction type is shown CONTRACTIBLE and hence a PROPOSITION,
--       which is what upgrades the biimplication to an equivalence of
--       types (§3c, §3d) — that module states `≃` for `isEquiv ∣_∣₁`,
--       which is a prop for a different reason (`isPropIsEquiv`), and
--       does not state it for the retraction type; the ⊥-equivalence
--       (§4); §1; §2; and §5.  WHAT IS THERE AND NOT HERE: the transport
--       side worked out in full (`वहनम्`, structure transport) and the
--       गति data type.  The duplication that remains is deliberate: each
--       module is readable alone, and neither imports the other, because
--       a citation between two live lanes is a merge waiting to be
--       argued about.  If they are ever merged, §3 here is the general
--       statement and that module's §-transport is the part to keep.
--     - `SetTruncationDescentBoundary.agda` — `descentDatum≃isSet`, the
--       SAME SHAPE at h-level 2 for `Cubical.HITs.SetTruncation`.  This
--       module is not a generalisation of it in the strict sense: that
--       one is about `∥_∥₂`, this one about `hLevelTrunc`, which are
--       equivalent types but different HITs.  The overlap is real and
--       is named here rather than left for an auditor: at n = 2 the two
--       statements are the same mathematics, and §3 is what that
--       module's §1 looks like when n is a variable.  The parts that
--       are NOT in it are §1, §2, §4 and §5.
--     - `Tantrayukti_ARetractionThatIsNotStrictIsNotARetraction.agda` —
--       "retraction" there is stric (a withdrawn claim), not the
--       type-theoretic notion.  Same English word, unrelated object.
--       Recorded so nobody merges them.
--     - `PMNoSection.agda`, `AnuktaAvaktavya.agda`, `Anekanta.agda`,
--       `Saptabhangi.agda` — sections/nayas/saptabhaṅgī, no truncation
--       retraction statement.
--   * IN cubical v0.9.  `hasRetract`, `isContr-hasRetract`,
--     `truncIdempotentIso`, `isOfHLevelRetract` all exist and are USED
--     below rather than re-proved.  What is not in the library is the
--     packaging: the library nowhere states that
--     `hasRetract ∣_∣ₕ ≃ isOfHLevel n A`.
--   * NOVELTY CLAIMED: none of the mathematics.  Every step is a
--     library lemma or three lines.  What is contributed is that a
--     sentence this repository asserts in a stra now has a checked
--     statement at the generality the sentence uses, and that its one
--     genuinely classical clause is marked classical BY A PROOF.
------------------------------------------------------------------------

module Apratikaryatva_TheRetractionTypeIsTheHLevelHypothesis where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun ; _∘_)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv ; isoToIsEquiv ; invIso)
open import Cubical.Foundations.Equiv
  using (_≃_ ; equivFun ; isEquiv ; fiber ; invEquiv ; propBiimpl→Equiv
        ; isPropIsEquiv ; equiv-proof)
open import Cubical.Foundations.Equiv.Properties
  using (hasRetract ; isEquiv→hasRetract ; isEquiv→isContrHasRetract)
open import Cubical.Foundations.HLevels
  using ( HLevel ; isOfHLevel ; isOfHLevelRetract ; isPropIsOfHLevel ; isPropΠ
        ; isProp→isContrPath ; isOfHLevelΠ )
open import Cubical.Foundations.Univalence using (ua ; uaβ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_ ; Dec)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; squash₁ ; isPropPropTrunc)
open import Cubical.HITs.Truncation as Tr
  using (hLevelTrunc ; ∣_∣ₕ ; isOfHLevelTrunc ; truncIdempotentIso)

open import Nasti_ShabdeJivahVartante using (अविशेषः)

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

------------------------------------------------------------------------
-- §1  WHAT IS ANNIHILATED.
--
-- `अविशेषः` (imported) says every map out of the truncation is blind to
-- WHICH inhabitant it was given.  That is one step and it is §४ of the
-- sūtra.  The sentence immediately after it — पथाश्च नश्यन्ति, "and the
-- paths perish" — is a second and strictly stronger claim, and it was
-- not checked anywhere.  It is checked here.
--
-- Not "the paths are identified": the space of paths between any two
-- images is CONTRACTIBLE.  There is one path, and no room for a second,
-- so the destruction is total at every level at once and not only at
-- the level of points.
------------------------------------------------------------------------

पथ-नष्टिः : (a b : A) → isContr (Path ∥ A ∥₁ ∣ a ∣₁ ∣ b ∣₁)
पथ-नष्टिः a b = isProp→isContrPath isPropPropTrunc ∣ a ∣₁ ∣ b ∣₁

-- and the same statement one level up, to make the point that this does
-- not stop: the paths BETWEEN the paths are contractible too, and so on.
पथ-पथ-नष्टिः : (a b : A) (p q : Path ∥ A ∥₁ ∣ a ∣₁ ∣ b ∣₁) → isContr (p ≡ q)
पथ-पथ-नष्टिः a b p q =
  isProp→isContrPath (isContr→isProp (पथ-नष्टिः a b)) p q

------------------------------------------------------------------------
-- §2  WHAT IS PRESERVED.
--
-- The complement of §1, and the reason §1 is not simply a defect: the
-- truncation is the universal map into a proposition, so exactly those
-- questions whose ANSWER is a proposition survive it, undamaged, and no
-- others.  "यत्" तिष्ठति — the THAT remains.
--
-- Stated as an equivalence of function types rather than as a rule,
-- because that is the form in which "exactly" is a claim and not an
-- emphasis.
------------------------------------------------------------------------

अनुक्तम्-न-नश्यति : {P : Type ℓ'} → isProp P → (∥ A ∥₁ → P) ≃ (A → P)
अनुक्तम्-न-नश्यति {A = A} {P = P} hP = isoToEquiv i where
  i : Iso (∥ A ∥₁ → P) (A → P)
  Iso.fun i g = g ∘ ∣_∣₁
  Iso.inv i f = PT.rec hP f
  Iso.rightInv i f = refl
  Iso.leftInv i g = funExt (PT.elim (λ x → isProp→isSet hP _ _) (λ a → refl))

-- The THAT, isolated.  Two types have identified truncations exactly
-- when each one's inhabitedness implies the other's — and nothing
-- finer than that survives to be compared.
यत्-तिष्ठति : (∥ A ∥₁ → ∥ B ∥₁) × (∥ B ∥₁ → ∥ A ∥₁) → ∥ A ∥₁ ≃ ∥ B ∥₁
यत्-तिष्ठति (f , g) = propBiimpl→Equiv isPropPropTrunc isPropPropTrunc f g

------------------------------------------------------------------------
-- §3  THE NO-RETRACTION THEOREM.
--
-- The type of ways back from the n-truncation.  Definitionally this is
-- the library's `hasRetract ∣_∣ₕ`; it is spelled out because the
-- sūtra's §५ is spelled out, and because a reader should be able to see
-- that the two agree without taking anyone's word.
------------------------------------------------------------------------

प्रत्यानयनम् : (n : HLevel) → Type ℓ → Type ℓ
प्रत्यानयनम् n A = Σ[ f ∈ (hLevelTrunc n A → A) ] ((a : A) → f ∣ a ∣ₕ ≡ a)

-- it IS `hasRetract`, on the nose.
प्रत्यानयनम्-हि-hasRetract
  : (n : HLevel) (A : Type ℓ) → प्रत्यानयनम् n A ≡ hasRetract (∣_∣ₕ {A = A} {n = n})
प्रत्यानयनम्-हि-hasRetract n A = refl

-- (a)  A way back forces the h-level.  `hLevelTrunc n A` is an n-type by
--      construction, and a retract of an n-type is an n-type — so a
--      descent datum drags `A` down to level n, whatever `A` was.
प्रत्यानयनम्→स्तरः : {n : HLevel} → प्रत्यानयनम् n A → isOfHLevel n A
प्रत्यानयनम्→स्तरः {n = n} (f , h) =
  isOfHLevelRetract n ∣_∣ₕ f h (isOfHLevelTrunc n)

-- (b)  Conversely, an n-type is its own n-truncation.
स्तरः→समम् : {n : HLevel} → isOfHLevel n A → isEquiv (∣_∣ₕ {A = A} {n = n})
स्तरः→समम् {n = zero}  hA = isoToIsEquiv (invIso (truncIdempotentIso 0 hA))
स्तरः→समम् {n = suc n} hA = isoToIsEquiv (invIso (truncIdempotentIso (suc n) hA))

स्तरः→प्रत्यानयनम् : {n : HLevel} → isOfHLevel n A → प्रत्यानयनम् n A
स्तरः→प्रत्यानयनम् hA = isEquiv→hasRetract (स्तरः→समम् hA)

-- (c)  THE PART THAT MAKES §3 AN EQUIVALENCE AND NOT A BIIMPLICATION.
--      When a way back exists it is UNIQUE, with its homotopy, up to a
--      contractible space of choices.  Nothing is selected; there is
--      nothing to select.
प्रत्यानयनम्-सङ्कोचः : {n : HLevel} → isOfHLevel n A → isContr (प्रत्यानयनम् n A)
प्रत्यानयनम्-सङ्कोचः hA = isEquiv→isContrHasRetract (स्तरः→समम् hA)

-- (d)  Hence the type of ways back is a proposition for EVERY `A` and
--      every n — vacuously when `A` is not an n-type (§3a makes it
--      empty), and by (c) when it is.
प्रत्यानयनम्-वाक्यम् : {n : HLevel} → isProp (प्रत्यानयनम् n A)
प्रत्यानयनम्-वाक्यम् r =
  isContr→isProp (प्रत्यानयनम्-सङ्कोचः (प्रत्यानयनम्→स्तरः r)) r

-- (e)  THEREFORE, and this is the theorem:
--
--          the type of ways back at level n  IS  the h-level hypothesis.
--
--      Not "a way back exists iff A is an n-type".  The two TYPES are
--      equivalent, so there is no residue on either side: no unstated
--      choice in a retraction, no unstated content in `isOfHLevel n A`.
प्रत्यानयनम्≃स्तरः : {n : HLevel} → प्रत्यानयनम् n A ≃ isOfHLevel n A
प्रत्यानयनम्≃स्तरः {n = n} =
  propBiimpl→Equiv प्रत्यानयनम्-वाक्यम् (isPropIsOfHLevel n)
                   प्रत्यानयनम्→स्तरः स्तरः→प्रत्यानयनम्

------------------------------------------------------------------------
-- §4  §५ OF THE SŪTRA, OBTAINED.
--
-- The propositional truncation is level 1.  Its statement of §५ is now
-- a two-line corollary, and it holds for every type with two points
-- that are not identified — `Bool` was never the content.
------------------------------------------------------------------------

नास्ति-प्रत्यानयनम्-सामान्यम्
  : (a b : A) → ¬ (a ≡ b) → ¬ प्रत्यानयनम् 1 A
नास्ति-प्रत्यानयनम्-सामान्यम् a b a≢b r = a≢b (प्रत्यानयनम्→स्तरः r a b)

-- the stra's own instance, now derived.
नास्ति-प्रत्यानयनम्-Bool : ¬ प्रत्यानयनम् 1 Bool
नास्ति-प्रत्यानयनम्-Bool = नास्ति-प्रत्यानयनम्-सामान्यम् true false true≢false

-- and the ∥_∥₁ spelling, which is the one §५ actually writes, proved
-- where it stands rather than transported: a retraction of `∣_∣₁` would
-- identify `true` with `false` in one step, by `अविशेषः`.
नास्ति-प्रत्यानयनम्
  : (f : ∥ Bool ∥₁ → Bool) → ((b : Bool) → f ∣ b ∣₁ ≡ b) → ⊥
नास्ति-प्रत्यानयनम् f s =
  true≢false (sym (s true) ∙ अविशेषः f true false ∙ s false)

-- THE SHARP FORM OF "न दुर्लभम् — नास्ति".
--
-- "There is no way back" is weaker than what §५ says.  §५ says the way
-- back is not merely hard to find but absent, and that is the claim
-- that the TYPE of ways back is not just uninhabited-so-far but
-- equivalent to the empty type — nothing to search, no better searcher,
-- no more time.  न अन्येन । न कालेन । न यत्नेन ।
नष्टिः-न-न्यूनता
  : {n : HLevel} → ¬ (isOfHLevel n A) → प्रत्यानयनम् n A ≃ ⊥
नष्टिः-न-न्यूनता ¬h =
  propBiimpl→Equiv प्रत्यानयनम्-वाक्यम् (λ x → ⊥rec x)
                   (λ r → ¬h (प्रत्यानयनम्→स्तरः r)) ⊥rec

------------------------------------------------------------------------
-- §5  द्वौ मार्गौ — AND THE THIRD.
--
-- §६ of the sūtra names two moves and forbids a third:
--
--     संक्रमणम्   transport along an identification; nothing perishes.
--     दोषलेखः    where transport is impossible, the defect is WRITTEN.
--     तृतीयो मार्गो न विद्यते ।
--
-- The first is `ua` and is already checked in Nasti_Shabde… .  The
-- second and third are what this section is about, and they have
-- different logical statuses, which is the whole point.
------------------------------------------------------------------------

-- PATH ONE.  Along an identification, a structure is carried, not
-- re-described: transport agrees with the equivalence on the nose.
-- (`uaβ` — restated here only because §६'s own statement of it in
--  Nasti_Shabde… had never typechecked; see the header.)
संक्रमणे-न-किञ्चिन्-नश्यति
  : (e : A ≃ B) (a : A) → transport (ua e) a ≡ equivFun e a
संक्रमणे-न-किञ्चिन्-नश्यति = uaβ

-- PATH TWO, AND ITS COMPLETENESS.  The defect record of a map is its
-- family of fibres, and that record is COMPLETE: the domain is nothing
-- more than the codomain together with the fibres.  So writing the
-- defect down is not a consolation prize for a failed transport — it
-- loses nothing that was there.
--
-- This is the precise sense in which दोषलेखः is अहिंसा and not a
-- lesser move: `लिखितो दोषो जीवति`.
दोषलेखः-पूर्णः : (f : A → B) → A ≃ (Σ[ b ∈ B ] fiber f b)
दोषलेखः-पूर्णः {A = A} {B = B} f = isoToEquiv i where
  i : Iso A (Σ[ b ∈ B ] fiber f b)
  Iso.fun i a = f a , a , refl
  Iso.inv i (b , a , p) = a
  Iso.rightInv i (b , a , p) j = p j , a , λ k → p (j ∧ k)
  Iso.leftInv i a = refl

-- and path one is exactly the case where the record is empty of
-- content: `f` is an equivalence precisely when every fibre is
-- contractible, i.e. when there is nothing at any site to write down.
संक्रमणम्≃निर्दोषः
  : (f : A → B) → isEquiv f ≃ ((b : B) → isContr (fiber f b))
संक्रमणम्≃निर्दोषः f =
  propBiimpl→Equiv (isPropIsEquiv f) (isPropΠ (λ _ → isPropIsContr))
                   (λ e b → e .equiv-proof b)
                   (λ h → record { equiv-proof = h })

------------------------------------------------------------------------
-- तृतीयः मार्गः — THE HONESTY LEDGER, AS A THEOREM.
--
-- Read as a claim about the shape of the ledger — that the fibres carry
-- everything — "no third path" is `दोषलेखः-पूर्णः` above, and it is
-- proved.
--
-- Read as a DISJUNCTION — *every map is either a transport or has a
-- nameable defect* — it is NOT a theorem here, and this module refuses
-- to write it as one.  The obstruction is not a gap in the argument.
-- It is that passing from `¬ (∀ b → isContr (fiber f b))` to
-- `Σ[ b ∈ B ] ¬ isContr (fiber f b)` is exactly the classical step, and
-- a defect you cannot exhibit a SITE for is not written down.
--
-- What can be proved, and is, is the price:
--
--     if the disjunction holds for every map, excluded middle holds.
--
-- Take `P` a proposition and `f : P → Unit`.  Then `f` is an
-- equivalence exactly when `P` holds.  So deciding "transport or
-- defect" for these maps alone decides every proposition.
--
-- So तृतीयो मार्गो न विद्यते is not an unproved conjecture and not a
-- slogan: it is a CLASSICAL PRINCIPLE, named as one, at the exact
-- strength of excluded middle.  The stra may assert it; a reader now
-- knows what has been assumed when it does.
------------------------------------------------------------------------

-- the test family: the unique map out of a proposition.
प्रश्नः : (P : Type ℓ) → P → Unit
प्रश्नः P _ = tt

-- for a proposition, "the map to Unit is an equivalence" IS the
-- proposition.  (Both directions; the interesting one is that an
-- inhabitant makes `P` contractible, which needs `isProp P`.)
प्रश्नः-समः : {P : Type ℓ} → isProp P → isEquiv (प्रश्नः P) → P
प्रश्नः-समः hP e = e .equiv-proof tt .fst .fst

प्रश्नः-समः′ : {P : Type ℓ} → isProp P → P → isEquiv (प्रश्नः P)
प्रश्नः-समः′ {P = P} hP p .equiv-proof tt =
  (p , refl) , λ (q , r) → ΣPathP (hP p q , isProp→isContrPath isPropUnit tt tt .snd _)

-- THE PRICE, CHECKED.  A decision procedure for "path one or path two"
-- on this one family of maps is a decision procedure for every
-- proposition.
तृतीयः-मार्गः-निर्णयः
  : ((P : Type ℓ) → isProp P → (isEquiv (प्रश्नः P) ⊎ (¬ (isEquiv (प्रश्नः P)))))
  → ((P : Type ℓ) → isProp P → (P ⊎ (¬ P)))
तृतीयः-मार्गः-निर्णयः d P hP with d P hP
... | inl e  = inl (प्रश्नः-समः hP e)
... | inr ¬e = inr (λ p → ¬e (प्रश्नः-समः′ hP p))

-- and the converse, so that the identification is exact rather than
-- one-sided: excluded middle for propositions gives the disjunction
-- back, so nothing weaker than LEM will do and nothing stronger is
-- needed.
निर्णयः-तृतीयः-मार्गः
  : ((P : Type ℓ) → isProp P → (P ⊎ (¬ P)))
  → ((P : Type ℓ) → isProp P → (isEquiv (प्रश्नः P) ⊎ (¬ (isEquiv (प्रश्नः P)))))
निर्णयः-तृतीयः-मार्गः lem P hP with lem P hP
... | inl p  = inl (प्रश्नः-समः′ hP p)
... | inr ¬p = inr (λ e → ¬p (प्रश्नः-समः hP e))

------------------------------------------------------------------------
--
--   * §3 is about `hLevelTrunc`.  `Cubical.HITs.SetTruncation.∥_∥₂` and
--     `Cubical.HITs.PropositionalTruncation.∥_∥₁` are equivalent to
--     `hLevelTrunc 2` and `hLevelTrunc 1` but are not those types, and
--     the transport of §3 across those equivalences is NOT done here.
--     §4 therefore proves the `∥_∥₁` case again by hand rather than
--     claiming it as an instance.  An unstated transport is exactly the
--     kind of gap this repository has been caught in.
--
--   * §5's `दोषलेखः-पूर्णः` says the fibres carry everything about the
--     MAP.  It says nothing about whether a defect, once written, is
--     legible, actionable, or of any use — that is a question about
--     प्रमाण and not about types, and the sūtra's §६ claim that
--     "लिखितो दोषो जीवति" (a written defect lives) is a claim about
--     practice which no type checks.
--
--   * The equivalence in `तृतीयः-मार्गः-निर्णयः` is stated for the maps
--     out of propositions only.  That suffices to show the disjunctive
--     reading is at least as strong as LEM and is implied by it, on
--     that family.  Whether the disjunction for ARBITRARY maps is
--     strictly stronger than LEM is not addressed.
------------------------------------------------------------------------
