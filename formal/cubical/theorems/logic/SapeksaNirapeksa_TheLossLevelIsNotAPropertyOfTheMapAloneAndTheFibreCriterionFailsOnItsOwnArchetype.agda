{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सापेक्ष–निरपेक्ष — हानिस्तरः न मानचित्रस्य धर्मः ; निरपेक्षं परिच्छेदं
-- स्वार्चेटाइपः एव हन्ति ।
--
-- (relative / absolute: the loss-level is not a property of the map, and
--  the criterion taken without its context is killed by its own archetype.)
--
-- ────────────────────────────────────────────────────────────────────
-- THE TERM.  सापेक्ष (with regard to) / निरपेक्ष (without regard to) is
-- the Jaina pair that decides whether a naya is a naya or a दुर्नय:
-- **Siddhasena Divkara, *Sanmatitarka* (Prakrit *Sammai-suttam*)
-- 1.21–25, date disputed, c. 5th c. CE** — a standpoint asserted
-- निरपेक्ष, apart from the others it stands among, is मिथ्या.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS REFUTES.
--
-- (recoverable only by outside supply) and ४ (नष्टिः, अप्रतिकार्या) are
-- both crowded fibres; `Loss.WholePartialDesa_…` refuses a fourth
-- constructor for `देश` because no criterion separated them.  The note
-- proposes one, in two halves:
--
--   level ४ — the fibre is the WHOLE source, and nothing anywhere sees
--             the difference;
--   level ३ — the fibre is a PROPER PART, and other maps out of the
--             source still see the difference.
--
-- `Avacchedaka_TheTruncationsFibreIsTheWholeSourceAndTheSeamHasItsCriterion`
-- checked the load-bearing half — every
-- fibre of `∣_∣₁` is equivalent to the whole source — and wrote the
-- criterion down as `सर्वहानिः f b = fiber f b ≃ A`, with the sentence:
-- *"विकलादेश says the fibre has two distinct points; that is true of a
-- map that drops one bit and equally true of a map that drops
-- everything.  सर्वहानिः says which."*
--
-- **That sentence is false, and §१ is one line.**  `सर्वैकम् : Bool → Unit`
-- is the map that drops one bit — `Sesa_…`'s own §5, and its struck
-- header names it "level २ of a five-level scale".  Its fibre over `tt`
-- is `Bool`, which IS the whole source.  So `सर्वहानिः` holds of it, and
-- the criterion does not separate ४ from ३; it does not separate ४
-- from २.
--
-- §२ shows this is not a stray instance.  `∥ Bool ∥₁ ≃ Unit`, and the
-- triangle commutes: at `A = Bool` the level-४ ARCHETYPE **is** the
-- level-२ archetype, up to an equivalence of the target.  §२'s last
-- theorem states the consequence in the census's own terms — the two
-- maps' fibre censuses are pointwise equivalent — so no reading of the
-- census whatsoever tells them apart.
--
-- §३ kills the other half.  "Other maps out of the source still see the
-- difference" holds AT THE LEVEL-४ ARCHETYPE: `idfun Bool` separates two
-- distinct points of `fiber ∣_∣₁ ∣ true ∣₁`.  It is vacuous wherever the
-- fibre is crowded at all, because विकलादेश's own evidence — two fibre
-- points and a proof they differ — is already such a separation.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THE COLLISION NAMES, §४, and this is the part worth keeping.
--
-- The two verdicts collide because "recoverable" was being asked of a
-- map निरपेक्ष.  Recovery is a question about a map TOGETHER WITH what
-- else the construction retained.  §४ fixes the same map `सर्वैकम्` and
-- varies only the retained context:
--
--   retain `idfun Bool`  →  ⟨सर्वैकम् , id⟩ is an EQUIVALENCE.  Nothing lost.
--   retain nothing       →  ⟨सर्वैकम् , सर्वैकम्⟩ is NOT.  The bit is gone.
--
-- One map, two verdicts, both checked.  So no predicate on `f` alone can
-- carry the level, and the scale as the note states it — indexed by the
-- map — cannot be completed by any criterion at all, this one included.
--
-- §५ pushes it to the level-४ archetype: `A ≃ ∥ A ∥₁ × A` for EVERY `A`.
-- Retaining the source recovers even the truncation.  अप्रतिकार्यता is a
-- statement about what is retained, not about `∣_∣₁`.
--
-- §६ locates where the level-२/level-४ collapse happens, so it is not
-- mistaken for a claim that truncation never loses: `∥ A ∥₁ ≃ Unit`
-- exactly when `A` is merely inhabited.  The distinction the scale wants
-- lives in the QUANTIFIER — uniformly in `A`, `∣_∣₁` has no section — and
-- a per-instance fibre criterion cannot reach a quantifier.
------------------------------------------------------------------------

module SapeksaNirapeksa_TheLossLevelIsNotAPropertyOfTheMapAloneAndTheFibreCriterionFailsOnItsOwnArchetype where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isProp→isContrPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- ०.  The criterion under test, restated here so this module is readable
--     without opening the one it refutes.  It is `Avacchedaka_…`'s §३,
--     copied verbatim in content.
------------------------------------------------------------------------

सर्वहानिः : {A B : Type ℓ} → (A → B) → B → Type ℓ
सर्वहानिः {A = A} f b = fiber f b ≃ A

------------------------------------------------------------------------
-- १.  THE REFUTATION.  The level-२ archetype satisfies the level-४
--     criterion.
--
-- `सर्वैकम्` is `Sesa_…` §5's map, whose struck header calls it "level २ of
-- a five-level scale" and whose loss it prices at exactly one bit.  Its
-- fibre over the single target point is `Bool` — the whole source —
-- because `Unit` is a proposition, so the path component of the Σ is
-- contractible and contracts away.  The proof is the SAME PROOF as
-- `Avacchedaka_…` §२'s, with `isPropUnit` in place of `isPropPropTrunc`,
-- which is the whole of why the criterion cannot discriminate: it is
-- reading propositionality of the target, and both targets are props.
------------------------------------------------------------------------

सर्वैकम् : Bool → Unit
सर्वैकम् _ = tt

एकबिन्दु-सर्वहानिः : सर्वहानिः सर्वैकम् tt
एकबिन्दु-सर्वहानिः = Σ-contractSnd (λ _ → isProp→isContrPath isPropUnit tt tt)

-- and it is genuinely crowded, so this is not the empty-fibre case:
-- two points of the fibre, produced as terms, provably distinct.
सर्वैकम्-वाम सर्वैकम्-दक्षिण : fiber सर्वैकम् tt
सर्वैकम्-वाम    = false , refl
सर्वैकम्-दक्षिण  = true  , refl

सर्वैकम्-द्वयम् : ¬ (सर्वैकम्-वाम ≡ सर्वैकम्-दक्षिण)
सर्वैकम्-द्वयम् p = false≢true (cong fst p)

------------------------------------------------------------------------
-- २.  WHY IT IS NOT A STRAY INSTANCE.  At `A = Bool` the level-४
--     archetype IS the level-२ archetype.
--
-- `∥ Bool ∥₁` is an inhabited proposition, hence contractible, hence
-- equivalent to `Unit`; and the triangle over `Bool` commutes by `refl`.
-- So `∣_∣₁ : Bool → ∥ Bool ∥₁` and `सर्वैकम् : Bool → Unit` are one map
-- read through an equivalence of its target.
------------------------------------------------------------------------

त्रुटि-Bool≃Unit : ∥ Bool ∥₁ ≃ Unit
त्रुटि-Bool≃Unit =
  isoToEquiv (iso (λ _ → tt) (λ _ → ∣ true ∣₁)
                  (λ _ → refl) (λ x → isPropPropTrunc _ x))

त्रिकोणम् : (b : Bool) → equivFun त्रुटि-Bool≃Unit ∣ b ∣₁ ≡ सर्वैकम् b
त्रिकोणम् _ = refl

-- The consequence, stated in the census's own terms.  Every fibre of the
-- level-४ archetype at `Bool` is equivalent to the single fibre of the
-- level-२ archetype.  A census is a function on fibres; two maps whose
-- censuses are pointwise equivalent cannot be told apart by one.
गणना-अभेदः : (x : ∥ Bool ∥₁) → fiber (∣_∣₁ {A = Bool}) x ≃ fiber सर्वैकम् tt
गणना-अभेदः x =
  compEquiv (Σ-contractSnd (λ a → isProp→isContrPath isPropPropTrunc ∣ a ∣₁ x))
            (invEquiv एकबिन्दु-सर्वहानिः)

------------------------------------------------------------------------
-- ३.  THE OTHER HALF, refuted by being satisfied where it must fail.
--
-- The note's level-३ side reads: the fibre is a proper part, and *other
-- maps out of the source still see the difference* — `साक्षि-स्थानम्`
-- naming the lost standpoint.  Here is that condition holding at the
-- level-४ archetype, where by hypothesis nothing anywhere sees the
-- difference: two distinct points of one fibre of `∣_∣₁`, and `idfun`
-- separating them.
--
-- It is vacuous, and the reason is structural rather than particular:
-- विकलादेश's evidence IS a separation.  To write the constructor at all
-- you must hand over two fibre points and a proof they differ, and for a
-- map into a set that proof already separates their sources.  A condition
-- discharged by the evidence of the case it is meant to classify
-- classifies nothing.
------------------------------------------------------------------------

त्रुटि-वाम त्रुटि-दक्षिण : fiber (∣_∣₁ {A = Bool}) ∣ true ∣₁
त्रुटि-वाम    = false , isPropPropTrunc _ _
त्रुटि-दक्षिण  = true  , refl

त्रुटि-द्वयम् : ¬ (त्रुटि-वाम ≡ त्रुटि-दक्षिण)
त्रुटि-द्वयम् p = false≢true (cong fst p)

-- a map out of the source that "still sees the difference", at level ४
साक्षी-निष्फलः : ¬ (idfun Bool (fst त्रुटि-वाम) ≡ idfun Bool (fst त्रुटि-दक्षिण))
साक्षी-निष्फलः = false≢true

------------------------------------------------------------------------
-- ४.  सापेक्षता — one map, two contexts, two verdicts.
--
-- `युग्मम् f w` is the map paired with what the construction kept.  The
-- question "was the bit recovered" is a question about the PAIR, and the
-- pair's answer moves while `f` stands still.
------------------------------------------------------------------------

युग्मम् : {A B S : Type ℓ} → (A → B) → (A → S) → (A → B × S)
युग्मम् f w a = f a , w a

-- context = retain the source.  Nothing is lost, as an equivalence.
सापेक्ष-समता : Bool ≃ (Unit × Bool)
सापेक्ष-समता =
  isoToEquiv (iso (युग्मम् सर्वैकम् (idfun Bool)) snd (λ _ → refl) (λ _ → refl))

सापेक्ष-समता-युग्मम् : (b : Bool) → equivFun सापेक्ष-समता b ≡ युग्मम् सर्वैकम् (idfun Bool) b
सापेक्ष-समता-युग्मम् _ = refl

-- context = retain nothing.  The same `सर्वैकम्`, and the bit is gone.
निरपेक्ष-वाम निरपेक्ष-दक्षिण : fiber (युग्मम् सर्वैकम् सर्वैकम्) (tt , tt)
निरपेक्ष-वाम   = false , refl
निरपेक्ष-दक्षिण = true  , refl

निरपेक्ष-न-समता : ¬ (isEquiv (युग्मम् सर्वैकम् सर्वैकम्))
निरपेक्ष-न-समता e =
  false≢true
    (cong fst (isContr→isProp (e .equiv-proof (tt , tt))
                              निरपेक्ष-वाम निरपेक्ष-दक्षिण))

------------------------------------------------------------------------
-- ५.  The same move at the level-४ archetype, for every `A`.
--
-- Retaining the source recovers the truncation too: `A ≃ ∥ A ∥₁ × A`,
-- with no hypothesis on `A`.  The forward map is `युग्मम् ∣_∣₁ id`.
--
-- This does not say truncation is harmless.  It says अप्रतिकार्यता is not
-- readable off `∣_∣₁`, because the trivial context already discharges it,
-- exactly as it does for `सर्वैकम्` in §४.
------------------------------------------------------------------------

पूर्ण-सन्दर्भः : {A : Type ℓ} → A ≃ (∥ A ∥₁ × A)
पूर्ण-सन्दर्भः {A = A} =
  isoToEquiv (iso (युग्मम् ∣_∣₁ (idfun A)) snd
    (λ { (x , a) i → isPropPropTrunc ∣ a ∣₁ x i , a })
    (λ _ → refl))

------------------------------------------------------------------------
-- ६.  Where §२'s collapse happens, so it is not mistaken for more.
--
-- `∥ A ∥₁ ≃ Unit` exactly when `A` is merely inhabited.  §२ used `Bool`,
-- which is inhabited, and that is the whole reason the level-४ archetype
-- degenerated into the level-२ one there.  For an `A` not known
-- inhabited the two maps are not comparable this way — and that is a
-- statement with a quantifier in it, which no criterion evaluated at one
-- map and one point of its codomain can express.
--
-- The uniform statement the scale actually wants is about all `A` at
-- once.
------------------------------------------------------------------------

वास्तव्यम्→एकम् : {A : Type ℓ} → ∥ A ∥₁ → (∥ A ∥₁ ≃ Unit)
वास्तव्यम्→एकम् x =
  isoToEquiv (iso (λ _ → tt) (λ _ → x) (λ _ → refl) (λ y → isPropPropTrunc x y))

एकम्→वास्तव्यम् : {A : Type ℓ} → (∥ A ∥₁ ≃ Unit) → ∥ A ∥₁
एकम्→वास्तव्यम् e = invEq e tt
