{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- Punarāgamana · सकलादेश / विकलादेश
--
-- सकलादेश — the total statement: the object with all its attributes
-- presented at once, through one attribute uttered, by अभेद-वृत्ति.
-- विकलादेश — the same content through भेद, the aspects taken severally,
-- one at a time.  **Malliea, *Sydvdamajar*, 1292 CE**, commenting
-- on Hemacandra's *Anyayogavyavacchedik*; earlier in the Akalaka
-- commentarial line (Vidynandin, Prabhcandra).
--
-- ग्रेड · शब्द, declared.  No edition of any of the above was opened by
-- me.  The attribution and date are carried from
-- `notes/SakalaVikalaDesa_TheFibreIsTheLossAndAnEmptyFibreIsAvaktavyamNotNasti.md` (absent from this repository),
-- which itself carries them from
-- `notes/ANEKANTA_THE_MACHINE_HAS_THREE_STANDPOINTS.md` (absent from this repository), and are owed at
-- verse level.  Nothing below is claimed to have been proved by
-- Malliea or anyone in that line.  What IS claimed is what that note
-- claims: the distinction they draw is finer than the one this library
-- was drawing, and the finer one is exhibitable here.
--
------------------------------------------------------------------------
-- WHY THIS MODULE EXISTS.  It repairs a defect in its neighbour.
--
-- `Residue_TheResidualIsTheOtherProjectionOfTheSameGraph` (this library,
-- earlier today) built a TWO-VALUED test — `isContr (शेष f b)` or not —
-- and wrote in its own header "there is no third reading".  That sentence
-- is a दुर्नय, and `Saptabhangi.दुर्नयः` is the proof of why: a two-valued
-- verdict on a threefold situation must identify two of the three.
--
-- The two it identified are the two ENDS of the scale:
--
--   * the fibre is **empty** — nothing was lost.  The medium simply has
--     no name for `b`.  This is अवक्तव्यम्, the fourth position, and the
--     tradition marks it धनात्मकम् — POSITIVE.
--   * the fibre is **crowded** — two or more points, not identified.
--     This is नष्टि, हिंसा, अप्रतिकार्या.
--
-- `isContr` returns `false` for both.  The tradition held them apart for
-- a millennium before there was a fibre to hang the distinction on.
--
-- THE REPAIR, and it is the one code change that note argues for and
-- explicitly declines to make (its §४): make the CENSUS a term.  `देश`
-- below is a datatype whose constructors carry their evidence, so a
-- diagnosis is a function `B → देश f b` — pointwise, over every point of
-- the codomain — rather than a verdict about the map.
--
-- §3 is why that matters, and it is the sharpest thing here: it turns
-- that note's three-line refutation of the SEQUENTIAL diagnostic into a
-- computed object.  The sequential diagnostic, "factor the proof, and the
-- first non-contractible fibre is where the information went", is
-- unsound in BOTH directions, and §3 exhibits both failures as censuses.
------------------------------------------------------------------------

module Punaragamana.WholePartialDesa_TheFibreCensusIsATermAndItRefutesTheSequentialDiagnostic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false ; false≢true ; isSetBool)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Fibre.Residue_TheResidualIsTheOtherProjectionOfTheSameGraph
  using (शेष)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 1.  देश — the census, as a term.
--
-- Not a verdict ABOUT a map.  A datatype indexed by a map and a POINT OF
-- ITS CODOMAIN, whose constructors carry the evidence the corpus already
-- exhibits by hand:
--
--   अवक्तव्यम्  the fibre is empty        — level ०, धनात्मकम्, nothing lost
--   सकलादेश   the fibre is contractible  — level १, one utterance carries all
--   विकलादेश   two points, not identified — level २+, the loss, exhibited
--
-- The evidence is not a tag.  `विकलादेश` cannot be written without
-- producing the two points and the proof they are distinct, which is
-- exactly `AHIMSA_SUTRA` §६'s second road: लिखितो दोषो जीवति.
------------------------------------------------------------------------

data देश {A B : Type ℓ} (f : A → B) (b : B) : Type ℓ where
  अवक्तव्यम् : (¬ शेष f b)                            → देश f b
  सकलादेश  : isContr (शेष f b)                       → देश f b
  विकलादेश  : (x y : शेष f b) → (¬ (x ≡ y))          → देश f b

-- A diagnosis is a census: pointwise, over the whole codomain at once.
गणना : {A B : Type ℓ} (f : A → B) → Type ℓ
गणना {B = B} f = (b : B) → देश f b

------------------------------------------------------------------------
-- 2.  The three are mutually exclusive — which is what makes it a census
--     and not three overlapping opinions.
------------------------------------------------------------------------

module _ {A B : Type ℓ} (f : A → B) (b : B) where

  -- an empty fibre is not a contractible one
  अवक्तव्य-न-सकल : (¬ शेष f b) → ¬ (isContr (शेष f b))
  अवक्तव्य-न-सकल e c = e (fst c)

  -- a contractible fibre has no two distinct points
  सकल-न-विकल : isContr (शेष f b) → (x y : शेष f b) → x ≡ y
  सकल-न-विकल c = isContr→isProp c

  -- and an empty fibre has no points at all, so a fortiori no two
  अवक्तव्य-न-विकल : (¬ शेष f b) → शेष f b → ⊥
  अवक्तव्य-न-विकल e = e

------------------------------------------------------------------------
-- 3.  THE REFUTATION, computed.
--
--   f : Unit → Bool   f _ = true
--   g : Bool → Unit   g _ = tt
--
-- Read the note's §४ off the censuses below:
--
--   * `f`'s census is सकलादेश at `true` and नास्ति at `false`.  Step one
--     has a NON-CONTRACTIBLE fibre and loses NOTHING — `Bool` merely has
--     a name `Unit` cannot utter.  So "the first non-contractible fibre
--     is where the information went" is false in one direction.
--
--   * `g`'s census is विकलादेश at `tt`.  Step two loses a bit.
--
--   * the composite is the identity on `Unit`, and its census is सकलादेश.
--     The genuine loss at step two does not appear in the composite at
--     all — the inexpressibility at step one and the collapse at step two
--     cancel.  False in the other direction too.
--
-- A binary test cannot state this, because it must call step one and step
-- two by the same name.  The census calls them नास्ति and विकलादेश.
------------------------------------------------------------------------

सत् : Unit → Bool
सत् _ = true

एकम् : Bool → Unit
एकम् _ = tt

संहति : Unit → Unit
संहति u = एकम् (सत् u)

-- step one, over `true`: contractible.  The unique point is (tt , refl).
सत्-गणना-सत्य : isContr (शेष सत् true)
fst सत्-गणना-सत्य         = tt , refl
snd सत्-गणना-सत्य (u , p) i = tt , isSetBool true true refl p i

-- step one, over `false`: EMPTY.  Nothing was lost; `Unit` cannot utter it.
सत्-गणना-असत्य : ¬ शेष सत् false
सत्-गणना-असत्य (_ , p) = true≢false p

सत्-गणना : गणना सत्
सत्-गणना true  = सकलादेश सत्-गणना-सत्य
सत्-गणना false = अवक्तव्यम् सत्-गणना-असत्य

-- step two, over the single point: CROWDED.  Exactly one bit is lost.
-- The two inhabitants are named, because `विकलादेश` requires them as
-- terms — the loss is exhibited, not asserted.
एकम्-वाम एकम्-दक्षिण : शेष एकम् tt
एकम्-वाम    = false , refl
एकम्-दक्षिण  = true  , refl

एकम्-गणना-द्वयम् : ¬ (एकम्-वाम ≡ एकम्-दक्षिण)
एकम्-गणना-द्वयम् p = false≢true (cong fst p)

एकम्-गणना : गणना एकम्
एकम्-गणना tt = विकलादेश एकम्-वाम एकम्-दक्षिण एकम्-गणना-द्वयम्

-- the composite: contractible.  It is the identity, and it loses nothing.
संहति-गणना-सम्पूर्ण : isContr (शेष संहति tt)
fst संहति-गणना-सम्पूर्ण         = tt , refl
snd संहति-गणना-सम्पूर्ण (u , p) i = tt , isSetUnit tt tt refl p i

संहति-गणना : गणना संहति
संहति-गणना tt = सकलादेश संहति-गणना-सम्पूर्ण

------------------------------------------------------------------------
-- 4.  What the census recovers, and where it stops.
--
-- The verdict is a SUMMARY of the census, and the summary is strictly
-- coarser: `isEquiv f` is by definition the statement that every point of
-- the census is सकलादेश.  That definition was in
-- `Cubical.Foundations.Equiv` the whole time; what was missing was the
-- reading of it — an equivalence is not a two-way map, it is a complete
-- simultaneous fibre census whose every entry is level १.
------------------------------------------------------------------------

-- so the verdict is recoverable from the census…
सर्व-सकल→समता : {A B : Type ℓ} (f : A → B)
              → ((b : B) → isContr (शेष f b)) → isEquiv f
सर्व-सकल→समता f c = record { equiv-proof = c }

समता→सर्व-सकल : {A B : Type ℓ} (f : A → B)
              → isEquiv f → (b : B) → isContr (शेष f b)
समता→सर्व-सकल f e b = e .equiv-proof b

-- …and the census is not recoverable from the verdict, which is the whole
-- point: `¬ isEquiv सत्` and `¬ isEquiv एकम्` are the same two words for
-- two opposite situations.
सत्-न-समता : ¬ (isEquiv सत्)
सत्-न-समता e = सत्-गणना-असत्य (fst (समता→सर्व-सकल सत् e false))

एकम्-न-समता : ¬ (isEquiv एकम्)
एकम्-न-समता e =
  एकम्-गणना-द्वयम्
    (isContr→isProp (समता→सर्व-सकल एकम् e tt) एकम्-वाम एकम्-दक्षिण)

------------------------------------------------------------------------
-- THE SEAM, written rather than closed.  दोषलेखः.
--
-- The note's scale has five levels; this module has three constructors.
-- Levels ३ (recoverable only by outside supply) and ४ (नष्टिः,
-- अप्रतिकार्या) are both crowded fibres, and both land in `विकलादेश` here.
--
-- They are not separated because the note establishes that the obvious
-- criterion does NOT separate them: `¬ Σ[ψ] (ψ ∘ collapse ≡ id)` holds of
-- both `Arpitanarpita.न-प्रत्यानयनम्` (level ३) and `AHIMSA_SUTRA`'s
-- `नास्ति-प्रत्यानयनम्` (level ४).  Its candidate criterion — the fibre is a
-- PROPER PART of the source at ३ and the WHOLE of it at ४ — rests on an
-- unchecked conjecture, `(x : ∥ A ∥₁) → fibre ∣_∣₁ x ≃ A`.
--
-- Adding a constructor for a distinction that has no criterion would be
-- the same दुर्नय this module exists to repair, one level down: a name
-- doing the work of a proof.  So `विकलादेश` is deliberately coarse, and
-- this paragraph is the seam.
------------------------------------------------------------------------
