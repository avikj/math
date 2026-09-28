{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- Punarāgamana · अधर्मिन्
--
-- धर्मिन् — the property-bearer, the SUBJECT of which something is
-- predicated.  Nyya's term, and the thing an inference must have before
-- it can have a पक्ष at all.  अधर्मिन् / निर्धर्मिन्, as used here, is not a
-- term I can source to a text: it is this repository's own compound,
-- introduced in `machine/Obstruction.hs` (absent from this repository) (`data Sthana = Position Bhanga
-- | ADharmin`, and `Nirdharmin` in its `Verdict`) for the case where the
-- question has no subject, so no bhaga is available and none is forced.
-- Per CLAUDE.md (absent from this repository)'s naming rule note 2, that is stated rather than
-- back-attributed: the Nyāya debt is धर्मिन्; the negated compound and
-- everything below are the repository's and this file's.
--
------------------------------------------------------------------------
-- WHY THIS MODULE EXISTS.  The three-valued census lacks a fourth case.
--
-- `WholePartialDesa_…` (this library) replaced a two-valued test
-- with a three-valued census — empty / contractible / crowded — because
-- `isContr` was merging नास्ति with नष्टि.
--
-- The census has no case for the question that has no subject.
-- `machine/Obstruction.hs` (absent from this repository) carries FOUR outcomes:
--
--     asti · nāsti · avaktavya · ADharmin
--
-- and its comment states the doctrine the fourth one exists for:
--
--     "Absence of an ACCEPT line is NOT recorded as nsti.  The log
--      records refusals and successes; it does not record a naya
--      declining to try."
--
-- Reading silence as denial is the error.  `देश f b` cannot make it,
-- because it cannot make the distinction at all: `देश` is INDEXED BY `f`
-- and by `b`.  Writing the type down already presupposes a map to take a
-- fibre of and a point to take it over.  "There is no subject here" is
-- not a value of `देश`; it is a statement about whether `देश` applies.
--
-- So the fourth outcome is not a missing constructor.  It lives one level
-- up, on the QUESTION rather than on the answer, which is precisely the
-- shape `Sthana = Position Bhanga | ADharmin` has in the Haskell lane.
-- §1 gives it that shape in Agda types, where the corpus has never had
-- it: grepping `formal/cubical/` for ADharmin / निर्धर्मिन् returns three
-- hits, all of them prose in headers.  `Nirnaya_TheVerdictCannotDropIts
-- Witness` names निर्धर्मिन् in its own vocabulary list and then defines
-- `प्रतिवचनम् c = निर्णयः c ⊎ अवक्तव्यम् c` — two outcomes.  The verdict that
-- cannot drop its witness drops this one.
--
-- §2 is the theorem that makes the fourth outcome load-bearing rather
-- than decorative, and it is `Saptabhangi.दुर्नयः` one notch wider:
-- three seeds into two values must identify two, and so must four names.
-- The citation is not the point; the instantiation is.  A boolean verdict
-- over these four merges either "no subject" with "no witness", or
-- "nothing lost" with "the loss" — and every one of those merges is the
-- durnaya the census exists to refuse.
--
-- §2 is proved here from scratch over four names.  Both `formal/cubical/`
-- and this library are pinned to Agda 2.8.0 with cubical v0.9 (see the
-- .agda-lib files); nothing is imported across the two trees.
--
-- Nirnaya's header carries a FIFTH name, तूष्णीम् — "the symbol outside
-- the vocabulary that silenced this naya" — which is neither an unposed
-- question nor an empty fibre.
------------------------------------------------------------------------

module Punaragamana.Adharmin_TheUnposedQuestionIsNotAnEmptyFibreAndTheCensusCannotSayIt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just)
open import Cubical.Data.Unit using (Unit* ; tt*)
open import Cubical.Relation.Nullary using (¬_)

open import Punaragamana.WholePartialDesa_TheFibreCensusIsATermAndItRefutesTheSequentialDiagnostic
  using (देश ; गणना)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 1.  प्रश्न and स्थान — the fourth outcome, one level up.
--
-- A प्रश्न is a question that may not have been posed.  `स्थान` is what
-- can be said about it, and it is a FUNCTION on the question rather than
-- a datatype over a map — which is the whole content: when there is no
-- map, there is nothing to index a `देश` by, and the honest residue is
-- not a fibre verdict but the absence of a subject to take one of.
------------------------------------------------------------------------

प्रश्न : Type ℓ → Type ℓ → Type ℓ
प्रश्न A B = Maybe (A → B)

स्थान : {A B : Type ℓ} → प्रश्न A B → Type ℓ
स्थान         nothing  = Unit*       -- अधर्मिन् : no subject; no fibre to take
स्थान {B = B} (just f) = गणना f      -- the census applies

-- the honest residue exists and carries nothing, which is the point:
-- it is not a claim about a map, because there is no map to claim about.
अधर्मिन् : {A B : Type ℓ} → स्थान {A = A} {B = B} nothing
अधर्मिन् = tt*

------------------------------------------------------------------------
-- 2.  चतुर्-दुर्नयः — four names into two values must merge two.
--
-- `Saptabhangi.दुर्नयः` proves this for the three seeds asti / nāsti /
-- avaktavya.  With the unposed question the outcomes are four, and the
-- same pigeonhole applies a notch wider.  The merge a boolean forces is
-- always one of the ones the whole apparatus exists to refuse.
------------------------------------------------------------------------

data चतुष्कम् : Type₀ where
  अधर्मिन्-पदम्  : चतुष्कम्   -- no subject: the question was not posed
  सकलादेश-पदम्  : चतुष्कम्   -- contractible fibre: nothing lost
  विकलादेश-पदम् : चतुष्कम्   -- crowded fibre: the loss
  अवक्तव्यम्-पदम् : चतुष्कम्   -- empty fibre: not sayable, and NOT a loss

-- distinctness, by a code into a four-element type
कोड : चतुष्कम् → Bool × Bool
कोड अधर्मिन्-पदम्   = false , false
कोड सकलादेश-पदम्   = false , true
कोड विकलादेश-पदम्  = true  , false
कोड अवक्तव्यम्-पदम्  = true  , true

भिन्नम् : चतुष्कम् → चतुष्कम् → Type₀
भिन्नम् x y = ¬ (कोड x ≡ कोड y)

-- the four merges a boolean can be forced into, named
अधर्मिन्≢अवक्तव्यम् : भिन्नम् अधर्मिन्-पदम् अवक्तव्यम्-पदम्
अधर्मिन्≢अवक्तव्यम् p = false≢true (cong fst p)

सकलादेश≢विकलादेश : भिन्नम् सकलादेश-पदम् विकलादेश-पदम्
सकलादेश≢विकलादेश p = false≢true (cong fst p)

अधर्मिन्≢सकलादेश : भिन्नम् अधर्मिन्-पदम् सकलादेश-पदम्
अधर्मिन्≢सकलादेश p = false≢true (cong snd p)

विकलादेश≢अवक्तव्यम् : भिन्नम् विकलादेश-पदम् अवक्तव्यम्-पदम्
विकलादेश≢अवक्तव्यम् p = false≢true (cong snd p)

अधर्मिन्≢विकलादेश : भिन्नम् अधर्मिन्-पदम् विकलादेश-पदम्
अधर्मिन्≢विकलादेश p = false≢true (cong fst p)

सकलादेश≢अवक्तव्यम् : भिन्नम् सकलादेश-पदम् अवक्तव्यम्-पदम्
सकलादेश≢अवक्तव्यम् p = false≢true (cong fst p)

-- THE THEOREM.  Any two-valued verdict on the four identifies two of them
-- that are distinct.  Proved by exhaustion on the verdict's four values —
-- sixteen cases, and in every one a merged pair is produced, not merely
-- asserted to exist.
चतुर्-दुर्नयः : (v : चतुष्कम् → Bool)
             → Σ[ x ∈ चतुष्कम् ] Σ[ y ∈ चतुष्कम् ] (भिन्नम् x y × (v x ≡ v y))
-- `with` will not serve here, and the reason is worth one line: the goal
-- mentions `v` at BOUND variables, not at the four literals, so there is
-- nothing in it for `with` to abstract.  The equations are carried
-- explicitly instead.
चतुर्-दुर्नयः v =
  विचारः (v अधर्मिन्-पदम्) (v सकलादेश-पदम्) (v विकलादेश-पदम्) (v अवक्तव्यम्-पदम्)
         refl refl refl refl
  where
    विचारः : (a s w k : Bool)
           → v अधर्मिन्-पदम्  ≡ a → v सकलादेश-पदम्  ≡ s
           → v विकलादेश-पदम् ≡ w → v अवक्तव्यम्-पदम् ≡ k
           → Σ[ x ∈ चतुष्कम् ] Σ[ y ∈ चतुष्कम् ] (भिन्नम् x y × (v x ≡ v y))
    विचारः false false _ _ pa ps _  _  =
      अधर्मिन्-पदम् , सकलादेश-पदम्  , अधर्मिन्≢सकलादेश   , (pa ∙ sym ps)
    विचारः true  true  _ _ pa ps _  _  =
      अधर्मिन्-पदम् , सकलादेश-पदम्  , अधर्मिन्≢सकलादेश   , (pa ∙ sym ps)
    विचारः false true  false _ pa _ pw _  =
      अधर्मिन्-पदम् , विकलादेश-पदम् , अधर्मिन्≢विकलादेश  , (pa ∙ sym pw)
    विचारः true  false true  _ pa _ pw _  =
      अधर्मिन्-पदम् , विकलादेश-पदम् , अधर्मिन्≢विकलादेश  , (pa ∙ sym pw)
    विचारः false true  true  true  _ ps _  pk =
      सकलादेश-पदम् , अवक्तव्यम्-पदम् , सकलादेश≢अवक्तव्यम्  , (ps ∙ sym pk)
    विचारः false true  true  false pa _ _  pk =
      अधर्मिन्-पदम् , अवक्तव्यम्-पदम् , अधर्मिन्≢अवक्तव्यम्  , (pa ∙ sym pk)
    विचारः true  false false true  pa _ _  pk =
      अधर्मिन्-पदम् , अवक्तव्यम्-पदम् , अधर्मिन्≢अवक्तव्यम्  , (pa ∙ sym pk)
    विचारः true  false false false _ ps pw _  =
      सकलादेश-पदम् , विकलादेश-पदम् , सकलादेश≢विकलादेश  , (ps ∙ sym pw)

------------------------------------------------------------------------
-- 3.  मौनं न निषेधः — silence is not denial.
--
-- The operative corollary, and the one `Obstruction.hs` (absent from this repository) states in prose:
-- a naya declining to try is not a naya denying.  In the census's terms,
-- अधर्मिन् is not अवक्तव्यम् — the unposed question is not the empty fibre,
-- and it is not the crowded one either.  Any verdict that cannot tell
-- them apart has already committed the error, whatever it reports.
------------------------------------------------------------------------

मौनं-न-निषेधः : (v : चतुष्कम् → Bool)
              → v अधर्मिन्-पदम् ≡ v अवक्तव्यम्-पदम्
              → Σ[ x ∈ चतुष्कम् ] Σ[ y ∈ चतुष्कम् ] (भिन्नम् x y × (v x ≡ v y))
मौनं-न-निषेधः v p = अधर्मिन्-पदम् , अवक्तव्यम्-पदम् , अधर्मिन्≢अवक्तव्यम् , p
