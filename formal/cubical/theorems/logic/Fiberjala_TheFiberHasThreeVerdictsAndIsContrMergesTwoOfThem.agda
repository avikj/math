{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- तन्तुजालम् — तन्तोः त्रयो निर्णयाः ; isContr द्वौ मेलयति ।
--
-- (the fiber has three verdicts, and `isContr` merges two of them.)
--
-- WHAT THIS IS FOR.  It is the CODOMAIN of a census.  A tool that walks this
-- corpus asking "is this datum determined?" needs somewhere to put its
-- answer, and if that somewhere is `Bool` the tool commits the very collapse
-- the corpus exists to refuse.  `Saptabhangi.दुर्नयः` proves it: ANY
-- two-valued verdict on three seeds identifies two of them.  §४ instantiates
-- that at the fiber, so the claim is not an analogy.
--
-- THE THREE VERDICTS, and the whole content is that they are THREE.
--
--   रिक्तम्  the fiber is EMPTY.  नष्टि / अवक्तव्यम्: there is no return, and
--          there is nothing to carry.  No `Carrier`, no `ua`, nothing to
--          transport.  §५ of अहिंसा-सूत्र-विस्तारः: अप्रतिकार्यम्.
--   एकम्    the fiber is CONTRACTIBLE.  पुनरागमन: the datum is determined,
--          rides free, and `singl` gives it with no hypothesis whatever.
--   बहु     the fiber has TWO DISTINCT POINTS.  Not a failure — the fiber is
--          the SUBJECT.  `TheFiberIsTheSubject`: the
--          obstruction reading calls it a barrier and stops; the भावना
--          reading calls it a set with a group acting on it and computes.
--
-- WHICH VERDICT YOU GET IS DECIDED BY WHICH SIDE OF `f a ≡ b` IS BOUND, and
-- that is the one-line criterion five independent lines of work in this
-- corpus arrived at separately:
--
--   bind b :  Σ[ b ∈ B ] (f a ≡ b)  =  singl (f a)   — एकम्, always, free.
--   bind a :  Σ[ a ∈ A ] (f a ≡ b)  =  fiber f b     — any of the three.
--
-- §२ is that sentence as two terms.  A determined datum carried as a FIELD
-- binds b; the same datum fixed as an INDEX binds a.  That is why
-- `Reduction A` is a Carrier and `SmithPresentation A B` is not, why the
-- kuaka's three slots refused, and why `Sol D k` is a level set rather
-- than a graph.
--
-- AND THE AGGREGATE IS ALREADY IN THE LIBRARY.  `isEquiv f` IS
-- `(b : B) → isContr (fiber f b)` — एकम् at every point at once, which is
-- सकलादेश and not a search with a first step.  §६ records that, and records
-- what it buys: when every fiber is एकम्, base and carried may be EXCHANGED,
-- so storing and generating are the same type — §४१ सारणी वा क्रिया as an
-- identity rather than a trade.
--
-- What exists in the corpus is
-- `NastaUddista_TheRankUnrankAlgebraTheMachineRunsOn.प्रस्तारः`, and it gives
--
--     प्रस्तारः : (rs : List ℕ) → Iso (अङ्कस्थान rs) (Fin (सङ्ख्या rs))
--
-- — a FINITE type, at each fixed छेद-सूची rs, from two separately proved
-- procedures (उद्दिष्ट by addition and multiplication, नष्ट by division) with
-- no table stored.  By univalence that is `अङ्कस्थान rs ≡ Fin (सङ्ख्या rs)`,
-- and at rs = [] it reads `Unit ≡ Fin 1`.
--
-- The exchange claim is that at each rs the space of
-- stored patterns and the range of indices are equal AS TYPES, so keeping the
-- सारणी and running the क्रिया are one object.  §४१ is an identity.
------------------------------------------------------------------------

module Fiberjala_TheFiberHasThreeVerdictsAndIsContrMergesTwoOfThem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber ; isEquiv ; equivIsEquiv ; idEquiv)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Unit using (Unit ; tt ; isContrUnit)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

import Saptabhangi as S

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- १ · त्रयो निर्णयाः — the three, as types.
------------------------------------------------------------------------

module _ {A : Type ℓ} {B : Type ℓ'} (f : A → B) where

  रिक्तम् : B → Type (ℓ-max ℓ ℓ')
  रिक्तम् b = ¬ (fiber f b)

  एकम् : B → Type (ℓ-max ℓ ℓ')
  एकम् b = isContr (fiber f b)

  बहु : B → Type (ℓ-max ℓ ℓ')
  बहु b = Σ[ x ∈ fiber f b ] Σ[ y ∈ fiber f b ] (¬ (x ≡ y))

  ----------------------------------------------------------------------
  -- २ · कस्मिन् पक्षे बद्धम् — which side is bound.
  --
  -- Binding the SECOND coordinate is `singl`, contractible with no
  -- hypothesis at all.  Binding the FIRST is `fiber`, which is any of the
  -- three.  One equation, two readings, opposite verdicts — and that is
  -- the whole criterion.
  ----------------------------------------------------------------------

  वहनम् : A → Type ℓ'
  वहनम् a = Σ[ b ∈ B ] (f a ≡ b)      -- bind b: the graph fiber

  प्रतिबिम्बम् : B → Type (ℓ-max ℓ ℓ')
  प्रतिबिम्बम् b = Σ[ a ∈ A ] (f a ≡ b) -- bind a: the preimage

  वहनम्-सदा-एकम् : (a : A) → isContr (वहनम् a)
  वहनम्-सदा-एकम् a = isContrSingl (f a)

  -- and the preimage IS the fiber, definitionally: the two readings differ
  -- only in which variable the Σ binds.
  प्रतिबिम्बम्-तन्तुः : (b : B) → प्रतिबिम्बम् b ≡ fiber f b
  प्रतिबिम्बम्-तन्तुः _ = refl

  ----------------------------------------------------------------------
  -- ३ · परस्पर-विरोधः — the three exclude one another.
  ----------------------------------------------------------------------

  रिक्त-एक-विरोधः : (b : B) → रिक्तम् b → एकम् b → ⊥
  रिक्त-एक-विरोधः b r e = r (e .fst)

  रिक्त-बहु-विरोधः : (b : B) → रिक्तम् b → बहु b → ⊥
  रिक्त-बहु-विरोधः b r m = r (m .fst)

  एक-बहु-विरोधः : (b : B) → एकम् b → बहु b → ⊥
  एक-बहु-विरोधः b e (x , y , x≢y) =
    x≢y (sym (e .snd x) ∙ e .snd y)

------------------------------------------------------------------------
-- ४ · दुर्नयः तन्तौ — THE POINT.  A two-valued verdict must merge two.
--
-- `Saptabhangi.दुर्नयः` says: any `f : सप्तभङ्गी → द्विपद` identifies two of
-- अस्ति / नास्ति / अवक्तव्य.  Read the three fiber verdicts as those three
-- seeds — रिक्तम् is अवक्तव्य (nothing sayable), एकम् is अस्ति, बहु is नास्ति —
-- and the conclusion transfers verbatim: a census whose answer type has two
-- values CANNOT distinguish the three, whatever it computes.
--
-- Stated by instantiating the existing theorem rather than reproving it.
------------------------------------------------------------------------

द्विपद-निर्णयो-मेलयति :
    (v : S.सप्तभङ्गी → S.द्विपद)
  →  (v S.स्यात्-अस्ति ≡ v S.स्यात्-नास्ति)
  ⊎ ((v S.स्यात्-अस्ति ≡ v S.स्यात्-अवक्तव्यम्)
  ⊎  (v S.स्यात्-नास्ति ≡ v S.स्यात्-अवक्तव्यम्))
द्विपद-निर्णयो-मेलयति = S.दुर्नयः

------------------------------------------------------------------------
-- ५ · न-एकम् किम् इति न वदति — "not contractible" does not say which.
--
-- The load-bearing half.  Two maps, both failing एकम् at a point, for
-- OPPOSITE reasons.  A verdict that reports only `¬ एकम्` has destroyed the
-- distinction between "nothing is there" and "the subject is there".
------------------------------------------------------------------------

-- रिक्त side: the map ⊥ → Unit misses tt.
शून्य-मार्गः : ⊥ → Unit
शून्य-मार्गः ()

रिक्तम्-अत्र : रिक्तम् शून्य-मार्गः tt
रिक्तम्-अत्र ()

-- बहु side: the map Bool → Unit collapses two points onto tt.
समाहार-मार्गः : Bool → Unit
समाहार-मार्गः _ = tt

बहु-अत्र : बहु समाहार-मार्गः tt
बहु-अत्र = (true , refl) , (false , refl) , λ p → true≢false (cong fst p)

-- Both fail एकम्, and nothing in that failure separates them.
उभयत्र-न-एकम् : (¬ एकम् शून्य-मार्गः tt) × (¬ एकम् समाहार-मार्गः tt)
उभयत्र-न-एकम् =
    (λ e → रिक्तम्-अत्र (e .fst))
  , (λ e → एक-बहु-विरोधः समाहार-मार्गः tt e बहु-अत्र)

------------------------------------------------------------------------
-- ६ · सकलादेशः — the aggregate, and it is already the library's.
--
-- `isEquiv f` is DEFINITIONALLY "एकम् at every b".  So the total verdict is
-- not a search with a first step — it is a census over the whole codomain
-- at once, which is exactly सकलादेश against विकलादेश.  It is a RECORD wrapping
-- that Π rather than the Π itself, so the two directions are one projection
-- and one copattern -- not refl, and saying so is the honest form.
------------------------------------------------------------------------

सकलादेशः : {A : Type ℓ} {B : Type ℓ'} (f : A → B)
         → isEquiv f → (b : B) → एकम् f b
सकलादेशः f = isEquiv.equiv-proof

सकलादेश-प्रत्यागमः : {A : Type ℓ} {B : Type ℓ'} (f : A → B)
                  → ((b : B) → एकम् f b) → isEquiv f
isEquiv.equiv-proof (सकलादेश-प्रत्यागमः f g) = g

-- and when the census comes back एकम् everywhere, base and carried may be
-- exchanged: `NastaUddista_….प्रस्तारः` gives `अङ्कस्थान rs ≡ Fin (सङ्ख्या rs)`
-- from exactly this, so at each छेद-सूची storing and generating are one type.
-- The identity is the smallest instance.
समता-मार्गः : {A : Type ℓ} → (b : A) → एकम् (λ (a : A) → a) b
समता-मार्गः {A = A} b = isEquiv.equiv-proof (equivIsEquiv (idEquiv A)) b

------------------------------------------------------------------------
-- ७ · शेषः — what a census still cannot say, and it is not on this axis.
--
-- रिक्तम् is "the question was posed and the answer is nowhere".  It is NOT
-- "no question was posed" — `interactive/Obstruction.hs` (absent from this repository) carries that as a
-- separate constructor (`Sthana = Position Bhanga | ADharmin`, "x != y has
-- no subject, so no bhanga"), and `Saptabhangi.समावेश-भेदः` puts it in the
-- types as the `⊎ Unit`: सप्तभङ्गी plus one void profile, अ-प्रतिपादनम्.
-- A fiber census reads a GIVEN map at a GIVEN point; where there is no
-- dharmin there is no map to take a fiber of, and this module is silent.
-- `Loss.Adharmin_…` treats that case; the two are complements and
-- neither subsumes the other.
------------------------------------------------------------------------
