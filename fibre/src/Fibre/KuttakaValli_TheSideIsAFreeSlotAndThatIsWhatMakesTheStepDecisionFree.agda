{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- कुट्टकवल्ली — पक्षः स्वतन्त्रः, तेन पदं निर्विचारम् ।
-- (the pulveriser's creeper: the side is a free slot, and keeping it is
--  what makes the step decision-free.)
--
-- SOURCE.  Āryabhaṭa, *Āryabhaṭīya*, गणितपाद 32–33, 499 CE — the कुट्टक,
-- whose instruction is "शेषं रक्ष", keep the remainder, and whose result
-- is read back by climbing the वल्ली (the creeper, the column of
-- quotients).  The three slots named here — पक्षः (side), परिमाणम्
-- (magnitude), शेषः (remainder) — are the quantities that survive one
-- round of the descent.
--
------------------------------------------------------------------------
-- WHICH SLOTS ARE BASE AND WHICH ARE CARRIED.
--
-- The honest answer is that ALL THREE SLOTS ARE BASE.  None of the three
-- is a function of the other two, and this is not an opinion here: it is
-- three theorems, `पक्षः-न-निर्धारितः`, `परिमाणम्-न-निर्धारितम्`,
-- `शेषः-न-निर्धारितः`, each exhibiting two त्रिक् that agree on two slots,
-- disagree on the third, and are provably distinct.  So there is no
-- Carrier whose base is two of the slots and whose carried datum is the
-- third.  Attempting one does not typecheck, and that is the law working.
--
-- What IS determined is the PAIR.  उत्थान : त्रिक् → ℕ × ℕ reads the pair
-- (a , b) back out of the record, and the pair is a function of the
-- record.  So the instance is
--
--     कुट्टक = Carrier उत्थान ,     base = त्रिक् ,     carried = ℕ × ℕ.
--
-- and the fibre Σ[ p ∈ ℕ × ℕ ] (उत्थान t ≡ p) = singl (उत्थान t) is
-- contractible, so त्रिक् ≃ कुट्टक and, by univalence, त्रिक् ≡ कुट्टक.
--
-- WHY THIS IS THE INTERESTING DIRECTION.  `वल्ली`, the step, is a total
-- function त्रिक् → त्रिक् written with NO comparison, NO `Dec`, NO `Bool`
-- — because पक्षः has already recorded which side the remainder fell on.
-- The subtractive Euclidean step needs a decision only for a base that
-- has thrown that slot away.  `वल्ली-वाम` / `वल्ली-दक्षिण` below prove that
-- this decision-free step IS the Euclidean one in pair coordinates:
-- (a , b) ↦ (a − b , b) when a > b, and (a , b − a) when b > a.
--
-- DEFECT, written rather than hidden.  `-` (the round trip
-- उत्थान (भेद a b) ≡ (a , b)) is the same statement as `पुनरागमनम्` in
-- `formal/cubical/Punaragamana.agda` (absent from this repository), and is reproved here.  That is a
-- duplication.  It is deliberate: this library takes no dependency
-- outside itself, and the alternative — importing across the repository
-- — would make `check.sh` (absent from this repository) no longer check what it says it checks.
--
-- `वल्ली` is the SUBTRACTIVE step (anthyphairesis), not
-- the division step a … a mod b.
-- getting it without a decision procedure is not done here.  The 
-- of the *ryabhaya* is the column of QUOTIENTS; what is formalised
-- below is the column of subtractions that produces them.  Anything
-- below that says "वल्ली" means the subtractive column.
------------------------------------------------------------------------

module Fibre.KuttakaValli_TheSideIsAFreeSlotAndThatIsWhatMakesTheStepDecisionFree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; znots; snotz; injSuc)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)

open import Fibre.Carrier
open import Fibre.Orbit

private
  ¬_ : Type → Type
  ¬ A = A → ⊥

------------------------------------------------------------------------
-- पक्षः — the side, as a type of its own, so that "which side" is a
-- projectable coordinate and not an implicit fact about a constructor.
------------------------------------------------------------------------

data पक्ष : Type where
  समः वामः दक्षिणः : पक्ष

पक्ष-कोड : पक्ष → Type
पक्ष-कोड समः    = Unit
पक्ष-कोड वामः   = ⊥
पक्ष-कोड दक्षिणः = ⊥

पक्ष-कोड' : पक्ष → Type
पक्ष-कोड' समः    = ⊥
पक्ष-कोड' वामः   = Unit
पक्ष-कोड' दक्षिणः = ⊥

वामः≢दक्षिणः : ¬ (वामः ≡ दक्षिणः)
वामः≢दक्षिणः p = subst पक्ष-कोड' p tt

------------------------------------------------------------------------
-- त्रिक् — the three slots, one record.  पक्षः is the constructor,
-- परिमाणम् is d, शेषः is the excess.  सम carries no excess because there
-- is none: equality is not "remainder zero on a side", it is no side.
------------------------------------------------------------------------

data त्रिक् : Type where
  सम    : (d : ℕ)   → त्रिक्
  वाम   : (d k : ℕ) → त्रिक्
  दक्षिण : (d k : ℕ) → त्रिक्

पक्षः : त्रिक् → पक्ष
पक्षः (सम _)      = समः
पक्षः (वाम _ _)   = वामः
पक्षः (दक्षिण _ _) = दक्षिणः

परिमाणम् : त्रिक् → ℕ
परिमाणम् (सम d)      = d
परिमाणम् (वाम d _)   = d
परिमाणम् (दक्षिण d _) = d

शेषः : त्रिक् → ℕ
शेषः (सम _)      = zero
शेषः (वाम _ k)   = suc k
शेषः (दक्षिण _ k) = suc k

------------------------------------------------------------------------
-- NO SLOT IS A FUNCTION OF THE OTHER TWO.
--
-- Each theorem exhibits two records agreeing on two coordinates by refl,
-- disagreeing on the third, and provably distinct.  Together they say:
-- त्रिक् is not `Carrier g` for any g out of a two-slot base, because the
-- fibre of the forgetful map is not contractible — it has two points that
-- are not joined.
------------------------------------------------------------------------

पक्षः-न-निर्धारितः :
    (परिमाणम् (वाम zero zero) ≡ परिमाणम् (दक्षिण zero zero))
  × ((शेषः (वाम zero zero) ≡ शेषः (दक्षिण zero zero))
  × (¬ (वाम zero zero ≡ दक्षिण zero zero)))
पक्षः-न-निर्धारितः = refl , (refl , λ p → वामः≢दक्षिणः (cong पक्षः p))

परिमाणम्-न-निर्धारितम् :
    (पक्षः (वाम zero zero) ≡ पक्षः (वाम (suc zero) zero))
  × ((शेषः (वाम zero zero) ≡ शेषः (वाम (suc zero) zero))
  × (¬ (वाम zero zero ≡ वाम (suc zero) zero)))
परिमाणम्-न-निर्धारितम् = refl , (refl , λ p → znots (cong परिमाणम् p))

शेषः-न-निर्धारितः :
    (पक्षः (वाम zero zero) ≡ पक्षः (वाम zero (suc zero)))
  × ((परिमाणम् (वाम zero zero) ≡ परिमाणम् (वाम zero (suc zero)))
  × (¬ (वाम zero zero ≡ वाम zero (suc zero))))
शेषः-न-निर्धारितः = refl , (refl , λ p → znots (injSuc (cong शेषः p)))

------------------------------------------------------------------------
-- उत्थान — the pair IS a function of the record.  This is the f of the
-- law.  a = d + शेषः on the वाम side, b = d + शेषः on the दक्षिण side,
-- a = b = d at सम.
------------------------------------------------------------------------

उत्थान : त्रिक् → ℕ × ℕ
उत्थान (सम d)      = d , d
उत्थान (वाम d k)   = d + suc k , d
उत्थान (दक्षिण d k) = d , d + suc k

------------------------------------------------------------------------
-- THE INSTANCE.
------------------------------------------------------------------------

कुट्टक : Type
कुट्टक = Carrier उत्थान

-- the four coordinates of a कुट्टक: three from the base, one carried
कुट्टक-पक्षः : कुट्टक → पक्ष
कुट्टक-पक्षः c = पक्षः (base c)

कुट्टक-परिमाणम् : कुट्टक → ℕ
कुट्टक-परिमाणम् c = परिमाणम् (base c)

कुट्टक-शेषः : कुट्टक → ℕ
कुट्टक-शेषः c = शेषः (base c)

कुट्टक-युग्मम् : कुट्टक → ℕ × ℕ
कुट्टक-युग्मम् c = carried c

कुट्टक-प्रमाण : (c : कुट्टक) → उत्थान (base c) ≡ कुट्टक-युग्मम् c
कुट्टक-प्रमाण c = witness c

-- the fibre is singl, hence contractible; hence the equivalence and the path
कुट्टक-क्षेत्र-सम्पूर्ण : (t : त्रिक्) → isContr (fibre उत्थान t)
कुट्टक-क्षेत्र-सम्पूर्ण = fibre-isContr उत्थान

त्रिक्-Iso-कुट्टक : Iso त्रिक् कुट्टक
त्रिक्-Iso-कुट्टक = Carrier-Iso उत्थान

त्रिक्≃कुट्टक : त्रिक् ≃ कुट्टक
त्रिक्≃कुट्टक = Carrier≃ उत्थान

त्रिक्≡कुट्टक : त्रिक् ≡ कुट्टक
त्रिक्≡कुट्टक = Carrier≡ उत्थान

अवतरण : त्रिक् → कुट्टक
अवतरण = descend उत्थान

आरोहः : कुट्टक → त्रिक्
आरोहः = ascend उत्थान

परिवहन : त्रिक् → कुट्टक
परिवहन = carry-transport उत्थान

परिवहन-अवतरण : (t : त्रिक्) → परिवहन t ≡ अवतरण t
परिवहन-अवतरण = carry-transport-descend उत्थान

------------------------------------------------------------------------
-- भेद — the descent that manufactures the record from a pair.  Decisionless:
-- it falls by structure, deepening the shared magnitude one head at a time,
-- and at zero the side that outlasted names itself.
------------------------------------------------------------------------

गभीर : त्रिक् → त्रिक्
गभीर (सम d)      = सम (suc d)
गभीर (वाम d k)   = वाम (suc d) k
गभीर (दक्षिण d k) = दक्षिण (suc d) k

भेद : ℕ → ℕ → त्रिक्
भेद zero    zero    = सम zero
भेद zero    (suc b) = दक्षिण zero b
भेद (suc a) zero    = वाम zero a
भेद (suc a) (suc b) = गभीर (भेद a b)

गभीर-उत्थान : (t : त्रिक्)
            → उत्थान (गभीर t) ≡ (suc (fst (उत्थान t)) , suc (snd (उत्थान t)))
गभीर-उत्थान (सम d)      = refl
गभीर-उत्थान (वाम d k)   = refl
गभीर-उत्थान (दक्षिण d k) = refl

-- the round trip.  this is `पुनरागमनम्` of
-- formal/cubical/Punaragamana.agda (absent from this repository), reproved so the library stays standalone.
उत्थान-भेद : (a b : ℕ) → उत्थान (भेद a b) ≡ (a , b)
उत्थान-भेद zero    zero    = refl
उत्थान-भेद zero    (suc b) = refl
उत्थान-भेद (suc a) zero    = refl
उत्थान-भेद (suc a) (suc b) =
  गभीर-उत्थान (भेद a b)
  ∙ cong (λ p → (suc (fst p) , suc (snd p))) (उत्थान-भेद a b)

------------------------------------------------------------------------
-- वल्ली — THE STEP, as a Φ on the base.
--
-- Written with no comparison, because पक्षः already says which way to
-- subtract.  At सम the algorithm has terminated and the step is the
-- identity: the shared magnitude IS the gcd, and nothing further is done
-- to it.  A fixed point is the honest encoding of "stop" for a total
-- endomorphism, and it is what lets the orbit be infinite without lying.
------------------------------------------------------------------------

वल्ली : त्रिक् → त्रिक्
वल्ली (सम d)      = सम d
वल्ली (वाम d k)   = भेद (suc k) d
वल्ली (दक्षिण d k) = भेद d (suc k)

-- …and it IS the subtractive Euclidean step, in pair coordinates.
वल्ली-वाम : (d k : ℕ) → उत्थान (वल्ली (वाम d k)) ≡ (suc k , d)
वल्ली-वाम d k = उत्थान-भेद (suc k) d

वल्ली-दक्षिण : (d k : ℕ) → उत्थान (वल्ली (दक्षिण d k)) ≡ (d , suc k)
वल्ली-दक्षिण d k = उत्थान-भेद d (suc k)

वल्ली-सम : (d : ℕ) → वल्ली (सम d) ≡ सम d
वल्ली-सम d = refl

-- The magnitude at सम is the common value of the pair, and it is fixed
-- by every further step: the gcd, once reached, is carried forever.
सम-स्थिरम् : (d : ℕ) (n : ℕ) → iterate वल्ली n (सम d) ≡ सम d
सम-स्थिरम् d zero    = refl
सम-स्थिरम् d (suc n) = सम-स्थिरम् d n

------------------------------------------------------------------------
-- THE LIFT, AND THE SQUARE.
--
-- Φ-square is `refl`: it closes DEFINITIONALLY, for an opaque variable,
-- because Σ has eta and `descend` does not pattern match.
-- Both are instances of the law.
------------------------------------------------------------------------

वल्ली-कुट्टक : कुट्टक → कुट्टक
वल्ली-कुट्टक = Φ-carrier उत्थान वल्ली

वल्ली-वर्गः : (t : त्रिक्) → वल्ली-कुट्टक (अवतरण t) ≡ अवतरण (वल्ली t)
वल्ली-वर्गः = Φ-square उत्थान वल्ली

वल्ली-आरोहः : (c : कुट्टक) → आरोहः (वल्ली-कुट्टक c) ≡ वल्ली (आरोहः c)
वल्ली-आरोहः = Φ-ascend उत्थान वल्ली

वल्ली-परिवहन : (t : त्रिक्) → परिवहन (वल्ली t) ≡ अवतरण (वल्ली t)
वल्ली-परिवहन = Φ-transport उत्थान वल्ली

-- the carried pair is recomputed at every step, never stale
वल्ली-युग्मम् : (t : त्रिक्)
             → कुट्टक-युग्मम् (वल्ली-कुट्टक (अवतरण t)) ≡ उत्थान (वल्ली t)
वल्ली-युग्मम् t = refl

------------------------------------------------------------------------
-- THE ORBIT.  The whole run of the pulveriser as one object.
------------------------------------------------------------------------

वल्ली-जाल : Type
वल्ली-जाल = Orbit कुट्टक

बुन : त्रिक् → वल्ली-जाल
बुन t = unfold वल्ली-कुट्टक (अवतरण t)

------------------------------------------------------------------------
-- Each holds by refl, so Agda must actually execute the descent.
--
--   (137,60) → (77,60) → (17,60) → (17,43) → (17,26) → (17,9)
--          → (8,9) → (8,1) → (7,1) → … → (1,1) = सम 1
--
-- gcd(137,60) = 1, which is why 137 is invertible mod 60 at all.
------------------------------------------------------------------------

गणना-आरम्भः : उत्थान (भेद 137 60) ≡ (137 , 60)
गणना-आरम्भः = refl

गणना-प्रथमम् : उत्थान (वल्ली (भेद 137 60)) ≡ (77 , 60)
गणना-प्रथमम् = refl

गणना-अन्तः : iterate वल्ली 20 (भेद 137 60) ≡ सम 1
गणना-अन्तः = refl

गणना-कुट्टक : कुट्टक-युग्मम् (lookup (बुन (भेद 137 60)) 20) ≡ (1 , 1)
गणना-कुट्टक = refl

-- and a case where the gcd is not 1: gcd(48,18) = 6
गणना-षट् : iterate वल्ली 10 (भेद 48 18) ≡ सम 6
गणना-षट् = refl
