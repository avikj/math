{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Krama — what a recitation order cannot seat at any price.
--
-- Dvipha showed a family whose cost falls from three anubandhas to two
-- when a sound may be recited twice.  That reads as an economy: repetition
-- saves a marker.  It is not an economy.  It lifts an OBSTRUCTION, and the
-- gap is not one marker but every marker there is.
--
-- SOURCE.  Pini, *Adhyy* 1.1.71 dir antyena sahet, over the
-- fourteen Mhevara-stras: the sounds in one recited line, classes named
-- as the stretch from a sound to an antya.  *Krama* is the tradition's word
-- for sequence — the krama-pāṭha is the first of the vikṛti recitations
-- (Prtikhya literature, ~500 BCE), where the order itself is the object
-- under discipline.  Here the object is likewise the order, and the
-- question is what orders can hold.
--
-- THE FAMILY.  Three sounds a b c; the three two-element classes
--
--     C = { {a b}, {b c}, {a c} }
--
-- pairwise ⊆-incomparable (§2), so width 3 and
-- `PratyaharaLaghava.markersDistinct` forces three anubandhas.
--
--   §3  `कदापि-न-आसीदति` — NO recitation order seats C, at ANY number of
--       anubandhas, when each sound is recited once.  Exhaustive over the
--       six orders in their marker-saturated form.
--   §4  `आवृत्त्या-आसीदति` — with repetition, three anubandhas seat C:
--       a b M₁ c a M₂ b c M₃.  Exactly the width.  The bound is attained.
--
-- So on this family μ₀ = ∞ and μ_∞ = 3 = width.  Repetition is not a
-- discount on the marker count.  It is the difference between nameable and
-- not nameable at all.
--
-- WHY SIX LINES ARE THE WHOLE SPACE (the WLOG, and it is airtight rather
-- than convenient).  Let L be any recited-once line naming C.  All three
-- sounds occur in L, each once, so L's sounds are one of six orders, and
-- every anubandha of L sits in one of the four gaps that order leaves.
-- Now: ADDING an anubandha never removes a class.  Inserting a marker into
-- L leaves the sound content of every stretch untouched — `prefixBefore m'`
-- for an existing m' gains at most an interleaved marker, `suffixFromLast s`
-- likewise, and a class is recorded by which SOUNDS it meets, markers being
-- boundaries and never members.  So every class of L is a class of the
-- saturated line for L's order, which carries a marker in all four gaps.
-- Six saturated lines therefore name a superset of everything any
-- recited-once line names, at any marker count whatsoever, and §3 checks
-- all six.  A marker in the first gap precedes no sound and names nothing;
-- it is kept so the saturation is visibly complete rather than pruned.
--
-- WHY, underneath the exhaustion.  `Antya.…` proves that a class is always
-- the suffix, from the nearest preceding recitation, of the stretch before
-- its antya — hence a contiguous factor of the line.  Recited once, the
-- sounds of a contiguous factor are an INTERVAL of the order, and {a c} is
-- an interval of no order in which b lies between them, which every order
-- seating {a b} and {b c} must be.  Repetition breaks this because a sound
-- gets a second position: `Antya.स्वच्छादिः-अन्त्येन` asks freshness only
-- to the RIGHT of the start, and never asks anything of what stands left.
-- That is the whole mechanism, and it is why the obstruction is not a cost.
--
--   * The Siva-sutra family contains such a cycle.  Three ATTESTED
--     pratyhras, restricted to the three sounds h y , are exactly C:
--
--        aṬ  = a i u ṛ ḷ e o ai au h y v r      ↾ {h y ś} = {h y}
--        śaL = ś ṣ s h                          ↾ {h y ś} = {ś h}
--        yaR = y v r l … k p ś ṣ s              ↾ {h y ś} = {y ś}
--
--     (sets recomputed from the fourteen stras, `machine/Astadhyayi.hs` (absent from this repository)
--     sivasutraTable; names from the attested list in
--     `machine/Pratyahara_TheIntervalDecisionProcedure.hs` (absent from this repository).)  h stands in
--     sūtra 5 (ha ya va ra Ṭ) and again in sūtra 14 (ha L) — before y, and
--     after ś — which is precisely the seat no single order provides.  So
--     the second h is not economy.  It is what makes the list nameable at
--     all.  That claim is proved in
--     `Vyavaya_TheAttestedTrioForcesATwiceRecitedSoundAndPaninisChoiceIsHa`.
--
-- Every claim is `refl`.
------------------------------------------------------------------------

module Order_NoRecitationOrderSeatsTheCycleSoRepetitionLiftsAnObstructionAndNotACost where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; _or_ ; if_then_else_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing) renaming (rec to mbRec)
open import Cubical.Data.Nat using (ℕ)

------------------------------------------------------------------------
-- §1  Three sounds, four anubandha positions, and the extractor.
--
-- The extractor is the one proved general in
-- `Antya_OneAnubandhaCarriesEveryFreshStartSuffixSoAChainCostsOneMarker`:
-- first occurrence of the antya cuts the stretch, last occurrence of the
-- start opens it.  It is restated over this alphabet rather than imported,
-- because Antya's public instantiation is at Dvipha's alphabet; the
-- defining equations are the same ones and Antya's §5 already shows what
-- such an agreement looks like when it is proved.
------------------------------------------------------------------------

data Akṣara : Type where
  a b c            : Akṣara      -- three sounds
  M₁ M₂ M₃ M₄      : Akṣara      -- four anubandha occurrences

eqA : Akṣara → Akṣara → Bool
eqA a  a  = true
eqA b  b  = true
eqA c  c  = true
eqA M₁ M₁ = true
eqA M₂ M₂ = true
eqA M₃ M₃ = true
eqA M₄ M₄ = true
eqA _  _  = false

anyL : {A : Type} → (A → Bool) → List A → Bool
anyL f []       = false
anyL f (x ∷ xs) = f x or anyL f xs

allL : {A : Type} → (A → Bool) → List A → Bool
allL f []       = true
allL f (x ∷ xs) = f x and allL f xs

sounds : List Akṣara
sounds = a ∷ b ∷ c ∷ []

antyas : List Akṣara
antyas = M₁ ∷ M₂ ∷ M₃ ∷ M₄ ∷ []

data Sig : Type where
  sg : Bool → Bool → Bool → Sig

occurs : Akṣara → List Akṣara → Bool
occurs y xs = anyL (λ x → eqA x y) xs

sig : List Akṣara → Sig
sig xs = sg (occurs a xs) (occurs b xs) (occurs c xs)

eqB : Bool → Bool → Bool
eqB true  y = y
eqB false y = not y

eqSig : Sig → Sig → Bool
eqSig (sg p q r) (sg u v w) = eqB p u and (eqB q v and eqB r w)

prefixBefore : Akṣara → List Akṣara → Maybe (List Akṣara)
prefixBefore m []       = nothing
prefixBefore m (x ∷ xs) =
  if eqA x m
  then just []
  else mbRec nothing (λ r → just (x ∷ r)) (prefixBefore m xs)

suffixFromLast : Akṣara → List Akṣara → Maybe (List Akṣara)
suffixFromLast s []       = nothing
suffixFromLast s (x ∷ xs) =
  mbRec (if eqA x s then just (x ∷ xs) else nothing) just (suffixFromLast s xs)

klass : Akṣara → Akṣara → List Akṣara → Maybe Sig
klass s m line =
  mbRec nothing
        (λ p → mbRec nothing (λ q → just (sig q)) (suffixFromLast s p))
        (prefixBefore m line)

names : List Akṣara → Sig → Bool
names line t =
  anyL (λ s → anyL (λ m → mbRec false (λ u → eqSig u t) (klass s m line)) antyas) sounds

------------------------------------------------------------------------
-- §2  The cycle, and its ⊆-width is three: all three pairwise
--     incomparable, so three anubandhas are forced and no fewer.
------------------------------------------------------------------------

चक्रम् : List Sig
चक्रम् =  sg true  true  false          -- {a b}
       ∷  sg false true  true           -- {b c}
       ∷  sg true  false true           -- {a c}
       ∷ []

impl : Bool → Bool → Bool
impl p q = not p or q

sub : Sig → Sig → Bool
sub (sg p q r) (sg u v w) = impl p u and (impl q v and impl r w)

comparable : Sig → Sig → Bool
comparable p q = sub p q or sub q p

-- every distinct pair of the cycle is incomparable: width three exactly
विस्तारः-त्रयम् : allL (λ p → allL (λ q →
                    if not (eqSig p q) then not (comparable p q) else true) चक्रम्) चक्रम्
                  ≡ true
विस्तारः-त्रयम् = refl

seats : List Akṣara → Bool
seats line = allL (names line) चक्रम्

------------------------------------------------------------------------
-- §3  The six recitation orders, saturated with anubandhas in all four
--     gaps.  Not one of them seats the cycle — so no recited-once line
--     does, at any marker count.  (The WLOG that makes these six the whole
--     space is in the header, and the saturation is why "at any marker
--     count" is not an overreach: adding markers never removes a class.)
------------------------------------------------------------------------

पूर्णाः-क्रमाः : List (List Akṣara)
पूर्णाः-क्रमाः =
    (M₁ ∷ a ∷ M₂ ∷ b ∷ M₃ ∷ c ∷ M₄ ∷ [])
  ∷ (M₁ ∷ a ∷ M₂ ∷ c ∷ M₃ ∷ b ∷ M₄ ∷ [])
  ∷ (M₁ ∷ b ∷ M₂ ∷ a ∷ M₃ ∷ c ∷ M₄ ∷ [])
  ∷ (M₁ ∷ b ∷ M₂ ∷ c ∷ M₃ ∷ a ∷ M₄ ∷ [])
  ∷ (M₁ ∷ c ∷ M₂ ∷ a ∷ M₃ ∷ b ∷ M₄ ∷ [])
  ∷ (M₁ ∷ c ∷ M₂ ∷ b ∷ M₃ ∷ a ∷ M₄ ∷ [])
  ∷ []

षट्-एव : length पूर्णाः-क्रमाः ≡ 6
षट्-एव = refl

कदापि-न-आसीदति : allL (λ l → not (seats l)) पूर्णाः-क्रमाः ≡ true
कदापि-न-आसीदति = refl

-- and the failure is not that these lines name nothing: each saturated
-- order does seat TWO of the three, and only the third is out of reach.
द्वयं-तु-आसीदति : allL (λ l → names l (sg true true false) and names l (sg false true true))
                       ((M₁ ∷ a ∷ M₂ ∷ b ∷ M₃ ∷ c ∷ M₄ ∷ []) ∷ [])
                  ≡ true
द्वयं-तु-आसीदति = refl

तृतीयं-न : names (M₁ ∷ a ∷ M₂ ∷ b ∷ M₃ ∷ c ∷ M₄ ∷ []) (sg true false true) ≡ false
तृतीयं-न = refl

------------------------------------------------------------------------
-- §4  Recited twice, three anubandhas seat it — and three is the width,
--     so the antichain bound is attained exactly.  a, b and c are each
--     recited a second time; each second recitation is the fresh start
--     that `Antya.स्वच्छादिः-अन्त्येन` asks for, and nothing is asked of
--     the earlier ones.
------------------------------------------------------------------------

आवृत्तिः : List Akṣara
आवृत्तिः = a ∷ b ∷ M₁ ∷ c ∷ a ∷ M₂ ∷ b ∷ c ∷ M₃ ∷ []

आवृत्त्या-आसीदति : seats आवृत्तिः ≡ true
आवृत्त्या-आसीदति = refl

-- the three classes, named, so the reading is not left to the reader
प्रथमा : klass a M₁ आवृत्तिः ≡ just (sg true true false)
प्रथमा = refl

द्वितीया : klass c M₂ आवृत्तिः ≡ just (sg true false true)
द्वितीया = refl

तृतीया : klass b M₃ आवृत्तिः ≡ just (sg false true true)
तृतीया = refl

-- Remove the second recitations and saturate with every anubandha: the
-- line collapses to §3's first order and stops seating the cycle.  The
-- difference is the repetition and nothing else.
लुप्ता-आवृत्तिः : seats (M₁ ∷ a ∷ M₂ ∷ b ∷ M₃ ∷ c ∷ M₄ ∷ []) ≡ false
लुप्ता-आवृत्तिः = refl

------------------------------------------------------------------------
-- THE RESTRICTION STEP.
-- `Vyavaya_TheAttestedTrioForcesATwiceRecitedSoundAndPaninis-
-- ChoiceIsHa.agda` (absent from this repository) proves the restriction step: on the
-- full fourteen-stra line (all 57 tokens, encoded), a, aL, yaR
-- compute by refl and restrict to exactly the cycle above — and the
-- impossibility is proved over ALL lines reciting h y  once each, via
-- class ⟹ contiguous factor ⟹ factor of the restriction, with the
-- split-enumeration carrying a completeness proof.  Not an exhaustion
-- over lines.
------------------------------------------------------------------------
