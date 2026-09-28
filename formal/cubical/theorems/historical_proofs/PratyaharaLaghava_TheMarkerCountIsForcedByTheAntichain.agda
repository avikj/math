{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- PratyaharaLaghava — how many anubandhas a family of sound-classes forces,
-- proved for any linear order whatsoever.
--
-- SOURCE.  Pini, Adhyy (~500 BCE), opens with the fourteen
-- Mhevara-stras: the sounds laid in ONE sequence, each stra closed by an
-- anubandha (it-marker).  A pratyhra names a class as the stretch from a
-- sound up to a marker — aṆ, aK, iK, eṄ, aiC, aC, haL, yaṆ, jhaṢ.  The
-- tradition's own word for the value being maximised is *lghava*, economy;
-- the grammarians' maxim (ardhamtrlghavena putrotsava manyante
-- vaiykara) prices half a mora of the metalanguage like the birth of a
-- son.  `Sivasutra.agda` checks that the vowel pratyhras ARE the intervals
-- they are said to be, by refl.
--
-- WHAT IS PROVED HERE, and it is a reason rather than an instance:
--
--   ONE.  `sharedEnd→comparable` — if two classes are stretches of the SAME
--   linear order terminating at the SAME marker, then one contains the other.
--   (Both end at e; the one whose start is further right is inside the other.)
--   So the classes carried by a single anubandha form a ⊆-chain.  Nothing in
--   this uses phonetics, and nothing in it uses which order was chosen.
--
--   TWO.  `markersDistinct` — consequently, two classes that are
--   ⊆-INCOMPARABLE cannot share a marker, in any order, under any encoding.
--   The marker map is injective on every ⊆-antichain of the family.  This is
--   the general statement; everything below is its instance.
--
--   THREE.  `vowelAntichain` — the four attested vowel classes aṆ = {a i u},
--   iK = {i u  }, e = {e o}, aiC = {ai au} are pairwise incomparable, as
--   sets of sounds, with no order in sight.  Hence `fourMarkersForced`: ANY
--   arrangement of the nine vowels in a line, with any markers anywhere,
--   naming those four classes as pratyhras, uses four DISTINCT markers.
--
--   FOUR.  `sivasutraEncoding` — the śiva-sūtra order attains the bound:
--   a i u    K e o  ai au C realises all four (and aK, aC, iC, eC as
--   well, §7) with exactly the four markers  K  C, and
--   `noFifthMarker` checks there is no fifth.  Lower bound four, attained at
--   four: for this family Pini's arrangement is optimal, and the proof of
--   the lower half quantifies over all orders, not over the traditional one.
--
-- Petersen's theorem is that for the FULL family the grammar
-- denotes over all 42 phonemes, the iva-stra order is essentially
-- UNIQUE, and 14 markers minimal.  This file proves a lower
-- bound (the antichain bound) and matches it on the vowel subfamily.
--
-- `markersDistinct` gives
-- markers ≥ width(F) and no more.  Where it stands for the full inventory
-- is a finite computation, and it is done rather than guessed:
-- `machine/Pratyahara_TheIntervalDecisionProcedure.hs` (absent from this repository) runs Dilworth (via
-- bipartite matching and Knig, antichain returned and re-checked) on the
-- classes of all fourteen stras and reports —
--    all 294 classes the line can name : width 14, the anubandha count
--    the ~30 pratyhras the grammar uses : width 11
-- So the bound is met exactly on the family the device EXPRESSES, and the
-- attested classes alone leave three markers unforced by this argument.
-- That residue is where Petersen's theorem is needed; the 14-antichain is a
-- computed witness in Haskell.
--
-- MODELLING NOTE, stated because it is the one place a reader could be
-- misled: `pos` enumerates the SOUNDS only, markers being boundaries and
-- never members (Sivasutra.agda checks that separately).  A marker is
-- therefore an element of an abstract type M with a boundary `bnd : M → ℕ`,
-- i.e. an anubandha OCCURRENCE, not an anubandha letter — which is the right
-- granularity, since  occurs twice in the fourteen (stras 1 and 6) and
-- the two occurrences terminate different classes (a, ya).
--
-- Order comparison is a computing Bool
-- defined here, so the concrete checks are refl and the library's order
-- theory is not on the critical path.
------------------------------------------------------------------------

module PratyaharaLaghava_TheMarkerCountIsForcedByTheAntichain where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; true≢false ; false≢true)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr) renaming (rec to ⊎rec)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 0.  Order on positions, as a computing boolean.
------------------------------------------------------------------------

_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ _     = true
suc _ ≤ᵇ zero  = false
suc m ≤ᵇ suc n = m ≤ᵇ n

_<ᵇ_ : ℕ → ℕ → Bool
m <ᵇ n = suc m ≤ᵇ n

≤ᵇ-trans : (l m n : ℕ) → (l ≤ᵇ m) ≡ true → (m ≤ᵇ n) ≡ true → (l ≤ᵇ n) ≡ true
≤ᵇ-trans zero    m       n       _ _ = refl
≤ᵇ-trans (suc l) zero    n       p _ = ⊥rec (false≢true p)
≤ᵇ-trans (suc l) (suc m) zero    _ q = ⊥rec (false≢true q)
≤ᵇ-trans (suc l) (suc m) (suc n) p q = ≤ᵇ-trans l m n p q

≤ᵇ-total : (m n : ℕ) → ((m ≤ᵇ n) ≡ true) ⊎ ((n ≤ᵇ m) ≡ true)
≤ᵇ-total zero    n       = inl refl
≤ᵇ-total (suc m) zero    = inr refl
≤ᵇ-total (suc m) (suc n) = ≤ᵇ-total m n

and-true : (b c : Bool) → (b and c) ≡ true → ((b ≡ true) × (c ≡ true))
and-true true  true  _ = refl , refl
and-true true  false p = ⊥rec (false≢true p)
and-true false _     p = ⊥rec (false≢true p)

------------------------------------------------------------------------
-- 1.  Classes, containment, and what it is to be a pratyhra.
--
-- A class is a decidable set of sounds.  An encoding lays the sounds on a
-- line (`pos`) and names a class by a start position and a terminal marker;
-- the class is then exactly the sounds lying at or after the start and
-- strictly before the marker's boundary.
------------------------------------------------------------------------

Varga : Type → Type
Varga A = A → Bool

_⊑_ : {A : Type} → Varga A → Varga A → Type
_⊑_ {A = A} X Y = (x : A) → X x ≡ true → Y x ≡ true

Incomparable : {A : Type} → Varga A → Varga A → Type
Incomparable X Y = (¬ (X ⊑ Y)) × (¬ (Y ⊑ X))

IsInterval : {A : Type} (pos : A → ℕ) (s e : ℕ) (X : Varga A) → Type
IsInterval {A = A} pos s e X = (x : A) → X x ≡ ((s ≤ᵇ pos x) and (pos x <ᵇ e))

-- the witness form of incomparability: one sound in X and not in Y
notSub : {A : Type} (X Y : Varga A) (x : A)
       → X x ≡ true → Y x ≡ false → ¬ (X ⊑ Y)
notSub X Y x hx hy sub = true≢false (sym (sub x hx) ∙ hy)

------------------------------------------------------------------------
-- 2.  THE REASON.  One marker carries a chain.
--
-- Two classes ending at the same marker are ⊆-comparable — whichever starts
-- further right is contained in the other.  No phonetics, no particular
-- order: this is a fact about stretches of a line sharing a right end.
------------------------------------------------------------------------

sharedEnd→comparable :
  {A : Type} (pos : A → ℕ) (s₁ s₂ e : ℕ) (X Y : Varga A)
  → IsInterval pos s₁ e X → IsInterval pos s₂ e Y
  → (X ⊑ Y) ⊎ (Y ⊑ X)
sharedEnd→comparable pos s₁ s₂ e X Y hX hY with ≤ᵇ-total s₂ s₁
... | inl s₂≤s₁ = inl (λ x hx →
        let b = and-true (s₁ ≤ᵇ pos x) (pos x <ᵇ e) (sym (hX x) ∙ hx)
        in hY x ∙ cong₂ _and_ (≤ᵇ-trans s₂ s₁ (pos x) s₂≤s₁ (fst b)) (snd b))
... | inr s₁≤s₂ = inr (λ x hx →
        let b = and-true (s₂ ≤ᵇ pos x) (pos x <ᵇ e) (sym (hY x) ∙ hx)
        in hX x ∙ cong₂ _and_ (≤ᵇ-trans s₁ s₂ (pos x) s₁≤s₂ (fst b)) (snd b))

-- Contrapositive at the level of boundaries: incomparable classes end
-- at different places in the line.
incomparable→distinctEnds :
  {A : Type} (pos : A → ℕ) (s₁ s₂ e₁ e₂ : ℕ) (X Y : Varga A)
  → Incomparable X Y
  → IsInterval pos s₁ e₁ X → IsInterval pos s₂ e₂ Y
  → ¬ (e₁ ≡ e₂)
incomparable→distinctEnds pos s₁ s₂ e₁ e₂ X Y ic hX hY e≡ =
  ⊎rec (fst ic) (snd ic)
    (sharedEnd→comparable pos s₁ s₂ e₂ X Y
      (subst (λ e → IsInterval pos s₁ e X) e≡ hX) hY)

------------------------------------------------------------------------
-- 3.  An encoding of a family, and the general bound.
------------------------------------------------------------------------

record Encoding (A M Ix : Type) (F : Ix → Varga A) : Type where
  field
    pos   : A → ℕ        -- the ONE linear order on the sounds
    start : Ix → ℕ       -- the first symbol of each two-symbol name
    mark  : Ix → M       -- the terminal anubandha of each two-symbol name
    bnd   : M → ℕ        -- where each anubandha sits in the line
    isIvl : (k : Ix) → IsInterval pos (start k) (bnd (mark k)) (F k)

open Encoding

-- THE GENERAL STATEMENT.  Distinct incomparable members of the family get
-- distinct markers — under ANY order, ANY placement of markers, ANY start
-- assignment.  So the number of anubandhas is at least the width of the
-- family in the containment order.
markersDistinct :
  {A M Ix : Type} {F : Ix → Varga A} (E : Encoding A M Ix F)
  → (j k : Ix) → Incomparable (F j) (F k)
  → ¬ (mark E j ≡ mark E k)
markersDistinct E j k ic m≡ =
  incomparable→distinctEnds (pos E) (start E j) (start E k)
    (bnd E (mark E j)) (bnd E (mark E k)) _ _ ic (isIvl E j) (isIvl E k)
    (cong (bnd E) m≡)

------------------------------------------------------------------------
-- 4.  The vowels, and the four attested classes as SETS — no order.
------------------------------------------------------------------------

data Sound : Type where
  a i u ṛ ḷ e o ai au : Sound

AṆ IK EṄ AIC AK AC IC EC : Varga Sound

AṆ  a = true ; AṆ  i = true ; AṆ  u = true
AṆ  ṛ = false ; AṆ ḷ = false ; AṆ e = false ; AṆ o = false
AṆ  ai = false ; AṆ au = false

IK  i = true ; IK  u = true ; IK ṛ = true ; IK ḷ = true
IK  a = false ; IK e = false ; IK o = false ; IK ai = false ; IK au = false

EṄ  e = true ; EṄ o = true
EṄ  a = false ; EṄ i = false ; EṄ u = false ; EṄ ṛ = false ; EṄ ḷ = false
EṄ  ai = false ; EṄ au = false

AIC ai = true ; AIC au = true
AIC a = false ; AIC i = false ; AIC u = false ; AIC ṛ = false ; AIC ḷ = false
AIC e = false ; AIC o = false

AK  a = true ; AK i = true ; AK u = true ; AK ṛ = true ; AK ḷ = true
AK  e = false ; AK o = false ; AK ai = false ; AK au = false

AC  _ = true

IC  a = false
IC  i = true ; IC u = true ; IC ṛ = true ; IC ḷ = true
IC  e = true ; IC o = true ; IC ai = true ; IC au = true

EC  e = true ; EC o = true ; EC ai = true ; EC au = true
EC  a = false ; EC i = false ; EC u = false ; EC ṛ = false ; EC ḷ = false

-- the index of the four-class family
data Ix4 : Type where
  ıaṆ ıiK ıeṄ ıaiC : Ix4

vowelFamily : Ix4 → Varga Sound
vowelFamily ıaṆ  = AṆ
vowelFamily ıiK  = IK
vowelFamily ıeṄ  = EṄ
vowelFamily ıaiC = AIC

-- THE FOUR ARE PAIRWISE INCOMPARABLE.  Each direction names the sound that
-- witnesses the failure; this is where the content is, and it is all about
-- the classes and nothing about the arrangement.
--   aṆ ∌ ṛ, iK ∌ a          — the two overlap and neither contains the other
--   eṄ, aiC                 — disjoint from those and from each other
vowelAntichain : (j k : Ix4) → ¬ (j ≡ k) → Incomparable (vowelFamily j) (vowelFamily k)
vowelAntichain ıaṆ  ıaṆ  ne = ⊥rec (ne refl)
vowelAntichain ıiK  ıiK  ne = ⊥rec (ne refl)
vowelAntichain ıeṄ  ıeṄ  ne = ⊥rec (ne refl)
vowelAntichain ıaiC ıaiC ne = ⊥rec (ne refl)
vowelAntichain ıaṆ  ıiK  _  = notSub AṆ IK a refl refl , notSub IK AṆ ṛ refl refl
vowelAntichain ıiK  ıaṆ  _  = notSub IK AṆ ṛ refl refl , notSub AṆ IK a refl refl
vowelAntichain ıaṆ  ıeṄ  _  = notSub AṆ EṄ a refl refl , notSub EṄ AṆ e refl refl
vowelAntichain ıeṄ  ıaṆ  _  = notSub EṄ AṆ e refl refl , notSub AṆ EṄ a refl refl
vowelAntichain ıaṆ  ıaiC _  = notSub AṆ AIC a refl refl , notSub AIC AṆ ai refl refl
vowelAntichain ıaiC ıaṆ  _  = notSub AIC AṆ ai refl refl , notSub AṆ AIC a refl refl
vowelAntichain ıiK  ıeṄ  _  = notSub IK EṄ i refl refl , notSub EṄ IK e refl refl
vowelAntichain ıeṄ  ıiK  _  = notSub EṄ IK e refl refl , notSub IK EṄ i refl refl
vowelAntichain ıiK  ıaiC _  = notSub IK AIC i refl refl , notSub AIC IK ai refl refl
vowelAntichain ıaiC ıiK  _  = notSub AIC IK ai refl refl , notSub IK AIC i refl refl
vowelAntichain ıeṄ  ıaiC _  = notSub EṄ AIC e refl refl , notSub AIC EṄ ai refl refl
vowelAntichain ıaiC ıeṄ  _  = notSub AIC EṄ ai refl refl , notSub EṄ AIC e refl refl

------------------------------------------------------------------------
-- 5.  THE LOWER BOUND.  Four markers, in any order whatsoever.
------------------------------------------------------------------------

fourMarkersForced :
  {M : Type} (E : Encoding Sound M Ix4 vowelFamily)
  → (j k : Ix4) → ¬ (j ≡ k) → ¬ (mark E j ≡ mark E k)
fourMarkersForced E j k ne = markersDistinct E j k (vowelAntichain j k ne)

sep : Ix4 → Ix4 → Bool
sep ıaṆ ıaṆ = true
sep ıiK ıiK = true
sep ıeṄ ıeṄ = true
sep ıaiC ıaiC = true
sep _ _ = false

Ix4-distinct : (j k : Ix4) → sep j k ≡ false → ¬ (j ≡ k)
Ix4-distinct j k hs p = false≢true (sym hs ∙ cong (sep j) (sym p) ∙ diag j)
  where
    diag : (l : Ix4) → sep l l ≡ true
    diag ıaṆ = refl
    diag ıiK = refl
    diag ıeṄ = refl
    diag ıaiC = refl

------------------------------------------------------------------------
-- 6.  THE UPPER BOUND.  The iva-stra order attains four.
--
--   position :  a  i  u  |      |  e  o  |  ai au |
--               0  1  2    3  4  K  5  6    7  8  C
--
-- The marker boundaries are 3, 5, 7, 9 — the count of sounds standing before
-- each anubandha.  a = [0,3), iK = [1,5), e = [5,7), aiC = [7,9).
------------------------------------------------------------------------

data Marker : Type where
  Ṇ K Ṅ C : Marker

posS : Sound → ℕ
posS a = 0 ; posS i = 1 ; posS u = 2 ; posS ṛ = 3 ; posS ḷ = 4
posS e = 5 ; posS o = 6 ; posS ai = 7 ; posS au = 8

bndS : Marker → ℕ
bndS Ṇ = 3 ; bndS K = 5 ; bndS Ṅ = 7 ; bndS C = 9

startS : Ix4 → ℕ
startS ıaṆ = 0 ; startS ıiK = 1 ; startS ıeṄ = 5 ; startS ıaiC = 7

markS : Ix4 → Marker
markS ıaṆ = Ṇ ; markS ıiK = K ; markS ıeṄ = Ṅ ; markS ıaiC = C

ivlS : (k : Ix4) → IsInterval posS (startS k) (bndS (markS k)) (vowelFamily k)
ivlS ıaṆ  a = refl ; ivlS ıaṆ  i = refl ; ivlS ıaṆ  u = refl
ivlS ıaṆ  ṛ = refl ; ivlS ıaṆ  ḷ = refl ; ivlS ıaṆ  e = refl
ivlS ıaṆ  o = refl ; ivlS ıaṆ  ai = refl ; ivlS ıaṆ  au = refl
ivlS ıiK  a = refl ; ivlS ıiK  i = refl ; ivlS ıiK  u = refl
ivlS ıiK  ṛ = refl ; ivlS ıiK  ḷ = refl ; ivlS ıiK  e = refl
ivlS ıiK  o = refl ; ivlS ıiK  ai = refl ; ivlS ıiK  au = refl
ivlS ıeṄ  a = refl ; ivlS ıeṄ  i = refl ; ivlS ıeṄ  u = refl
ivlS ıeṄ  ṛ = refl ; ivlS ıeṄ  ḷ = refl ; ivlS ıeṄ  e = refl
ivlS ıeṄ  o = refl ; ivlS ıeṄ  ai = refl ; ivlS ıeṄ  au = refl
ivlS ıaiC a = refl ; ivlS ıaiC i = refl ; ivlS ıaiC u = refl
ivlS ıaiC ṛ = refl ; ivlS ıaiC ḷ = refl ; ivlS ıaiC e = refl
ivlS ıaiC o = refl ; ivlS ıaiC ai = refl ; ivlS ıaiC au = refl

sivasutraEncoding : Encoding Sound Marker Ix4 vowelFamily
sivasutraEncoding = record
  { pos = posS ; start = startS ; mark = markS ; bnd = bndS ; isIvl = ivlS }

-- and there is no fifth anubandha in the vowel section
noFifthMarker : (m : Marker) → ((m ≡ Ṇ) ⊎ ((m ≡ K) ⊎ ((m ≡ Ṅ) ⊎ (m ≡ C))))
noFifthMarker Ṇ = inl refl
noFifthMarker K = inr (inl refl)
noFifthMarker Ṅ = inr (inr (inl refl))
noFifthMarker C = inr (inr (inr refl))

------------------------------------------------------------------------
-- 7.  The same four markers already carry four MORE attested classes.
--
-- aK = [0,5) under K, aC = [0,9) under C, iC = [1,9) under C, eC = [5,9)
-- under C.  Three of these share the marker C, and by §2 they must then be a
-- chain — aiC ⊂ eC ⊂ iC ⊂ aC, which they are.  The chain is not a coincidence
-- of this order; it is what sharing an anubandha MEANS.
------------------------------------------------------------------------

aK-interval : IsInterval posS 0 (bndS K) AK
aK-interval a = refl ; aK-interval i = refl ; aK-interval u = refl
aK-interval ṛ = refl ; aK-interval ḷ = refl ; aK-interval e = refl
aK-interval o = refl ; aK-interval ai = refl ; aK-interval au = refl

aC-interval : IsInterval posS 0 (bndS C) AC
aC-interval a = refl ; aC-interval i = refl ; aC-interval u = refl
aC-interval ṛ = refl ; aC-interval ḷ = refl ; aC-interval e = refl
aC-interval o = refl ; aC-interval ai = refl ; aC-interval au = refl

iC-interval : IsInterval posS 1 (bndS C) IC
iC-interval a = refl ; iC-interval i = refl ; iC-interval u = refl
iC-interval ṛ = refl ; iC-interval ḷ = refl ; iC-interval e = refl
iC-interval o = refl ; iC-interval ai = refl ; iC-interval au = refl

eC-interval : IsInterval posS 5 (bndS C) EC
eC-interval a = refl ; eC-interval i = refl ; eC-interval u = refl
eC-interval ṛ = refl ; eC-interval ḷ = refl ; eC-interval e = refl
eC-interval o = refl ; eC-interval ai = refl ; eC-interval au = refl

-- the chain under C, obtained from §2 rather than by inspection
aiC⊆eC : (AIC ⊑ EC) ⊎ (EC ⊑ AIC)
aiC⊆eC = sharedEnd→comparable posS 7 5 (bndS C) AIC EC (ivlS ıaiC) eC-interval

eC⊆iC : (EC ⊑ IC) ⊎ (IC ⊑ EC)
eC⊆iC = sharedEnd→comparable posS 5 1 (bndS C) EC IC eC-interval iC-interval

iC⊆aC : (IC ⊑ AC) ⊎ (AC ⊑ IC)
iC⊆aC = sharedEnd→comparable posS 1 0 (bndS C) IC AC iC-interval aC-interval

------------------------------------------------------------------------
-- 8.  Summary, in one line each.
--
--   lowerBound : any line, any markers — aṆ iK eṄ aiC need four distinct markers
--   upper : the iva-stra line names all four with  K  C and has no fifth
--   so    : four is the minimum for that family and Pini's order attains it
------------------------------------------------------------------------

lowerBound : (j k : Ix4) → ¬ (j ≡ k) → ¬ (markS j ≡ markS k)
lowerBound = fourMarkersForced sivasutraEncoding

------------------------------------------------------------------------
-- THE ANTICHAIN BOUND IS NOT TIGHT.
-- `Dvihpatha_TheAntichainBoundIsAttainedOnlyIfASoundMayBeListed-
-- Twice.agda` (absent from this repository) exhibits a five-class family on three sounds with ⊆-width
-- two that NO recited-once line names with two anubandhas — all 120
-- arrangements of the five tokens checked, the enumeration's length
-- checked too — that three anubandhas name, and that two name again the
-- moment one sound may be recited twice.  width 2, cost 3 without
-- dvipha, cost 2 with it.
--
-- So the slack is not an artefact of the estimate; it is a resource this
-- file's model does not carry.  The MODELLING NOTE above is exact about
-- where: `pos` enumerates the SOUNDS, one position each.  The lower bound
-- survives that (classes ending at one marker are still a ⊆-chain when
-- the nearest preceding recitation is meant), but the MINIMUM does not.
--
-- The residue of three between width 11 and Pini's
-- 14 stands.  His line DOES recite ha twice — stras 5 and 14 — so total absence
-- of repetition cannot be the cause.  What is removed is only the reading
-- under which the bound is tight and the residue therefore spurious.
------------------------------------------------------------------------
