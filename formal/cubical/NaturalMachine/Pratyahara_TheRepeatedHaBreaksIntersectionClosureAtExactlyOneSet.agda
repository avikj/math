{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Pratyahara_TheRepeatedHaBreaksIntersectionClosureAtExactlyOneSet
--
-- SOURCE, WITH TEXT AND DATE.
--
--   Pini, *Adhyy*, c. 500 BCE.  The fourteen stras standing at
--   its head (iva-stri / mhevara-stri) lay every sound of
--    in ONE linear order, each sūtra closing in an अनुबन्ध
--   (it-marker).  The abbreviation is licensed by A 1.1.71
--   आदिरन्तेन सहेता — *ādir antyena sahetā*, "an initial [sound] together
--   with a final इत् [denotes the sounds in between]"; the it-status of
--   the closing consonant is A 1.3.3 हलन्त्यम् *halantyam*, and its
--   elision A 1.3.9 तस्य लोपः *tasya lopaḥ*.
--
--   ह occurs TWICE in the fourteen: in the fifth sūtra हयवरट् and again,
--   alone, in the fourteenth हल्.  ण् likewise occurs twice as an
--   अनुबन्ध, closing the first (अ इ उ ण्) and the sixth (ल ण्).
--
--   COMMENTARY LAYER.  Ktyyana's vrttikas and
--   Patañjali's *Mahābhāṣya* (c. 150 BCE) are where the repetition of ह
--   and the two  are argued.
--
-- WHAT IS CLAIMED OF PINI.  Only the data: the fourteen stras in the
-- order given, the it-markers as given, ह twice, ण् twice.  That
-- encoding is corroborated against an independent implementation from
-- inside the tradition —
-- `/root/agda-libs/vidyut/vidyut-prakriya/src/sounds.rs`, whose `SUTRAS`
-- table is sound-for-sound and marker-for-marker the same list, and
-- whose scan (like `from` below) starts at the FIRST occurrence of the
-- initial sound and disambiguates the second ण् by an external
-- convention it names `R2`.
--
-- ────────────────────────────────────────────────────────────────────
-- THE QUESTION, AND TWO ANSWERS THAT DIFFER
--
-- Is the family of classes nameable by the device closed under
-- non-empty intersection?
--
--   FROM THE SYMMETRY.  A pratyhra is an interval of one linear
--   order.  Intervals are closed under intersection.  The construction
--   is equivariant under every relabelling of the sounds that fixes the
--   markers (§4, proved), so the answer cannot depend on which sound
--   sits where; it is a structural invariant of the interval
--   representation, and it is YES.
--
--   FROM THE INDIVIDUAL OBJECT.  What the device names is not the
--   interval but its IMAGE under the position→sound labelling, and that
--   labelling is not injective: ह occupies two positions.  Images of an
--   intersection-closed family under a non-injective map need not be
--   intersection-closed.  So the answer is not fixed by the symmetry and
--   has to be computed on the individual string.
--
-- Computed on the individual string it is NO (§5), by one witness:
--
--       हश् ∩ शल्  =  { ह } ,   and { ह } bears no name.
--
-- The equivariance of §4 is exact and it is blind to this: `map σ` of
-- the list still carries σ(ह) twice, so the invariant transports the
-- failure instead of detecting it.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   §3  the classical pratyhras by refl on the full fourteen,
--       including the pair अण् / यण् that turns on the SECOND ण्, and
--       हल् = 34 entries denoting 33 consonants;
--   §4  relabelling equivariance of `from`, `upto`, `between`, by list
--       induction — the symmetry statement, in full generality;
--   §5  हश् ∩ शल् ≡ ह ∷ [], and `ह ∷ []` is named by NO legal pair
--       (sound , anubandha) — all 42 × 13 = 546 refuted; packaged as
--       `intersection-closure-fails` and as `not-intersection-closed`;
--   §5b the two ILLEGAL pairs that do name it, kept because they show
--       the result is sharp in both of Pini's endpoint restrictions;
--   §6  searching the LAST occurrence
--       of the initial sound makes { ह } nameable and destroys हल् and
--       हश् — the two classes the repetition exists to supply.
--
-- STANDING ON EARLIER WORK, none of it re-landed.  `Sivasutra.agda`
-- checks `upto` on the vowel prefix;
-- `NaturalMachine.NonInitialPratyaharasAndOneIntersectionInstance` adds
-- the start-search `from`, the two-endpoint `between`, and ONE
-- intersection instance on that prefix.  This module supplies the consonant
-- stras and settles closure in the negative.  `NaturalMachine.Pratyahara` proves
-- at three letters that repetition is FORCED and that one repetition
-- SUFFICES for totality; `NaturalMachine.PratyaharaBuysTotalityWithLocality`
-- proves the repetition costs LOCALITY (one name, two sets).  §5 is a
-- third cost, distinct from both and not implied by either: the family
-- of denoted SETS loses intersection-closure.
--
-- `Sym`, `isMarker`, `eqSym`, `from`, `upto`, `between` are restated here
-- rather than imported because `Sivasutra.Sym` carries the nine vowels
-- and four markers only; the definitions are the earlier ones unchanged.
------------------------------------------------------------------------

module NaturalMachine.Pratyahara_TheRepeatedHaBreaksIntersectionClosureAtExactlyOneSet where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_ ; _or_ ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  The fourteen stras
------------------------------------------------------------------------

data Sym : Type where
  -- sounds, in iva-stra order
  a i u ṛ ḷ e o ai au                     : Sym   -- 1–4
  ha ya va ra                             : Sym   -- 5   हयवरट्
  la                                      : Sym   -- 6   लण्
  ña ma ṅa ṇa na                          : Sym   -- 7   ञमङणनम्
  jha bha                                 : Sym   -- 8   झभञ्
  gha ḍha dha                             : Sym   -- 9   घढधष्
  ja ba ga ḍa da                          : Sym   -- 10  जबगडदश्
  kha pha cha ṭha tha ca ṭa ta            : Sym   -- 11  खफछठथचटतव्
  ka pa                                   : Sym   -- 12  कपय्
  śa ṣa sa                                : Sym   -- 13  शषसर्
  -- it-markers (अनुबन्ध).  Ṇ closes sūtra 1 AND sūtra 6.
  Ṇ K Ṅ C Ṭ M Ñ Ṣ Ś V Y R L               : Sym

isMarker : Sym → Bool
isMarker Ṇ = true
isMarker K = true
isMarker Ṅ = true
isMarker C = true
isMarker Ṭ = true
isMarker M = true
isMarker Ñ = true
isMarker Ṣ = true
isMarker Ś = true
isMarker V = true
isMarker Y = true
isMarker R = true
isMarker L = true
isMarker _ = false

eqSym : Sym → Sym → Bool
eqSym a a = true
eqSym i i = true
eqSym u u = true
eqSym ṛ ṛ = true
eqSym ḷ ḷ = true
eqSym e e = true
eqSym o o = true
eqSym ai ai = true
eqSym au au = true
eqSym ha ha = true
eqSym ya ya = true
eqSym va va = true
eqSym ra ra = true
eqSym la la = true
eqSym ña ña = true
eqSym ma ma = true
eqSym ṅa ṅa = true
eqSym ṇa ṇa = true
eqSym na na = true
eqSym jha jha = true
eqSym bha bha = true
eqSym gha gha = true
eqSym ḍha ḍha = true
eqSym dha dha = true
eqSym ja ja = true
eqSym ba ba = true
eqSym ga ga = true
eqSym ḍa ḍa = true
eqSym da da = true
eqSym kha kha = true
eqSym pha pha = true
eqSym cha cha = true
eqSym ṭha ṭha = true
eqSym tha tha = true
eqSym ca ca = true
eqSym ṭa ṭa = true
eqSym ta ta = true
eqSym ka ka = true
eqSym pa pa = true
eqSym śa śa = true
eqSym ṣa ṣa = true
eqSym sa sa = true
eqSym Ṇ Ṇ = true
eqSym K K = true
eqSym Ṅ Ṅ = true
eqSym C C = true
eqSym Ṭ Ṭ = true
eqSym M M = true
eqSym Ñ Ñ = true
eqSym Ṣ Ṣ = true
eqSym Ś Ś = true
eqSym V V = true
eqSym Y Y = true
eqSym R R = true
eqSym L L = true
eqSym _ _ = false

-- The fourteen, in order.  ह appears at sūtra 5 and again at sūtra 14;
-- ण् appears at sūtra 1 and again at sūtra 6.
sivasutra14 : List Sym
sivasutra14 =
  a ∷ i ∷ u ∷ Ṇ ∷
  ṛ ∷ ḷ ∷ K ∷
  e ∷ o ∷ Ṅ ∷
  ai ∷ au ∷ C ∷
  ha ∷ ya ∷ va ∷ ra ∷ Ṭ ∷
  la ∷ Ṇ ∷
  ña ∷ ma ∷ ṅa ∷ ṇa ∷ na ∷ M ∷
  jha ∷ bha ∷ Ñ ∷
  gha ∷ ḍha ∷ dha ∷ Ṣ ∷
  ja ∷ ba ∷ ga ∷ ḍa ∷ da ∷ Ś ∷
  kha ∷ pha ∷ cha ∷ ṭha ∷ tha ∷ ca ∷ ṭa ∷ ta ∷ V ∷
  ka ∷ pa ∷ Y ∷
  śa ∷ ṣa ∷ sa ∷ R ∷
  ha ∷ L ∷ []

------------------------------------------------------------------------
-- 2.  The extractor, exactly as the two earlier modules define it
--
-- `upto` is `Sivasutra.upto`; `from` and `between` are
-- `NonInitialPratyaharasAndOneIntersectionInstance`'s.  Restated over
-- the larger `Sym`, unchanged.
------------------------------------------------------------------------

upto : Sym → List Sym → List Sym
upto m [] = []
upto m (x ∷ xs) =
  if eqSym x m
  then []
  else (if isMarker x then upto m xs else x ∷ upto m xs)

from : Sym → List Sym → List Sym
from s [] = []
from s (x ∷ xs) = if eqSym x s then x ∷ xs else from s xs

between : Sym → Sym → List Sym → List Sym
between s m xs = upto m (from s xs)

------------------------------------------------------------------------
-- 3.  The classical pratyhras, on the full fourteen, each by refl
--
-- अण् and यण् are the pair that turns on the SECOND ण्: the start-search
-- of `from` carries यण् past the first ण् to the one closing लण्.  The
-- earlier modules could not exhibit this, the vowel prefix having only
-- one ण्.
------------------------------------------------------------------------

aṆ : between a Ṇ sivasutra14 ≡ a ∷ i ∷ u ∷ []
aṆ = refl

yaṆ : between ya Ṇ sivasutra14 ≡ ya ∷ va ∷ ra ∷ la ∷ []
yaṆ = refl

aK : between a K sivasutra14 ≡ a ∷ i ∷ u ∷ ṛ ∷ ḷ ∷ []
aK = refl

aC : between a C sivasutra14 ≡ a ∷ i ∷ u ∷ ṛ ∷ ḷ ∷ e ∷ o ∷ ai ∷ au ∷ []
aC = refl

iK : between i K sivasutra14 ≡ i ∷ u ∷ ṛ ∷ ḷ ∷ []
iK = refl

-- यम् : the nasals
yaM : between ya M sivasutra14
    ≡ ya ∷ va ∷ ra ∷ la ∷ ña ∷ ma ∷ ṅa ∷ ṇa ∷ na ∷ []
yaM = refl

-- शर् : the sibilants
śaR : between śa R sivasutra14 ≡ śa ∷ ṣa ∷ sa ∷ []
śaR = refl

-- शल् : sibilants and ह — reaches the SECOND ह
śaL : between śa L sivasutra14 ≡ śa ∷ ṣa ∷ sa ∷ ha ∷ []
śaL = refl

-- हश् : the voiced consonants, twenty of them
haŚ : between ha Ś sivasutra14
    ≡ ha ∷ ya ∷ va ∷ ra ∷ la ∷ ña ∷ ma ∷ ṅa ∷ ṇa ∷ na
    ∷ jha ∷ bha ∷ gha ∷ ḍha ∷ dha ∷ ja ∷ ba ∷ ga ∷ ḍa ∷ da ∷ []
haŚ = refl

-- हल् : the consonants.  THIRTY-FOUR entries, THIRTY-THREE sounds — ह is
-- emitted twice, once from stra 5 and once from stra 14.  The
-- repetition is visible in the extracted list itself.
haL : between ha L sivasutra14
    ≡ ha ∷ ya ∷ va ∷ ra ∷ la ∷ ña ∷ ma ∷ ṅa ∷ ṇa ∷ na
    ∷ jha ∷ bha ∷ gha ∷ ḍha ∷ dha ∷ ja ∷ ba ∷ ga ∷ ḍa ∷ da
    ∷ kha ∷ pha ∷ cha ∷ ṭha ∷ tha ∷ ca ∷ ṭa ∷ ta ∷ ka ∷ pa
    ∷ śa ∷ ṣa ∷ sa ∷ ha ∷ []
haL = refl

-- अल् : every sound.  Forty-three entries, forty-two sounds.
aL : between a L sivasutra14
   ≡ a ∷ i ∷ u ∷ ṛ ∷ ḷ ∷ e ∷ o ∷ ai ∷ au
   ∷ ha ∷ ya ∷ va ∷ ra ∷ la ∷ ña ∷ ma ∷ ṅa ∷ ṇa ∷ na
   ∷ jha ∷ bha ∷ gha ∷ ḍha ∷ dha ∷ ja ∷ ba ∷ ga ∷ ḍa ∷ da
   ∷ kha ∷ pha ∷ cha ∷ ṭha ∷ tha ∷ ca ∷ ṭa ∷ ta ∷ ka ∷ pa
   ∷ śa ∷ ṣa ∷ sa ∷ ha ∷ []
aL = refl

------------------------------------------------------------------------
-- 4.  THE SYMMETRY, PROVED IN FULL GENERALITY
--
-- Any relabelling σ of the symbols that respects equality-testing and
-- the marker predicate commutes with the whole extractor.  Nothing here
-- is a refl on data: it is induction on the list, and it holds for every
-- list, every σ, every start and every marker.
--
-- The conserved quantity is the SHAPE of the family — which positions
-- each name picks out.  Which sound sits at a position is not a
-- variable the extractor sees.
------------------------------------------------------------------------

module Relabelling
  (σ : Sym → Sym)
  (σ-eq : (x y : Sym) → eqSym (σ x) (σ y) ≡ eqSym x y)
  (σ-mark : (x : Sym) → isMarker (σ x) ≡ isMarker x)
  where

  from-equiv : (s : Sym) (xs : List Sym)
             → from (σ s) (map σ xs) ≡ map σ (from s xs)
  from-equiv s [] = refl
  from-equiv s (x ∷ xs) =
    cong (λ b → if b then σ x ∷ map σ xs else from (σ s) (map σ xs)) (σ-eq x s)
    ∙ step
    where
      step : (if eqSym x s then σ x ∷ map σ xs else from (σ s) (map σ xs))
           ≡ map σ (from s (x ∷ xs))
      step with eqSym x s
      ... | true  = refl
      ... | false = from-equiv s xs

  upto-equiv : (m : Sym) (xs : List Sym)
             → upto (σ m) (map σ xs) ≡ map σ (upto m xs)
  upto-equiv m [] = refl
  upto-equiv m (x ∷ xs) =
    cong₂ (λ b c → if b then []
                   else (if c then upto (σ m) (map σ xs)
                              else σ x ∷ upto (σ m) (map σ xs)))
          (σ-eq x m) (σ-mark x)
    ∙ step
    where
      step : (if eqSym x m then []
              else (if isMarker x then upto (σ m) (map σ xs)
                                  else σ x ∷ upto (σ m) (map σ xs)))
           ≡ map σ (upto m (x ∷ xs))
      step with eqSym x m | isMarker x
      ... | true  | _     = refl
      ... | false | true  = upto-equiv m xs
      ... | false | false = cong (σ x ∷_) (upto-equiv m xs)

  between-equiv : (s m : Sym) (xs : List Sym)
                → between (σ s) (σ m) (map σ xs) ≡ map σ (between s m xs)
  between-equiv s m xs =
    cong (upto (σ m)) (from-equiv s xs) ∙ upto-equiv m (from s xs)

------------------------------------------------------------------------
-- 5.  THE INDIVIDUAL OBJECT, AND WHERE IT DIFFERS FROM THE SYMMETRY
--
-- `nameable` ranges over the forty-two distinct sounds as di and the
-- thirteen distinct anubandhas as antya it: 546 candidate pairs, which
-- is exactly what A 1.1.71 with A 1.3.3 licenses.
--
-- Two
-- illegal pairs name { ह } and are checked in §5b: `between ha ya`,
-- which stops at a SOUND, and `between R L`, which starts at an
-- it-MARKER.  Neither is a pratyāhāra — the antya must be an इत् (A
-- 1.3.3 हलन्त्यम्) and an इत् is elided and is not a sound of the
-- language (A 1.3.9 तस्य लोपः).  So the negative result is exactly as
-- strong as the device's own two restrictions and no stronger:
-- widening the candidate set
-- does not widen the theorem, it changes the object.
------------------------------------------------------------------------

eqList : List Sym → List Sym → Bool
eqList [] [] = true
eqList [] (_ ∷ _) = false
eqList (_ ∷ _) [] = false
eqList (x ∷ xs) (y ∷ ys) = if eqSym x y then eqList xs ys else false

-- The forty-two distinct sounds: the legal di of a pratyhra.
allSounds : List Sym
allSounds =
  a ∷ i ∷ u ∷ ṛ ∷ ḷ ∷ e ∷ o ∷ ai ∷ au
  ∷ ha ∷ ya ∷ va ∷ ra ∷ la ∷ ña ∷ ma ∷ ṅa ∷ ṇa ∷ na
  ∷ jha ∷ bha ∷ gha ∷ ḍha ∷ dha ∷ ja ∷ ba ∷ ga ∷ ḍa ∷ da
  ∷ kha ∷ pha ∷ cha ∷ ṭha ∷ tha ∷ ca ∷ ṭa ∷ ta ∷ ka ∷ pa
  ∷ śa ∷ ṣa ∷ sa ∷ []

-- The thirteen distinct anubandhas: the legal antya it.
allMarkers : List Sym
allMarkers = Ṇ ∷ K ∷ Ṅ ∷ C ∷ Ṭ ∷ M ∷ Ñ ∷ Ṣ ∷ Ś ∷ V ∷ Y ∷ R ∷ L ∷ []

anySym : (Sym → Bool) → List Sym → Bool
anySym p [] = false
anySym p (x ∷ xs) = p x or anySym p xs

-- is `t` the value of `between s m` for SOME legal pair (sound , marker)?
nameable : List Sym → Bool
nameable t =
  anySym (λ s → anySym (λ m → eqList (between s m sivasutra14) t) allMarkers) allSounds

-- the intersection of two extracted classes, as lists
mem : Sym → List Sym → Bool
mem s [] = false
mem s (x ∷ xs) = if eqSym x s then true else mem s xs

inter : List Sym → List Sym → List Sym
inter [] ys = []
inter (x ∷ xs) ys = if mem x ys then x ∷ inter xs ys else inter xs ys

isNil : List Sym → Bool
isNil [] = true
isNil (_ ∷ _) = false

-- Both classes are named.
haŚ-named : nameable (between ha Ś sivasutra14) ≡ true
haŚ-named = refl

śaL-named : nameable (between śa L sivasutra14) ≡ true
śaL-named = refl

-- Their intersection is { ह }, and it is not empty.
haŚ∩śaL : inter (between ha Ś sivasutra14) (between śa L sivasutra14) ≡ ha ∷ []
haŚ∩śaL = refl

haŚ∩śaL-nonempty : isNil (inter (between ha Ś sivasutra14) (between śa L sivasutra14)) ≡ false
haŚ∩śaL-nonempty = refl

-- And { ह } bears no name: 42 × 13 = 546 candidate pairs, all refuted.
ha-alone-unnameable : nameable (ha ∷ []) ≡ false
ha-alone-unnameable = refl

-- Packaged.  The family the device generates is NOT closed under
-- non-empty intersection.
intersection-closure-fails :
  Σ[ X ∈ List Sym ] Σ[ P ∈ List Sym ]
    ((nameable X ≡ true)
     × (nameable P ≡ true)
     × (isNil (inter X P) ≡ false)
     × (nameable (inter X P) ≡ false))
intersection-closure-fails =
  between ha Ś sivasutra14 ,
  between śa L sivasutra14 ,
  haŚ-named , śaL-named , haŚ∩śaL-nonempty ,
  subst (λ z → nameable z ≡ false) (sym haŚ∩śaL) ha-alone-unnameable

-- stated as the impossibility it is
not-intersection-closed :
  ¬ ((X P : List Sym) → nameable X ≡ true → nameable P ≡ true
     → isNil (inter X P) ≡ false → nameable (inter X P) ≡ true)
not-intersection-closed h =
  true≢false
    (sym (h (between ha Ś sivasutra14) (between śa L sivasutra14)
            haŚ-named śaL-named haŚ∩śaL-nonempty)
     ∙ subst (λ z → nameable z ≡ false) (sym haŚ∩śaL) ha-alone-unnameable)

------------------------------------------------------------------------
-- 5b.  The two illegal pairs that do name { ह }
--
-- They are why the candidate set is the device's and
-- not a wider one, and they show the negative result is sharp — it fails
-- the moment either of Pini's two restrictions on the endpoints is
-- dropped.
------------------------------------------------------------------------

-- stop at a SOUND rather than an anubandha (excluded by A 1.3.3)
illegal-stop-names-ha : between ha ya sivasutra14 ≡ ha ∷ []
illegal-stop-names-ha = refl

-- start at an it-MARKER, which A 1.3.9 elides (so it is no sound at all)
illegal-start-names-ha : between R L sivasutra14 ≡ ha ∷ []
illegal-start-names-ha = refl

------------------------------------------------------------------------
-- 6.  Last-occurrence search, and what it costs
--
-- The failure at
-- { ह } is an artefact of `from` taking the FIRST occurrence of the
-- initial sound.  Take the LAST occurrence instead and { ह } becomes
-- nameable — `between ha L` then runs from sūtra 14's ह to ल् and
-- denotes exactly {  } — and this half is checked below.
--
-- §6b is the cost: under last-occurrence search,
-- हल् and हश् are not merely different — they are unnameable.  `fromLast
-- ha` can never again reach stra 5, so no pair whatever names the
-- consonants or the voiced consonants.
--
-- So the convention is not free and not arbitrary.  First-occurrence
-- search is what the repetition of ह is FOR: it is the convention under
-- which the second ह extends हल् to the end of the list rather than
-- starting a new class.  Last-occurrence search trades one unnameable set for two, and
-- the two it lost are classes the Adhyy uses constantly.
------------------------------------------------------------------------

fromLast : Sym → List Sym → List Sym
fromLast s [] = []
fromLast s (x ∷ xs) =
  if eqSym x s
  then (if isNil (fromLast s xs) then x ∷ xs else fromLast s xs)
  else fromLast s xs

betweenLast : Sym → Sym → List Sym → List Sym
betweenLast s m xs = upto m (fromLast s xs)

nameableLast : List Sym → Bool
nameableLast t =
  anySym (λ s → anySym (λ m → eqList (betweenLast s m sivasutra14) t) allMarkers) allSounds

-- 6a.  {  } does become nameable.
claimR-half-true : betweenLast ha L sivasutra14 ≡ ha ∷ []
claimR-half-true = refl

claimR-ha-nameable : nameableLast (ha ∷ []) ≡ true
claimR-ha-nameable = refl

-- 6b.  हल् and हश् are lost outright.
claimR-loses-haL : nameableLast (between ha L sivasutra14) ≡ false
claimR-loses-haL = refl

claimR-loses-haŚ : nameableLast (between ha Ś sivasutra14) ≡ false
claimR-loses-haŚ = refl

claimR-refuted :
  (nameableLast (ha ∷ []) ≡ true)
  × (nameableLast (between ha L sivasutra14) ≡ false)
  × (nameableLast (between ha Ś sivasutra14) ≡ false)
claimR-refuted = claimR-ha-nameable , claimR-loses-haL , claimR-loses-haŚ

------------------------------------------------------------------------
-- 7.  WHAT §5 DOES AND DOES NOT BEAR ON
--
-- IT DOES NOT TOUCH PETERSEN 2004.  That theorem concerns the family of
-- classes Pini's rules REQUIRE, and asks whether a linear order
-- represents it by intervals — and, given that it does, whether his
-- order is minimal.  §5 concerns the family the device GENERATES, which
-- is larger: every (start, marker) pair, whether or not any rule uses
-- it.  A required family can be intersection-closed while the generated
-- family is not, and { ह } is precisely a set no rule needs a
-- two-symbol name for.  The two statements do not contradict and neither
-- implies the other.
--
-- IT DOES CONSTRAIN A READING ALREADY IN THIS CORPUS.
-- `notes/INDIC_FORMAL_TRADITIONS_MAP.md` (absent from this repository) §1.1 records the iva-stras as
-- "an interval representation of an intersection-closed set family over
-- a linear order".  Read as a statement about the required family that
-- is the received claim and nothing here disturbs it.  Read as a
-- statement about the device — as the shorter phrase "the pratyāhāras
-- are intersection-closed" invites — it is false, and §5 is the
-- counterexample.  The distinction is exactly the non-injectivity of the
-- labelling, which is exactly the repeated ह.
--
-- THE COST LEDGER OF THE REPETITION, NOW THREE ENTRIES, EACH CHECKED IN
-- A DIFFERENT MODULE.  Repetition buys totality (`Pratyahara`, forced at
-- three letters; one repetition suffices).  It costs locality
-- (`PratyaharaBuysTotalityWithLocality`: one name, two sets — the अण्
-- ambiguity).  It costs intersection-closure of the generated family
-- (§5).  The third is not a corollary of the second: the collision in
-- that module is between two runs sharing a NAME, and § 5's failure is
-- between two SETS with no shared name at all.
------------------------------------------------------------------------
