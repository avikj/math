{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.AnyonyaAbhava
--
-- अन्योन्याभाव — mutual absence — and why Vaiśeṣika-Nyāya keeps it as a
-- SEPARATE category from संसर्गाभाव instead of reducing one to the other.
--
-- ────────────────────────────────────────────────────────────────────
-- THE DOCTRINE, AND WHY THIS MODULE EXISTS
--
-- `NaturalMachine.Abhava` builds अभाव as a record carrying its
-- प्रतियोगिन् and अवच्छेदक, and analyses the tower ¬, ¬¬, ¬¬¬.  All of
-- that is संसर्गाभाव: the absence of a RELATION at a locus — the pot is
-- not on the floor.  Praastapda's division (*Padrthadharmasagraha*,
-- c. 6th c.) and every Nyya text after it insist on a second kind:
--
--     अन्योन्याभाव — the absence of IDENTITY.  A cloth is not a pot.
--     Its प्रतियोगिन् is the pot, its अनुयोगिन् the cloth, and what is
--     absent is तादात्म्य, identity itself, not a relation between two
--     things that are already distinct.
--
-- The reduction has been attempted in both directions for a thousand
-- years and Navya-Nyya rejects both.  This module is that dispute,
-- made exact — and the tradition turns out to be right in a way the
-- classical reading cannot see, because CLASSICALLY THE TWO ARE
-- INTERDERIVABLE AND THE DISPUTE IS EMPTY.  Constructively they are not.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   §2  अन्योन्याभाव IS an अभाव in this corpus's own sense: it
--       instantiates `Abhava.Abhāva` with प्रतियोगिन् `_≡ b`.  So the
--       record was already general enough, which is worth knowing
--       before adding anything to it.
--
--   §3  अन्योन्य ⟹ संसर्ग, freely.  Two points the अवच्छेदक identifies
--       but whose values are mutually absent destroy every decoder at
--       once.  This is the corpus's collision lemma, and naming its
--       parts is not decoration: the hypothesis `q x ≡ q x'` is
--       precisely an अवच्छेदक, the qualification under which the two
--       are not distinguished.
--
--   §4  संसर्ग ⟹ अन्योन्य only up to ¬¬, and even that needs the
--       प्रतियोगिन् to be decidable.  So the reduction FAILS, and it
--       fails by exactly one step of the tower `Abhava` §2 measures.
--
--   §5  Under a decidable अवच्छेदक the step is free (`Abhava
--       .dec-collapses`), and the two categories become interderivable.
--
-- ────────────────────────────────────────────────────────────────────
-- THE POINT, WHICH IS NOT A TRANSLATION
--
-- The two-fold division is not scholastic hair-splitting and it is not
-- a taxonomy of examples.  It tracks a real obstruction, the obstruction
-- is one level of the negation tower, and it dissolves exactly when the
-- प्रतियोगिन् is decidable.  A reader with excluded middle sees two
-- names for one thing and concludes the Naiyyikas were counting
-- angels; a reader without it finds the distinction forced.
--
-- That is the same verdict `Abhava` reached about the THREE-tall tower
-- and for the same reason, which is itself evidence that the Nyya
-- analysis of अभाव is tracking constructive structure throughout and
-- not in one lucky place.
--
-- SOURCES.  Praastapda, *Padrthadharmasagraha* (c. 6th c.), where
-- अभाव's division is set out; Udayana, *Nyāyakusumāñjali* (c. 1000);
-- Gagea, *Tattvacintmai*, abhva-khaa (c. 1325), where the
-- प्रतियोगिता analysis is refined; Raghunātha Śiromaṇi,
-- *Padrthatattvanirpaa* (c. 1500), on which categories survive
-- scrutiny.  The mathematics below is this corpus's; the DIVISION and
-- the claim of irreducibility are theirs, and are what is being tested.
------------------------------------------------------------------------

module NaturalMachine.AnyonyaAbhava where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary
  using (¬_ ; Dec ; yes ; no ; Discrete ; Stable ; Separated)
open import Cubical.Relation.Nullary.Properties
  using (Discrete→Separated)
open import Cubical.Foundations.Prelude using (isSet)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

open import NaturalMachine.Abhava using (Abhāva ; delimitor ; absent ; dec-collapses)
open import NaturalMachine.FiniteInformation
  using (FactorsThrough ; FiberConstant ; fiberConstant→factorsThrough)
open import NaturalMachine.TranscriptDescent using (collisionObstructsDecoder)

private
  variable
    ℓ ℓx ℓy ℓt : Level

------------------------------------------------------------------------
-- 1.  अन्योन्याभाव: the absence of identity, not of a relation
------------------------------------------------------------------------

Anyonya : {T : Type ℓt} → T → T → Type ℓt
Anyonya a b = ¬ (a ≡ b)

------------------------------------------------------------------------
-- 2.  It is an अभाव in the corpus's own sense
--
-- अनुयोगिन् becomes the delimitor, प्रतियोगिन् the family `_≡ b`.  Nothing
-- had to be added to the record: it was built general enough, and this
-- is the check rather than the assertion.
------------------------------------------------------------------------

anyonya-is-abhava : {T : Type ℓt} (a b : T) → Anyonya a b → Abhāva T (_≡ b)
Abhāva.delimitor (anyonya-is-abhava a b _)  = a
Abhāva.absent    (anyonya-is-abhava a b ne) = ne

anyonya-from-abhava : {T : Type ℓt} (b : T) (A : Abhāva T (_≡ b))
                    → Anyonya (delimitor A) b
anyonya-from-abhava b A = absent A

------------------------------------------------------------------------
-- 3.  अन्योन्य ⟹ संसर्ग, with no hypothesis
--
-- The अवच्छेदक is `q x ≡ q x'`: the qualification under which the two
-- loci are NOT distinguished.  Under it, a mutual absence of their
-- values is the absence of every decoding relation at once.
------------------------------------------------------------------------

anyonya→samsarga :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (q : X → Y) (t : X → T) {x x' : X}
  → q x ≡ q x'                       -- अवच्छेदक: identified here
  → Anyonya (t x) (t x')             -- अन्योन्याभाव: not identical there
  → ¬ FactorsThrough q t             -- संसर्गाभाव: no relation, anywhere
anyonya→samsarga q t = collisionObstructsDecoder q t

------------------------------------------------------------------------
-- 4.  संसर्ग ⟹ अन्योन्य ONLY UP TO ¬¬, and only with a decidable
--     प्रतियोगिन् — so the reduction fails
------------------------------------------------------------------------

Collision : {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
          → (X → Y) → (X → T) → Type (ℓ-max ℓx (ℓ-max ℓy ℓt))
Collision {X = X} q t =
  Σ[ x ∈ X ] Σ[ x' ∈ X ] ((q x ≡ q x') × Anyonya (t x) (t x'))

samsarga→¬¬anyonya :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (dT : Discrete T) (q : X → Y) (t : X → T)
  → ¬ FactorsThrough q t
  → ¬ ¬ (Collision q t)
samsarga→¬¬anyonya dT q t noDecoder noCollision =
  noDecoder (fiberConstant→factorsThrough (Discrete→isSet dT) q t constant)
  where
  constant : FiberConstant q t
  constant x x' same =
    Discrete→Separated dT (t x) (t x')
      (λ ne → noCollision (x , x' , same , ne))

------------------------------------------------------------------------
-- 5.  And the missing step is exactly one level of the tower
--
-- If the collision claim itself is decidable, `Abhava.dec-collapses`
-- closes it and the two categories become interderivable.  So the
-- irreducibility is not absolute: it is indexed by the अवच्छेदक, which
-- is what an अवच्छेदक is for.
------------------------------------------------------------------------

samsarga→anyonya-when-decidable :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (dT : Discrete T) (q : X → Y) (t : X → T)
  → Dec (Collision q t)
  → ¬ FactorsThrough q t
  → Collision q t
samsarga→anyonya-when-decidable dT q t dC noDecoder =
  dec-collapses dC (samsarga→¬¬anyonya dT q t noDecoder)

-- the two directions, side by side, at a decidable delimitor
categories-agree-when-decidable :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (dT : Discrete T) (q : X → Y) (t : X → T) (dC : Dec (Collision q t))
  → (Collision q t → ¬ FactorsThrough q t)
  × (¬ FactorsThrough q t → Collision q t)
categories-agree-when-decidable dT q t dC =
    (λ c → anyonya→samsarga q t {x = c .fst} {x' = c .snd .fst}
             (c .snd .snd .fst) (c .snd .snd .snd))
  , samsarga→anyonya-when-decidable dT q t dC

------------------------------------------------------------------------
-- 6.  What was tested, and what it says about the tradition.
--
-- TESTED, not assumed: that the Vaiśeṣika division of अभाव into
-- संसर्ग and अन्योन्य is doing work.  It is.  One direction is free,
-- the other costs a step of the negation tower, and the cost is
-- discharged exactly by decidability of the प्रतियोगिन्.
--
-- The classical reader cannot see this.  With excluded middle §4's ¬¬
-- evaporates, the two categories are interderivable at every delimitor,
-- and the thousand-year dispute over whether one reduces to the other
-- looks like a dispute about nothing.  It is not: it is a dispute about
-- a distinction that only a constructive setting can register, conducted
-- by people who did not have one and were right anyway.
--
-- This is the second time in this corpus that the Nyya analysis of
-- अभाव has turned out to track constructive structure — `Abhava` §2–3
-- was the first, on the height of the tower.  Two is not a coincidence
-- worth explaining away.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 8.  CORRECTION FROM READING.
--
-- `notes/JAINA_PRAMANA_NAYA_NIKSEPA.md` (absent from this repository) sets down the Jaina scheme in
-- its own order, and reading it end to end makes two defects in this
-- module visible that no amount of checking would have caught.
--
-- FIRST: TWO DARANAS ARE BEING USED AS ONE TOOLKIT.
--
-- अन्योन्याभाव with its प्रतियोगिन् and अनुयोगिन् is Nyāya-Vaiśeṣika.
-- The सप्तभङ्गी with syāt-qualified asti/nāsti is Jaina.  These are
-- rival schools that dispute each other's categories — Jaina logicians
-- reject the Naiyyika treatment of negation, and the Naiyyikas reject
-- anekntavda.  This thread has been drawing on both as though they
-- were one box of instruments, which is precisely the selection habit
-- the corpus's own directive warns against: taking from each tradition
-- the part that converts, and never the dispute.
--
-- SECOND, AND SPECIFIC: THE GROUND IS MISSING.
--
--     Anyonya a b = ¬ (a ≡ b)
--
-- is bare negation.  The Jaina नास्ति is never that.  Every नास्ति is
-- relative to a stated fourfold ground —
--
--     स्व-द्रव्य / पर-द्रव्य    own substance / another's
--     स्व-क्षेत्र / पर-क्षेत्र    own field / another's
--     स्व-काल / पर-काल        own time / another's
--     स्व-भाव / पर-भाव        own state / another's
--
-- — and carries स्यात्.  A pot IS with respect to its own substance,
-- place, time and state, and IS NOT with respect to another's; that is
-- why the first two भङ्गs are not contradictory.  Unqualified negation
-- is not a भङ्ग at all.
--
-- What this module actually defines is the Naiyyika mutual absence,
-- for which bare negation with a प्रतियोगिन् is right.  The `Abhāva`
-- record supplies ONE delimitor; the Jaina scheme specifies FOUR, and I
-- never said which — or whether any — of the four my `q` is standing
-- for.  Downstream, `TheFibreIsTheSubject`, `AsiddhatvaBreaksFactoring`,
-- `AnuvrttiIsTheSameTrade`, `PratyaharaBuysTotalityWithLocality` and
-- `TheSecondNaIsTheCollision` all use `Anyonya` and inherit this.
--
-- The theorems are unaffected: they are about bare negation and they
-- prove what they say.  The NAMING is what is wrong, and in a thread
-- whose whole subject is that a coarse label loses a distinction the
-- finer object carries, that is not a small thing to have done.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 9.  CORRECTIONS TO §5 AND §6, made in
--     `NaturalMachine.TheDelimitorNeedsOnlyStability`.
--
-- (1) §5's hypothesis is stronger than §5's use.  `dec-collapses` is
--     applied only as `¬ ¬ A → A`, which is `Stable`.  The gap between
--     the two categories closes under `Stable (Collision q t)`, and the
--     decidable form is a corollary by `Dec→Stable`.  §6's sentence
--     "the cost is discharged exactly by decidability of the
--     प्रतियोगिन्" should read: by STABILITY of it.  Decidability is
--     sufficient and is not what is used.
--
-- (2) `Dec (Collision q t)` holds on a class of sites: for a
--     two-point state space with `Discrete Y` and `Discrete T` it
--     holds, by exhaustion over four pairs.
--
-- (3) §6 says "Two is not a coincidence worth explaining away."  Two
--     instances are two instances, and nothing downstream of that
--     sentence was ever computed.  The observation stands; the
--     inference drawn from it does not.
--
-- (4) §6 says the dispute was "conducted by people who did not have
--     one and were right anyway."  That scores the past by proximity
--     to a constructive setting — a दुर्नय.  What is sayable: the
--     Nyāya division of अभाव into संसर्ग and अन्योन्य is a distinction,
--     it is registered in this formalism, and the two directions cost
--     differently here.  Whether the Naiyyikas were tracking what
--     this formalism tracks is a question about them that this corpus
--     has no means to settle.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 10.  THE NAME, AGAINST AN AUDIT THAT WAS ALREADY IN THE REPOSITORY
--
-- `notes/ABHAVA.md` (absent from this repository) §2 carries a primary-text audit (Annambhaa,
-- `Tarkasagraha` §§57 and 80, the provenance and its limits recorded
-- there).  Its table reads, for
-- the fourth kind:
--
--     mutual absence | anyonybhva | difference: a is not b |
--     "non-identity, NOT observational separation by itself"
--
-- and its closing line about four earlier equations is
--
--     "These four struck equations were modern constructions, not
--      consequences of the fourfold."
--
-- §1 above is compatible with that: `Anyonya a b = ¬ (a ≡ b)` is
-- non-identity and nothing more.  `Collision q t` — two states a coarse
-- map identifies and a fine map separates — is observational
-- separation, which is a different thing.
--
-- The theorems do not depend on the gloss.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- PRIOR ART.
--
-- `notes/ABHAVA.md` (absent from this repository) A6 locates arXiv:2605.12548, *Cubical Type Theoretic
-- Navya-Nyya* (Panday & Ghosh), whose stated content includes DEPENDENT
-- DELIMITATION (avacchedaka) and TYPED ABSENCE (abhva) in cubical type
-- theory — the same substrate and the same notions this module touches.
--
-- NO NOVELTY IS CLAIMED for anything below.
------------------------------------------------------------------------
