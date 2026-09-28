{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- व्युत्पत्ति — the surface form is a lossy projection of derivation,
-- and meaning rides the derivation, not the surface.
--
-- (vyutpatti: the derivational formation of a word — dhātu, root, plus
-- pratyaya, affix.  Classical vykaraa vocabulary, used for the objects
-- it names; the theorems are this corpus's, not attributed to any text.)
--
-- THE BRIDGE, stated as this machine's own law applied to language.
-- Human language reaches the machine at the SURFACE — strings.  But in
-- the grammatical tradition a word IS its formation: dhtu + affixes,
-- with the meaning composed along the derivation (the kt and taddhita
-- pratyayas each carrying their semantic contribution).  That is
-- content-addressing: व्युत्पत्ति is the claim that the word's identity
-- is the hash of its construction — which is this machine's identity
-- law, arrived at from the other end, ~2,500 years earlier.
--
-- The obstruction to the bridge is exactly a fibre: the map
--
--     surface : Derivation → String
--
-- is NOT injective — sandhi and homonymy collapse distinct derivations
-- onto one string.  A pun (lea) is a two-point fibre of `surface`,
-- played deliberately.  So meaning CANNOT factor through the surface
-- (this module's theorem २: any factoring through a surface with a
-- collision forces two different meanings equal — refuted by
-- exhibition), while meaning DOES factor through derivation by
-- construction (theorem १: artha is a fold over the derivation).
--
-- Consequence for the endeavor: the human↔machine bridge cannot be
-- string-to-term; it must be derivation-to-term — carry the vyutpatti,
-- not the spelling.  The Adhyy engine (interactive/Astadhyayi.hs (absent from this repository))
-- already holds the lost material alongside the surface (sthnivadbhva,
-- lopa channels); this module is the abstract statement of WHY that
-- design is forced: recover-from-surface is exactly a section of a map
-- with inhabited multi-point fibres, and no such section exists.
--
-- The concrete witness is kept small and abstract (two derivations, one
-- surface, two arthas); a real  lea instantiates it — the
-- classical stock example is the dual reading of `go` (cow / speech /
-- earth in compound contexts):
-- the mathematics needs only that ONE collision exists, and the engine's
-- own corpus supplies collisions mechanically (GhanaPatha prints them).
------------------------------------------------------------------------

module Vyutpatti_TheSurfaceFormIsALossyProjectionOfDerivationAndMeaningRidesTheDerivation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Sigma using (Σ; _,_; _×_)

-- A minimal derivational syntax: roots and one layer of affixation.
-- (The real tree is interactive/Astadhyayi.hs (absent from this repository)'s; two constructors suffice
-- for the theorems, which are about the SHAPE of the situation.)
data Dhatu : Type₀ where
  dhA dhB : Dhatu

data Pratyaya : Type₀ where
  pK : Pratyaya

data Derivation : Type₀ where
  root  : Dhatu → Derivation
  affix : Pratyaya → Derivation → Derivation

-- Meaning composes along the derivation — a fold.  This is theorem १
-- by construction: artha factors through Derivation.
data Artha : Type₀ where
  cowness speechness : Artha
  agentOf : Artha → Artha

artha : Derivation → Artha
artha (root dhA)     = cowness
artha (root dhB)     = speechness
artha (affix pK d)   = agentOf (artha d)

-- The surface: sandhi/homonymy collapse.  Both roots surface as the
-- same string — the śleṣa situation, minimally.
data Surface : Type₀ where
  go  : Surface            -- the colliding surface form
  gok : Surface            -- the affixed form (collapsed likewise)

surface : Derivation → Surface
surface (root _)      = go
surface (affix pK _)  = gok

-- the collision, exhibited:
collision : surface (root dhA) ≡ surface (root dhB)
collision = refl

-- and the meanings genuinely differ:
isCow : Artha → Bool
isCow cowness    = true
isCow _          = false

artha-differs : artha (root dhA) ≡ artha (root dhB) → ⊥
artha-differs p = true≢false (cong isCow p)

------------------------------------------------------------------------
-- २ · MEANING CANNOT FACTOR THROUGH THE SURFACE.  Any m with
-- m ∘ surface ≡ artha would equate the two arthas across the collision.
no-surface-semantics :
  Σ (Surface → Artha) (λ m → (d : Derivation) → m (surface d) ≡ artha d)
  → ⊥
no-surface-semantics (m , h) =
  artha-differs (sym (h (root dhA)) ∙ cong m collision ∙ h (root dhB))

------------------------------------------------------------------------
-- ३ · NO SECTION RECOVERS THE DERIVATION.  A reader of surfaces cannot
-- reconstruct the formation: any s with surface ∘ s ≡ id picks ONE
-- point of each fibre, and the collision fibre has two — so some
-- derivation is not recovered.  Stated as: no section can be right
-- about both colliding roots.
no-faithful-reader :
  Σ (Surface → Derivation)
    (λ s → (s go ≡ root dhA) × (s go ≡ root dhB))
  → ⊥
no-faithful-reader (s , hA , hB) = rootsDiffer (sym hA ∙ hB)
  where
  isA : Derivation → Bool
  isA (root dhA) = true
  isA _          = false
  rootsDiffer : root dhA ≡ root dhB → ⊥
  rootsDiffer p = true≢false (cong isA p)
