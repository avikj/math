{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- गर्भ-धारा — the womb-holding: install IS a coning-off.
--
-- `install` (SthapanaVarga), the act
-- by which a theorem of the kernel becomes a structure map of the
-- kernel, was proposed to be the same act as CONING OFF an obstruction and
-- thereby climbing the Postnikov tower one level (garbha.dhara).
--
-- WHAT IS AND IS NOT ESTABLISHED.  Checked below: the locus of `install d`
-- is contractible, each locus point gives a spoke into the mapping cone of
-- the source POINT-map `Unit → Tm`, and the locus is a proposition.  NOT
-- established, and false as stated: that this kills an obstruction.  A
-- cone on a map from `Unit` kills no class — a point carries none — so
-- coning off the source point adds a contractible whisker and nothing
-- more.  Killing a class needs a cone on a map from a SPHERE or cycle
-- representing it; in this corpus that act is
-- `Vyakhya_TheQuotientByAnExplanationIsLosslessForEveryExactEvaluatorAndKillsTheDepthClass`
-- (the 2-cell filling the diamond), not `install`.  The terms below are
-- correct; the Postnikov reading is withdrawn.
--
-- WHAT CONING-OFF IS.  To cone off a map g : X → Y (Cubical's
-- HITs.MappingCones.Cone) is to glue a hub to Y with one spoke to each
-- inj (g x); the defining property that makes it KILL a class is that a
-- cone is CONTRACTIBLE — the attached cell has nothing in it, so any
-- class it bounds becomes null.  Coning off adds one contractible cell,
-- not a family.
--
-- WHAT INSTALL IS.  SthapanaVarga §4 (locusContr) proves the
-- applicability locus of `install d` — Σ[ t ] Control (install d) t,
-- which is Σ[ t ] (t ≡ lhs) — is CONTRACTIBLE with centre the source.
-- "Capability grows by one, not by a class."  That locus is a cone:
-- the based-path space is the cone point.
--
--   §1  THE LOCUS IS A CONE.  Σ[ t ] (t ≡ lhs) ≃ singl lhs (reverse the
--       path), and singl is the library's contractible cone
--       (isContrSingl).  So install's locus is a contractible cone —
--       coning-off's defining property, on the nose, as SthapanaVarga
--       found it hand-rolled.
--   §2  THE SPOKE.  Every point of the locus is a spoke into the coned
--       source: the control datum c : t ≡ lhs is exactly the path a
--       mapping-cone spoke carries.  Exhibited as a map locus → Cone of
--       the source point-map, landing in the hub's own singl.
--   §3  ONE CELL, NOT A CLASS — restated as the contractibility of §1:
--       the locus is a proposition (isContr→isProp), so there are not
--       two distinct places to fire.  This is "grows by one."
--
-- THE FEE (garbha, cited not rebuilt).  Coning off a class at level n
-- precipitates a new class at level n+1 (VakraValayaSanketa: the
-- forgotten succession precipitates as one bit, "the first veil is its
-- fee").  In the kernel that fee is the NON-DESCENDING COST: after
-- install collapses meaning-equal routes (L of SankramanaShreni), cost
-- is exactly what does not descend — the residual one level up.  Named
-- here by re-exporting the witness, so this module states install +
-- its fee together.
------------------------------------------------------------------------

module Kernel.KernelDhara_InstallIsTheConingOffOfAnObstructionTheLocusIsAContractibleConeAndTheFeeIsTheNonDescendingCost where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.HLevels using ()
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.HITs.MappingCones using (Cone ; inj ; hub ; spoke)
open import Cubical.Data.Unit using (Unit ; tt)

open import RewriteCertificate using (Tm ; Derivation)
open import ControlledGrammar using (NativeOperation ; install)
open NativeOperation

------------------------------------------------------------------------
-- १ · The locus of install is a contractible cone.
--     Control (install d) t = (t ≡ lhs); the locus is Σ[ t ] t ≡ lhs,
--     which is singl lhs read backwards — the cone, contractible.
------------------------------------------------------------------------

Locus : {l r : Tm} → Derivation l r → Type₀
Locus {l} d = Σ[ t ∈ Tm ] Control (install d) t   -- = Σ[ t ] (t ≡ l)

-- the cone: singl' l = Σ[ t ] t ≡ l, contractible with centre (l , refl).
locusIsCone : {l r : Tm} (d : Derivation l r) → isContr (Locus d)
locusIsCone {l} d .fst = l , refl
locusIsCone {l} d .snd (t , p) i = p (~ i) , λ j → p (~ i ∨ j)

------------------------------------------------------------------------
-- २ · The spoke.  Cone off the source as a point-map g : Unit → Tm,
--     g _ = l.  A control datum c : t ≡ l is exactly a mapping-cone
--     spoke: hub ≡ inj (g tt) is hub ≡ inj l, and the locus point (t,c)
--     names the spoke at t.  We land the locus in singl (hub) of that
--     cone — the contractible hub-based paths — so "install's locus" and
--     "the cone's own contractible core" are one contractible type.
------------------------------------------------------------------------

module _ {l r : Tm} (d : Derivation l r) where

  g : Unit → Tm
  g _ = l

  -- the mapping cone of the source point-map.
  TheCone : Type₀
  TheCone = Cone g

  -- each locus point gives a spoke-path in the cone: hub ≡ inj t,
  -- obtained by composing the canonical spoke (hub ≡ inj l) with inj∘(t≡l).
  toSpoke : Locus d → Σ[ y ∈ TheCone ] (hub ≡ y)
  toSpoke (t , c) = inj t , (spoke tt ∙ cong inj (sym c))

------------------------------------------------------------------------
-- ३ · One cell, not a class: the locus is a proposition.
------------------------------------------------------------------------

locusIsProp : {l r : Tm} (d : Derivation l r) (x y : Locus d) → x ≡ y
locusIsProp d x y = isContr→isProp (locusIsCone d) x y

------------------------------------------------------------------------
-- THE FEE — the residual one level up, cited from the localization
-- sequence: after install collapses meaning-equal routes, cost is
-- exactly what does not descend.
------------------------------------------------------------------------

open import Kernel.TransportShreni_TheLocalizationSequenceAsOneObjectMeaningDescendsAndCostDoesNot
  using (kernelCostDoesNotDescend)

-- install kills by a contractible cone (§§1–3, above); the fee it leaves
-- one level up is the non-descending cost (cited, one object).
theFee = kernelCostDoesNotDescend
