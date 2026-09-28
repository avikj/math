{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TransporterPortReduction
--
-- A PORT IS NOT A NEW KIND OF CONSTRAINT.  It is the same constraint at
-- a bigger point.
--
-- `machinery/situated_constructor_port.py` (absent from this repository) (legacy, read not run) claims
-- to be "a three-point executable theorem": a live *port* — a supplied
-- relation `g ▸ c ≡ r` on top of the endpoint relation `g ▸ s ≡ t` —
-- "trivializes a constructor torsor without canonizing it", certified by
-- enumerating `S₃`.  This module states and checks what that enumeration
-- was standing in for, and it needs no enumeration, because it needs no
-- new theorem: the ported transporter of an action `A` is *literally the
-- unported transporter of the product action* `A × B` at the pair point
-- `(s , c)`.  Restore and balance — the unfamiliar operation is reduced
-- to the one already justified.
--
-- Everything torsor-theoretic is then cited, not reproved, from
-- `StabilizerTorsor` (R0027; `isTorsorT`,
-- `uniqueCertificate→contrStab`, `contrStab→uniqueCertificate`).  The
-- new content of this file is exactly four things:
--
--   §1  `prodAction`         the diagonal action on pairs, so that
--                            "port" becomes a defined notion and not a
--                            primitive one.
--   §2  `portUnfold`         a ported transporter IS a group element
--                            satisfying both relations (an equivalence,
--                            not a convention).
--       `stabProj`,          adding a port never enlarges the
--       `stabProj-inj`       stabilizer: the joint stabilizer embeds in
--                            the base one.  Monotonicity of the
--                            selection, checked.
--   §3  `RedundantPort`,     THE CLERK'S TEST.  A port whose relation is
--       `redundantPort-      already implied by the endpoint relation
--        CertifiesNothing`   cannot certify anything the endpoint
--                            relation did not already certify.  So a
--                            declared port either exhibits a stabilizer
--                            element that MOVES its context, or it is
--                            decoration.  This is the statement the
--                            Python module's `SelectionCertificate.
--                            verifies` checks at run time for one input;
--                            here it is checked for every action, every
--                            group, once.
--   §4  two controls,        `unitPortRedundant`: a port into a set the
--       opposite verdicts    group cannot move is redundant for every
--                            action — so "the port fired" is not a
--                            consequence of a port being *declared*.
--                            `regularPortTrivializes`: a port into the
--                            regular action at `1g` forces the joint
--                            stabilizer to be contractible for every
--                            group and every base action, however large
--                            the unported stabilizer was.
--                            Without the first, §3 has no bite; without
--                            the second, §3 would be a proof that ports
--                            never work.
------------------------------------------------------------------------

module TransporterPortReduction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Algebra.Group.Base

open import StabilizerTorsor using (Action ; module Torsor)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

------------------------------------------------------------------------
-- §1  The diagonal action on pairs.
--
-- This is the whole reduction.  Once it exists, "port" is a defined
-- word: a port on a transporter of `A` is a transporter of `A × B`.
------------------------------------------------------------------------

prodAction : (G : Group ℓ) {X : Type ℓ'} {Y : Type ℓ''}
           → Action G X → Action G Y → Action G (X × Y)
Action.isSetX (prodAction G A B) =
  isSet× (Action.isSetX A) (Action.isSetX B)
Action._▸_ (prodAction G A B) g (x , y) =
  Action._▸_ A g x , Action._▸_ B g y
Action.▸-1g (prodAction G A B) (x , y) =
  ΣPathP (Action.▸-1g A x , Action.▸-1g B y)
Action.▸-· (prodAction G A B) g h (x , y) =
  ΣPathP (Action.▸-· A g h x , Action.▸-· B g h y)

------------------------------------------------------------------------
-- §2  Ports, unfolded; and the monotonicity of porting.
------------------------------------------------------------------------

module Port (G : Group ℓ) {X : Type ℓ'} {Y : Type ℓ''}
            (A : Action G X) (B : Action G Y) where

  private
    module AX = Action A
    module AY = Action B

  -- The three torsor structures in play.  `P` is the ported one; it is
  -- not a new construction, it is `Torsor` at the product action.
  module TX = Torsor G A
  module TY = Torsor G B
  module P  = Torsor G (prodAction G A B)

  -- The base type: `g` carries `s` to `t` AND `c` to `r`.  This is the
  -- Python module's `SelectionCertificate.verifies` as a type.
  Ported : (s t : X) (c r : Y) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  Ported s t c r =
    Σ[ g ∈ ⟨ G ⟩ ] ((AX._▸_ g s ≡ t) × (AY._▸_ g c ≡ r))

  -- (2.1) A ported transporter IS a transporter of the product action.
  -- An equivalence, so nothing is lost or smuggled by the reduction.
  portUnfold : (s t : X) (c r : Y) → Ported s t c r ≃ P.T (s , c) (t , r)
  portUnfold s t c r = Σ-cong-equiv-snd (λ _ → ΣPath≃PathΣ)

  -- The two directions, named, since the proofs below use them.
  toPort : {s t : X} {c r : Y} → Ported s t c r → P.T (s , c) (t , r)
  toPort (g , p , q) = g , ΣPathP (p , q)

  fromPort : {s t : X} {c r : Y} → P.T (s , c) (t , r) → Ported s t c r
  fromPort (g , e) = g , cong fst e , cong snd e

  -- (2.2) Forgetting the port.  The Python module's last line, "port
  -- withdrawn: lawful transporter = …", is this map.
  forgetPort : {s t : X} {c r : Y} → P.T (s , c) (t , r) → TX.T s t
  forgetPort (g , e) = g , cong fst e

  -- (2.3) MONOTONICITY.  A port never enlarges the stabilizer: the joint
  -- stabilizer embeds into the base stabilizer.  (`stabProj` is even a
  -- group homomorphism for the transporter composition; not needed.)
  stabProj : {s : X} {c : Y} → P.Stab (s , c) → TX.Stab s
  stabProj = forgetPort

  stabProj-inj : {s : X} {c : Y} (u v : P.Stab (s , c))
               → stabProj u ≡ stabProj v → u ≡ v
  stabProj-inj u v e = P.transporterPath (cong fst e)

  ------------------------------------------------------------------
  -- §3  THE CLERK'S TEST.
  --
  -- Declaring a port is free.  What makes a port do work is that some
  -- element of the base stabilizer MOVES the port's context.  If none
  -- does, the port is redundant, and then it certifies nothing that the
  -- endpoint relation did not already certify.
  ------------------------------------------------------------------

  RedundantPort : X → Y → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  RedundantPort s c = (g : ⟨ G ⟩) → AX._▸_ g s ≡ s → AY._▸_ g c ≡ c

  -- Under redundancy the projection of (2.3) has an inverse, so the two
  -- stabilizers agree.  Nothing was cut.
  redundantSection : {s : X} {c : Y}
                   → RedundantPort s c → TX.Stab s → P.Stab (s , c)
  redundantSection red (g , p) = g , ΣPathP (p , red g p)

  redundantIso : {s : X} {c : Y}
               → RedundantPort s c → Iso (P.Stab (s , c)) (TX.Stab s)
  Iso.fun      (redundantIso red)   = stabProj
  Iso.inv      (redundantIso red)   = redundantSection red
  Iso.rightInv (redundantIso red) u = TX.transporterPath refl
  Iso.leftInv  (redundantIso red) u = P.transporterPath refl

  -- The theorem.  If a REDUNDANT port makes the ported selection unique,
  -- then the unported selection was already unique: the port bought
  -- nothing.  (`isContr (TX.Stab s)` is R0027's exact trivialization
  -- criterion for the unported transporter, `TX.contrStab→
  -- uniqueCertificate`.)
  redundantPortCertifiesNothing : {s t : X} {c r : Y}
    → RedundantPort s c
    → P.T (s , c) (t , r)
    → isProp (P.T (s , c) (t , r))
    → isContr (TX.Stab s)
  redundantPortCertifiesNothing {s} {t} {c} {r} red pt prop =
    isOfHLevelRetractFromIso 0 (invIso (redundantIso red))
      (P.uniqueCertificate→contrStab pt prop)

  -- Contrapositive, in the form a clerk uses it, and at an arbitrary
  -- conclusion so that it composes with whatever the caller's refutation
  -- of `isContr (TX.Stab s)` happens to be: a redundant port cannot
  -- deliver a unique certificate over a nontrivial base stabilizer.
  redundantPort-noSelection : {W : Type ℓ'''} {s t : X} {c r : Y}
    → RedundantPort s c
    → P.T (s , c) (t , r)
    → (isContr (TX.Stab s) → W)
    → isProp (P.T (s , c) (t , r)) → W
  redundantPort-noSelection red pt no prop =
    no (redundantPortCertifiesNothing red pt prop)

  ------------------------------------------------------------------
  -- §4  The criterion itself, cited from R0027 at the product action.
  -- Nothing is reproved; this is the point of the reduction.
  ------------------------------------------------------------------

  portDecides→trivialJointStab : {s t : X} {c r : Y}
    → P.T (s , c) (t , r) → isProp (P.T (s , c) (t , r))
    → isContr (P.Stab (s , c))
  portDecides→trivialJointStab = P.uniqueCertificate→contrStab

  trivialJointStab→portDecides : {s t : X} {c r : Y}
    → isContr (P.Stab (s , c)) → isProp (P.T (s , c) (t , r))
  trivialJointStab→portDecides = P.contrStab→uniqueCertificate

  -- …and the non-canonicity, also cited: even when the port decides,
  -- any two ported certificates differ by a UNIQUE joint-stabilizer
  -- element.  Trivialized, not canonized.
  portedTorsor : {s t : X} {c r : Y} (t₁ t₂ : P.T (s , c) (t , r))
    → isContr (Σ[ u ∈ P.Stab (s , c) ] ((P._∙T_ t₁ u) ≡ t₂))
  portedTorsor = P.isTorsorT

------------------------------------------------------------------------
-- §5  Iteration: k ports.
--
-- The general procedure, with no case left hidden.  A k-port selection
-- problem is a 1-port selection problem for the (k−1)-fold product
-- action; `prodAction` is associative enough that no new construction is
-- needed at any k.  `twoPortAction` is written out so that the shape is
-- visible; every k is the same line.
--
-- The tuple of points whose joint stabilizer is contractible is a BASE
-- of the action in the sense of computational group theory (Sims 1970;
-- Schreier–Sims); this iteration is its stabilizer chain.  Cited.
------------------------------------------------------------------------

twoPortAction : (G : Group ℓ) {X : Type ℓ'} {Y : Type ℓ''} {Z : Type ℓ'''}
  → Action G X → Action G Y → Action G Z → Action G (X × (Y × Z))
twoPortAction G A B C = prodAction G A (prodAction G B C)

------------------------------------------------------------------------
-- §6  Controls, with opposite verdicts.
--
-- Both are needed.  Without `unitPortRedundant`, §3 might be vacuous
-- (no port is ever redundant).  Without `regularPortTrivializes`, §3
-- might be a proof that ports never do anything.
------------------------------------------------------------------------

-- (6.1) A port into a set the group cannot move.  Redundant for EVERY
-- base action, every group, every point.  So declaring a port is not
-- evidence that a port fired.
UnitAction : (G : Group ℓ) → Action G Unit
Action.isSetX (UnitAction G)      = isSetUnit
Action._▸_ (UnitAction G) g x     = x
Action.▸-1g (UnitAction G) x      = refl
Action.▸-· (UnitAction G) g h x   = refl

unitPortRedundant : (G : Group ℓ) {X : Type ℓ'} (A : Action G X) (s : X)
  → Port.RedundantPort G A (UnitAction G) s tt
unitPortRedundant G A s g p = refl

-- (6.2) A port into the regular action at the identity.  The joint
-- stabilizer is contractible for EVERY group and EVERY base action —
-- including bases whose own stabilizer is all of G.
regularAction : (G : Group ℓ) → Action G ⟨ G ⟩
Action.isSetX (regularAction G)    = GroupStr.is-set (snd G)
Action._▸_ (regularAction G)       = GroupStr._·_ (snd G)
Action.▸-1g (regularAction G)      = GroupStr.·IdL (snd G)
Action.▸-· (regularAction G) g h x = sym (GroupStr.·Assoc (snd G) g h x)

module _ (G : Group ℓ) where
  open GroupStr (snd G)

  regularStabContr : isContr (Torsor.Stab G (regularAction G) 1g)
  regularStabContr =
    Torsor.idT G (regularAction G) 1g ,
    λ u → Torsor.transporterPath G (regularAction G)
            (sym (sym (·IdR (fst u)) ∙ snd u))

  -- The port trivializes: joint stabilizer contractible, for any base.
  regularPortTrivializes : {X : Type ℓ'} (A : Action G X) (s : X)
    → isContr (Torsor.Stab G (prodAction G A (regularAction G)) (s , 1g))
  regularPortTrivializes A s =
    ( Torsor.idT G (prodAction G A (regularAction G)) (s , 1g)
    , λ u → Torsor.transporterPath G (prodAction G A (regularAction G))
              (sym (sym (·IdR (fst u)) ∙ cong snd (snd u))) )

  -- …hence every ported certificate against the regular port is unique,
  -- however big the unported stabilizer `Stab s` was.
  regularPortDecides : {X : Type ℓ'} (A : Action G X) (s : X) {t : X} {r : ⟨ G ⟩}
    → isProp (Torsor.T G (prodAction G A (regularAction G)) (s , 1g) (t , r))
  regularPortDecides A s =
    Torsor.contrStab→uniqueCertificate G (prodAction G A (regularAction G))
      (regularPortTrivializes A s)
