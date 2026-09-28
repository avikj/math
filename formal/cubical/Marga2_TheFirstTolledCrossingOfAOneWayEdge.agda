{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- मार्ग २ — the first tolled crossing of a one-way edge.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS.  The corpus's road network elsewhere carries
-- theorems only along two-way edges: equivalences, isomorphisms, and the
-- grade-three "two independent proofs that agree" channel of
-- `YugmaPurana_…agda` §५.  This module executes, by hand, the ROUTER'S
-- TOLL PROTOCOL for a genuinely ONE-WAY edge — a lossy map, along which
-- nothing travels for free — and carries one theorem across it.  The
-- protocol, in the order it is executed below:
--
--   §१  THE EDGE.     `par : Valli → Bool`, the length-parity of the
--       vall.  One-way and irreversibly so: infinitely many valls per
--       parity bit, no section chosen, none needed.
--
--   §२  THE TOLL.     A theorem crosses a lossy edge only on presenting
--       a descent witness: `FiberConstant par t` — the toll-gate
--       predicate of `NaturalMachine.FiniteInformation`, IMPORTED, not
--       restated.  The traveller is  t = det ∘ replay,  and the toll is
--       paid at `शुल्कम्` from `KuttakaValli.detReplay` plus one
--       induction (`sgnPar`) showing the sign is a function of the
--       parity bit alone.
--
--   §३  THE RECEIPT.  What the edge retains is priced: the fibre
--       quotient is EXACTLY ℤ/2, by `YugmaPurana_TheValliRecoversIts-
--       LengthModuloTwoAndNoFurther.agda` (absent from this repository) — its चिह्नं-दैर्घ्यात् is the
--       coarse form (length determines sign) which the toll here refines
--       (parity already determines it, `शुल्कम्-चिह्नं-दैर्घ्यात्-अनुसारि`),
--       and its विषम-पूरणम् is why no coarser edge than parity can carry
--       this traveller (`अशून्य-शुल्कम्` below: the edge to the point
--       refuses it).
--
--   §४  THE CROSSING. The decoder is CONSTRUCTED twice.  Directly:
--       `अवतरणम् = sgnOf : Bool → R` with `अवतरण-नियमः : sgnOf (par v) ≡
--       det (replay v)`.  And through the toll gate itself:
--       `उत्तीर्णम् : FactorsThrough par (det ∘ replay)` via
--       `fiberConstant→factorsThrough` (isSet ℤ paid, choice not), whose
--       computation rule `उत्तीर्ण-गणना` on states is REFL — the decoder
--       computes, it is not merely asserted to exist.
--
--   §५  THE NEGATIVE CONTROL.  The corpus's discipline: a gate that
--       admits everything certifies nothing.  `length : Valli → ℕ` is
--       refused at the same gate — `निषेधः` exhibits the two-point
--       witness ([] against a two-step vall, same parity, lengths 0
--       and 2) on which FiberConstant fails, and with it FactorsThrough.
--
-- ────────────────────────────────────────────────────────────────────
--
--   As
--     `YugmaPurana_…agda` §५ already insists, `replay` forgets far more
--     than length; the edge crossed is `par`, and the only traveller
--     ticketed is the determinant of the endpoint.
--
--   The toll-gate predicate is quoted from
--     `NaturalMachine.FiniteInformation` by import.  No definition of
--     FactorsThrough/FiberConstant is restated here; if that module's
--     meaning shifts, this crossing re-prices automatically.
------------------------------------------------------------------------

module Marga2_TheFirstTolledCrossingOfAOneWayEdge where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; znots)
open import Cubical.Data.Int using (isSetℤ)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Functions.Image using (restrictToImage)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver using (solve!)

open import Gamma0Partner using (R ; M)
open import M2Unimodular using (det)
open import KuttakaValli using (Valli ; replay ; sgn ; detReplay)
open import YugmaPurana_TheValliRecoversItsLengthModuloTwoAndNoFurther
  using (चिह्नं-दैर्घ्यात्)

-- THE TOLL-GATE PREDICATE, imported from the corpus's own toll office.
open import NaturalMachine.FiniteInformation
  using ( FactorsThrough ; FiberConstant
        ; fiberConstant→factorsThrough ; factorsThrough→fiberConstant )

open CommRingStr (ℤCommRing .snd)

------------------------------------------------------------------------
-- §१ · THE EDGE — par, the length-parity, and why it is one-way.
--
-- `par` never inspects a quotient; it counts steps mod 2.  It is lossy
-- twice over: it forgets every entry of the vall, and then all of the
-- length except its last bit.  Both fibres are infinite.
------------------------------------------------------------------------

par : Valli → Bool
par []      = false
par (q ∷ v) = not (par v)

-- the parity is a function of the length (needed for the receipt in §३)
parOfLen : ℕ → Bool
parOfLen zero    = false
parOfLen (suc n) = not (parOfLen n)

par-length : (v : Valli) → par v ≡ parOfLen (length v)
par-length []      = refl
par-length (q ∷ v) = cong not (par-length v)

------------------------------------------------------------------------
-- §२ · THE TOLL — the descent witness for det ∘ replay along par.
--
-- The traveller: t v = det (replay v).  The fare: prove t is constant
-- on the fibres of par.  Paid in two coins — `detReplay` (the endpoint's
-- determinant IS the sign) and `sgnPar` (the sign is a function of the
-- parity bit; one induction, one ring identity per branch).
------------------------------------------------------------------------

-- the sign each parity class carries
sgnOf : Bool → R
sgnOf false = 1r
sgnOf true  = - 1r

private
  sgnOf-not : (b : Bool) → sgnOf (not b) ≡ (- 1r) · sgnOf b
  -- `solve!` is passed a goal with NO variables here, and the solver
  -- builds its environment as a Vec whose length must match: it reports
  -- `0 != 1 of type ℕ`, which is a fact about the tactic and not about
  -- the ring.  Over ℤ both sides are closed terms, so they compute, and
  -- `refl` is both shorter and honest about why.
  sgnOf-not false = refl
  sgnOf-not true  = refl

sgnPar : (v : Valli) → sgn v ≡ sgnOf (par v)
sgnPar []      = refl
sgnPar (q ∷ v) = cong ((- 1r) ·_) (sgnPar v) ∙ sym (sgnOf-not (par v))

-- THE TOLL, presented at the gate: det ∘ replay is fibre-constant
-- along the parity edge.
शुल्कम् : FiberConstant par (λ v → det (replay v))
शुल्कम् v w p =
  detReplay v
    ∙∙ (sgnPar v ∙∙ cong sgnOf p ∙∙ sym (sgnPar w))
    ∙∙ sym (detReplay w)

------------------------------------------------------------------------
-- §३ · THE RECEIPT — the fibre priced at exactly ℤ/2.
--
-- Coarse bound, already on file: चिह्नं-दैर्घ्यात् (YugmaPurana §१) says
-- the sign is determined by the LENGTH.  The toll refines it: the sign
-- is determined by the length's PARITY, and the refinement recovers the
-- filed statement through par-length — so the receipt is consistent
-- with the ledger it sharpens.  That the price cannot drop below ℤ/2 —
-- that no coarser edge carries this traveller — is §५'s अशून्य-शुल्कम्,
-- YugmaPurana's विषम-पूरणम् read as a refusal.
------------------------------------------------------------------------

-- the toll implies the filed length-form of the law (यत्-तिष्ठति,
-- re-derived through the tolled edge rather than re-proved)
शुल्कम्-चिह्नं-दैर्घ्यात्-अनुसारि :
  (v w : Valli) → length v ≡ length w → det (replay v) ≡ det (replay w)
शुल्कम्-चिह्नं-दैर्घ्यात्-अनुसारि v w p =
  शुल्कम् v w (par-length v ∙∙ cong parOfLen p ∙∙ sym (par-length w))

-- and the two receipts agree where both are issued: the crossing's
-- account of the sign matches YugmaPurana's, on every equal-length pair.
receipts-agree :
  (v w : Valli) (p : length v ≡ length w)
  → चिह्नं-दैर्घ्यात् v w p ≡ (sgnPar v ∙∙ cong sgnOf (par-length v ∙∙ cong parOfLen p ∙∙ sym (par-length w)) ∙∙ sym (sgnPar w))
receipts-agree v w p = isSetℤ (sgn v) (sgn w) _ _

------------------------------------------------------------------------
-- §४ · THE CROSSING — the decoder, constructed.
--
-- Twice.  First bare-handed: sgnOf itself is total on Bool, and the
-- decode law is a path computed from the two coins directly.  Then
-- through the imported toll gate, which types the decoder on the IMAGE
-- of the edge and hands back a computation rule that is REFL on states.
------------------------------------------------------------------------

-- (a) the bare decoder: parity bit in, determinant out
अवतरणम् : Bool → R
अवतरणम् = sgnOf

अवतरण-नियमः : (v : Valli) → अवतरणम् (par v) ≡ det (replay v)
अवतरण-नियमः v = sym (detReplay v ∙ sgnPar v)

-- (b) the certified crossing: the FactorsThrough witness, minted by the
-- toll office from the toll.  Fee: isSet ℤ.  Not charged: choice.
उत्तीर्णम् : FactorsThrough par (λ v → det (replay v))
उत्तीर्णम् = fiberConstant→factorsThrough isSetℤ par (λ v → det (replay v)) शुल्कम्

-- its computation rule on states is definitional — the crossing
-- COMPUTES; this line is `refl`, not a lemma.
उत्तीर्ण-गणना :
  (v : Valli) → fst उत्तीर्णम् (restrictToImage par v) ≡ det (replay v)
उत्तीर्ण-गणना v = refl

------------------------------------------------------------------------
-- §५ · THE NEGATIVE CONTROL — a traveller refused, as it must be.
--
-- `length` itself walks up to the same gate and is turned away: [] and
-- a two-step vall sit in ONE fibre of par (both even) with lengths 0
-- and 2.  FiberConstant fails on that two-point witness, so
-- FactorsThrough fails with it — the gate is a gate, not a doorway.
------------------------------------------------------------------------

निषेधः : ¬ FiberConstant par length
निषेधः fc = znots (fc [] (0r ∷ 0r ∷ []) refl)

निषेधः-उत्तीर्णे : ¬ FactorsThrough par length
निषेधः-उत्तीर्णे ft = निषेधः (factorsThrough→fiberConstant par length ft)

-- and the dual control, pricing the toll from below: the EDGE TO THE
-- POINT (forget even the parity) refuses det ∘ replay — [] and a
-- one-step vall land on determinants 1 and −1.  So the parity bit is
-- not decorative: coarsen the edge once more and the crossing dies.
-- This is विषम-पूरणम् read as a refusal at a gate.
अशून्य-शुल्कम् : ¬ FiberConstant (λ (_ : Valli) → tt) (λ v → det (replay v))
अशून्य-शुल्कम् fc = one≢-one (fc [] (0r ∷ []) refl ∙ detReplay (0r ∷ []) ∙ eq)
  where
  open import Cubical.Data.Int using (pos ; negsuc ; posNotnegsuc)
  eq : (- 1r) · 1r ≡ - 1r
  eq = solve! ℤCommRing
  one≢-one : ¬ (Path R 1r (- 1r))
  one≢-one = posNotnegsuc 1 0
