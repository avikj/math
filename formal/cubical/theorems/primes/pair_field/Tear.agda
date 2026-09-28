{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Tear
--
-- D0025 §16 and §18, D0016 §B and §C: the tear as an OBJECT, and Γ as
-- the operation that makes the next stage's material out of it.
--
-- §16:  a separator "becomes a new object/cell in the theory graph".
-- §18:  "a failed gluing condition is exactly the tear that the next
--        Braid stage must repair."
-- D0016 §C:  Γ_α : 𝒪_α → Cell(𝒞_{α+1}), attached along ∂𝒪_α, with
--        ∂Γ⟨δ⁽ⁿ⁾⟩ = δ⁽ⁿ⁺¹⁾, and §I: "the boundary is the womb of the
--        successor form".
--
-- This is the operation whose absence is the whole complaint in §27,
-- and the concrete form of it in `machine/MathMachine.hs` (absent from this repository) is that a
-- round refuted 9,001 conjectures and failed to prove 34,320 and
-- DELETED all 43,321, keeping 30 successes.  Every one of those was a
-- witnessed distinction.  A machine that keeps only what succeeded is
-- accumulating jewels; the material of the next stage is what tore.
--
-- WHAT IS PROVED HERE.  That this net actually tears -- not as a
-- possibility, as an exhibited term.  Each thread family carries an
-- invariant BY DEFINITION (a shared-centre thread is a proof that the
-- centres agree), and the composite of the two families carries
-- NEITHER.  Concrete jewels are given and the disagreement is proved,
-- not asserted.  Then Γ takes a tear to a jewel, so the next stage's
-- material is produced by the failure rather than chosen from a menu --
-- which is the exact difference between this and the machine's `GROW`,
-- where running dry takes the next symbol off a hard-coded list.
--
------------------------------------------------------------------------

module Tear where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Relation.Nullary
open import RootedNet
open import ThreadYoneda

------------------------------------------------------------------------
-- §1  What each thread family carries, and what it does not
--
-- These are not lemmas about the relations, they ARE the relations: a
-- `sharedCentre` thread is precisely a proof that the true centres
-- agree.  Writing them out is what makes the failure in §3 legible as a
-- failure of TRANSPORT rather than as an accident of two numbers.
------------------------------------------------------------------------

centreCarried : {i j : Jewel} → Thread i j → Type
centreCarried {i} {j} _ = trueCentre i ≡ trueCentre j

radiusCarried : {i j : Jewel} → Thread i j → Type
radiusCarried {i} {j} _ = radius i ≡ radius j

-- a shared-centre thread transports the centre, and nothing says it
-- transports the radius
centreThreadCarries : (i j : Jewel) (p : trueCentre i ≡ trueCentre j)
                    → centreCarried {i} {j} (sharedCentre p)
centreThreadCarries _ _ p = p

radiusThreadCarries : (i j : Jewel) (p : radius i ≡ radius j)
                    → radiusCarried {i} {j} (sharedRadius p)
radiusThreadCarries _ _ p = p

------------------------------------------------------------------------
-- §2  Three jewels and a mixed weave
--
--   i = (3,1)   true centre 4, radius 1
--   m = (2,2)   true centre 4, radius 2     -- shares i's centre
--   k = (5,2)   true centre 7, radius 2     -- shares m's radius
--
-- so i → m → k is a legitimate two-step weave, every step of it exact.
------------------------------------------------------------------------

i₀ m₀ k₀ : Jewel
i₀ = jewel 3 1
m₀ = jewel 2 2
k₀ = jewel 5 2

step₁ : Thread i₀ m₀
step₁ = sharedCentre refl

step₂ : Thread m₀ k₀
step₂ = sharedRadius refl

mixed : Weave i₀ k₀
mixed = step₁ ◃ step₂ ◃ idPath

------------------------------------------------------------------------
-- §3  The tear: neither invariant survives the composite
------------------------------------------------------------------------

4≢7 : ¬ (trueCentre i₀ ≡ trueCentre k₀)
4≢7 p = znots (injSuc (injSuc (injSuc (injSuc p))))

1≢2 : ¬ (radius i₀ ≡ radius k₀)
1≢2 p = znots (injSuc p)

------------------------------------------------------------------------
-- §4  The tear as an object
--
-- A tear is not the absence of a proof.  It is a POSITIVE datum: two
-- jewels, a weave that really connects them, an observable that really
-- disagrees, and the size of the disagreement.  That last field is what
-- makes it generative rather than merely a complaint -- D0016 §B's
-- defect δ_σ = 𝔥_σ ⊖ 1 is a difference, and a difference has a size.
--
-- The gap is written additively (`gapWitness`) so that no truncated
-- subtraction enters, the discipline `PairConic` fixed for this net.
------------------------------------------------------------------------

record Tear : Type where
  constructor tear
  field
    from    : Jewel
    to      : Jewel
    along   : Weave from to
    gap     : ℕ
    -- the observable really disagrees ...
    parted  : ¬ (trueCentre from ≡ trueCentre to)
    -- ... and this is by exactly `gap`
    gapWitness : trueCentre to ≡ trueCentre from + gap

open Tear public

-- and this net really does tear
centreTear : Tear
centreTear = tear i₀ k₀ mixed 3 4≢7 refl

------------------------------------------------------------------------
-- §5  Γ: the successor form, born from the boundary
--
-- "सीमा = उत्तररूपस्य योनिः."  Γ sends a tear to a jewel of the next
-- stage: the one centred where the weave started, with the DEFECT as
-- its radius.  So the new material is a function of the failure and of
-- nothing else -- no menu, no list of symbols to widen to.
--
-- The equation below is `refl`.  It is stated anyway because it is the
-- one thing that has to be true of Γ for the construction to mean what
-- §C says: the generated cell REMEMBERS the defect it came from
-- (∂Γ⟨δ⟩ = δ).  Its proof is nothing; its content is the definition.
------------------------------------------------------------------------

Γ : Tear → Jewel
Γ t = jewel (centre (from t)) (gap t)

Γ-remembers : (t : Tear) → radius (Γ t) ≡ gap t
Γ-remembers t = refl

-- The generated jewel is a jewel of this same net, so the next stage is
-- reached without leaving the language -- which is what lets the
-- operation iterate at all.
Γ-of-the-tear : Γ centreTear ≡ jewel 3 3
Γ-of-the-tear = refl
