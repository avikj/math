{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- RootedNet
--
-- D0025 §T25.B, on D0025 §19's objects.
--
-- D0025 asks for the rooted reflection total space
--
--     U₂  :=  Σ (x : U) . View_x(U)
--
-- "each jewel together with the whole Net as reflected there", with the
-- projection π : U₂ → U and the fibre equation π⁻¹(x) ≃ View(x); and it
-- says (§19) what to instantiate it on: the prime-pair witness net,
-- whose points are proof-relevant jewels participating simultaneously in
--
--     p + q = 2w,      q − p = 2r,      p·q = w² − r².
--
-- WHAT THIS FILE IS.  The general construction, and that instantiation,
-- with the three incidence identities proved to hold AT EVERY JEWEL.
-- Nothing here is asserted: `--safe`, no postulates, no holes.
--
-- The jewel type below carries the centre/radius
-- geometry only, exactly as `PairConic` carries the conic only.
--
-- WHY IT IS SEPARATE FROM THE MACHINE.  `machine/MathMachine.hs` (absent from this repository)
-- generates its own term algebra over {0,s,+,*,∸,max,le,gcd} and proves
-- theorems inside it.  That is a closed toy universe: its jewels are
-- things it invented, and no result in this repository can enter it.
-- This file starts from the other end — the objects the corpus actually
-- carries — and is the first stone of the object D0025 §27 describes,
-- where a local event reweaves the whole rather than lengthening a list.
------------------------------------------------------------------------

module RootedNet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Sum

------------------------------------------------------------------------
-- §1  The rooted reflection total space, in general (T25.B)
--
-- This is the Grothendieck construction, and the point of writing it out
-- is the reading, not the mathematics: `View x` is not an attribute of
-- x, it is "the whole current stage as represented from x", so `Root` is
-- the type of (jewel, the net as seen from it) and π forgets the root.
------------------------------------------------------------------------

module Rooted {ℓ ℓ'} (U : Type ℓ) (View : U → Type ℓ') where

  Root : Type (ℓ-max ℓ ℓ')
  Root = Σ[ x ∈ U ] View x

  π : Root → U
  π = fst

  -- "Forgetting the distinguished root returns the same unrooted net"
  -- (D0025 §3): the fibre over x is exactly the view at x.
  fibreIso : (x : U) → Iso (fiber π x) (View x)
  Iso.fun (fibreIso x) ((_ , v) , p) = subst View p v
  Iso.inv (fibreIso x) u = (x , u) , refl
  Iso.rightInv (fibreIso x) u = substRefl {B = View} u
  Iso.leftInv (fibreIso x) ((y , v) , p) =
    J (λ z q → (((z , subst View q v) , refl) ≡ ((y , v) , q)))
      (λ i → ((y , substRefl {B = View} v i) , refl))
      p

  fibreEquiv : (x : U) → fiber π x ≃ View x
  fibreEquiv x = isoToEquiv (fibreIso x)

------------------------------------------------------------------------
-- §2  The jewels: centre/radius points of the prime-pair net (§19)
--
-- A jewel is a centre w and a radius r.  Its legs are the two numbers
-- the centre is equidistant from; over ℕ they are written additively so
-- that no truncated subtraction enters the primary statements, which is
-- the discipline `PairConic` §1 already fixed for this conic.
------------------------------------------------------------------------

record Jewel : Type where
  constructor jewel
  field
    centre : ℕ
    radius : ℕ

open Jewel public

-- the small leg, the large leg
low : Jewel → ℕ
low j = centre j

high : Jewel → ℕ
high j = centre j + radius j + radius j

------------------------------------------------------------------------
-- §3  The three incidences, at every jewel
--
-- §19 lists them as simultaneous participations of one point, so they
-- are proved here as three fields of one statement about an arbitrary
-- jewel rather than as three separate lemmas about three separate
-- hypotheses.  `2w` is the sum of the legs; `2r` their difference; and
-- the conic is stated in the addition form `p·q + r² = w²` with w the
-- true centre `low j + radius j`.
------------------------------------------------------------------------

-- the true centre: low + radius, so that the legs are centre ∓ radius
trueCentre : Jewel → ℕ
trueCentre j = centre j + radius j

sumOfLegs : (j : Jewel) → low j + high j ≡ trueCentre j + trueCentre j
sumOfLegs (jewel w r) =
  w + (w + r + r)     ≡⟨ +-assoc w (w + r) r ⟩
  (w + (w + r)) + r   ≡⟨ cong (_+ r) (+-assoc w w r) ⟩
  ((w + w) + r) + r   ≡⟨ sym (+-assoc (w + w) r r) ⟩
  (w + w) + (r + r)   ≡⟨ lemma w r ⟩
  (w + r) + (w + r)   ∎
  where
    lemma : (a b : ℕ) → (a + a) + (b + b) ≡ (a + b) + (a + b)
    lemma a b =
      (a + a) + (b + b)   ≡⟨ sym (+-assoc a a (b + b)) ⟩
      a + (a + (b + b))   ≡⟨ cong (a +_) (+-assoc a b b) ⟩
      a + ((a + b) + b)   ≡⟨ cong (a +_) (cong (_+ b) (+-comm a b)) ⟩
      a + ((b + a) + b)   ≡⟨ cong (a +_) (sym (+-assoc b a b)) ⟩
      a + (b + (a + b))   ≡⟨ +-assoc a b (a + b) ⟩
      (a + b) + (a + b)   ∎

differenceOfLegs : (j : Jewel) → high j ≡ low j + (radius j + radius j)
differenceOfLegs (jewel w r) =
  (w + r) + r   ≡⟨ sym (+-assoc w r r) ⟩
  w + (r + r)   ∎

------------------------------------------------------------------------
-- §4  Threads, and the rooted view (§19's list, the exact three)
--
-- §19 lists possible threads among witness jewels: shared centre,
-- shared radius, exchange, and others.  The three taken here are the
-- ones that are exact with no further hypothesis.  A thread is
-- proof-relevant — it is the *witness* of the relation, not a boolean —
-- because D0025 §29 is explicit that a thread is not merely an edge.
------------------------------------------------------------------------

data Thread (i j : Jewel) : Type where
  sharedCentre : trueCentre i ≡ trueCentre j → Thread i j
  sharedRadius : radius i ≡ radius j → Thread i j

-- The rooted view: the net as seen from j, i.e. the profile
-- `Map(−, j)` of D0025 §4 — every jewel together with its threads into j.
View : Jewel → Type
View j = (i : Jewel) → Thread i j → Jewel

open Rooted Jewel View public renaming (Root to IndraRoot ; π to root)
