{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ThreadYoneda
--
-- D0025 §4 and T25.A, made a theorem about this net rather than a
-- picture about categories in general.
--
-- §4 boxes two claims:
--
--     a thread between jewels
--       = a coherent transformation between their total reflection profiles
--
--     a jewel is completely determined, up to the correct equivalence,
--       by how every other jewel maps into it
--
-- and T25.A asks for `Map(x,y) ≃ Nat(y x, y y)` in the chosen setting.
-- This file proves both directions of that correspondence for the
-- prime-pair net of `RootedNet`, with the naturality condition
-- written out rather than inherited.
--
-- THE PREREQUISITE, and why it was not free.  `RootedNet.Thread` is
-- the sum of two exact relations (shared centre, shared radius).
-- Neither is closed under composition with the other: a shared-centre
-- thread followed by a shared-radius thread is in general neither.  So
-- the generators do NOT form a category.
-- `Weave` below is the reflexive-transitive closure -- the free category
-- on the two families -- which is the smallest honest repair and is
-- what makes composition, and therefore Yoneda, available at all.
--
-- WHAT IS PROVED:
--
--   * `Weave` is a category: identity on both sides, associativity.
--   * `yonedaTo`   : a thread-path induces a transformation of profiles,
--                    and that transformation is NATURAL.
--   * `yonedaFrom` : every natural transformation comes from a path,
--                    namely its value at the identity.
--   * the two round trips: `yonedaFrom ∘ yonedaTo` is the identity on
--     the nose, and `yonedaTo ∘ yonedaFrom` is pointwise the identity
--     on natural transformations.
--
-- WHY IT MATTERS HERE.  D0025 §16 is the operative sentence: a local
-- event must propagate through the whole Net by transport/naturality,
-- and §27 identifies the absence of that propagation as the entire
-- failure of the machine work.  Naturality is that propagation, and
-- this file is where it stops being a word.
------------------------------------------------------------------------

module ThreadYoneda where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import RootedNet

------------------------------------------------------------------------
-- §1  Thread-paths: the free category on the two exact relations
------------------------------------------------------------------------

data Weave : Jewel → Jewel → Type where
  idPath : {i : Jewel} → Weave i i
  _◃_    : {i j k : Jewel} → Thread i j → Weave j k → Weave i k

infixr 5 _◃_

-- composition, written in diagrammatic order: `p ⊙ q` goes i → j → k
_⊙_ : {i j k : Jewel} → Weave i j → Weave j k → Weave i k
idPath  ⊙ q = q
(t ◃ p) ⊙ q = t ◃ (p ⊙ q)

infixr 6 _⊙_

------------------------------------------------------------------------
-- §2  The category laws
--
-- Left identity is definitional; the other two are inductions on the
-- path, which is why `Weave` was defined as a cons-list rather than as
-- an abstract transitive closure.
------------------------------------------------------------------------

⊙-idL : {i j : Jewel} (p : Weave i j) → idPath ⊙ p ≡ p
⊙-idL p = refl

⊙-idR : {i j : Jewel} (p : Weave i j) → p ⊙ idPath ≡ p
⊙-idR idPath = refl
⊙-idR (t ◃ p) = cong (t ◃_) (⊙-idR p)

⊙-assoc : {i j k l : Jewel}
        → (p : Weave i j) (q : Weave j k) (r : Weave k l)
        → (p ⊙ q) ⊙ r ≡ p ⊙ (q ⊙ r)
⊙-assoc idPath  q r = refl
⊙-assoc (t ◃ p) q r = cong (t ◃_) (⊙-assoc p q r)

------------------------------------------------------------------------
-- §3  The reflection profile of a jewel
--
-- `Profile j` is D0025 §4's `Map(−, j)`: the assignment sending every
-- jewel to the threads running from it into j.  This is the presheaf
-- the Yoneda statement is about, and it is the exact sense in which a
-- jewel carries "the whole Net as reflected there" -- not a copy of the
-- net, but the totality of the ways into it.
------------------------------------------------------------------------

Profile : Jewel → Jewel → Type
Profile j i = Weave i j

-- A transformation of profiles, and the naturality that makes it
-- COHERENT in §4's sense: it must commute with pre-composition, i.e.
-- it must not depend on the route by which a jewel reaches the root.
Transformation : Jewel → Jewel → Type
Transformation i j = (k : Jewel) → Profile i k → Profile j k

Natural : {i j : Jewel} → Transformation i j → Type
Natural {i} {j} η =
  {k l : Jewel} (t : Weave l k) (p : Profile i k) → η l (t ⊙ p) ≡ t ⊙ η k p

------------------------------------------------------------------------
-- §4  Yoneda, both directions (T25.A for this net)
------------------------------------------------------------------------

-- A thread-path IS a transformation of profiles: post-compose with it.
yonedaTo : {i j : Jewel} → Weave i j → Transformation i j
yonedaTo t k p = p ⊙ t

-- ...and that transformation is natural, by associativity alone.
yonedaTo-natural : {i j : Jewel} (t : Weave i j) → Natural (yonedaTo t)
yonedaTo-natural t s p = ⊙-assoc s p t

-- Every transformation is determined by where it sends the identity.
yonedaFrom : {i j : Jewel} → Transformation i j → Weave i j
yonedaFrom η = η _ idPath

------------------------------------------------------------------------
-- §5  The two round trips
------------------------------------------------------------------------

-- One direction is exact and needs nothing: the identity is the left
-- unit of composition.
yoneda-from-to : {i j : Jewel} (t : Weave i j) → yonedaFrom (yonedaTo t) ≡ t
yoneda-from-to t = refl

-- The other is where naturality does the work.  Instantiating it at the
-- path `p` itself turns "η at p" into "η at the identity, transported
-- along p" -- which is precisely §4's claim that a jewel is determined
-- by how everything maps into it.
yoneda-to-from : {i j : Jewel} (η : Transformation i j) → Natural η
               → (k : Jewel) (p : Profile i k)
               → yonedaTo (yonedaFrom η) k p ≡ η k p
yoneda-to-from η nat k p =
  p ⊙ (η _ idPath)   ≡⟨ sym (nat p idPath) ⟩
  η k (p ⊙ idPath)   ≡⟨ cong (η k) (⊙-idR p) ⟩
  η k p              ∎

------------------------------------------------------------------------
-- §6  The reweave (D0025 §16, T25.F), in the one form available here
--
-- "Suppose a new equivalence is proved, e : x ≃ y.  Univalence supplies
-- ua(e) : x = y.  Every dependent family P transports.  Therefore one
-- local equivalence changes the reflection structure everywhere it is
-- referenced."
--
-- For jewels the identification is a path in `Jewel`, and the statement
-- that the profile follows it is `subst`.  It is one line, and that is
-- the point: in this setting propagation is not machinery to be built,
-- it is what an identification MEANS.  The machine in `machine/` has no
-- such structure, so a proved theorem there can change nothing except
-- the normaliser -- which is the concrete form of §27's complaint.
------------------------------------------------------------------------

reweave : {i j : Jewel} → i ≡ j → (k : Jewel) → Profile i k → Profile j k
reweave p k = subst (λ x → Profile x k) p

reweave-refl : {i k : Jewel} (q : Profile i k) → reweave refl k q ≡ q
reweave-refl {i} {k} q = substRefl {B = λ x → Profile x k} q

-- and a thread-path is carried along an identification of its endpoints
reweaveComposes : {i j : Jewel} (p : i ≡ j) (k : Jewel) (q : Profile i k)
                → reweave p k q ≡ subst (λ x → Weave k x) p q
reweaveComposes p k q = refl
