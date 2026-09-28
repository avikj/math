{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SetTruncationDescentBoundary
--
-- THE EXACT BOUNDARY BEYOND SET-LEVEL DESCENT, AS AN EQUIVALENCE OF
-- TYPES RATHER THAN AS A FINITE EXAMPLE.
--
-- WHAT THIS REPLACES
--
-- this module does not edit it) states the boundary by exhibiting one
-- object: the order-three Smith automorphism, whose action groupoid at
-- a fixed point is `B C₃`, whose orbit set is a singleton, and whose
-- identity functor therefore cannot factor through that singleton.
-- The note's stated replay is
--
--     python3 machinery/higher_coequalizer_boundary.py (absent from this repository)
--
-- and `CLAUDE.md` (absent from this repository) (owner, 2026-08-13) says a Python script that prints
-- a number is exactly the thing that stands in for an error analysis
-- nobody did.  Per `CLAUDE.md` (absent from this repository)'s standing rule — *before running any
-- computation, write down the theorem it would replace, then prove it*
-- — the theorem that replay is standing in for is §1 below.  It needs
-- no group, no finiteness, no Smith normal form and no fixed point:
--
--     the type of set-level descent data for the identity map of `A`
--     IS the proposition `isSet A`.
--
-- So the C₃ apparatus is not the boundary; hlevel is.  The note's
-- example is one point of the equivalence's empty side.
--
-- WHAT IS CHECKED
--
--   §1  `Retracts₀ A`            the descent datum: `id_A` factors
--                                through the set truncation.
--       `retract→isSet`         one direction (a retract of a set).
--       `isSet→retract`         the other (`setTruncIdempotent`).
--       `isPropRetracts₀`        the datum is a proposition — this is
--                                the part neither direction gives, and
--                                the part that makes §1 an equivalence
--                                rather than a logical biconditional.
--       `descentDatum≃isSet`    the equivalence.
--
--   §2  `idDescends→allDescend`  the identity is the UNIVERSAL test:
--                                once it descends, every `A`-valued
--                                task descends, from any domain.
--       `descend-unique`         and the descent is unique.
--
--   §3  `insideView`             for EVERY type, at EVERY point, the
--                                space of things identified with you,
--                                *together with the identification you
--                                travelled along*, is contractible.
--                                No hypothesis.  This is the exact
--                                sense in which the obstruction of §1
--                                is invisible from inside.
--
--   §4  `noDescentS¹`            the concrete refutation, imported
--                                rather than re-derived: `S¹NotSet`
--                                lives in
--                                `SetBaseNoMonodromy`.
--                                `insideViewS¹` is §3 at the same
--                                object.  §4 is the two lenses
--                                disagreeing about one type, in two
--                                lines each.
--
-- NOVELTY: none claimed.  Both implications are library one-liners
-- (`isOfHLevelRetract 2`; `setTruncIdempotentIso`), and "a retract of
-- an n-type is an n-type" is standard HoTT.  What is not in cubical
-- v0.5, in cubical master, in agda-unimath, or in this repository
-- (all four grepped 2026-08-14) is the *packaging as an equivalence of
-- types* — i.e. `isPropRetracts₀`.  Even that is surely folklore.  The
-- contribution is that a note in this corpus asserted this boundary on
-- the authority of a Python run, and now does not have to.
--
-- Prior art searched before writing, per PROTOCOL §0: `~/agda-libs/`
-- (cubical v0.5 and master, agda-unimath, Coq-HoTT, UniMath, 1lab),
-- this repository, and WebSearch.  Grades and vocabulary are recorded
------------------------------------------------------------------------

module SetTruncationDescentBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; propBiimpl→Equiv)
open import Cubical.Foundations.HLevels
  using (isOfHLevelRetract ; isPropIsSet ; isPropΠ)
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.S1 using (S¹)
open import Cubical.HITs.SetTruncation as SetTrunc
  using (∥_∥₂ ; ∣_∣₂ ; isSetSetTrunc)

open import SetBaseNoMonodromy using (S¹NotSet)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- §1  THE BOUNDARY
--
-- `∥ A ∥₂` is the universal set under `A`; `∣_∣₂` is the unit.  The
-- question the coequalizer note asks — can the identity be recovered
-- after the collapse? — is the question whether `∣_∣₂` has a
-- retraction.
------------------------------------------------------------------------

-- The descent datum for `id_A`.  Voevodsky's lens applied literally:
-- do not ask *whether* the identity descends, ask what the type of
-- descents is.
Retracts₀ : Type ℓ → Type ℓ
Retracts₀ A = Σ[ f ∈ (∥ A ∥₂ → A) ] ((a : A) → f ∣ a ∣₂ ≡ a)

-- (a)  A retract of a set is a set.  `∥ A ∥₂` is a set by
--      construction, so a descent forces `A` down to hlevel 2 —
--      whatever `A` was.
retract→isSet : {A : Type ℓ} → Retracts₀ A → isSet A
retract→isSet (f , h) = isOfHLevelRetract 2 ∣_∣₂ f h isSetSetTrunc

-- (b)  Conversely a set is its own truncation, so the descent exists
--      and computes on the nose.
isSet→retract : {A : Type ℓ} → isSet A → Retracts₀ A
isSet→retract hA = SetTrunc.rec hA (idfun _) , λ _ → refl

-- (c)  The datum is a proposition.  Note the shape of the argument:
--      to prove `isProp X` it suffices to prove `X → isProp X`, and
--      here the hypothesis `X` is used only to extract `isSet A`,
--      which is then what makes the two components rigid.  If `A` is
--      not a set there is nothing to compare, and the statement holds
--      for the empty reason.
isPropRetracts₀ : {A : Type ℓ} → isProp (Retracts₀ A)
isPropRetracts₀ {A = A} r s = same r r s
  where
  same : Retracts₀ A → isProp (Retracts₀ A)
  same r₀ (f , h) (g , k) =
    ΣPathP ( fg
           , isProp→PathP (λ i → isPropΠ (λ a → hA (fg i ∣ a ∣₂) a)) h k )
    where
    hA : isSet A
    hA = retract→isSet r₀

    fg : f ≡ g
    fg = funExt (SetTrunc.elim (λ x → isProp→isSet (hA (f x) (g x)))
                               (λ a → h a ∙ sym (k a)))

-- (d)  Therefore: the type of set-level descent data for the identity
--      map of `A` *is* the proposition that `A` is a set.  Not "there
--      is a descent iff `A` is a set" — the two TYPES are equivalent.
descentDatum≃isSet : {A : Type ℓ} → Retracts₀ A ≃ isSet A
descentDatum≃isSet =
  propBiimpl→Equiv isPropRetracts₀ isPropIsSet retract→isSet isSet→retract

------------------------------------------------------------------------
-- §2  WHY THE IDENTITY IS THE RIGHT TEST
--
-- The coequalizer note is careful to say that "a numerical stabilizer
-- order is not by itself a counterexample: it is constant on orbits
-- and hence can be attached as a set-valued function on the orbit
-- set", and that the counterexample must consume the loop.  That
-- carefulness is exactly §2: descent of the identity is the strongest
-- demand one can make, and it implies every other one.
------------------------------------------------------------------------

-- If `id_A` descends then every `A`-valued task descends, from any
-- domain whatsoever — because `A` is then a set, and `∥_∥₂` is the
-- universal map into a set.
idDescends→allDescend :
  {A : Type ℓ} {C : Type ℓ'} → Retracts₀ A
  → (t : C → A) → Σ[ g ∈ (∥ C ∥₂ → A) ] ((c : C) → g ∣ c ∣₂ ≡ t c)
idDescends→allDescend r t = SetTrunc.rec (retract→isSet r) t , λ _ → refl

-- …and the descent is unique, so nothing is chosen.  (`DescentLaw.agda`
-- proves the analogue for set QUOTIENTS; this is the set TRUNCATION,
-- which is the recipient the coequalizer note actually needs, since it
-- quotients a groupoid rather than a relation on a set.)
descend-unique :
  {C : Type ℓ} {A : Type ℓ'} (hA : isSet A) (t : C → A)
  → (g : ∥ C ∥₂ → A) → ((c : C) → g ∣ c ∣₂ ≡ t c)
  → (x : ∥ C ∥₂) → g x ≡ SetTrunc.rec hA t x
descend-unique hA t g agree =
  SetTrunc.elim (λ x → isProp→isSet (hA (g x) (SetTrunc.rec hA t x))) agree

------------------------------------------------------------------------
-- §3  THE INSIDE VIEW
--
-- Thurston's lens: what does the object look like to someone living in
-- it?  Answer, and it is a theorem about EVERY type with no hypothesis
-- at all: standing at `a`, the space of points you can reach *paired
-- with the identification you travelled along* is contractible.  You
-- are always at the centre of a trivial world.
--
-- This is `isContrSingl`, an eight-year-old library one-liner.  It is
-- restated here under a name that says what it is being used for,
-- because §1 and §3 are the two lenses giving OPPOSITE answers about
-- the same type, and the whole point of this module is that both are
-- theorems.  Nothing is refuted; the answers are about different
-- questions, and the note that owns the boundary asks only the first.
------------------------------------------------------------------------

insideView : {A : Type ℓ} (a : A) → isContr (Σ[ x ∈ A ] (a ≡ x))
insideView a = isContrSingl a

-- The global datum the inside view does NOT give you: forgetting which
-- identification you travelled along is exactly the passage to `∥_∥₂`,
-- and §1 says that passage is reversible only at hlevel 2.

------------------------------------------------------------------------
-- §4  ONE OBJECT, TWO ANSWERS
--
-- `S¹` is the smallest non-set this repository already owns a
-- refutation for: `SetBaseNoMonodromy.S¹NotSet`, whose
-- content is the Bool double cover and `subst Cover loop true ≡ false`.
-- Imported, not re-derived.
------------------------------------------------------------------------

-- Voevodsky's answer: NO.  There is no descent datum, and by §1(c) not
-- merely "no canonical one" — the type of them is empty.
noDescentS¹ : Retracts₀ S¹ → ⊥
noDescentS¹ r = S¹NotSet (retract→isSet r)

-- Thurston's answer, about the same type, in the same file: from
-- inside, at every point, the world is contractible.
insideViewS¹ : (a : S¹) → isContr (Σ[ x ∈ S¹ ] (a ≡ x))
insideViewS¹ = insideView

-- `Retracts₀` is not a global section of the contractible `insideView`
-- fibres; those are different data types.
-- The actual dependent section space `(a : A) → Σ[ x ∈ A ] (a ≡ x)` is
-- contractible for every A; `Retracts₀ A` is left-inverse data for the
-- set-truncation unit.  `ContractibleFiberSectionBoundary.agda` checks the
-- distinction and the S¹ no-equivalence control.  The theorems above remain
