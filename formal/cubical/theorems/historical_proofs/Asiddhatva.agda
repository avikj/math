{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Asiddhatva — Pāṇini 8.2.1 as a termination technique for rewriting
-- systems, with the impossibility half that makes it necessary.
--
-- THE SOURCE.  Adhyy 8.2.1, `prvatrsiddham`: everything from this
-- sūtra to the end of the text is asiddha — "as if not having taken
-- effect" — with respect to everything before it.  The last three quarter-
-- chapters (8.2, 8.3, 8.4, the tripd) therefore produce output that the
-- preceding rules, and the earlier rules *within* the tripd, cannot
-- observe.  Pini, ~500 BCE; Ktyyana's vrttikas ~250 BCE; Patajali's
-- Mahbhya ~150 BCE.
--
-- THE WITNESS IS NOT INVENTED.  It is what the engine in `machine/
-- Astadhyayi.hs` (absent from this repository) actually does when it derives `vk` ("speech") from the
-- stem `vc`, and its `asiddhaAudit` prints the refusal:
--
--     vc  --8.2.30 co ku-->          vk
--          --8.2.39 jhal jao 'nte--> vg
--          --8.4.56 vvasne-->         vk
--     8.2.1 prvatrsiddham: 8.2.39 would fire on this output, refused
--
-- 8.2.39 sends k to g.  8.4.56 sends g back to k.  Let 8.2.39 see what
-- 8.4.56 produced and the derivation runs forever.  This module is that
-- two-rule cycle, and four theorems about it.
--
-- WHAT IS PROVED HERE
--
--   noNormalForm      the unstratified system has NO normal form: every
--                     element of the carrier admits a step.  Exhaustive,
--                     three cases.
--   noNormalizer      hence no normalizing function exists at all — not a
--                     clever one, not any.
--   everyLength       and reductions of every finite length exist from
--                     every point.
--
--   noStrictOrder     THE SHARP ONE.  There is no strict order — merely
--                     irreflexive and transitive — in which every rule
--                     step decreases.  Not a reduction order; not even a
--                     strict partial order.  So EVERY termination
--                     technique that works by exhibiting such an order
--                     fails on this system: recursive path orders, the
--                     Knuth–Bendix order, polynomial interpretations,
--                     matrix interpretations, and Knuth–Bendix completion
--                     itself, which is parameterised by a reduction order
--                     and cannot orient a cycle.  The proof is four lines:
--                     k > g and g > k give k > k.
--
--   vākByRefl         the stratified evaluator computes vāc ↦ vāk on the
--                     nose, and is a total function, accepted by the
--                     termination checker.
--   asiddhaLoadBearing
--                     and its result is NOT a fixpoint of the earlier
--                     stratum — 8.2.39 would fire on it.  The refusal is
--                     what terminates the system.  Take asiddhatva away and
--                     `noNormalForm` is what you have left.
--
-- SO THE STATEMENT IS: this rewriting system is not order-terminating, and
-- Pini terminates it anyway, by a constraint on which rules may OBSERVE
-- which outputs rather than by a measure that decreases.  He then shipped
-- that constraint across three quarter-chapters of a ~3983-rule production
-- system.
--
-- PRIOR ART.  The
-- qualitative parallel is documented:
-- asiddhatva has long been read as rule-suspension / level ordering —
-- Kiparsky, "On the Architecture of Pini's Grammar" (
-- Computational Linguistics, LNCS 5402, 2009, and earlier circulated
-- versions), and a full monograph exists on the suspension principle
-- itself.  Stratified and hierarchical termination is also known in
-- rewriting theory (Bergstra–Klop on layered systems; Ohlebusch on
-- modularity of termination, 1990s) — so the technique is not unknown to
-- the field, it is *late* to it, and it is not what the field teaches as
-- the general method.  What is
-- checked here is the impossibility half: the exhibition of a rule pair
-- inside the tripd for which no strict order exists at all.
--
-- No postulates, no holes, --safe.  Every theorem below is an exhaustive
-- finite case analysis or a `refl`.
------------------------------------------------------------------------

module Asiddhatva where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  The carrier: the pada-final sound of `vc`, along the path the
--     derivation actually takes.
------------------------------------------------------------------------

data Antya : Type where
  c g k : Antya

------------------------------------------------------------------------
-- 2.  The three stras, and the quarter-chapter each lives in.  The
--     quarter is not decoration: 8.2.1 makes it the thing that decides
--     what may be observed.
------------------------------------------------------------------------

data Sutra : Type where
  coḥ-kuḥ      : Sutra    -- 8.2.30  cU becomes kU at pada-end
  jhalāṃ-jaśo  : Sutra    -- 8.2.39  jhaL becomes jaŚ at pada-end
  vāvasāne     : Sutra    -- 8.4.56  jhaL becomes caR in pause

pāda : Sutra → ℕ
pāda coḥ-kuḥ     = 2      -- 8.2
pāda jhalāṃ-jaśo = 2      -- 8.2
pāda vāvasāne    = 4      -- 8.4

------------------------------------------------------------------------
-- 3.  The rules, restricted to this carrier.
------------------------------------------------------------------------

data _⟶⟨_⟩_ : Antya → Sutra → Antya → Type where
  fire-8-2-30 : c ⟶⟨ coḥ-kuḥ     ⟩ k
  fire-8-2-39 : k ⟶⟨ jhalāṃ-jaśo ⟩ g
  fire-8-4-56 : g ⟶⟨ vāvasāne    ⟩ k

-- The UNSTRATIFIED system: any rule, any time, no 8.2.1.
_⟶_ : Antya → Antya → Type
x ⟶ y = Σ Sutra (λ s → x ⟶⟨ s ⟩ y)

------------------------------------------------------------------------
-- 4.  Without 8.2.1 there is no normal form anywhere.
------------------------------------------------------------------------

Normal : Antya → Type
Normal x = (y : Antya) → ¬ (x ⟶ y)

oneStep : (x : Antya) → Σ Antya (λ y → x ⟶ y)
oneStep c = k , (coḥ-kuḥ     , fire-8-2-30)
oneStep k = g , (jhalāṃ-jaśo , fire-8-2-39)
oneStep g = k , (vāvasāne    , fire-8-4-56)

noNormalForm : (x : Antya) → ¬ (Normal x)
noNormalForm x nf = nf (fst (oneStep x)) (snd (oneStep x))

-- Hence no normalizing function exists — not a clever strategy, none.
noNormalizer : ¬ (Σ (Antya → Antya) (λ f → (x : Antya) → Normal (f x)))
noNormalizer (f , nf) = noNormalForm (f c) (nf c)

-- And reductions of every finite length exist from every point.
data Chain : ℕ → Antya → Antya → Type where
  done : {x : Antya} → Chain zero x x
  more : {n : ℕ} {x y z : Antya} → x ⟶ y → Chain n y z → Chain (suc n) x z

everyLength : (n : ℕ) (x : Antya) → Σ Antya (λ y → Chain n x y)
everyLength zero    x = x , done
everyLength (suc n) x =
  fst (everyLength n (fst (oneStep x)))
  , more (snd (oneStep x)) (snd (everyLength n (fst (oneStep x))))

------------------------------------------------------------------------
-- 5.  THE IMPOSSIBILITY.  No strict order orients this system.
--
--     A reduction order — what every order-based termination method and
--     Knuth–Bendix completion require — is in particular irreflexive and
--     transitive.  Only those two properties are used below, so the result
--     is strictly stronger than "no reduction order": not even a bare
--     strict partial order will do.
------------------------------------------------------------------------

record StrictOrder (R : Antya → Antya → Type) : Type where
  field
    irrefl : (x : Antya) → ¬ (R x x)
    trans⟨⟩ : {x y z : Antya} → R x y → R y z → R x z

-- R orients the system: for every rule step x ⟶ y we have x R y ("x > y").
Orients : (Antya → Antya → Type) → Type
Orients R = {x y : Antya} → x ⟶ y → R x y

noStrictOrder : (R : Antya → Antya → Type) → StrictOrder R → Orients R → ⊥
noStrictOrder R so or =
  StrictOrder.irrefl so k
    (StrictOrder.trans⟨⟩ so
      (or {k} {g} (jhalāṃ-jaśo , fire-8-2-39))    -- k > g,  by 8.2.39
      (or {g} {k} (vāvasāne    , fire-8-4-56)))   -- g > k,  by 8.4.56

------------------------------------------------------------------------
-- 6.  8.2.1, and the system terminates.
--
--     Each quarter-chapter runs to its own fixpoint, in order, and is
--     never re-entered.  `tripd` is a total function; the termination
--     checker accepts it, which is the whole point, given §5.
------------------------------------------------------------------------

-- what 8.2 does, as a function (8.2.39's output g is ja already, so 8.2
-- has nothing further to say about it)
step82 : Antya → Antya
step82 c = k
step82 k = g
step82 g = g

-- what 8.4 does
step84 : Antya → Antya
step84 c = c
step84 k = k
step84 g = k

-- saturation of each quarter, and the proof that it IS saturation
sat82 : Antya → Antya
sat82 x = step82 (step82 x)

sat82-fixed : (x : Antya) → step82 (sat82 x) ≡ sat82 x
sat82-fixed c = refl
sat82-fixed k = refl
sat82-fixed g = refl

sat84 : Antya → Antya
sat84 x = step84 x

sat84-fixed : (x : Antya) → step84 (sat84 x) ≡ sat84 x
sat84-fixed c = refl
sat84-fixed k = refl
sat84-fixed g = refl

-- the tripd: 8.2, then 8.4, and no way back
tripādī : Antya → Antya
tripādī x = sat84 (sat82 x)

-- vāc ↦ vāk, on the nose
vākByRefl : tripādī c ≡ k
vākByRefl = refl

------------------------------------------------------------------------
-- 7.  And asiddhatva is load-bearing, not bookkeeping.
--
--     The result is not a fixpoint of the EARLIER quarter.  8.2.39 would
--     fire on it and send k back to g, and then 8.4.56 sends it to k, and
--     §4 is what you have.  The refusal to let 8.2 observe 8.4's output is
--     the entire termination argument.
------------------------------------------------------------------------

isG : Antya → Bool
isG c = false
isG g = true
isG k = false

g≢k : ¬ (g ≡ k)
g≢k p = true≢false (cong isG p)

asiddhaLoadBearing : ¬ (step82 (tripādī c) ≡ tripādī c)
asiddhaLoadBearing = g≢k

-- The same fact stated positively: 8.2.39 applies to the derived form.
eightTwoThirtyNineWouldFire : (tripādī c) ⟶⟨ jhalāṃ-jaśo ⟩ g
eightTwoThirtyNineWouldFire = fire-8-2-39

-- and it is refused because its quarter precedes the one that produced
-- the form it would consume — which is what 8.2.1 says, and all it says.
refusedBecauseEarlier : pāda jhalāṃ-jaśo ≡ 2
refusedBecauseEarlier = refl

producedByLater : pāda vāvasāne ≡ 4
producedByLater = refl

------------------------------------------------------------------------
-- WHICH STRA THIS MODULE IS ABOUT.  The corpus contains a second module
-- about \"asiddhatva\" that models the other one.
--
-- This file is 8.2.1 पूर्वत्रासिद्धम्: any SUBSEQUENT rule is asiddha with
-- respect to any rule that PRECEDES it, so the tripd applies strictly in
-- the order enumerated and the later output is invisible backwards.  That
-- one-way, backwards blindness is exactly what `tripd` implements above
-- and exactly what `asiddhaLoadBearing` shows is doing the work: without
-- it, 8.2.39 and 8.4.56 cycle k → g → k forever, and §5 proves no strict
-- order can stop them.
--
-- `NaturalMachine/AsiddhatvaBreaksFactoring.agda` proves a different
-- thing -- that a rule reading a form ERASURE has already
-- destroyed does not factor through the current form.  That behaviour, "sees the form as it was, not as it now is",
-- is 6.4.22 असिद्धवदत्राभात्: inside the block 6.4.22-6.4.129 the rules are
-- asiddhavat with respect to EACH OTHER and apply as if simultaneously.
-- Mutual and simultaneous, not one-way and ordered.
--
-- THE TWO ARE THE TWO POLES OF ONE DISTINCTION, and the corpus already
-- names it in Jain terms: `Saptabhangi.क्रम-सह-भेदः` proves that krama
-- (successive) and saha (simultaneous) arpaa reach different positions,
-- so simultaneity is not sequential both-ness.  Read across:
--
--     8.2.1  krama   ordered, one-way blindness   buys TERMINATION (here)
--     6.4.22 saha    mutual, simultaneous         buys INFORMATION
--                                                 (AsiddhatvaBreaksFactoring)
--
-- Pini spends a stra on each.  They are not variants of one device.  The
-- correspondence is a reading; the stra
-- identification is sourced.
------------------------------------------------------------------------
