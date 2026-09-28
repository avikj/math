{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AnyapohaArthakriya_TheExclusionCountIsNotAnInvariantOfTheEffectQuotient
--
-- cf-tessera-k-4, 2026-08-20.  Draw: `seed cf-tessera-k --swarm 8`, draw 4.
--
-- ====================================================================
-- THE TWO SOURCES.
--
--   DIGNĀGA, *Pramāṇasamuccaya* V (c. 480-540).  अन्यापोह / anyāpoha:
--   a general term carries no positive shared feature.  Its content is
--   the exclusion of what it is not.  A term is fixed by its contrast.
--
--   DHARMAKĪRTI, *Pramāṇavārttika* (c. 600-660).  अर्थक्रिया /
--   arthakriy: effect-performing capacity.  Dharmakrti keeps apoha
--   and puts a causal ground under it -- particulars fall together
--   because they do the same work, and the exclusion is downstream of
--   that, not primitive.
--
-- THEY DISAGREE, AND THE DISAGREEMENT IS THE OBJECT HERE, NOT A SEAM TO
-- BE SMOOTHED.  Dignga's exclusion has no positive ground behind it;
-- Dharmakrti supplies one.  What forced the move is on the record from
-- the other side: Uddyotakara (*Nyyavrttika*) and Kumrila
-- (*lokavrttika*, Apohavda) press that an exclusion is never bare --
-- it carries the very thing whose absence it is -- so exclusion cannot
-- be the ground.  This corpus already carries that exchange, in
-- `NaturalMachine.ExclusionRecoversGroundAtAPrice` (which names the two
-- rivals and refuses to adjudicate them) and in
-- `ApohaParyaya_WhetherConceptualContentIsNegativeIsWhatTheTwoSchools-
-- ActuallyDispute` (which locates the Bauddha-Jaina dispute).  Neither
-- of those is the Bauddha-internal split, and neither is this file's
-- question.
--
-- CLAIMED OF THE SOURCES: only the distinction between individuating a
-- thing by what it excludes and individuating it by what it does, and
-- that the two men ground these differently.
--
-- PROVENANCE GRADE, stated because an unchecked provenance is the same
-- class of error as a fitted constant: author, work, approximate date,
-- and the doctrine each work is known for.  NO chapter or verse is
-- verified against an edition; this container has no route to a text,
-- and no verse number is asserted anywhere above or below.
--
-- ====================================================================
-- THE OBJECT: HOW BIG IS A MEMORY, AND THE TWO ANSWERS.
--
-- `notes/CONTEXTUAL_QUANTUM_DIMENSION.md` (absent from this repository) (codex-quantum-process,
-- 2026-08-12), broadcast as
-- `collab/messages/0313-codex-quantum-process-contextual-quantum-
-- dimension-result.md` (absent from this repository), prices one finite process two ways:
--
--   k = cdim  -- the minimum number of contexts whose joint response
--                separates every class.  How many exclusions pin a
--                state down.  ANYPOHA'S NUMBER.
--   Q         -- the cardinality of the predictive quotient: how many
--                distinct response laws must coexist.  How much work
--                the states do.  ARTHAKRIY'S NUMBER.
--
-- and proves `Q ≤ m^k` (m the observation-alphabet size), with an
-- equality family attaining it.  The note's own instruction is to
-- report the pair and never to call cdim a memory dimension.
--
-- The lenses split on which number IS the memory, and this module is
-- that split, checked:
--
--   §3  ARTHAKRIY.  Once a family separates, the relation it induces
--       is equality -- so the effect quotient does not depend on which
--       separating family was offered.  General, any carrier.
--
--   §4-§5  ANYĀPOHA.  On ONE carrier, Bool × Bool, with the SAME
--       quotient throughout, three separating families whose minimum
--       sizes are 1, 2 and 3.  The exclusion count is a function of the
--       contrast class offered, not of the thing individuated.
--
-- §6: on this object Dharmakrti's criterion picks out the invariant
-- and Dignga's does not, for the reason Dharmakrti gave.
--
-- ====================================================================
-- §2 REFUTES A CLAIM OF MINE.  I read `Q ≤ m^k` together with its
-- equality family and formed
--
--     CLAIM R:  cdim = ⌈log_m Q⌉, i.e. Q and m determine k.
--
-- It is false, and `Ind-needs-three` below kills it: m = 2, Q = 4,
-- ⌈log₂ 4⌉ = 2, cdim = 3.  The equality family in the note is not
-- generic; equality there was obtained by CHOOSING the admitted
-- contexts.  `Q ≤ m^k` prices the best alphabet, never the one in hand.
-- My first witness attempt is also recorded dead, in §5.
--

module AnyapohaArthakriya_TheExclusionCountIsNotAnInvariantOfTheEffectQuotient where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; _or_ ; _⊕_ ; true≢false)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  THE MODELLING, STATED BEFORE IT IS USED.
--
-- A FAMILY is a set of admitted contexts, each an observable on the
-- carrier with its own observation type.  This is the corpus's existing
-- object: a probe is a total response map (`machinery/
-- active_observer_design.py` (absent from this repository)), a channel's content is its fibre
-- partition (`runtime/render/channel.py` (absent from this repository)), and a standpoint is an
-- observable `q : X → Y` (`NaturalMachine.ExclusionRecoversGround-
-- AtAPrice`).  The one addition is that the INDEX is part of the data,
-- because the whole question below is whether the size of the index is
-- determined by anything other than itself.
--
-- The index is a TYPE, not an entry in an enumeration; nothing here
-- assumes the admitted contexts are countable.
------------------------------------------------------------------------

record Family (X : Type₀) : Type₁ where
  constructor family
  field
    Idx : Type₀
    Obs : Idx → Type₀
    ask : (i : Idx) → X → Obs i

open Family

-- Two states are indistinguishable for a family when every admitted
-- context answers the same on both.  This is the effect relation.
Indist : {X : Type₀} (F : Family X) → X → X → Type₀
Indist F x y = (i : Idx F) → ask F i x ≡ ask F i y

-- A family separates when indistinguishable means identical.
Separating : {X : Type₀} (F : Family X) → Type₀
Separating {X} F = (x y : X) → Indist F x y → x ≡ y

-- Identity is always indistinguishable, for every family.  No
-- hypothesis: this is `cong`.
≡→Indist : {X : Type₀} (F : Family X) {x y : X} → x ≡ y → Indist F x y
≡→Indist F p i = cong (ask F i) p

------------------------------------------------------------------------
-- 2.  CONVENIENCE CONSTRUCTORS.  Families of index size one, two and
--     three over a fixed observation type.
------------------------------------------------------------------------

data Three : Type₀ where
  t₀ t₁ t₂ : Three

Only : {X Y : Type₀} → (X → Y) → Family X
Only {X} {Y} q = family Unit (λ _ → Y) (λ _ → q)

Pair : {X Y : Type₀} → (X → Y) → (X → Y) → Family X
Pair {X} {Y} q r = family Bool (λ _ → Y) sel
  where
    sel : Bool → X → Y
    sel false = q
    sel true  = r

Triple : {X Y : Type₀} → (X → Y) → (X → Y) → (X → Y) → Family X
Triple {X} {Y} q r s = family Three (λ _ → Y) sel
  where
    sel : Three → X → Y
    sel t₀ = q
    sel t₁ = r
    sel t₂ = s

------------------------------------------------------------------------
-- 3.  ARTHAKRIY.  THE EFFECT RELATION IS NOT A FUNCTION OF THE FAMILY.
--
-- If F separates, then everything F identifies, EVERY family identifies
-- -- because F identifies only identicals, and identicals are
-- identified by anything.  So among separating families the induced
-- relation is one and the same relation, on any carrier, with no
-- finiteness, decidability or size hypothesis anywhere.
--
-- This is the exact sense in which "how many response laws coexist" is
-- an invariant of the process: it is `_≡_` on the carrier, and the
-- admitted contexts drop out.
------------------------------------------------------------------------

separating→collapses : {X : Type₀} (F G : Family X)
  → Separating F → (x y : X) → Indist F x y → Indist G x y
separating→collapses F G sepF x y u = ≡→Indist G (sepF x y u)

-- Symmetrically, hence: any two separating families induce the very
-- same effect relation.  This is the arthakriy invariant.
same-effect-relation : {X : Type₀} (F G : Family X)
  → Separating F → Separating G
  → (x y : X) → (Indist F x y → Indist G x y) × (Indist G x y → Indist F x y)
same-effect-relation F G sepF sepG x y =
  separating→collapses F G sepF x y , separating→collapses G F sepG x y

-- And it is equality, stated without reference to any second family.
separating→is-≡ : {X : Type₀} (F : Family X) → Separating F
  → (x y : X) → (Indist F x y → x ≡ y) × (x ≡ y → Indist F x y)
separating→is-≡ F sepF x y = sepF x y , ≡→Indist F

------------------------------------------------------------------------
-- 4.  ONE CARRIER, THREE SEPARATING FAMILIES.
--
-- Carrier: four states.  By §3 the effect quotient is the same for all
-- three families below -- it is equality on `St`, four classes.
------------------------------------------------------------------------

St : Type₀
St = Bool × Bool

-- (a) THE WHOLE STATE, read by one context.  Observation alphabet is
--     St itself, m = 4.
Whole : Family St
Whole = Only {St} {St} (λ x → x)

Whole-sep : Separating Whole
Whole-sep x y u = u tt

-- (b) THE TWO COORDINATES, m = 2.
p₀ p₁ : St → Bool
p₀ x = fst x
p₁ x = snd x

Coord : Family St
Coord = Pair p₀ p₁

Coord-sep : Separating Coord
Coord-sep x y u i = (u false i , u true i)

-- Neither coordinate alone separates.
p₀-alone-fails : ¬ Separating (Only p₀)
p₀-alone-fails sep =
  true≢false (cong snd (sep (true , true) (true , false) (λ _ → refl)))

p₁-alone-fails : ¬ Separating (Only p₁)
p₁-alone-fails sep =
  true≢false (cong fst (sep (true , true) (false , true) (λ _ → refl)))

-- (c) THREE STATE-INDICATORS, m = 2.  Each context answers "are you
--     this one?" for one of three of the four states; the fourth state
--     is the one that answers no to everything.
ind₀ ind₁ ind₂ : St → Bool
ind₀ x = fst x and snd x
ind₁ x = fst x and not (snd x)
ind₂ x = not (fst x) and snd x

Ind : Family St
Ind = Triple ind₀ ind₁ ind₂

-- The three together separate: the state is reconstructible from the
-- three answers.
reconInd : Bool → Bool → Bool → St
reconInd u v w = (u or v , u or w)

reconInd-ok : (x : St) → reconInd (ind₀ x) (ind₁ x) (ind₂ x) ≡ x
reconInd-ok (false , false) = refl
reconInd-ok (false , true)  = refl
reconInd-ok (true  , false) = refl
reconInd-ok (true  , true)  = refl

Ind-sep : Separating Ind
Ind-sep x y u =
  sym (reconInd-ok x)
  ∙ (λ i → reconInd (u t₀ i) (u t₁ i) (u t₂ i))
  ∙ reconInd-ok y

------------------------------------------------------------------------
-- 5.  NO TWO OF THE THREE INDICATORS SEPARATE.
--
-- Each pair leaves one collision standing, and the survivor is always
-- the unnamed fourth state: an exclusion family that names three things
-- cannot, with two of its names withdrawn, tell the two it no longer
-- names apart.  That is the contrast-class dependence, concretely.
------------------------------------------------------------------------

ind₀₁-fails : ¬ Separating (Pair ind₀ ind₁)
ind₀₁-fails sep =
  true≢false
    (cong snd
      (sep (false , true) (false , false) (λ { false → refl ; true → refl })))

ind₀₂-fails : ¬ Separating (Pair ind₀ ind₂)
ind₀₂-fails sep =
  true≢false
    (cong fst
      (sep (true , false) (false , false) (λ { false → refl ; true → refl })))

ind₁₂-fails : ¬ Separating (Pair ind₁ ind₂)
ind₁₂-fails sep =
  true≢false
    (cong fst
      (sep (true , true) (false , false) (λ { false → refl ; true → refl })))

-- Packaged: `Ind` separates and no two-member subfamily of it does.
-- This is the kill for CLAIM R of the header (m = 2, Q = 4, cdim = 3).
Ind-needs-three :
  Separating Ind
  × (¬ Separating (Pair ind₀ ind₁))
  × (¬ Separating (Pair ind₀ ind₂))
  × (¬ Separating (Pair ind₁ ind₂))
Ind-needs-three = Ind-sep , ind₀₁-fails , ind₀₂-fails , ind₁₂-fails

------------------------------------------------------------------------
-- 5'.  MY FIRST WITNESS, RECORDED DEAD.
--
-- Before the indicators I tried {p₀ , p₁ , parity} as the three-context
-- family, on the reasoning that parity is "a context the coordinates do
-- not name".  It witnesses nothing: any two of its three members
-- already separate, because parity plus either coordinate recovers the
-- other.  Checked below rather than asserted, since the whole content
-- of §5 is a claim about subfamilies and I do not get to make that
-- claim loosely in one place and tightly in another.
--

par : St → Bool
par x = fst x ⊕ snd x

reconPar : Bool → Bool → St
reconPar u v = (u , u ⊕ v)

reconPar-ok : (x : St) → reconPar (p₀ x) (par x) ≡ x
reconPar-ok (false , false) = refl
reconPar-ok (false , true)  = refl
reconPar-ok (true  , false) = refl
reconPar-ok (true  , true)  = refl

-- so a two-member subfamily of {p₀ , p₁ , par} already separates:
p₀-par-sep : Separating (Pair p₀ par)
p₀-par-sep x y u =
  sym (reconPar-ok x)
  ∙ (λ i → reconPar (u false i) (u true i))
  ∙ reconPar-ok y

------------------------------------------------------------------------
-- 6.  THE SPLIT, AND HOW NARROW THE VERDICT IS.
--
-- Same carrier, same effect quotient throughout (§3 applied to the
-- three separating families of §4).  Minimum admitted-context counts:
-- one for `Whole`, two for `Coord` (§4, `p₀-alone-fails`,
-- `p₁-alone-fails`), three for `Ind` (§5).
--
-- So: the effect count is an invariant of the carrier; the exclusion
-- count is a function of the contrast class handed to you, and not of
-- the thing individuated.  On the question "how big is the memory",
-- arthakriy answers and anypoha, alone, cannot -- and the mechanism
-- of the failure is the one Dharmakrti's causal ground was introduced
-- to repair, and the one Uddyotakara and Kumrila pressed from outside.
--
-- HOW NARROW.  This is a verdict about ONE question about ONE object,
-- and it is not a ranking of two men or two positions.  Dignga's
-- number is real and it is not memory: `notes/CONTEXTUAL_QUANTUM_-
-- DIMENSION.md` (absent from this repository) already priced it as interrogation cost, and the three
-- families above are three interrogation designs for one memory, which
-- is a fact about designs and not a defect in any of them.  A term
-- fixed by its contrast is a perfectly good term; it is just not a
-- cardinality.  Anything stronger than that would be a durnaya --
-- a standpoint asserting itself by denying another -- and this module
-- does not assert it.
--
-- NOT SETTLED HERE: the minimum over ALL families on a carrier (that is
-- a quantity, and §4 gives one at 1 for `St`); whether `Whole`'s
-- alphabet-size 4 should be charged against its context count, which is
-- the trade `Q ≤ m^k` prices and which no theorem above bounds from
-- below for a GIVEN family; and Dignga's own scope analysis of "the
-- other" (synonyms, sub- and superordinates), which
-- `notes/EXCLUSION_IS_NOT_AN_OPERATOR.md` (absent from this repository) §3 also records as OPEN.
------------------------------------------------------------------------

-- The two answers, side by side, as one checked object.
vivādaḥ :
    -- arthakriy: for any carrier, any two separating families induce
    -- the same effect relation.
    ( {X : Type₀} (F G : Family X) → Separating F → Separating G
      → (x y : X) → (Indist F x y → Indist G x y) × (Indist G x y → Indist F x y) )
    -- anypoha: on one carrier with one effect quotient, three
    -- separating families needing one, two and three contexts.
  × ( Separating Whole )
  × ( Separating Coord × (¬ Separating (Only p₀)) × (¬ Separating (Only p₁)) )
  × ( Separating Ind
      × (¬ Separating (Pair ind₀ ind₁))
      × (¬ Separating (Pair ind₀ ind₂))
      × (¬ Separating (Pair ind₁ ind₂)) )
vivādaḥ =
    (λ F G sepF sepG x y → same-effect-relation F G sepF sepG x y)
  , Whole-sep
  , (Coord-sep , p₀-alone-fails , p₁-alone-fails)
  , Ind-needs-three
