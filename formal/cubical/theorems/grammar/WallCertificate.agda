{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- WallCertificate
--
--
-- The machine's loop is CLOSE / CERTIFY / PORT / GROW, and CERTIFY is the
-- step that was described but never carried: "prove the wall: grammar
-- induction (all terms factor through the ports granted) + exact residual
-- check", so that saturation stops being an empirical whimper ("nothing
-- new formed for a while") and becomes a certificate ("no future term of
-- mine CAN form; here is the proof").  Its Python original is retired by
-- the ban.  This module is the statement, checked.
--
--
-- WHAT IS GENERAL, AND WHAT IS INSTANCE  (read this before quoting it)
--
-- GENERAL — §1, `Algebra.Wall.wall`.  A term algebra over an ARBITRARY
--   signature (a type `Op` of operations with arities `ar : Op → ℕ`),
--   an ARBITRARY carrier `A`, an ARBITRARY interpretation, terms with
--   variables in an ARBITRARY type `V`, and an ARBITRARY binary relation
--   `_≈_` on `A`.  Nothing is assumed of `≈`: not reflexivity, not
--   symmetry, not transitivity, not propositionality (same discipline as
--   `ProjectionChargeAudit2.Descent`, whose relation is equally naked).
--   The theorem is: if every operation preserves `≈` argument-wise
--   (`IsCongruence`), then for every term `t` and every pair of
--   environments related pointwise, `eval ρ t ≈ eval σ t`.  Proof: one
--   mutual structural induction over terms and argument lists, four
--   clauses, no side conditions.  THIS is the wall.  Note where the
--   hypothesis is used and where it is not: the variable case consumes
--   the pointwise hypothesis directly, so no reflexivity of `≈` is ever
--   needed — the wall is a statement about the SIGNATURE, not about the
--   relation being an equivalence.
--
-- INSTANCE — §2–§5.  One concrete finite world, chosen to be the charge
--   world the rest of this corpus already uses: carrier `Bool × Bool`
--   (`ProjectionChargeAudit.State`), partition by total charge
--   `tot (a,b) = a ⊕ b`, vocabulary {swap, mix} (unary + binary).  Every
--   claim in §2–§5 is about that world only.  The finite counts are
--   exhaustive over its four states and are `refl`; they are exact
--   symbolic computation, hence proof (CLAUDE.md (absent from this repository)), not measurement.
--
--
-- THE FOUR THINGS DELIVERED
--
--   §1  wall                    grammar induction, general form:
--                               congruence ⇒ no term separates.
--   §3  theWall, noSeparation   the instance.  `noSeparation` is the
--                               certificate's headline: for EVERY term t
--                               of the granted vocabulary and every pair
--                               x ≈ y, t cannot separate x from y.
--       saturation              and the exact converse: the relation
--                               "no term of mine distinguishes x from y"
--                               IS `≈`, as an equivalence of props.  So
--                               the partition is not merely stable under
--                               the vocabulary — it is precisely the
--                               vocabulary's resolving power.  CLOSE has
--                               provably nothing left to do.
--   §4  readNotCongruence       THE BREACH.  A wall theorem with no
--       formation, breaks       exhibited breach is decorative.  Grant
--                               one further unary operation — read the
--                               local coordinate, `rd⁺` — which is NOT a
--                               congruence, and the machine's OWN grammar
--                               immediately forms
--                                   mix (rd⁺ x) x
--                               whose total charge is the SECOND bit:
--                               the hidden fibre coordinate, formed out
--                               of one port grant plus the old
--                               vocabulary.  That is the formation event,
--                               with the exact separated pair
--                               (false,false) ≁ (true,true) exhibited.
--       embed, noSeparationEmb  and the port is the ONLY route: old terms
--                               keep their meanings verbatim under the
--                               grown signature (`embed-eval`), so no
--                               term that avoids `rd⁺` separates anything.
--                               PORT and GROW are the only doors, checked.
--   §5  everyTermDescends       THE RESIDUAL AS AN OBJECT.  Every term's
--       quotient≃Bool           charge descends to the quotient (reusing
--       torsor-*                `ProjectionChargeAudit2.Descent` verbatim
--       worldSplit              — descent ≃ respect, so this is the same
--       *-size                  theorem twice), the quotient is exactly
--                               `Bool` (two classes, the port menu), each
--                               class is a free transitive torsor under
--                               the annihilator {(false,false),(true,true)}
--                               ≅ ℤ/2 (`torsor-transitive`,
--                               `torsor-free`), and the world splits as
--                               visible × hidden, `State ≃ Bool × Bool`
--                               with first factor the term-visible charge
--                               and second factor the residue no term
--                               reaches (`hidden-varies-in-class`).  The
--                               "endpoint × fibre" of THE_MACHINE.md (absent from this repository), as
--                               an equivalence rather than a picture.
--
-- Read with: ProjectionChargeAudit2 (Descends ≃ Respects — §5 instantiates
-- it), NaturalMachine/GaugeOrbitClasses (transcript fibres = cosets of the
-- annihilator — the same wall in the character-theoretic presentation;
-- §5's torsor statements are its two-bit shadow).
--
-- --safe, no postulates, no holes, no `Type`-level cheats.
------------------------------------------------------------------------

module WallCertificate where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt; Unit*; tt*)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.SetQuotients as SQ using (_/_; [_]; eq/; squash/)

import ProjectionChargeAudit2 as PCA2

------------------------------------------------------------------------
-- §1  THE GENERAL THEOREM: grammar induction
--
-- A signature is a type of operations with arities.  Terms over it, with
-- variables in V, are the free algebra; `Args n` is a list of n terms
-- (kept as its own inductive type rather than `Vec Term n` so that the
-- structural induction of `wall` is visibly terminating without a
-- termination-checker detour through `map`).
------------------------------------------------------------------------

-- Argument tuples, by recursion on the arity.  (Deliberately NOT `Vec`:
-- matching on a length-indexed vector needs injectivity of `suc`, which
-- Cubical Agda flags as not-yet-supported pattern matching.  Recursion on
-- ℕ has no index to unify, so everything below is warning-free and
-- computes on transports.)
Tup : ∀ {ℓ} (A : Type ℓ) → ℕ → Type ℓ
Tup A zero    = Unit*
Tup A (suc n) = A × Tup A n

module Grammar {ℓ ℓ'} (Op : Type ℓ) (ar : Op → ℕ) (V : Type ℓ') where

  infixr 5 _◂_

  data Term : Type (ℓ-max ℓ ℓ')
  data Args : ℕ → Type (ℓ-max ℓ ℓ')

  data Term where
    var  : V → Term
    node : (o : Op) → Args (ar o) → Term

  data Args where
    ε   : Args zero
    _◂_ : {n : ℕ} → Term → Args n → Args (suc n)

-- An algebra for the signature: a carrier and an interpretation.

module Algebra {ℓ ℓ' ℓA} (Op : Type ℓ) (ar : Op → ℕ) (V : Type ℓ')
               (A : Type ℓA) (⟦_⟧op : (o : Op) → Tup A (ar o) → A) where

  open Grammar Op ar V public

  eval     : (V → A) → Term → A
  evalArgs : {n : ℕ} → (V → A) → Args n → Tup A n

  eval ρ (var v)     = ρ v
  eval ρ (node o as) = ⟦ o ⟧op (evalArgs ρ as)

  evalArgs ρ ε        = tt*
  evalArgs ρ (t ◂ as) = eval ρ t , evalArgs ρ as

  ----------------------------------------------------------------------
  -- The wall, for an arbitrary relation on the carrier.
  ----------------------------------------------------------------------

  module Wall {ℓR} (_≈_ : A → A → Type ℓR) where

    -- ≈ argument-wise on argument tuples.
    Pointwise : {n : ℕ} → Tup A n → Tup A n → Type ℓR
    Pointwise {n = zero}  _        _        = Unit*
    Pointwise {n = suc n} (x , xs) (y , ys) = (x ≈ y) × Pointwise xs ys

    -- The hypothesis: every operation preserves ≈ argument-wise.
    -- (For an equivalence relation this is exactly "the partition is a
    -- congruence for the vocabulary".)
    IsCongruence : Type (ℓ-max (ℓ-max ℓ ℓA) ℓR)
    IsCongruence = (o : Op) (xs ys : Tup A (ar o))
                 → Pointwise xs ys → ⟦ o ⟧op xs ≈ ⟦ o ⟧op ys

    -- Two environments related pointwise: the "x ≈ y" of the informal
    -- statement, for terms in many variables.
    Related : (V → A) → (V → A) → Type (ℓ-max ℓ' ℓR)
    Related ρ σ = (v : V) → ρ v ≈ σ v

    module _ (isCong : IsCongruence) where

      -- ***  THE WALL  ***
      -- No term built from the granted operations separates ≈-related
      -- inputs.  Structural induction; the variable case is the
      -- hypothesis, the node case is the congruence.
      wall     : (t : Term) {ρ σ : V → A} → Related ρ σ → eval ρ t ≈ eval σ t
      wallArgs : {n : ℕ} (as : Args n) {ρ σ : V → A} → Related ρ σ
               → Pointwise (evalArgs ρ as) (evalArgs σ as)

      wall (var v)     rel = rel v
      wall (node o as) rel = isCong o _ _ (wallArgs as rel)

      wallArgs ε        rel = tt*
      wallArgs (t ◂ as) rel = wall t rel , wallArgs as rel

------------------------------------------------------------------------
-- §2  THE INSTANCE: the two-bit charge world and its vocabulary
--
-- Carrier: sign/charge pairs.  Partition: equal total charge — the gauge
-- classes of ProjectionChargeAudit / GaugeOrbitClasses, here as the
-- machine's current partition after CLOSE.
------------------------------------------------------------------------

State : Type₀
State = Bool × Bool

tot : State → Bool
tot (a , b) = a ⊕ b

-- the machine's current partition (`≈`, not `~`: `~` is the cubical
-- interval reversal)
_≈_ : State → State → Type₀
x ≈ y = tot x ≡ tot y

-- Bool algebra used below; all of it is finite case analysis.

⊕-self : (x : Bool) → x ⊕ x ≡ false
⊕-self false = refl
⊕-self true  = refl

⊕-cancelʳ : (u v : Bool) → (u ⊕ v) ⊕ v ≡ u
⊕-cancelʳ u v = sym (⊕-assoc u v v) ∙ cong (u ⊕_) (⊕-self v) ∙ ⊕-identityʳ u

⊕-cancelˡ : (a u : Bool) → a ⊕ u ≡ a → u ≡ false
⊕-cancelˡ a u q = sym (⊕-invol a u) ∙ cong (a ⊕_) q ∙ ⊕-self a

-- the middle-four interchange, the only fact the binary operation needs
⊕-middle : (a b c d : Bool) → (a ⊕ c) ⊕ (b ⊕ d) ≡ (a ⊕ b) ⊕ (c ⊕ d)
⊕-middle false false c     d = refl
⊕-middle false true  false d = refl
⊕-middle false true  true  d = refl
⊕-middle true  false false d = refl
⊕-middle true  false true  d = sym (notnot d)
⊕-middle true  true  false d = notnot d
⊕-middle true  true  true  d = refl

⊕-flip : (a b : Bool) → (not a ⊕ not b) ≡ a ⊕ b
⊕-flip false b = notnot b
⊕-flip true  b = refl

b≢not : (b : Bool) → ¬ (b ≡ not b)
b≢not false p = false≢true p
b≢not true  p = true≢false p

-- The operations the machine can currently write.

swapS : State → State
swapS (a , b) = (b , a)

mixS : State → State → State
mixS (a , b) (c , d) = (a ⊕ c , b ⊕ d)

-- The operation it CANNOT currently write: reading the local coordinate.
-- This is the port grant of §4, not part of the vocabulary.
readS : State → State
readS (a , b) = (a , false)

-- the two charge laws of the granted vocabulary
tot-swap : (x : State) → tot (swapS x) ≡ tot x
tot-swap (a , b) = ⊕-comm b a

tot-mix : (x y : State) → tot (mixS x y) ≡ tot x ⊕ tot y
tot-mix (a , b) (c , d) = ⊕-middle a b c d

-- The signature.

data Vocab : Type₀ where
  sw mx : Vocab

arV : Vocab → ℕ
arV sw = 1
arV mx = 2

⟦_⟧V : (o : Vocab) → Tup State (arV o) → State
⟦ sw ⟧V (x , _)     = swapS x
⟦ mx ⟧V (x , y , _) = mixS x y

module M = Algebra Vocab arV Unit State ⟦_⟧V
open M using (Term; Args; var; node; ε; _◂_; eval; evalArgs)
module MW = M.Wall _≈_

-- one-variable environments: the term is evaluated "at x"
env : State → (Unit → State)
env x _ = x

------------------------------------------------------------------------
-- §3  THE WALL, INSTANTIATED — and the certificate
------------------------------------------------------------------------

-- The partition is a congruence for the whole vocabulary.  Two lines,
-- one per operation; this is the entire hypothesis the machine must
-- discharge at CERTIFY time.
vocabCongruence : MW.IsCongruence
vocabCongruence sw (x , _) (y , _) (p , _) =
  tot-swap x ∙ p ∙ sym (tot-swap y)
vocabCongruence mx (x , y , _) (x' , y' , _) (p , q , _) =
  tot-mix x y ∙ cong₂ _⊕_ p q ∙ sym (tot-mix x' y')

-- Non-vacuity of the LANGUAGE (as distinct from §4's non-vacuity of the
-- wall).  The wall would be uninteresting if every term were the
-- identity; it is not — `swap` moves states, it simply moves them inside
-- their class.
swapTerm mixTerm : Term
swapTerm = node sw (var tt ◂ ε)
mixTerm  = node mx (var tt ◂ var tt ◂ ε)

swapTerm-moves : ¬ (eval (env (true , false)) swapTerm ≡ (true , false))
swapTerm-moves q = false≢true (cong fst q)

mixTerm-moves : ¬ (eval (env (true , false)) mixTerm ≡ (true , false))
mixTerm-moves q = false≢true (cong fst q)

-- ***  THE WALL (instance)  ***
theWall : (t : Term) (x y : State) → x ≈ y → eval (env x) t ≈ eval (env y) t
theWall t x y p = MW.wall vocabCongruence t (λ _ → p)

-- The certificate's headline, in the contrapositive form the machine
-- needs: "no future term of mine can form a new distinction".
Separates : Term → State → State → Type₀
Separates t x y = (x ≈ y) × (¬ (eval (env x) t ≈ eval (env y) t))

noSeparation : (t : Term) (x y : State) → ¬ Separates t x y
noSeparation t x y (p , np) = np (theWall t x y p)

-- The exact converse, which is what makes this SATURATION and not just
-- stability: the relation "no term of mine distinguishes x from y" is
-- exactly ≈.  (⇒ is the single term `var`; ⇐ is the wall.)
Indistinguishable : State → State → Type₀
Indistinguishable x y = (t : Term) → eval (env x) t ≈ eval (env y) t

indist→≈ : (x y : State) → Indistinguishable x y → x ≈ y
indist→≈ x y h = h (var tt)

≈→indist : (x y : State) → x ≈ y → Indistinguishable x y
≈→indist x y p t = theWall t x y p

isPropIndistinguishable : (x y : State) → isProp (Indistinguishable x y)
isPropIndistinguishable x y = isPropΠ λ t → isSetBool _ _

-- saturation, as an equivalence of propositions
saturation : (x y : State) → Indistinguishable x y ≃ (x ≈ y)
saturation x y =
  propBiimpl→Equiv (isPropIndistinguishable x y) (isSetBool _ _)
                   (indist→≈ x y) (≈→indist x y)

------------------------------------------------------------------------
-- §4  THE BREACH — the formation event
--
-- A wall theorem without an exhibited breach is decorative.  GROW the
-- signature by one unary operation `rd⁺` (read the local coordinate:
-- the port grant), and everything changes at once.
------------------------------------------------------------------------

data Vocab⁺ : Type₀ where
  sw⁺ mx⁺ rd⁺ : Vocab⁺

arV⁺ : Vocab⁺ → ℕ
arV⁺ sw⁺ = 1
arV⁺ mx⁺ = 2
arV⁺ rd⁺ = 1

⟦_⟧⁺ : (o : Vocab⁺) → Tup State (arV⁺ o) → State
⟦ sw⁺ ⟧⁺ (x , _)     = swapS x
⟦ mx⁺ ⟧⁺ (x , y , _) = mixS x y
⟦ rd⁺ ⟧⁺ (x , _)     = readS x

module M⁺ = Algebra Vocab⁺ arV⁺ Unit State ⟦_⟧⁺
open M⁺ using ()
  renaming ( Term to Term⁺ ; Args to Args⁺ ; var to var⁺ ; node to node⁺
           ; ε to ε⁺ ; _◂_ to _◂⁺_ ; eval to eval⁺ ; evalArgs to evalArgs⁺ )
module MW⁺ = M⁺.Wall _≈_

-- the two states the wall keeps merged, and the witness that they are
x₀ x₁ : State
x₀ = (false , false)
x₁ = (true  , true)

x₀≈x₁ : x₀ ≈ x₁
x₀≈x₁ = refl

-- (i) the grown vocabulary is NOT a congruence: the hypothesis of the
-- wall theorem fails, and it fails at the granted operation.
readNotCongruence : ¬ MW⁺.IsCongruence
readNotCongruence isCong =
  false≢true (isCong rd⁺ (x₀ , tt*) (x₁ , tt*) (x₀≈x₁ , tt*))

-- (ii) THE FORMATION EVENT.  The port alone is not the news; the news is
-- that the machine's OLD grammar, applied to the port, immediately forms
-- an observable that reads the hidden coordinate:
--
--     formation  =  mix (rd⁺ v) v          tot (formation at (a,b)) = b
--
formation : Term⁺
formation = node⁺ mx⁺ (node⁺ rd⁺ (var⁺ tt ◂⁺ ε⁺) ◂⁺ (var⁺ tt ◂⁺ ε⁺))

formation-reads-fibre : (x : State) → tot (eval⁺ (env x) formation) ≡ snd x
formation-reads-fibre (a , b) = cong (_⊕ b) (⊕-self a)

-- and it separates the pair the wall kept merged.  This is the exact
-- term, the exact pair, and the exact new distinction.
Separates⁺ : Term⁺ → State → State → Type₀
Separates⁺ t x y = (x ≈ y) × (¬ (eval⁺ (env x) t ≈ eval⁺ (env y) t))

theFormationEvent : Separates⁺ formation x₀ x₁
theFormationEvent = x₀≈x₁ , false≢true

-- (iii) …and the port is the ONLY route.  Old terms embed into the grown
-- signature with their meanings unchanged, hence still separate nothing:
-- a separating term must USE the granted operation.
embed     : Term → Term⁺
embedArgs : {n : ℕ} → Args n → Args⁺ n

embed (var v)      = var⁺ v
embed (node sw as) = node⁺ sw⁺ (embedArgs as)
embed (node mx as) = node⁺ mx⁺ (embedArgs as)

embedArgs ε        = ε⁺
embedArgs (t ◂ as) = embed t ◂⁺ embedArgs as

agree-sw : (v : Tup State 1) → ⟦ sw⁺ ⟧⁺ v ≡ ⟦ sw ⟧V v
agree-sw (x , _) = refl

agree-mx : (v : Tup State 2) → ⟦ mx⁺ ⟧⁺ v ≡ ⟦ mx ⟧V v
agree-mx (x , y , _) = refl

embed-eval     : (ρ : Unit → State) (t : Term) → eval⁺ ρ (embed t) ≡ eval ρ t
embed-evalArgs : (ρ : Unit → State) {n : ℕ} (as : Args n)
               → evalArgs⁺ ρ (embedArgs as) ≡ evalArgs ρ as

embed-eval ρ (var v)      = refl
embed-eval ρ (node sw as) =
  cong ⟦ sw⁺ ⟧⁺ (embed-evalArgs ρ as) ∙ agree-sw (evalArgs ρ as)
embed-eval ρ (node mx as) =
  cong ⟦ mx⁺ ⟧⁺ (embed-evalArgs ρ as) ∙ agree-mx (evalArgs ρ as)

embed-evalArgs ρ ε        = refl
embed-evalArgs ρ (t ◂ as) =
  ΣPathP (embed-eval ρ t , embed-evalArgs ρ as)

noSeparationEmb : (t : Term) (x y : State) → ¬ Separates⁺ (embed t) x y
noSeparationEmb t x y (p , np) =
  np ( cong tot (embed-eval (env x) t)
     ∙ theWall t x y p
     ∙ cong tot (sym (embed-eval (env y) t)) )

------------------------------------------------------------------------
-- §5  THE RESIDUAL AS AN OBJECT
--
-- Given the wall, what remains hidden is not formless.  It is: the
-- quotient (the port menu), the annihilator group acting on each class
-- (the remainder torsor), and the splitting of the world into the part
-- terms see and the part they cannot.
------------------------------------------------------------------------

-- (a) Every term's charge descends to the quotient.  This is
-- ProjectionChargeAudit2's criterion reused verbatim: `Respects` is
-- exactly `theWall`, so `Descends` comes for free — and by that module's
-- `isPropDescends` the descended observable is unique.
module TermDescent (t : Term) =
  PCA2.Descent {X = State} _≈_ isSetBool (λ x → tot (eval (env x) t))

everyTermRespects : (t : Term) → TermDescent.Respects t
everyTermRespects t x y p = theWall t x y p

everyTermDescends : (t : Term) → TermDescent.Descends t
everyTermDescends t = TermDescent.respects→descends t (everyTermRespects t)

-- (b) The quotient — the exact menu a PORT could grant — is `Bool`:
-- two classes, no more.
visible : State / _≈_ → Bool
visible = SQ.rec isSetBool tot (λ x y p → p)

classOf : Bool → State / _≈_
classOf u = [ (u , false) ]

quotient≃Bool : (State / _≈_) ≃ Bool
quotient≃Bool = isoToEquiv (iso visible classOf ri li)
  where
    ri : (u : Bool) → visible (classOf u) ≡ u
    ri u = ⊕-identityʳ u

    li : (z : State / _≈_) → classOf (visible z) ≡ z
    li = SQ.elimProp (λ _ → squash/ _ _)
                     (λ x → eq/ _ _ (⊕-identityʳ (tot x)))

-- (c) The remainder torsor.  The annihilator is the set of gauge
-- elements of zero charge; it acts on States by `mixS`, preserving the
-- class (`ann-acts`), transitively on each class (`torsor-transitive`)
-- and freely (`torsor-free`).  So a ≈-class IS a torsor under a group of
-- order two — the two-bit shadow of GaugeOrbitClasses' "fibres of the
-- transcript map are cosets of the annihilator".
Ann : State → Type₀
Ann g = tot g ≡ false

ann-acts : (x g : State) → Ann g → mixS x g ≈ x
ann-acts x g h = tot-mix x g ∙ cong (tot x ⊕_) h ∙ ⊕-identityʳ (tot x)

torsor-transitive : (x y : State) → x ≈ y
                  → Σ[ g ∈ State ] (Ann g × (mixS x g ≡ y))
torsor-transitive (a , b) (c , d) p =
  mixS (a , b) (c , d)
  , ( tot-mix (a , b) (c , d) ∙ cong (_⊕ (c ⊕ d)) p ∙ ⊕-self (c ⊕ d)
    , ΣPathP (⊕-invol a c , ⊕-invol b d) )

torsor-free : (x g : State) → mixS x g ≡ x → g ≡ (false , false)
torsor-free (a , b) (g₁ , g₂) p =
  ΣPathP ( ⊕-cancelˡ a g₁ (cong fst p)
         , ⊕-cancelˡ b g₂ (cong snd p) )

-- the distinguished nontrivial gauge element, and the flip it induces
gaugeFlip : State → State
gaugeFlip (a , b) = (not a , not b)

gaugeFlip-is-mix : (x : State) → gaugeFlip x ≡ mixS x (true , true)
gaugeFlip-is-mix (a , b) = ΣPathP (sym (⊕-comm a true) , sym (⊕-comm b true))

gauge-merged : (x : State) → x ≈ gaugeFlip x
gauge-merged (a , b) = sym (⊕-flip a b)

-- (d) The world splits: visible × hidden.  `tot` is the term-visible
-- coordinate; the second bit is the residue.  This is THE_MACHINE.md (absent from this repository)'s
-- "states with hidden structure (endpoint × fiber)" as an equivalence.
hidden : State → Bool
hidden (a , b) = b

split : State → Bool × Bool
split x = (tot x , hidden x)

worldSplit : State ≃ (Bool × Bool)
worldSplit = isoToEquiv (iso split unsplit ri li)
  where
    unsplit : Bool × Bool → State
    unsplit (u , v) = (u ⊕ v , v)

    ri : (p : Bool × Bool) → split (unsplit p) ≡ p
    ri (u , v) = ΣPathP (⊕-cancelʳ u v , refl)

    li : (x : State) → unsplit (split x) ≡ x
    li (a , b) = ΣPathP (⊕-cancelʳ a b , refl)

-- what remains hidden, exactly: the second coordinate varies inside a
-- class (so the class has genuinely distinct members) and no term of the
-- granted vocabulary reaches it (so the machine cannot know which).
hidden-varies-in-class : (x : State) → ¬ (hidden x ≡ hidden (gaugeFlip x))
hidden-varies-in-class (a , b) q = b≢not b q

class-members-distinct : (x : State) → ¬ (x ≡ gaugeFlip x)
class-members-distinct x q = hidden-varies-in-class x (cong hidden q)

residual-invisible : (t : Term) (x : State) → ¬ Separates t x (gaugeFlip x)
residual-invisible t x = noSeparation t x (gaugeFlip x)

-- (e) The exact residual check, exhaustively over the four states.
-- Finite symbolic computation; every one of these is `refl`.
b2n : Bool → ℕ
b2n false = zero
b2n true  = suc zero

countStates : (State → Bool) → ℕ
countStates f =
  b2n (f (false , false)) +
  (b2n (f (false , true)) +
  (b2n (f (true , false)) + b2n (f (true , true))))

eqB : Bool → Bool → Bool
eqB false y = not y
eqB true  y = y

inClass : Bool → State → Bool
inClass u x = eqB (tot x) u

inAnn : State → Bool
inAnn g = not (tot g)

carrier-size : countStates (λ _ → true) ≡ 4
carrier-size = refl

-- two classes, each of size two: |State| = |menu| · |torsor|
class-false-size : countStates (inClass false) ≡ 2
class-false-size = refl

class-true-size : countStates (inClass true) ≡ 2
class-true-size = refl

-- the remainder group has order two, so the PORT menu below it has
-- exactly one nontrivial step (the quotients of ℤ/2 are 1 and ℤ/2)
ann-size : countStates inAnn ≡ 2
ann-size = refl

-- and the annihilator is exactly {(false,false),(true,true)}: the second
-- member is the gauge flip, whose orbit is the class.
ann-members : (inAnn (false , false) ≡ true) × (inAnn (true , true) ≡ true)
ann-members = refl , refl

ann-nonmembers : (inAnn (false , true) ≡ false) × (inAnn (true , false) ≡ false)
ann-nonmembers = refl , refl

------------------------------------------------------------------------
-- WHAT THE MACHINE MAY NOW SAY AT CERTIFY, AND WHAT IT MAY NOT
--
-- May say (each name is a checked term above):
--   "Complete relative to ports."          saturation
--   "No future term of mine can form."     noSeparation
--   "…and none in the grown language
--    either, unless it uses the grant."    noSeparationEmb
--   "Remainder = this group."              Ann, torsor-transitive,
--                                          torsor-free, ann-size
--   "Menu = these two classes."            quotient≃Bool
--   "The world is endpoint × fibre."       worldSplit
--   "One grant suffices to breach it,
--    and here is the term that does."      readNotCongruence, formation,
--                                          theFormationEvent
--
-- May NOT say: that this is the machine's actual world.  §2–§5 are one
-- finite instance.  The general theorem (§1) is what transfers: to run
-- CERTIFY on a real vocabulary, discharge `IsCongruence` for it — which
-- is one obligation per operation, exactly as `vocabCongruence` is two
-- lines here — and `wall` supplies the rest with no further work.  The
-- residual side (§5) does NOT transfer for free: the quotient being a
-- torsor under a computable group is a theorem about THIS world (and,
-- in the corpus, about the stabilizer tower R0032/33/36/37); in general
-- the residual is only "the quotient", with no group promised.  Saying
-- otherwise would be exactly the overclaim CLAUDE.md (absent from this repository) was written about.
------------------------------------------------------------------------
