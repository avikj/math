{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Obstruction
--
-- The checked kernel of obstruction-indexed vocabulary proposal.
--
-- Source: `runtime/vocabulary/README.md` §7.  The measured result there
-- is a plateau: a proposer that generalises shapes *already built* is
-- closed under "already built" — twelve installed constructors moved no
-- benchmark, because every proposal was drawn from the history of
-- successful matches, and a conservative extension by an
-- already-matched shape changes nothing.  The named fix is a proposer
-- driven by the *residual of a failed match*: read why the matcher
-- failed (B3: the redex is buried under a 3-ary head no binary pattern
-- covers) and name exactly the missing structure.
--
-- This module states and CHECKS both halves in a small substrate.  How
-- much of §7 survives the shrinking is the subject of T7′ and T10 below.
--
--   * `Tm`      — unary constructor terms over a countable alphabet of
--                 head shapes (a term language in which a definitional
--                 body and its unfolding are non-degenerate; that it is
--                 the "smallest" such language is an informal judgement,
--                 not a theorem, and nothing below depends on it).
--   * `Vocab`   — the installed vocabulary, a list of head shapes; the
--                 root matcher `Matches` and the full-term predicate
--                 `Over` are Bool-membership tests against it.
--   * `Obstruction V` — the residual of a failed match: the uncovered
--                 head (`residual`), the base subterm below the failure
--                 frontier (`arg`, all of whose heads are covered — the
--                 failure is exactly at the root), the failure evidence
--                 (`failed`), and a base body read off from the
--                 residual analysis (`witness`) for the head to
--                 abbreviate.
--   * `propose` — the obstruction-indexed proposer: a *function* from
--                 obstructions to definitional extensions (name = the
--                 residual, body = the witness, freshness = the failure
--                 evidence itself — gate D1 is not a side condition
--                 here, it is the obstruction).
--
-- Theorems (all checked, none postulated — `--safe`):
--
--   T1 `defining-equation`      the new head unfolds by its body.
--   T2 `unfold-elim` /
--      `propose-eliminable`     elimination AT THE LEVEL OF COVERAGE:
--                               every term over the extended vocabulary
--                               unfolds to a term all of whose heads are
--                               base.  NOT conservativity of a theory:
--                               no provability relation is modelled
--                               anywhere in this file, so "conservative"
--                               here is eliminability of the new head
--                               from `Over`, and nothing more.
--   T3 `match-conservative`     installing a head changes matchability
--                               at no OTHER head.  This is a membership
--                               skip lemma.
--   T4 `match-mono`, `Over-mono` extension loses nothing.
--   T5 `progress-after` +
--      `progress-before` +
--      `strictly-extends`       one proposal strictly extends the
--                               matchable set, at the stuck term.
--   T6 `obstruction-eliminated` the residual cannot obstruct the
--                               extended vocabulary: proposing consumes
--                               the obstruction.
--   T7 `extend-absorbed` /
--      `plateau`                THE PLATEAU THEOREM, for the modelled
--                               frequency proposer: a proposal drawn
--                               from an already-matched head leaves the
--                               matcher EQUAL (a path of functions, by
--                               funExt), and hence any finite chain of
--                               such proposals does too.
--   T7′ `freq-reaches-every-installed` /
--      `freq-memb-absorbed` /
--      `freq-Over-plateau`      what T7 actually says: the heads a
--                               `FreqChain` step can name are EXACTLY
--                               the already-installed ones, so such a
--                               chain changes no membership test at all
--                               — the matcher path is a shadow of an
--                               inert vocabulary, not of an argument
--                               about frequencies.
--   T8 `frequency-cannot-reach` no chain of the modelled frequency
--                               proposer ever matches an obstruction's
--                               stuck term — while one obstruction step
--                               does (T5).
--   T9 `obs-complete`           coverage: every term is fully covered
--                               after a finite chain of obstruction-
--                               proposals.  ("Completeness" would name a
--                               proof system; there is none here.)
--   T10 `class-preserves-outside` /
--      `class-cannot-reach` /
--      `class-can-grow`         §7's argument without T7's degeneracy: a
--                               proposer closed under a SHAPE CLASS may
--                               install unboundedly many genuinely new
--                               heads and still never reach an
--                               obstruction whose residual is outside
--                               the class.  This, not T7/T8, is the
--                               faithful rendering of the source.
--
------------------------------------------------------------------------

module ObstructionSubstrate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; if_then_else_ ; true≢false ; false≢true ; dichotomyBool)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 0.  Booleans and decidable shape equality, self-contained.
------------------------------------------------------------------------

Shape : Type₀
Shape = ℕ

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

eqℕ-refl : (n : ℕ) → eqℕ n n ≡ true
eqℕ-refl zero    = refl
eqℕ-refl (suc n) = eqℕ-refl n

eqℕ→≡ : (m n : ℕ) → eqℕ m n ≡ true → m ≡ n
eqℕ→≡ zero    zero    _ = refl
eqℕ→≡ zero    (suc n) p = Empty.rec (false≢true p)
eqℕ→≡ (suc m) zero    p = Empty.rec (false≢true p)
eqℕ→≡ (suc m) (suc n) p = cong suc (eqℕ→≡ m n p)

≢→eqℕ-false : (m n : ℕ) → ¬ m ≡ n → eqℕ m n ≡ false
≢→eqℕ-false zero    zero    ¬p = Empty.rec (¬p refl)
≢→eqℕ-false zero    (suc n) _  = refl
≢→eqℕ-false (suc m) zero    _  = refl
≢→eqℕ-false (suc m) (suc n) ¬p = ≢→eqℕ-false m n (λ q → ¬p (cong suc q))

if≡true : {A : Type₀} {x y : A} {b : Bool} → b ≡ true → (if b then x else y) ≡ x
if≡true {x = x} {y = y} p = cong (λ w → if w then x else y) p

if≡false : {A : Type₀} {x y : A} {b : Bool} → b ≡ false → (if b then x else y) ≡ y
if≡false {x = x} {y = y} p = cong (λ w → if w then x else y) p

------------------------------------------------------------------------
-- 1.  Vocabularies and membership.
------------------------------------------------------------------------

Vocab : Type₀
Vocab = List Shape

memb : Shape → Vocab → Bool
memb x []      = false
memb x (s ∷ V) = if eqℕ x s then true else memb x V

memb-here : (x : Shape) (V : Vocab) → memb x (x ∷ V) ≡ true
memb-here x V = if≡true (eqℕ-refl x)

memb-skip : (x s : Shape) (V : Vocab) → ¬ x ≡ s → memb x (s ∷ V) ≡ memb x V
memb-skip x s V ¬p = if≡false (≢→eqℕ-false x s ¬p)

memb-mono : (x s : Shape) (V : Vocab) → memb x V ≡ true → memb x (s ∷ V) ≡ true
memb-mono x s V h = helper (dichotomyBool (eqℕ x s))
  where
  helper : (eqℕ x s ≡ true) ⊎ (eqℕ x s ≡ false) → memb x (s ∷ V) ≡ true
  helper (inl e) = if≡true e
  helper (inr e) = if≡false e ∙ h

-- Extension by an already-present head is invisible to membership.
-- This is the engine of the plateau theorem (T7).
memb-absorb : (s : Shape) (V : Vocab) → memb s V ≡ true
            → (x : Shape) → memb x (s ∷ V) ≡ memb x V
memb-absorb s V h x = helper (dichotomyBool (eqℕ x s))
  where
  helper : (eqℕ x s ≡ true) ⊎ (eqℕ x s ≡ false) → memb x (s ∷ V) ≡ memb x V
  helper (inl e) = if≡true e ∙ sym (cong (λ z → memb z V) (eqℕ→≡ x s e) ∙ h)
  helper (inr e) = if≡false e

------------------------------------------------------------------------
-- 2.  Terms, coverage, the root matcher.
------------------------------------------------------------------------

data Tm : Type₀ where
  var  : Tm
  node : Shape → Tm → Tm

-- Substitution for the one parameter.
plug : Tm → Tm → Tm
plug var        u = u
plug (node c t) u = node c (plug t u)

-- Every head of the term is installed vocabulary ("the term is base").
Over : Vocab → Tm → Type₀
Over V var        = Unit
Over V (node c t) = (memb c V ≡ true) × Over V t

-- The root matcher: does some installed pattern fire at the root?
-- (A bare parameter names no structure, so nothing fires on it.)
Matches : Vocab → Tm → Type₀
Matches V var        = ⊥
Matches V (node c t) = memb c V ≡ true

plug-Over : (V : Vocab) (b u : Tm) → Over V b → Over V u → Over V (plug b u)
plug-Over V var        u _         hu = hu
plug-Over V (node c b) u (hc , hb) hu = hc , plug-Over V b u hb hu

-- T4, both forms.
Over-mono : (V : Vocab) (s : Shape) (t : Tm) → Over V t → Over (s ∷ V) t
Over-mono V s var        _         = tt
Over-mono V s (node c u) (hc , hu) = memb-mono c s V hc , Over-mono V s u hu

match-mono : (V : Vocab) (s : Shape) (t : Tm) → Matches V t → Matches (s ∷ V) t
match-mono V s var        m = Empty.rec m
match-mono V s (node c u) m = memb-mono c s V m

-- T3: conservativity of the matcher.  Installing a new head changes
-- matchability at NO other head — the path of types is by cong, not
-- assertion.  This is the model's rendering of gate D3: the new name
-- constrains no old symbol.
match-conservative : (V : Vocab) (s c : Shape) (u : Tm) → ¬ c ≡ s
                   → Matches (s ∷ V) (node c u) ≡ Matches V (node c u)
match-conservative V s c u ¬p = cong (_≡ true) (memb-skip c s V ¬p)

------------------------------------------------------------------------
-- 3.  Definitional extension, unfolding, elimination.
------------------------------------------------------------------------

-- Unfold the defined head d with base body b (the body's parameter
-- receives the unfolded argument).  D4's content — the body mentions
-- only earlier vocabulary — is `Over V b` below, so one pass
-- eliminates.
unfold : Shape → Tm → Tm → Tm
unfold d b var        = var
unfold d b (node c t) =
  if eqℕ c d then plug b (unfold d b t) else node c (unfold d b t)

-- T1: the defining equation, checked.
defining-equation : (d : Shape) (b : Tm) (t : Tm)
                  → unfold d b (node d t) ≡ plug b (unfold d b t)
defining-equation d b t = if≡true (eqℕ-refl d)

-- T2: elimination.  A definitional extension is conservative because
-- every term of the extended vocabulary unfolds to a base term — the
-- standard argument, executed by induction rather than cited.
unfold-elim : (V : Vocab) (d : Shape) (b : Tm) → Over V b
            → (t : Tm) → Over (d ∷ V) t → Over V (unfold d b t)
unfold-elim V d b bB var        _         = tt
unfold-elim V d b bB (node c t) (hc , ht) = helper (dichotomyBool (eqℕ c d))
  where
  helper : (eqℕ c d ≡ true) ⊎ (eqℕ c d ≡ false)
         → Over V (unfold d b (node c t))
  helper (inl e) =
    subst (Over V)
          (sym (if≡true {x = plug b (unfold d b t)} {y = node c (unfold d b t)} e))
          (plug-Over V b (unfold d b t) bB (unfold-elim V d b bB t ht))
  helper (inr e) =
    subst (Over V)
          (sym (if≡false {x = plug b (unfold d b t)} {y = node c (unfold d b t)} e))
          ( (sym (if≡false {x = true} {y = memb c V} e) ∙ hc)
          , unfold-elim V d b bB t ht )

------------------------------------------------------------------------
-- 4.  Obstructions: the residual of a failed match.
------------------------------------------------------------------------

record Obstruction (V : Vocab) : Type₀ where
  field
    residual    : Shape                     -- the head no pattern covers
    arg         : Tm                        -- what it was carrying
    argBase     : Over V arg                -- failure is exactly at the root
    failed      : memb residual V ≡ false   -- the failure, as evidence
    witness     : Tm                        -- base body read off from the
    witnessBase : Over V witness            --   residual analysis

  -- The term the matcher failed on.
  stuckTm : Tm
  stuckTm = node residual arg

open Obstruction

extend : (V : Vocab) → Obstruction V → Vocab
extend V o = residual o ∷ V

------------------------------------------------------------------------
-- 5.  The proposer: obstructions → definitional extensions.
------------------------------------------------------------------------

record Extension (V : Vocab) : Type₀ where
  field
    name     : Shape
    fresh    : memb name V ≡ false          -- gate D1
    body     : Tm
    bodyBase : Over V body                  -- gate D4

open Extension

-- The proposal is a FUNCTION of the residual: name the missing head,
-- let it abbreviate the witness.  Freshness is not checked — it IS the
-- failure evidence.  An obstruction-indexed proposer gets D1 for free
-- because it only ever names what just failed to match.
propose : (V : Vocab) → Obstruction V → Extension V
propose V o = record
  { name = residual o ; fresh = failed o
  ; body = witness o  ; bodyBase = witnessBase o }

install : (V : Vocab) → Extension V → Vocab
install V e = name e ∷ V

-- Installing the proposal is exactly extension by the obstruction —
-- definitionally.
propose-installs : (V : Vocab) (o : Obstruction V)
                 → install V (propose V o) ≡ extend V o
propose-installs V o = refl

-- The proposal is determined by the residual: obstructions with the
-- same residual extend the matcher identically.  This is `cong` and
-- nothing else: it holds of ANY V-indexed construction applied to
-- `residual o`, so it records that `extend` ignores the obstruction's
-- other four fields, and carries no information about the proposer.
proposal-determined : (V : Vocab) (o o' : Obstruction V)
                    → residual o ≡ residual o'
                    → Matches (extend V o) ≡ Matches (extend V o')
proposal-determined V o o' p = cong (λ s → Matches (s ∷ V)) p

-- T2 for the proposal: the proposed definition eliminates — the
-- extension it makes is definitional, hence conservative.
propose-eliminable : (V : Vocab) (o : Obstruction V) (t : Tm)
                   → Over (install V (propose V o)) t
                   → Over V (unfold (residual o) (witness o) t)
propose-eliminable V o t h =
  unfold-elim V (residual o) (witness o) (witnessBase o) t h

------------------------------------------------------------------------
-- 6.  T5: progress.  One proposal strictly extends the matchable set.
------------------------------------------------------------------------

progress-before : (V : Vocab) (o : Obstruction V) → ¬ Matches V (stuckTm o)
progress-before V o m = true≢false (sym m ∙ failed o)

progress-after : (V : Vocab) (o : Obstruction V) → Matches (extend V o) (stuckTm o)
progress-after V o = memb-here (residual o) V

strictly-extends : (V : Vocab) (o : Obstruction V)
                 → Σ[ t ∈ Tm ] ((¬ Matches V t) × Matches (extend V o) t)
strictly-extends V o = stuckTm o , progress-before V o , progress-after V o

-- T6: proposing consumes the obstruction — the same residual cannot
-- obstruct the extended vocabulary.
obstruction-eliminated : (V : Vocab) (o : Obstruction V)
  → ¬ (Σ[ o' ∈ Obstruction (extend V o) ] residual o' ≡ residual o)
obstruction-eliminated V o (o' , p) =
  true≢false ( sym (memb-here (residual o) V)
             ∙ sym (cong (λ z → memb z (extend V o)) p)
             ∙ failed o' )

------------------------------------------------------------------------
-- 7.  T7: the plateau theorem.
--
-- The frequency-based proposer draws its candidate from the history of
-- SUCCESSFUL matches: it can only ever name the head of a term the
-- matcher already fired on.  Extension by such a head leaves the
-- matcher EQUAL — not equivalent, equal, as a path of functions
-- Tm → Type₀ — and therefore so does any finite chain of such
-- proposals.  Naming re-describes the matchable set; it does not
-- enlarge it.
--
-- In THIS model the
-- candidate is not merely drawn from a closed shape class, it is a head
-- already installed, so the conclusion is automatic and the paragraph
-- above describes the datatype rather than a frequency proposer.
------------------------------------------------------------------------

extend-absorbed : (V : Vocab) (s : Shape) → memb s V ≡ true
                → Matches (s ∷ V) ≡ Matches V
extend-absorbed V s h = funExt lem
  where
  lem : (t : Tm) → Matches (s ∷ V) t ≡ Matches V t
  lem var        = refl
  lem (node c u) = cong (_≡ true) (memb-absorb s V h c)

-- What the frequency proposer can see: the head of a matched term.
headShape : (V : Vocab) (t : Tm) → Matches V t → Shape
headShape V var        m = Empty.rec m
headShape V (node c _) _ = c

headShape-built : (V : Vocab) (t : Tm) (m : Matches V t)
                → memb (headShape V t m) V ≡ true
headShape-built V var        m = Empty.rec m
headShape-built V (node c u) m = m

-- A finite run of the frequency proposer: each step names the head of
-- some term the current vocabulary already matches ("already built").
data FreqChain (V : Vocab) : Vocab → Type₀ where
  done : FreqChain V V
  step : {W : Vocab} → FreqChain V W
       → (t : Tm) (m : Matches W t)
       → FreqChain V (headShape W t m ∷ W)

plateau : {V W : Vocab} → FreqChain V W → Matches W ≡ Matches V
plateau done = refl
plateau (step {W = W} ch t m) =
  extend-absorbed W (headShape W t m) (headShape-built W t m) ∙ plateau ch

------------------------------------------------------------------------
-- T7′.  HOW MUCH OF T7 IS THE DATATYPE.  Exactly this much.
--
-- The step constructor names `headShape W t m`, which by
-- `headShape-built` is ALREADY INSTALLED in W.  The converse holds too:
-- every installed head is the head of some term the vocabulary matches,
-- namely `node s var` (`freq-reaches-every-installed`).  So the heads a
-- frequency step can name are EXACTLY the installed ones — no fewer and
-- no more — and the statement of the plateau is not about the
-- matcher at all, it is about membership:
--
--   `freq-memb-absorbed` : a frequency chain changes NO membership test.
--
-- `plateau` is that fact's `Matches` shadow and `freq-Over-plateau` is
-- its `Over` shadow.  In this model a frequency step cannot install
-- anything, so nothing can change.  That is strictly more degenerate
-- than the ceiling the source reports, where the frequency proposer DID
-- install twelve heads that were not there before and the point was that
-- all twelve stayed inside one shape class.  T10 below is that argument
-- without the degeneracy.
------------------------------------------------------------------------

freq-reaches-every-installed : (W : Vocab) (s : Shape) → memb s W ≡ true
  → Σ[ t ∈ Tm ] Σ[ m ∈ Matches W t ] (headShape W t m ≡ s)
freq-reaches-every-installed W s h = node s var , h , refl

freq-memb-absorbed : {V W : Vocab} → FreqChain V W → (x : Shape) → memb x W ≡ memb x V
freq-memb-absorbed done                  x = refl
freq-memb-absorbed (step {W = W} ch t m) x =
  memb-absorb (headShape W t m) W (headShape-built W t m) x ∙ freq-memb-absorbed ch x

freq-Over-invariant : {V W : Vocab} → FreqChain V W → (t : Tm) → Over W t ≡ Over V t
freq-Over-invariant ch var        = refl
freq-Over-invariant ch (node c u) i =
  (freq-memb-absorbed ch c i ≡ true) × freq-Over-invariant ch u i

freq-Over-plateau : {V W : Vocab} → FreqChain V W → Over W ≡ Over V
freq-Over-plateau ch = funExt (freq-Over-invariant ch)

------------------------------------------------------------------------
-- 8.  T8: the §7 sentence, as one checked statement.
--
-- No chain of frequency-proposals, of any length, ever matches an
-- obstruction's stuck term.  One obstruction-proposal does
-- (`progress-after`).  The proposal mechanism closed under "already
-- built" cannot leave the schema's shape space; the one indexed by the
-- residual of a failed match steps out of it immediately.
------------------------------------------------------------------------

frequency-cannot-reach : (V : Vocab) (o : Obstruction V) {W : Vocab}
                       → FreqChain V W → ¬ Matches W (stuckTm o)
frequency-cannot-reach V o ch m =
  progress-before V o
    (transport (cong (λ P → P (stuckTm o)) (plateau ch)) m)

------------------------------------------------------------------------
-- T10.  §7's argument with the degeneracy removed.
--
-- The source's closure is over a SHAPE CLASS ("every proposal is a
-- binary product"), not over the installed set: the reported run did
-- install twelve new heads, and its point was that none of them was
-- 3-ary.  A faithful model must therefore let the vocabulary GROW
-- without bound and still deny it the obstruction.  `ClassChain C` is
-- that proposer: it may install any head satisfying C, as often as it
-- likes.
--
--   `class-preserves-outside` it changes no membership test OFF C;
--   `class-cannot-reach`      it never matches the stuck term of an
--                             obstruction whose residual is off C;
--   `class-can-grow`          and — unlike `FreqChain`, which by
--                             `freq-memb-absorbed` can never change any
--                             membership test at all — it really does
--                             install heads that were not there.
--
-- So this subsumes T8's content without T7's degeneracy.  Note what is
-- lost in this version: the matcher genuinely changes (on C), so
-- no PATH of matchers is available and `Matches W ≡ Matches V` is false
-- in general.  T7's headline — "leaves the matcher EQUAL, not
-- equivalent, EQUAL" — is a symptom of the degenerate model, not extra
-- strength.  Invariance off the class is the statement that survives.
------------------------------------------------------------------------

data ClassChain (C : Shape → Bool) (V : Vocab) : Vocab → Type₀ where
  done : ClassChain C V V
  step : {W : Vocab} → ClassChain C V W → (s : Shape) → C s ≡ true
       → ClassChain C V (s ∷ W)

class-preserves-outside : (C : Shape → Bool) {V W : Vocab} → ClassChain C V W
                        → (x : Shape) → C x ≡ false → memb x W ≡ memb x V
class-preserves-outside C done             x cx = refl
class-preserves-outside C (step {W = W} ch s cs) x cx =
    memb-skip x s W (λ p → true≢false (sym cs ∙ sym (cong C p) ∙ cx))
  ∙ class-preserves-outside C ch x cx

class-cannot-reach : (C : Shape → Bool) (V : Vocab) (o : Obstruction V)
                   → C (residual o) ≡ false
                   → {W : Vocab} → ClassChain C V W → ¬ Matches W (stuckTm o)
class-cannot-reach C V o cr ch m =
  true≢false (sym m ∙ class-preserves-outside C ch (residual o) cr ∙ failed o)

class-can-grow : (C : Shape → Bool) (V : Vocab) (s : Shape)
               → C s ≡ true → memb s V ≡ false
               → Σ[ W ∈ Vocab ] ( ClassChain C V W
                                × (memb s W ≡ true)
                                × (¬ (memb s W ≡ memb s V)) )
class-can-grow C V s cs e =
    (s ∷ V) , step done s cs , memb-here s V
  , λ q → true≢false (sym (memb-here s V) ∙ q ∙ e)

------------------------------------------------------------------------
-- 9.  T9: completeness of obstruction-indexed proposal.
--
-- A finite chain of obstruction-proposals covers any term: repair
-- innermost-first, and each uncovered head yields an obstruction whose
-- proposal installs it.  (The chain constructed here uses the
-- degenerate witness `var`; a witness policy is a refinement, not a
-- prerequisite.)
------------------------------------------------------------------------

data ObsChain (V : Vocab) : Vocab → Type₀ where
  done : ObsChain V V
  step : {W : Vocab} → ObsChain V W → (o : Obstruction W) → ObsChain V (extend W o)

obs-complete : (V : Vocab) (t : Tm)
             → Σ[ W ∈ Vocab ] (ObsChain V W × Over W t)
obs-complete V var = V , done , tt
obs-complete V (node c u) with obs-complete V u
... | W , ch , ou = finish (dichotomyBool (memb c W))
  where
  finish : (memb c W ≡ true) ⊎ (memb c W ≡ false)
         → Σ[ X ∈ Vocab ] (ObsChain V X × Over X (node c u))
  finish (inl e) = W , ch , (e , ou)
  finish (inr e) =
    (c ∷ W)
    , step ch (record { residual = c ; arg = u ; argBase = ou
                      ; failed = e ; witness = var ; witnessBase = tt })
    , (memb-here c W , Over-mono W c u ou)
