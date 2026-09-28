{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CompileBridge
--
-- The hypothesis of `GenerativeLoop.Compile.generated-step-improves`,
-- derived.
--
-- `GenerativeLoop.Compile` proves: *given* an obstruction `o` whose
-- residual IS the `checkpoint` capability, one obstruction-indexed
-- proposal flips the compiler's branch from `restart` to `resume`, at
-- the same answer and strictly smaller counted cost.  This module proves
-- that running the generative loop on a task that demands `checkpoint`
-- PRODUCES such an obstruction, and hence the composite with no
-- hypothesis.
--
--
-- WHAT IS CHECKED
--
-- D. The term/vocabulary side, in full generality (§D).
--
--   D1 `HeadOccurs`, `demands`  a task term DEMANDS a capability when
--                               that shape occurs as one of its heads;
--                               `demands` is the Bool decision, and the
--                               pair `demands-true` / `demands-occurs`
--                               makes it faithful (both directions, so
--                               the Bool is not decoration).
--   D2 `Over→memb`              if a vocabulary covers a task, every
--                               capability the task demands is installed.
--   D3 `Names`, `chain-names`   THE KEY LEMMA, and it is about chains,
--                               not about the probe's internals: if a
--                               shape is absent at the start of an
--                               `ObsChain` and present at its end, then
--                               SOME step of that chain has that shape as
--                               its obstruction's residual.  A chain
--                               installs one head per step and installs
--                               nothing else, so a head that appeared was
--                               named.
--   D4 `namedAt`                extracts the intermediate vocabulary and
--                               the obstruction itself from `Names`.
--
-- E. The bridge (module `Bridge k checkpoint`, §E).
--
--   E1 `loop-produces-checkpoint`
--                               THE HYPOTHESIS, DERIVED.  For every base
--                               vocabulary V in which `checkpoint` is not
--                               installed and every task term t that
--                               demands `checkpoint`, running
--                               `GenerativeLoop.generative-loop V t`
--                               yields a chain one of whose obstructions
--                               `o : Obstruction X` satisfies
--                               `residual o ≡ checkpoint`.
--                               Nothing is assumed; the term is built
--                               from `generative-loop` and D3.
--   E2 `generation-improves`    THE UNCONDITIONAL COMPOSITE.  Exactly the
--                               conclusion of `generated-step-improves`,
--                               with its hypothesis replaced by the two
--                               facts about the TASK (checkpoint not yet
--                               installed, task demands checkpoint).  The
--                               improvement is derived, not
--                               hypothesised.
--
-- F. A compiler that is a function of the term too (§F).
--
--   In `GenerativeLoop` §C the compiler reads only the vocabulary.
--   Here the compiler is a total function of the TERM as well.  READ §H
--   BEFORE READING THIS AS AN INTEGRATION: the term contributes exactly
--   one bit (which capability the task demands); the task's arithmetic
--   arguments are carried NATIVELY as `ℕ`, and §H proves they have to be.
--
--   F1 `compileTm : Vocab → Tm → ℕ → ℕ → Plan`
--                               the task term is scanned for the
--                               capability it demands; the vocabulary is
--                               consulted for whether that capability is
--                               installed; `m n : ℕ` are the task's own
--                               arguments and are NOT encoded in the term.
--   F2 `compileTm-agrees`       on tasks that demand `checkpoint` it
--                               agrees with the stipulated `compile`
--                               (so nothing new is smuggled in), and
--   F3 `compileTm-undemanding`  on tasks that do not demand it, it emits
--                               `restart` regardless of the vocabulary
--                               (a capability the task never asks for
--                               cannot change the program).
--   F4 `generation-compiles-better`
--                               E2 restated with `compileTm` in place of
--                               `compile`: ONE task term `t`, compiled
--                               before and after the generated step, to
--                               `restart` and then `resume`, same answer,
--                               strictly cheaper.
--
-- G. A concrete task, with everything computed (§G).
--
--   G1 `first-step-names-resume`
--                               `refl`.  On the concrete task
--                               `taskTm = node resumeCap (node tickCap
--                               (node readCap var))` over the concrete
--                               base vocabulary `tickCap ∷ readCap ∷ []`,
--                               the loop's OWN step function
--                               `generative-step` reduces to an
--                               obstruction whose residual is literally
--                               `resumeCap`.  Not "some step of the
--                               chain": the FIRST one, by computation.
--                               NEGATIVE CONTROL, excluded from the
--                               aggregate because it must fail:
--                               `NaturalMachine/Control/WrongFirstStep.agda`
--                               asserts the same `refl` at `tickCap` and
--                               is rejected with `0 != 1 of type
--                               Agda.Builtin.Nat.Nat` (exit 42, error
--                               quoted verbatim in that file's header).
--                               So G1's `refl` is not the empty kind of
--                               `refl`.
--   G2 `taskObstruction`,
--      `taskObstruction-names`  that obstruction, extracted, with its
--                               naming proof.
--   G3 `ConcreteTask.task-step-improves`
--                               `generated-step-improves` applied at
--                               `baseVocab` and `taskObstruction` —
--                               the original conditional theorem with its
--                               condition supplied by G2.
--   G4 `ConcreteTask.task-compiles-better`
--                               F4 at the concrete task.
--   G5 `ConcreteTask.task-underdetermined`
--                               and the boundary at the same instance:
--                               after all of the above, the state
--                               (baseVocab , taskTm) still does not
--                               determine the answer (§H2 applied).
--
-- H. THE NEGATIVE RESULT: the loop's state underdetermines the answer.
--
--   codex-vajra's collision proves that the natural arithmetic plug into this
--   substrate FAILS, by an exact collision: on Z/30 the signals
--   F = (1,…,1) and G = (2,…,2) generate the same order-1 cyclotomic
--   sector, hence translate to the identical formal term with identical
--   `deficit`, while their autocorrelations are (30,…,30) and
--   (120,…,120).  Support survives translation; coefficients do not.  So
--   no decoder from the present `Tm`/`Vocab` state recovers the
--   arithmetic answer, and encoding a sector number into a `Shape` would
--   be a bridge that passes the kernel while missing the mathematics.
--
--   That constraint is honoured here by proving its analogue INSIDE this
--   substrate rather than by asserting compliance:
--
--   H1 `answers-differ`         two runs of the improved plan at
--                               different arithmetic arguments compute
--                               different digit words (via `valueC` and
--                               `AcceptanceTest.replay-observed`, so the
--                               separation is by the certified observer,
--                               not by inspection of constructors).
--   H2 `state-underdetermines-answer`
--                               THE NO-GO, in vajra's shape:
--                               for EVERY vocabulary V and EVERY term t,
--                               there is no `decode : Vocab → Tm → CanWord`
--                               with `decode V t ≡ exec (resume m (suc n))`
--                               for all m, n.  One term, one vocabulary,
--                               many answers.  The loop's state names the
--                               capability; it does not carry the object.
--   H3 `decoder-exists-pointwise`
--                               POSITIVE CONTROL FOR H2, proved here.
--                               At FIXED `m n` the Σ-type H2 negates is
--                               inhabited (by a constant function).  So
--                               H2 is not true for want of an inhabitant
--                               of `CanWord` or by a degeneracy of `Σ`:
--                               it is exactly a statement about
--                               UNIFORMITY in the arguments — the
--                               quantifier `(m n : ℕ)` cannot be pushed
--                               inside.  The witness is constant, so this
--                               certifies non-vacuity and nothing more.
--
--   H2 is why `compileTm` takes `m n : ℕ` natively: that signature is
--   FORCED, not chosen.  §E-§G are exactly the part of the story that
--   survives H2 — which capability the task needs, whether generation
--   supplies it, and which of two plans is emitted — and nothing in
--   §E-§G decodes an arithmetic answer from a term.
--
-- I. The interface an arithmetic payload must satisfy (§I).
--
--   `ArithmeticPayload` is a record with vajra's five required items:
--   shape-indexed native data, a composition law, semantics from
--   installed payloads to answers, semantic preservation under
--   `unfold`, and a cost that is a separate field from the structural
--   measure — plus `payload-separates`, the field that demands the F/G
--   collision be resolvable.
--
--   I2 `ArithmeticPayloadOver`  THE JOINT WITH THE MORPHISM CLASS, and why it exists.
--   `ArithmeticPayload` fixes DATA and never fixes the
--   TRANSFORMATIONS under which that data may be re-presented — so any
--   carrier or minimality notion it implies is underdetermined.  Its
--   instance: the k = 3 Mbius residual has unrestricted carrier rank 1
--   and graded carrier rank 3, the same payload under two morphism
--   classes.  That separation is PROVED inside the substrate in
--   `PayloadMorphism` (§F there).  Accordingly `ArithmeticPayloadOver Ans M` takes the
--   morphism class `M` AS A PARAMETER and demands a minimal carrier IN
--   THAT CLASS; `payload-carrier-determined` then proves the demanded
--   number is unique, which is exactly what the parameter buys and what
--   `ArithmeticPayload` could not say.  IT TOO IS DEFINED AND NOT
--   INHABITED.
--
--  * §G's `resumeCap`/`tickCap`/`readCap` are numerals with suggestive
--    identifiers; the mathematics is unchanged if they are renamed.
--  * E1 locates the checkpoint-naming step SOMEWHERE in the chain and
--    returns the intermediate vocabulary `X` at which it occurs.  It does
--    NOT claim the step is the first, nor that it is unique, nor that
--    `X ≡ V`.  Only in the concrete instance §G is the step shown to be
--    the first, and that is by computation on numerals (G1 is `refl`),
--    which generalises to nothing.  That the computation has a SPECIFIC
--    answer rather than being satisfied by any `refl` is the negative
--    control `NaturalMachine/Control/WrongFirstStep.agda` (excluded from
--    `agda`; it must fail, and does).
--  * H2 negates a Σ-type and is therefore worth nothing until that
--    Σ-type is known to be inhabitable.  It is, at fixed arguments:
--    H3 `decoder-exists-pointwise` in this file.  Both controls for this
--    module are cited by path, not described — the
--    positive one here as H3, the negative one at
--    `NaturalMachine/Control/WrongFirstStep.agda`.  Neither control
--    builds a decoder that reads anything off `(V , t)`: H3's witness is
--    a constant function and certifies non-vacuity only.
--  * D3 is a statement about `ObsChain`s, not about the loop's search
--    strategy.  It says a chain that made a head appear must have named
--    it.  It says nothing about which head the probe picks, in what
--    order, or whether that order is good.
--  * No optimality, no minimality: inherited from `GenerativeLoop` (the
--    step bound `chainLen ch ≤ deficit V t` is a bound).
--  * The cost model is inherited unchanged from `AcceptanceTest`: `cost`
--    counts `sucC` ticks a plan SCHEDULES, priced at one unit each.
--    "Strictly cheaper" means strictly fewer scheduled transitions of the
--    certified odometer.  The native-work theorem is `CountedDigitsEdge`.
--  * By H2 no arithmetic integration is available
--    from this state.  In particular §F does NOT unify the substrates:
--    `compileTm` reads one bit off the term (`demands checkpoint t`) and
--    takes the task's numbers natively.  A reader who wants "the term
--    determines the program" gets only that bit; everything numerical is
--    passed around the term, not through it.  The corresponding sector-
--    number encoding, which would look like integration, is refused here
--    on vajra's grounds and is not present anywhere in this file.
--  * H2 is a no-go about DECODERS FROM THE STATE, not an impossibility
--    theorem about the enterprise: it says a function of `(Vocab , Tm)`
--    cannot be the answer.  It does not say no extension of the substrate
--    can carry the answer — §I names one that could.
--  * `ArithmeticPayload` is kept alongside `ArithmeticPayloadOver` (I2).
--  * The witness policy is degenerate wherever the loop builds
--    obstructions (`witness = var`); conservativity holds for any base
--    witness, and nothing here makes bodies informative.
------------------------------------------------------------------------

module CompileBridge where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; injSuc ; znots)
open import Cubical.Data.Nat.Order using (_<_ ; _≤_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; if_then_else_ ; true≢false ; false≢true ; dichotomyBool)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import ObstructionSubstrate
open Obstruction
open import GenerativeLoop
open import PayloadMorphism
  using (MorphismClass ; MinCarrier ; min-unique)

import AcceptanceTest
import Digits

------------------------------------------------------------------------
-- D1.  What a task DEMANDS.
--
-- A task is a term; the capabilities it demands are the shapes occurring
-- as its heads.  `HeadOccurs` is the proposition, `demands` the Bool
-- decision, and the two lemmas below make them agree in both directions
-- (so `demands` is faithful, in the sense `GenerativeLoop`'s B0 pair is
-- faithful for `deficit`).
------------------------------------------------------------------------

HeadOccurs : Shape → Tm → Type₀
HeadOccurs s var        = ⊥
HeadOccurs s (node c u) = (c ≡ s) ⊎ HeadOccurs s u

demands : Shape → Tm → Bool
demands s var        = false
demands s (node c u) = if eqℕ c s then true else demands s u

demands-true : (s : Shape) (t : Tm) → HeadOccurs s t → demands s t ≡ true
demands-true s var        h       = Empty.rec h
demands-true s (node c u) (inl p) =
  if≡true {x = true} {y = demands s u} (cong (eqℕ c) (sym p) ∙ eqℕ-refl c)
demands-true s (node c u) (inr h) = branch (dichotomyBool (eqℕ c s))
  where
  branch : (eqℕ c s ≡ true) ⊎ (eqℕ c s ≡ false) → demands s (node c u) ≡ true
  branch (inl e) = if≡true  {x = true} {y = demands s u} e
  branch (inr e) = if≡false {x = true} {y = demands s u} e ∙ demands-true s u h

demands-occurs : (s : Shape) (t : Tm) → demands s t ≡ true → HeadOccurs s t
demands-occurs s var        e = Empty.rec (false≢true e)
demands-occurs s (node c u) e = branch (dichotomyBool (eqℕ c s))
  where
  branch : (eqℕ c s ≡ true) ⊎ (eqℕ c s ≡ false) → HeadOccurs s (node c u)
  branch (inl q) = inl (eqℕ→≡ c s q)
  branch (inr q) =
    inr (demands-occurs s u (sym (if≡false {x = true} {y = demands s u} q) ∙ e))

------------------------------------------------------------------------
-- D2.  Coverage installs every demanded capability.
------------------------------------------------------------------------

Over→memb : (V : Vocab) (t : Tm) (s : Shape)
          → Over V t → HeadOccurs s t → memb s V ≡ true
Over→memb V var        s _         h       = Empty.rec h
Over→memb V (node c u) s (hc , _)  (inl p) = cong (λ z → memb z V) (sym p) ∙ hc
Over→memb V (node c u) s (_  , hu) (inr h) = Over→memb V u s hu h

------------------------------------------------------------------------
-- D3.  THE KEY LEMMA: a chain that made a head appear NAMED it.
--
-- Each `ObsChain` step extends the vocabulary by exactly one shape — the
-- residual of that step's obstruction — and by nothing else.  So a shape
-- absent at the start of a chain and present at its end must be the
-- residual of one of the steps.  This is what connects the loop's OUTPUT
-- (a vocabulary covering the target) back to the obstructions it built
-- on the way, and it needs nothing from the probe's search strategy.
------------------------------------------------------------------------

Names : Shape → {V W : Vocab} → ObsChain V W → Type₀
Names s done        = ⊥
Names s (step ch o) = Names s ch ⊎ (residual o ≡ s)

chain-names : (s : Shape) {V W : Vocab} (ch : ObsChain V W)
            → memb s V ≡ false → memb s W ≡ true → Names s ch
chain-names s done a b = true≢false (sym b ∙ a)
chain-names s (step {W = X} ch o) a b = branch (dichotomyBool (eqℕ s (residual o)))
  where
  branch : (eqℕ s (residual o) ≡ true) ⊎ (eqℕ s (residual o) ≡ false)
         → Names s (step ch o)
  branch (inl e) = inr (sym (eqℕ→≡ s (residual o) e))
  branch (inr e) =
    inl (chain-names s ch a (sym (if≡false {x = true} {y = memb s X} e) ∙ b))

-- D4.  ... and the obstruction is extractable, together with the
-- intermediate vocabulary it lives over.
namedAt : (s : Shape) {V W : Vocab} (ch : ObsChain V W) → Names s ch
        → Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] (residual o ≡ s)
namedAt s done               h       = Empty.rec h
namedAt s (step ch o)        (inl h) = namedAt s ch h
namedAt s (step {W = X} ch o) (inr p) = X , o , p

------------------------------------------------------------------------
-- E-F.  The bridge proper, over a base `2 + k` and a capability name.
------------------------------------------------------------------------

module Bridge (k : ℕ) (checkpoint : Shape) where

  open AcceptanceTest k
    using (Plan ; restart ; resume ; cost ; exec ; betterProgram ; replay-observed) public
  open Digits k using (CanWord ; valueC) public
  open Compile k checkpoint public

  ----------------------------------------------------------------------
  -- The shape of an improvement at one obstruction.  This is verbatim
  -- the conclusion of `GenerativeLoop.Compile.generated-step-improves`;
  -- naming it lets the composites below be read.
  ----------------------------------------------------------------------

  ImprovementAt : (X : Vocab) (o : Obstruction X) (m n : ℕ) → Type₀
  ImprovementAt X o m n =
      ( (r : Tm) → Over (install X (propose X o)) r
                 → Over X (unfold (residual o) (witness o) r) )   -- conservative
    × (¬ Matches X (stuckTm o))                                   -- was stuck
    × (Matches (extend X o) (stuckTm o))                          -- now matches
    × (compile X m (suc n) ≡ restart m (suc n))                   -- before
    × (compile (extend X o) m (suc n) ≡ resume m (suc n))         -- after
    × (exec (resume m (suc n)) ≡ exec (restart m (suc n)))        -- same answer
    × (cost (resume m (suc n)) < cost (restart m (suc n)))        -- cheaper

  ----------------------------------------------------------------------
  -- E1.  THE HYPOTHESIS, DERIVED.
  --
  -- Run the loop on a task that demands the checkpoint capability from a
  -- vocabulary that does not have it.  The loop terminates with coverage
  -- (`generative-loop`); coverage means the capability is now installed
  -- (D2); a chain that installed it named it (D3); and the naming step's
  -- obstruction is extractable (D4).  Nothing is assumed.
  ----------------------------------------------------------------------

  loop-produces-checkpoint :
    (V : Vocab) (t : Tm)
    → memb checkpoint V ≡ false        -- the capability is not yet had
    → HeadOccurs checkpoint t          -- the task demands it
    → Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] (residual o ≡ checkpoint)
  loop-produces-checkpoint V t absent occ = read (generative-loop V t)
    where
    read : Σ[ W ∈ Vocab ] Σ[ ch ∈ ObsChain V W ]
             (Over W t × (chainLen ch ≤ deficit V t))
         → Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] (residual o ≡ checkpoint)
    read (W , ch , cov , _) =
      namedAt checkpoint ch
        (chain-names checkpoint ch absent (Over→memb W t checkpoint cov occ))

  ----------------------------------------------------------------------
  -- The two membership facts at the naming step, both read off the
  -- obstruction itself: `failed` IS the absence, `memb-here` the
  -- presence.  (Same two lines as `Compile`'s private `absent`/`present`,
  -- which are not exported.)
  ----------------------------------------------------------------------

  private
    absentAt : (X : Vocab) (o : Obstruction X) → residual o ≡ checkpoint
             → memb checkpoint X ≡ false
    absentAt X o p = sym (cong (λ s → memb s X) p) ∙ failed o

    presentAt : (X : Vocab) (o : Obstruction X) → residual o ≡ checkpoint
              → memb checkpoint (extend X o) ≡ true
    presentAt X o p =
      cong (λ s → memb s (extend X o)) (sym p) ∙ memb-here (residual o) X

  ----------------------------------------------------------------------
  -- E2.  THE UNCONDITIONAL COMPOSITE.
  --
  -- `generated-step-improves` with its hypothesis discharged: the input
  -- is now a task, not an obstruction with a promise about it.
  ----------------------------------------------------------------------

  generation-improves :
    (V : Vocab) (t : Tm)
    → memb checkpoint V ≡ false
    → HeadOccurs checkpoint t
    → (m n : ℕ)
    → Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] ImprovementAt X o m n
  generation-improves V t absent occ m n =
    build (loop-produces-checkpoint V t absent occ)
    where
    build : Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] (residual o ≡ checkpoint)
          → Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] ImprovementAt X o m n
    build (X , o , p) = X , o , generated-step-improves X o p m n

  ----------------------------------------------------------------------
  -- F.  `Tm` terms compiling to `Plan`s.
  --
  -- THE STIPULATION, in one definition: a compiler that reads the task
  -- term for the capability it demands and the vocabulary for whether
  -- that capability is installed.  It is stipulated in exactly the sense
  -- `Compile.compile` is — nothing derives it — but it is now a function
  -- of the term, so `Tm` targets and `Plan` programs are joined by a map
  -- rather than by a shared parameter.
  ----------------------------------------------------------------------

  compileTm : Vocab → Tm → ℕ → ℕ → Plan
  compileTm V t m n =
    if demands checkpoint t
      then (if memb checkpoint V then resume m n else restart m n)
      else restart m n

  -- F2: on tasks that demand the capability, the term-directed compiler
  -- IS the vocabulary-directed one — no new content is smuggled in.
  compileTm-agrees : (V : Vocab) (t : Tm) (m n : ℕ) → HeadOccurs checkpoint t
                   → compileTm V t m n ≡ compile V m n
  compileTm-agrees V t m n occ =
    if≡true {x = compile V m n} {y = restart m n} (demands-true checkpoint t occ)

  -- F3: a capability the task never asks for cannot change the program.
  compileTm-undemanding : (V : Vocab) (t : Tm) (m n : ℕ)
                        → demands checkpoint t ≡ false
                        → compileTm V t m n ≡ restart m n
  compileTm-undemanding V t m n e =
    if≡false {x = compile V m n} {y = restart m n} e

  compileTm-absent : (V : Vocab) (t : Tm) (m n : ℕ) → memb checkpoint V ≡ false
                   → compileTm V t m n ≡ restart m n
  compileTm-absent V t m n a = branch (dichotomyBool (demands checkpoint t))
    where
    branch : (demands checkpoint t ≡ true) ⊎ (demands checkpoint t ≡ false)
           → compileTm V t m n ≡ restart m n
    branch (inl e) =
      if≡true {x = compile V m n} {y = restart m n} e ∙ compile-absent V m n a
    branch (inr e) = compileTm-undemanding V t m n e

  compileTm-present : (V : Vocab) (t : Tm) (m n : ℕ) → HeadOccurs checkpoint t
                    → memb checkpoint V ≡ true
                    → compileTm V t m n ≡ resume m n
  compileTm-present V t m n occ b =
    compileTm-agrees V t m n occ ∙ compile-present V m n b

  ----------------------------------------------------------------------
  -- F4.  The same statement with ONE task term compiled on both sides.
  ----------------------------------------------------------------------

  TermImprovementAt : (X : Vocab) (o : Obstruction X) (t : Tm) (m n : ℕ) → Type₀
  TermImprovementAt X o t m n =
      ( (r : Tm) → Over (install X (propose X o)) r
                 → Over X (unfold (residual o) (witness o) r) )
    × (¬ Matches X (stuckTm o))
    × (Matches (extend X o) (stuckTm o))
    × (compileTm X t m (suc n) ≡ restart m (suc n))
    × (compileTm (extend X o) t m (suc n) ≡ resume m (suc n))
    × (exec (resume m (suc n)) ≡ exec (restart m (suc n)))
    × (cost (resume m (suc n)) < cost (restart m (suc n)))

  generation-compiles-better :
    (V : Vocab) (t : Tm)
    → memb checkpoint V ≡ false
    → HeadOccurs checkpoint t
    → (m n : ℕ)
    → Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] TermImprovementAt X o t m n
  generation-compiles-better V t absent occ m n =
    build (loop-produces-checkpoint V t absent occ)
    where
    build : Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] (residual o ≡ checkpoint)
          → Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] TermImprovementAt X o t m n
    build (X , o , p) =
        X , o
      , generated-definition-conservative X o
      , progress-before X o
      , progress-after X o
      , compileTm-absent X t m (suc n) (absentAt X o p)
      , compileTm-present (extend X o) t m (suc n) occ (presentAt X o p)
      , fst (betterProgram m n)
      , snd (betterProgram m n)

  ----------------------------------------------------------------------
  -- H.  THE NEGATIVE RESULT.
  --
  -- codex-vajra's collision, transported into this substrate.  There the
  -- signals F = (1,…,1) and G = (2,…,2) on Z/30 have the same cyclotomic
  -- support — hence the same translated term and the same `deficit` —
  -- and different autocorrelations.  Here the corresponding fact is that
  -- the pair (V , t) is constant in the task's arithmetic arguments while
  -- the answer is not: the loop's state records WHICH CAPABILITY is
  -- needed and never WHICH OBJECT the task is about.
  --
  -- The separation is made by the certified observer `valueC` through
  -- `AcceptanceTest.replay-observed`, not by inspecting digit-word
  -- constructors.
  ----------------------------------------------------------------------

  answers-differ : ¬ (exec (resume 0 (suc 0)) ≡ exec (resume 1 (suc 0)))
  answers-differ q =
    znots (injSuc ( sym (replay-observed 0 (suc 0))
                  ∙ cong valueC q
                  ∙ replay-observed 1 (suc 0) ))

  -- H2.  No function of the loop's state is the task's answer — for any
  -- vocabulary and any target term whatsoever.  This is why `compileTm`
  -- takes the arithmetic arguments natively: the signature is forced.
  state-underdetermines-answer :
    (V : Vocab) (t : Tm)
    → ¬ ( Σ[ decode ∈ (Vocab → Tm → CanWord) ]
            ((m n : ℕ) → decode V t ≡ exec (resume m (suc n))) )
  state-underdetermines-answer V t (decode , h) =
    answers-differ (sym (h 0 0) ∙ h 1 0)

  ----------------------------------------------------------------------
  -- H3.  THE POSITIVE CONTROL FOR H2 (designed annihilation,
  -- collab/PROTOCOL.md (absent from this repository) §7; the matching negative control is
  -- `NaturalMachine/Control/WrongFirstStep.agda`, which must fail).
  --
  -- WHAT IT RULES OUT.  H2 negates a Σ-type, so it would be true for a
  -- boring reason if that Σ-type were empty for want of an inhabitant of
  -- `CanWord`, or by some degeneracy of `Σ`, or because no `decode` of
  -- the stated type exists at all.  Drop the uniformity — fix `m` and `n`
  -- before choosing `decode` instead of after — and the Σ-type IS
  -- inhabited, by a constant function.  So H2 is a statement about
  -- UNIFORMITY IN THE ARGUMENTS and nothing else: it says the quantifier
  -- `(m n : ℕ)` cannot be pushed inside the Σ.  The answer type is not
  -- empty; the state simply cannot track it as `m` and `n` vary.
  --
  -- The witness is a constant function, so this certifies non-vacuity and
  -- nothing more: no decoder that reads anything off `(V , t)` is built
  -- here, and none is claimed to exist.
  ----------------------------------------------------------------------

  decoder-exists-pointwise :
    (V : Vocab) (t : Tm) (m n : ℕ)
    → Σ[ decode ∈ (Vocab → Tm → CanWord) ] (decode V t ≡ exec (resume m (suc n)))
  decoder-exists-pointwise V t m n = (λ _ _ → exec (resume m (suc n))) , refl

------------------------------------------------------------------------
-- I.  THE INTERFACE.
--
-- What an arithmetic payload must carry: the five fields below, plus
-- `payload-separates`, which is the demand that the F/G collision be
-- resolvable — exactly what §H proves the bare state cannot do.
------------------------------------------------------------------------

record ArithmeticPayload : Type₁ where
  field
    -- (1) native coefficient/certificate data, indexed by the shape that
    --     names its sector.  This is what a `Shape` alone does not carry.
    Datum   : Shape → Type₀
    -- the task answers (correlation vectors, certificates, …)
    Ans     : Type₀
    -- installed payloads: a store attached to a vocabulary
    Store   : Vocab → Type₀
    atom    : {V : Vocab} → Store V → (s : Shape) → memb s V ≡ true → Ans
    -- installing a definitional extension installs a payload with it
    installP : {V : Vocab} → Store V → (d : Shape) (b : Tm) → Over V b
             → Datum d → Store (d ∷ V)

    -- (2) a checked composition law: the answer of a composite task is
    --     built from the answer of its head and the answer of the rest.
    combine : Ans → Ans → Ans
    -- (3) semantics: installed payloads plus a covered task term give an
    --     answer, compositionally.
    sem     : {V : Vocab} → Store V → (t : Tm) → Over V t → Ans
    sem-node : {V : Vocab} (st : Store V) (c : Shape) (u : Tm)
             → (hc : memb c V ≡ true) (hu : Over V u)
             → sem st (node c u) (hc , hu) ≡ combine (atom st c hc) (sem st u hu)

    -- (4) unfolding a generated definition preserves the semantics.  This
    --     is `Obstruction.unfold-elim` upgraded from coverage to meaning.
    unfold-preserves :
      {V : Vocab} (st : Store V) (d : Shape) (b : Tm) (bB : Over V b)
      (x : Datum d) (t : Tm) (h : Over (d ∷ V) t)
      → sem (installP st d b bB x) t h
        ≡ sem st (unfold d b t) (unfold-elim V d b bB t h)

    -- (5) a cost that is a SEPARATE field from the structural measure.
    --     Nothing may identify `vcost` with `deficit`; the termination
    --     argument of `GenerativeLoop` must remain the structural one.
    Cost    : Type₀
    vcost   : {V : Vocab} → Store V → (t : Tm) → Over V t → Cost

    -- The F/G requirement: one term, one vocabulary, two payloads, two
    -- different answers.  A carrier without this field would collide
    -- exactly as `state-underdetermines-answer` says the bare state does.
    payload-separates :
      Σ[ V ∈ Vocab ] Σ[ t ∈ Tm ] Σ[ h ∈ Over V t ]
      Σ[ st ∈ Store V ] Σ[ st' ∈ Store V ] (¬ (sem st t h ≡ sem st' t h))

------------------------------------------------------------------------
-- I2.  THE SAME JOINT WITH THE MORPHISM CLASS AS A PARAMETER.
--
-- The record above fixes the payload's DATA and never fixes the class of
-- transformations under which the data may be re-presented, so its
-- implied "minimal carrier" is underdetermined — the instance,
-- the k = 3 Mbius residual with unrestricted carrier rank 1 and graded
-- carrier rank 3, is proved as `PayloadMorphism.minimal-carrier-depends-
-- on-class`, with the promotion table (1,3), (1,2), (1,1), (0,0).  A
-- third class, in which a differential forces a larger carrier, is
-- proved there too (`chain-min-interval`), with the zero-boundary false
-- control (`chain-min-loop`).
--
-- The difference is one parameter and one field: the class `M` is now part
-- of the interface, and the payload must have a MINIMAL CARRIER IN `M`.
-- By `PayloadMorphism.min-unique` that number is then unique — see
-- `payload-carrier-determined` below, which is the precise sense in
-- which naming the class buys something.
--
------------------------------------------------------------------------

record ArithmeticPayloadOver (Ans : Type₀) (M : MorphismClass Ans) : Type₁ where
  field
    -- (1) native coefficient/certificate data, indexed by the shape that
    --     names its sector, and a store attached to a vocabulary.
    Datum   : Shape → Type₀
    Store   : Vocab → Type₀
    atom    : {V : Vocab} → Store V → (s : Shape) → memb s V ≡ true → Ans
    installP : {V : Vocab} → Store V → (d : Shape) (b : Tm) → Over V b
             → Datum d → Store (d ∷ V)

    -- (2) a checked composition law.
    combine : Ans → Ans → Ans
    -- (3) semantics, compositionally.
    sem     : {V : Vocab} → Store V → (t : Tm) → Over V t → Ans
    sem-node : {V : Vocab} (st : Store V) (c : Shape) (u : Tm)
             → (hc : memb c V ≡ true) (hu : Over V u)
             → sem st (node c u) (hc , hu) ≡ combine (atom st c hc) (sem st u hu)

    -- (4) unfolding a generated definition preserves the semantics.
    unfold-preserves :
      {V : Vocab} (st : Store V) (d : Shape) (b : Tm) (bB : Over V b)
      (x : Datum d) (t : Tm) (h : Over (d ∷ V) t)
      → sem (installP st d b bB x) t h
        ≡ sem st (unfold d b t) (unfold-elim V d b bB t h)

    -- (5) a cost that is a SEPARATE field from the structural measure.
    Cost    : Type₀
    vcost   : {V : Vocab} → Store V → (t : Tm) → Over V t → Cost

    -- (6) THE MORPHISM CLASS.  A payload has no minimal carrier until the
    --     admissible transformations are declared; they are declared by
    --     the parameter `M`, and this pair of fields demands that every
    --     covered task's answer have a minimal carrier IN THAT CLASS.
    --     Nothing identifies `carrier` with `deficit`: as with `vcost`,
    --     the structural measure stays untouched.
    carrier : {V : Vocab} → Store V → (t : Tm) → Over V t → ℕ
    carrier-minimal : {V : Vocab} (st : Store V) (t : Tm) (h : Over V t)
                    → MinCarrier M (sem st t h) (carrier st t h)

    -- The F/G requirement, unchanged.
    payload-separates :
      Σ[ V ∈ Vocab ] Σ[ t ∈ Tm ] Σ[ h ∈ Over V t ]
      Σ[ st ∈ Store V ] Σ[ st' ∈ Store V ] (¬ (sem st t h ≡ sem st' t h))

-- WHAT THE PARAMETER BUYS, proved about the record without inhabiting
-- it: with the class named, `carrier` is not a choice.  Any number
-- satisfying the same minimality demand is that number.
module _ {Ans : Type₀} {M : MorphismClass Ans} (P : ArithmeticPayloadOver Ans M) where

  open ArithmeticPayloadOver P

  payload-carrier-determined :
    {V : Vocab} (st : Store V) (t : Tm) (h : Over V t) (m : ℕ)
    → MinCarrier M (sem st t h) m → m ≡ carrier st t h
  payload-carrier-determined st t h m mc =
    min-unique M (sem st t h) m (carrier st t h) mc (carrier-minimal st t h)

------------------------------------------------------------------------
-- G.  A concrete task, with the naming step COMPUTED.
--
-- Three capability names and a task that composes them:
--
--   resumeCap  "resume the odometer from a checkpoint word"  (missing)
--   tickCap    "advance the odometer one tick"               (installed)
--   readCap    "read the digit word"                         (installed)
--
--   taskTm = node resumeCap (node tickCap (node readCap var))
--
-- The identifiers are suggestive; the objects are the numerals 0, 1, 2.
-- What is checked is that the loop's own step function, run on this
-- target from this vocabulary, reduces to an obstruction whose residual
-- is `resumeCap` — G1 below is `refl`.
------------------------------------------------------------------------

resumeCap tickCap readCap : Shape
resumeCap = 0
tickCap   = 1
readCap   = 2

baseVocab : Vocab
baseVocab = tickCap ∷ readCap ∷ []

taskTm : Tm
taskTm = node resumeCap (node tickCap (node readCap var))

-- The two facts about the task, both by computation on numerals.
resumeCap-absent : memb resumeCap baseVocab ≡ false
resumeCap-absent = refl

task-demands-resume : HeadOccurs resumeCap taskTm
task-demands-resume = inl refl

-- Reading a step result.  `generative-step` returns coverage or an
-- obstruction-with-decrease; this says the second happened and names it.
StepResult : Vocab → Tm → Type₀
StepResult V t =
  Over V t ⊎ (Σ[ o ∈ Obstruction V ] (deficit (extend V o) t < deficit V t))

ResidualIs : (s : Shape) (V : Vocab) (t : Tm) → StepResult V t → Type₀
ResidualIs s V t (inl _)       = ⊥
ResidualIs s V t (inr (o , _)) = residual o ≡ s

obsOf : (s : Shape) (V : Vocab) (t : Tm) (r : StepResult V t)
      → ResidualIs s V t r → Obstruction V
obsOf s V t (inl _)       h = Empty.rec h
obsOf s V t (inr (o , _)) _ = o

obsOf-residual : (s : Shape) (V : Vocab) (t : Tm) (r : StepResult V t)
               → (h : ResidualIs s V t r) → residual (obsOf s V t r h) ≡ s
obsOf-residual s V t (inl _)       h = Empty.rec h
obsOf-residual s V t (inr (o , _)) h = h

-- G1.  The loop's FIRST step on this task names the missing capability.
-- By computation: `probe` searches innermost-first, `readCap` and
-- `tickCap` are installed, `resumeCap` is not.
first-step-names-resume :
  ResidualIs resumeCap baseVocab taskTm (generative-step baseVocab taskTm)
first-step-names-resume = refl

-- G2.  That obstruction, and its naming proof.
taskObstruction : Obstruction baseVocab
taskObstruction = obsOf resumeCap baseVocab taskTm
                        (generative-step baseVocab taskTm) first-step-names-resume

taskObstruction-names : residual taskObstruction ≡ resumeCap
taskObstruction-names =
  obsOf-residual resumeCap baseVocab taskTm
                 (generative-step baseVocab taskTm) first-step-names-resume

------------------------------------------------------------------------
-- G3-G4.  The conditional theorem, with its condition supplied.
------------------------------------------------------------------------

module ConcreteTask (k : ℕ) where

  open Bridge k resumeCap

  -- G3: `GenerativeLoop.Compile.generated-step-improves` at the concrete
  -- vocabulary and the concrete obstruction the loop produced.  The
  -- hypothesis `residual o ≡ checkpoint` is G2, not an assumption.
  task-step-improves : (m n : ℕ) → ImprovementAt baseVocab taskObstruction m n
  task-step-improves m n =
    generated-step-improves baseVocab taskObstruction taskObstruction-names m n

  -- ... and the same through the loop, as the general bridge delivers it.
  task-generation-improves :
    (m n : ℕ) → Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] ImprovementAt X o m n
  task-generation-improves =
    generation-improves baseVocab taskTm resumeCap-absent task-demands-resume

  -- G4: and with the task term itself compiled on both sides.
  task-compiles-better :
    (m n : ℕ) → Σ[ X ∈ Vocab ] Σ[ o ∈ Obstruction X ] TermImprovementAt X o taskTm m n
  task-compiles-better =
    generation-compiles-better baseVocab taskTm resumeCap-absent task-demands-resume

  -- G5: and the boundary, at the same concrete task.  After all of the
  -- above, the state `(baseVocab , taskTm)` STILL does not determine the
  -- answer — §H at this instance.  What generation supplied is the
  -- capability, not the object.
  task-underdetermined :
    ¬ ( Σ[ decode ∈ (Vocab → Tm → CanWord) ]
          ((m n : ℕ) → decode baseVocab taskTm ≡ exec (resume m (suc n))) )
  task-underdetermined = state-underdetermines-answer baseVocab taskTm

------------------------------------------------------------------------
-- Base-10 witness that the parameterised bridge really instantiates.
------------------------------------------------------------------------

module Base10Task = ConcreteTask 8
