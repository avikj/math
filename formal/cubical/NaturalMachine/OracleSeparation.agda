{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.OracleSeparation
--
-- TARGET.md (absent from this repository) §2 W3 (= `notes/BARRIER.md` (absent from this repository) §2's closing sentence / Problem 1),
-- at the sharpest form the finite parity model admits.  W3 IS TWO
-- QUESTIONS WITH OPPOSITE ANSWERS, and both answers are landed here as
-- checked terms.
--
-- THE SPLIT (see also `InterfaceSeparation.agda`).
--
--   W3 as written: "prove no post-processing of value queries simulates
--   functional-equation queries."  Split on what 'functional-equation
--   query' means:
--
--   (Q1) THE UNSPECIALIZED EQUATION — "is a(mn) = a(m)a(n)?", which is
--        BARRIER §3(2)'s literal oracle.  Answer: NO SEPARATION, and
--        trivially so.  The answer to every such query is the constant
--        `true` on the whole class, so the EMPTY set of value queries
--        already simulates the interface.  This is
--        `OracleQueries.fe-simulated-by-constant`, cited, not re-proved:
--        the program's own definitions pick this reading, and under it W3
--        is FALSE.
--
--   (Q2) THE SPECIALIZED INSTANCE — λ(pn) = −λ(n), the form the entropy
--        decrement actually consumes (BARRIER §2 row 3): the equation with
--        the charged fact λ(p) = −1 already installed.  Answer: the
--        SEPARATION IS REAL, and it is proved here against the strongest
--        value-side observer the model can express:
--
--        an observer holding the FULL transcript of the neutral sector —
--        the answer to EVERY even-Ω value query at once, and (in the
--        extended form) the answer to every unspecialized FE query too —
--        composed with an ARBITRARY post-processor F, cannot compute the
--        answer to even ONE specialized instance
--        (`no-postprocessing-simulates-sfe`).  Meanwhile that one
--        instance, used as an oracle, DECIDES the gauge flip, with the
--        decision procedure constructed (`one-sfe-decides`).
--
-- THE QUANTIFIER IS THE CONTENT.  `ParitySeparator.no-decision` and
-- `ChargeCriterion.neutral⇒no-separator` quantify over FINITE QUERY LISTS
-- and deciders `List Bool → Bool`.  What W3 asks about is post-processing,
-- so the statement here quantifies over
--
--     ALL functions  F : (full transcript) → A,  A an arbitrary type
--
-- — uncountably many, non-computable ones included, over the WHOLE
-- neutral sector at once, not a finite sample of it.  The theorem
-- (`no-charged-predicate`) is that no such F computes ANY flip-charged
-- predicate whatsoever.  The proof is still `cong F` — because by
-- poincaré's coset theorem (`GaugeOrbitClasses` §5: transcript fibres are
-- cosets of the query annihilator, and τ₋ annihilates the entire neutral
-- sector) the two full transcripts are EQUAL as functions, so there is
-- nothing downstream of them for any F to see.  §6 records the bridge to
-- that coset reading as a term, not just a remark.
--
-- WHERE THE CHARGE ACTUALLY LIVES.  The residue of the split is exact and
-- is the last theorem of the file: the specialized instance is
-- interreducible with a single charged VALUE query —
--
--     sans σ (sfe p n)  ≡  not (σ p)          (`sans-eval`)
--                       ≡  not (val σ [p])    (`sfe-is-one-charged-value`)
--
-- for EVERY n, including neutral n.  So "functional-equation access" in
-- its potent, specialized form is one odd-Ω value reading wearing the
-- equation as clothing; the equation contributes zero charge and the
-- installed value λ(p) = −1 contributes all of it — `OracleQueries`'
-- conclusion, now with the separation half proved rather than predicted.
-- The oracle separation W3 wanted is therefore NOT value-vs-equation; it
-- is NEUTRAL-SECTOR-vs-CHARGED-READING, and the equation is a carrier of
-- charge, never a source (`OracleQueries.Gen-neutral` is the conservation
-- law behind that sentence).
--
-- Contents (no holes, no postulates, --safe):
--
--   §1  EvenQuery, evenTr        the FULL even-Ω value transcript, as a
--       evenTr-collapse          function; it is EQUAL for σ and flip σ
--       NeutralQ, neuTr          the extension: all even values AND all
--       neuTr-collapse           unspecialized FE queries at once
--   §2  Charged                  a predicate the flip moves, somewhere
--       module Blindness         THE QUANTIFIER: for any transcript that
--         post-blind             collapses, every post-processor F into
--         no-charged             every type computes only flip-invariant
--                                predicates
--   §3  no-charged-predicate     the two instantiations: full even-value
--       no-charged-predicate⁺    transcript; extended transcript
--   §4  SFE, sans                the specialized instance λ(pn) = −λ(n)
--       sans-eval                its answer is not(σ p) — for every n
--       sfe-flips                so the flip moves it at every argument
--       one-sfe-decides          ONE instance decides the flip, decider
--                                constructed, at every base point σ
--   §5  sfe-answer-charged       the instance's answer is a charged
--       no-postprocessing-       predicate, hence: NO post-processor of
--         simulates-sfe          the full neutral transcript simulates
--                                even one specialized instance — W3(Q2)
--       sfe-is-one-charged-value …and one odd-Ω value query does, so the
--                                separation line runs between sectors,
--                                not between interfaces
--   §6  collapse-is-coset        the bridge to GaugeOrbitClasses §5
------------------------------------------------------------------------

module NaturalMachine.OracleSeparation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Relation.Nullary using (¬_)

open import NaturalMachine.ParitySeparator
open import NaturalMachine.ChargeCriterion using (σ₊ ; hd)
open import NaturalMachine.OracleQueries
  using (Query ; value ; fequ ; ans ; Neutral ; ans-agree ; ·-idem)
open import NaturalMachine.GaugeOrbitClasses
  using (τ₋ ; flip-is-τ₋ ; _⋆_ ; ·-not ; ·-unit-r)

------------------------------------------------------------------------
-- §1  The full transcripts, and their collapse.
--
-- Not a finite list of queries: the whole neutral sector at once, as a
-- FUNCTION from (query, proof of neutrality) to answer.  `evenTr σ` is
-- everything an even-Ω value observer can ever hold; `neuTr σ` adds the
-- answer to every unspecialized FE query as well.  The collapse lemmas
-- say each transcript is EQUAL — one function, `funExt` — for σ and its
-- gauge flip.  This is the input the universal quantifier of §2 eats.
------------------------------------------------------------------------

EvenQuery : Type
EvenQuery = Σ[ n ∈ Number ] (sgn (Ω n) ≡ true)

evenTr : Signs → EvenQuery → Bool
evenTr σ q = val σ (fst q)

evenTr-collapse : (σ : Signs) → evenTr σ ≡ evenTr (flip σ)
evenTr-collapse σ = funExt (λ q → sym (neutral-blind σ (fst q) (snd q)))

-- The extension: every neutral query of the two-interface oracle of
-- `OracleQueries` — all even-Ω values AND all unspecialized FE queries,
-- the latter neutral unconditionally (`Neutral (fequ m n) = Unit`).
NeutralQ : Type
NeutralQ = Σ[ q ∈ Query ] Neutral q

neuTr : Signs → NeutralQ → Bool
neuTr σ q = ans σ (fst q)

neuTr-collapse : (σ : Signs) → neuTr σ ≡ neuTr (flip σ)
neuTr-collapse σ = funExt (λ q → ans-agree σ (fst q) (snd q))

------------------------------------------------------------------------
-- §2  The universal quantifier over post-processors.
--
-- `Charged P`: the gauge flip moves P somewhere.  The Blindness module is
-- the whole of W3's negative half, stated once for any transcript that
-- collapses: EVERY function F out of the transcript space — into every
-- type, computable or not — factors through the collapse, so it computes
-- only flip-invariant predicates.  The quantifier over post-processors is
-- the explicit `(F : (I → Bool) → A)`; nothing about F is assumed.
------------------------------------------------------------------------

Charged : ∀ {ℓ} {A : Type ℓ} → (Signs → A) → Type ℓ
Charged P = Σ[ σ ∈ Signs ] (¬ (P σ ≡ P (flip σ)))

module Blindness (I : Type)
                 (t : Signs → I → Bool)
                 (collapse : (σ : Signs) → t σ ≡ t (flip σ)) where

  -- Any post-processing of the transcript returns equal results on σ and
  -- flip σ.  `cong F` — because the transcripts are the same object.
  post-blind : ∀ {ℓ} {A : Type ℓ} (F : (I → Bool) → A) (σ : Signs)
             → F (t σ) ≡ F (t (flip σ))
  post-blind F σ = cong F (collapse σ)

  -- "F computes P from the transcript": extensional, over every σ.
  Computes : ∀ {ℓ} {A : Type ℓ} → ((I → Bool) → A) → (Signs → A) → Type ℓ
  Computes F P = (σ : Signs) → F (t σ) ≡ P σ

  -- THE NEGATIVE HALF OF W3: no post-processor computes any charged
  -- predicate.  Note the shape — the impossible object is the PAIR
  -- (F computes P, P is charged), for arbitrary F, P, and target type.
  no-charged : ∀ {ℓ} {A : Type ℓ} (F : (I → Bool) → A) (P : Signs → A)
             → Computes F P → ¬ Charged P
  no-charged F P comp (σ , moved) =
    moved (sym (comp σ) ∙ post-blind F σ ∙ comp (flip σ))

------------------------------------------------------------------------
-- §3  The two instantiations.
------------------------------------------------------------------------

module EvenBlind    = Blindness EvenQuery evenTr evenTr-collapse
module NeutralBlind = Blindness NeutralQ  neuTr  neuTr-collapse

-- An observer holding the answer to EVERY even-Ω value query, with
-- unlimited post-processing, decides no charged predicate.
no-charged-predicate :
    ∀ {ℓ} {A : Type ℓ} (F : (EvenQuery → Bool) → A) (P : Signs → A)
  → EvenBlind.Computes F P → ¬ Charged P
no-charged-predicate = EvenBlind.no-charged

-- …and handing it every unspecialized FE answer as well changes nothing.
no-charged-predicate⁺ :
    ∀ {ℓ} {A : Type ℓ} (F : (NeutralQ → Bool) → A) (P : Signs → A)
  → NeutralBlind.Computes F P → ¬ Charged P
no-charged-predicate⁺ = NeutralBlind.no-charged

------------------------------------------------------------------------
-- §4  The converse boundary: one specialized instance decides the flip.
--
-- `sfe p n` asks "is a(p·n) = −a(n)?" — the entropy-decrement reading
-- λ(pn) = −λ(n) of BARRIER §2 row 3, i.e. the functional equation with
-- the value λ(p) = −1 installed.  In the sign group "x = y" is "x·y is
-- the unit", so the oracle returns val σ (p∷n) · not (val σ n).
--
-- `sans-eval` is the whole story: the answer is not (σ p), for EVERY n —
-- the n-dependence cancels through the equation, and what remains is
-- exactly the charged value the specialization had installed.  The even-Ω
-- argument n, neutral as a value reading, is decisive here only because
-- the equation transports the charge of p across it.
------------------------------------------------------------------------

data SFE : Type where
  sfe : ℕ → Number → SFE

sans : Signs → SFE → Bool
sans σ (sfe p n) = val σ (p ∷ n) · not (val σ n)

-- (a · b) · not b ≡ not a : the cancellation the equation performs.
·-cancel-not : (a b : Bool) → (a · b) · not b ≡ not a
·-cancel-not true  true  = refl
·-cancel-not true  false = refl
·-cancel-not false true  = refl
·-cancel-not false false = refl

sans-eval : (σ : Signs) (p : ℕ) (n : Number) → sans σ (sfe p n) ≡ not (σ p)
sans-eval σ p n = ·-cancel-not (σ p) (val σ n)

-- The flip moves the answer at EVERY argument of the interface.
sfe-flips : (σ : Signs) (p : ℕ) (n : Number)
          → sans (flip σ) (sfe p n) ≡ not (sans σ (sfe p n))
sfe-flips σ p n = sans-eval (flip σ) p n ∙ sym (cong not (sans-eval σ p n))

-- One specialized-FE query, used as an oracle, decides the flip — at
-- every base point σ, every prime index p, every carrier n, with the
-- decision procedure CONSTRUCTED: compare the answer with the expected
-- one (the comparison is `_·_`, which is equality in the sign group).
sobs : Signs → List SFE → List Bool
sobs σ qs = map (sans σ) qs

DecidesFlip : Signs → List SFE → Type
DecidesFlip σ qs =
  Σ[ decide ∈ (List Bool → Bool) ]
    ((decide (sobs σ qs) ≡ true) × (decide (sobs (flip σ) qs) ≡ false))

one-sfe-decides : (σ : Signs) (p : ℕ) (n : Number)
                → DecidesFlip σ (sfe p n ∷ [])
one-sfe-decides σ p n =
    (λ ℓ → sans σ (sfe p n) · hd ℓ)
  , ·-idem (sans σ (sfe p n))
  , ( cong (λ z → sans σ (sfe p n) · z) (sfe-flips σ p n)
    ∙ ·-not (sans σ (sfe p n)) )

------------------------------------------------------------------------
-- §5  THE SEPARATION, and where its charge lives.
--
-- The target: the answer of the single instance `sfe 0 []`, as a
-- predicate on sign assignments.  It is charged (`sfe-answer-charged`),
-- so §3 forbids every post-processor of the full neutral transcript from
-- computing it.  That is W3's Q2, with the quantifier over
-- post-processors explicit and the query side maximal:
--
--   value side:  ALL even-Ω values + ALL unspecialized FE answers,
--                arbitrary F on top
--   FE side:     ONE specialized instance
--
-- and the FE side wins.  Then `sfe-is-one-charged-value` closes the
-- ledger: the same instance is simulated exactly by one odd-Ω value
-- query, so the separating line is neutral-vs-charged, not
-- value-vs-equation.  Q1's collapse (`OracleQueries`) and Q2's
-- separation (here) are the two opposite answers.
------------------------------------------------------------------------

theQuery : SFE
theQuery = sfe 0 []

sfe-answer : Signs → Bool
sfe-answer σ = sans σ theQuery

sfe-answer-charged : Charged sfe-answer
sfe-answer-charged = σ₊ , (λ e → true≢false (sym e))

-- W3(Q2), the headline: no post-processing of the full neutral-value
-- transcript simulates even one specialized functional-equation query.
no-postprocessing-simulates-sfe :
    (F : (NeutralQ → Bool) → Bool)
  → ¬ ((σ : Signs) → F (neuTr σ) ≡ sfe-answer σ)
no-postprocessing-simulates-sfe F sim =
  no-charged-predicate⁺ F sfe-answer sim sfe-answer-charged

-- …a fortiori for the even-value-only observer.
no-evenvalue-postprocessing-simulates-sfe :
    (F : (EvenQuery → Bool) → Bool)
  → ¬ ((σ : Signs) → F (evenTr σ) ≡ sfe-answer σ)
no-evenvalue-postprocessing-simulates-sfe F sim =
  no-charged-predicate F sfe-answer sim sfe-answer-charged

-- The residue: the specialized instance IS one charged value query.
-- Unrestricted value access simulates it in one reading; only the
-- neutral sector cannot.  The equation carries the charge of the
-- installed value λ(p) = −1 across any n; it adds none of its own.
sfe-is-one-charged-value :
    (σ : Signs) (p : ℕ) (n : Number)
  → sans σ (sfe p n) ≡ not (val σ (p ∷ []))
sfe-is-one-charged-value σ p n =
  sans-eval σ p n ∙ cong not (sym (·-unit-r (σ p)))

------------------------------------------------------------------------
-- §6  The coset reading, as a term.
--
-- `GaugeOrbitClasses` §5: transcript fibres are cosets of the query
-- annihilator.  The collapse of §1 is that theorem's instance at the
-- full neutral sector, whose annihilator contains τ₋: translating any σ
-- by the parity element does not move its full transcript.  So the
-- observable class of the neutral sector identifies σ with τ₋ ⋆ σ, and
-- §5's separation says the specialized-FE oracle splits exactly that
-- identification — one coset coordinate, the ⟨·,1⟩ bit.
------------------------------------------------------------------------

collapse-is-coset : (σ : Signs) → neuTr (τ₋ ⋆ σ) ≡ neuTr σ
collapse-is-coset σ =
  cong neuTr (sym (flip-is-τ₋ σ)) ∙ sym (neuTr-collapse σ)
