{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ChargeIsStrictRefinement
--
-- THE W2 ADAPTER, AS A TERM — what it buys, and the exact reason it does
-- not buy the whole of W2 by itself.
--
-- smallest of its four: "one Lean/Agda transport; after it, 'is this
-- probe charged?' is a term, not an audit."  This module is that
-- transport.  It has three parts, and the middle one is the merge:
--
--   §3  the transported Lean iff is EXACTLY the annihilator statement of
--       `GaugeOrbitClasses` — two theorems in two lanes that were the
--       same theorem and did not know it;
--   §4  the parity charge criterion is that iff EVALUATED AT ONE GROUP
--       ELEMENT, τ₋; and the audit it licenses is made total, so the
--       reader supplies a query list and nothing else;
--   §5  therefore the transport alone does NOT deliver a charge
--       criterion — a typed negative whose witness is not mine.
--
--
-- WHAT IS BEING TRANSPORTED.
--
-- `formal/lean/Pairfield/AdaptiveResidualStrictRefinementIff.lean`,
-- `insert_strictly_refines_iff_exists_agree_separates`:
--
--     experimentPartition M (insert suffix tests)
--         < experimentPartition M tests
--   ↔ ∃ left right : State M,
--        (∀ test ∈ tests, test ∈ left.val ↔ test ∈ right.val)
--      ∧ ¬(suffix ∈ left.val ↔ suffix ∈ right.val)
--
-- "Inserting a test is strictly informative iff it separates a pair of
-- states which every installed test identifies."  The dictionary the
-- synthesis proposed, written out:
--
--     Lean                                 here
--     ------------------------------------ ---------------------------
--     State M            (DFA residuals)   Signs = ℕ → Bool
--                                          (sign assignments on primes)
--     List A             (a suffix/test)   Number = List ℕ
--                                          (a factor multiset; Ω = length)
--     test ∈ (s.val : Language A) : Prop   val s t : Bool
--     tests : Finset (List A)              qs : List Number
--     the experiment partition             `Identifies qs` (§2)
--     strict refinement on insertion       `AgreeSeparate qs t` (§2)
--
-- The Lean iff is the licence to take the right-hand side as the
-- DEFINITION of "strictly informative": the theorem says the two are the
-- same predicate, so nothing is lost.  That is the entire meaning of
-- "definitional" here, and §2 is where it is cashed.
--
--
-- WHY AGDA AND NOT LEAN.
--
-- Every object the transport lands on — `Signs`, `Number`, `Ω`, `val`,
-- `flip`, `sgn`, the gauge group `Gauge` with its action `_⋆_`, the
-- annihilator `AllNeutral`, `HasOdd`, `AllEven` — is already Agda, in
-- this directory, and so are the three theorems the adapter has to reach
-- (`ParitySeparator.no-decision`, `ChargeCriterion.charge-criterion`,
-- `GaugeOrbitClasses.classes-⇐/⇒`).  Going the other way would mean
-- presenting sign assignments as DFAs over the infinite alphabet ℕ with
-- `Fintype (State M)` — manufacturing exactly the finiteness the parity
-- side does not have, in order to import a theorem whose statement is
-- four lines.  Second reason: §4's audit must COMPUTE, since `refl` is
-- what supplies the index a reader used to supply by hand.
--
--
-- PRIOR ART IN THIS CORPUS, consumed and credited (searched BEFORE
-- writing, per `CLAUDE.md` (absent from this repository)).
--
--   `NaturalMachine/GaugeOrbitClasses.agda` — the character law `val-⋆`,
--     the annihilator subgroup qs^⊥ = `AllNeutral · qs`, and the class
--     theorem (transcript fibres = cosets of qs^⊥).  §3 below is the
--     statement that the Lean iff transports to precisely that
--     annihilator; every lemma §3 uses is from there.
--   THE WITNESS OF §5 IS NOT NEW.  It is `GaugeOrbitClasses` §6's τ₀,
--     the single-prime flip, and that module already states it:
--     ("`AllEven` is not 'sees no gauge structure'; it is
--     'annihilated by the total flip'").  What §5 adds is only its
--     CONSEQUENCE FOR THIS TRANSPORT — that the Lean iff, transported,
--     is a statement about the whole annihilator and therefore cannot
--     by itself be a charge criterion.  Translation is not a result;
--     the result is §3 and §4, and §5 is the typed limit on them.
--   `NaturalMachine/ChargeCriterion.agda`, `ParitySeparator.agda` — the
--     criterion and the no-go it converses.  §4 does not reprove them;
--     it removes the hand step in front of them.
--
--
------------------------------------------------------------------------

module ChargeIsStrictRefinement where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; _or_ ; true≢false ; false≢true)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import ParitySeparator
open import ChargeCriterion
open import GaugeOrbitClasses

------------------------------------------------------------------------
-- §1  Boolean bookkeeping.
--
-- Each of these turns a computed Bool back into a path, which is the
-- only way §4's `refl` can do the work a reader used to do by hand.
------------------------------------------------------------------------

private
  orTrue : (a b : Bool) → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
  orTrue true  b p = inl refl
  orTrue false b p = inr p

  orFalse-l : (a b : Bool) → a or b ≡ false → a ≡ false
  orFalse-l true  b p = ⊥.rec (true≢false p)
  orFalse-l false b p = refl

  orFalse-r : (a b : Bool) → a or b ≡ false → b ≡ false
  orFalse-r true  b p = ⊥.rec (true≢false p)
  orFalse-r false b p = p

  notTrue→false : (b : Bool) → not b ≡ true → b ≡ false
  notTrue→false true  p = ⊥.rec (false≢true p)
  notTrue→false false p = refl

  notFalse→true : (b : Bool) → not b ≡ false → b ≡ true
  notFalse→true true  p = refl
  notFalse→true false p = ⊥.rec (true≢false p)

  -- Two Bools differ exactly when their product is −1.  This is where
  -- the Lean "¬(… ↔ …)" turns into an element of the annihilator's
  -- complement, and it is the only step of §3 that is not bookkeeping.
  ·-distinct : (a b : Bool) → ¬ (a ≡ b) → b · a ≡ false
  ·-distinct true  true  p = ⊥.rec (p refl)
  ·-distinct true  false p = refl
  ·-distinct false true  p = refl
  ·-distinct false false p = ⊥.rec (p refl)

------------------------------------------------------------------------
-- §2  The Lean statement, transported.
--
-- `Test` is the transported `List A` (a suffix); `State` the transported
-- `State M`.  The transported `test ∈ s.val` is `val s t` — a Bool, not
-- a Prop, because the observation here is an evaluation and not a
-- membership; the biconditional of the Lean statement becomes a path of
-- Bools and its negation becomes `SeparatesPair`.
--
-- Note what happens to the Lean typeclass burden.  `Finset (List A)`
-- becomes a plain `List Test` — nothing below deduplicates, so
-- `DecidableEq A` is not needed.  `Fintype (State M)` has NO image at
-- all: `State` here is the free space {±1}^P of `TARGET.md` (absent from this repository) §3.  That
-- missing hypothesis is not an oversight; §5 is what it costs.
------------------------------------------------------------------------

Test : Type
Test = Number

State : Type
State = Signs

infix 4 _∈_

_∈_ : Test → List Test → Type
t ∈ []       = ⊥
t ∈ (u ∷ ts) = (t ≡ u) ⊎ (t ∈ ts)

-- "∀ test ∈ tests, test ∈ left.val ↔ test ∈ right.val"
Identifies : List Test → State → State → Type
Identifies ts s₁ s₂ = (t : Test) → t ∈ ts → val s₁ t ≡ val s₂ t

-- "¬(suffix ∈ left.val ↔ suffix ∈ right.val)"
SeparatesPair : Test → State → State → Type
SeparatesPair t s₁ s₂ = ¬ (val s₁ t ≡ val s₂ t)

-- The whole Lean right-hand side: the agree-and-separate witness set.
-- By `insert_strictly_refines_iff_exists_agree_separates` this IS
-- "inserting t strictly refines the experiment partition", so this
-- definition carries the transported LEFT-hand side too.
AgreeSeparate : List Test → Test → Type
AgreeSeparate ts t =
  Σ[ s₁ ∈ State ] Σ[ s₂ ∈ State ] (Identifies ts s₁ s₂ × SeparatesPair t s₁ s₂)

-- Pointwise/structural bridges.  `GaugeOrbitClasses.AllNeutral` and
-- `ParitySeparator.AllEven` are structural list predicates; the Lean
-- statement quantifies with a membership.  Both directions are needed.
allNeutral→pointwise : (τ : Gauge) (ts : List Test) → AllNeutral τ ts
                     → (t : Test) → t ∈ ts → val τ t ≡ true
allNeutral→pointwise τ (u ∷ ts) (e , _)    t (inl p) = cong (val τ) p ∙ e
allNeutral→pointwise τ (u ∷ ts) (_ , rest) t (inr m) =
  allNeutral→pointwise τ ts rest t m

pointwise→allNeutral : (τ : Gauge) (ts : List Test)
                     → ((t : Test) → t ∈ ts → val τ t ≡ true) → AllNeutral τ ts
pointwise→allNeutral τ []       f = tt
pointwise→allNeutral τ (u ∷ ts) f =
  f u (inl refl) , pointwise→allNeutral τ ts (λ t m → f t (inr m))

allEven→pointwise : (ts : List Test) → AllEven ts
                  → (t : Test) → t ∈ ts → sgn (Ω t) ≡ true
allEven→pointwise (u ∷ ts) (e , _)    t (inl p) = cong (λ z → sgn (Ω z)) p ∙ e
allEven→pointwise (u ∷ ts) (_ , rest) t (inr m) = allEven→pointwise ts rest t m

------------------------------------------------------------------------
-- §3  THE MERGE.
--
-- The transported Lean iff is exactly the annihilator statement of
-- `GaugeOrbitClasses`:
--
--     a probe t is strictly informative over an installed set qs
--   ⟺ some gauge element annihilated by every installed query is
--     NOT annihilated by t
--   ⟺ qs^⊥ ⊄ {t}^⊥,  i.e. inserting t shrinks the annihilator.
--
-- This is what "the merge, not the program" meant.  `GaugeOrbitClasses`
-- §5 proves that transcript fibres are the cosets of qs^⊥; the Lean
-- theorem proves that inserting a test strictly refines the experiment
-- partition iff an identified pair is separated.  A partition into
-- cosets is strictly refined exactly when the subgroup shrinks, and
-- `annihilator-iff` below is that sentence as a term.
--
-- The two directions are the two halves of "the state space is a torsor
-- over the gauge group": ⇐ turns a group element into a pair by acting
-- on the base point σ₊, and ⇒ turns a pair back into a group element by
-- taking its difference s₂ ⋆ s₁ (which is a difference because G has
-- exponent 2 — `GaugeOrbitClasses.ann-self-inverse`).
------------------------------------------------------------------------

-- The right-hand side: qs^⊥ is not contained in {t}^⊥.
ShrinksAnnihilator : List Test → Test → Type
ShrinksAnnihilator ts t = Σ[ τ ∈ Gauge ] (AllNeutral τ ts × (val τ t ≡ false))

shrinks→agreeSeparate : (ts : List Test) (t : Test)
                      → ShrinksAnnihilator ts t → AgreeSeparate ts t
shrinks→agreeSeparate ts t (τ , neutral , charged) =
    σ₊ , (τ ⋆ σ₊)
  , (λ u m → sym (neutral-invisible τ σ₊ u
                    (allNeutral→pointwise τ ts neutral u m)))
  , λ p → true≢false ( sym (val-σ₊ t) ∙ p
                     ∙ charged-visible τ σ₊ t charged
                     ∙ cong not (val-σ₊ t) )

agreeSeparate→shrinks : (ts : List Test) (t : Test)
                      → AgreeSeparate ts t → ShrinksAnnihilator ts t
agreeSeparate→shrinks ts t (s₁ , s₂ , ident , sep) =
    (s₂ ⋆ s₁)
  , pointwise→allNeutral (s₂ ⋆ s₁) ts
      (λ u m → val-⋆ s₂ s₁ u
             ∙ cong (λ z → val s₂ u · z) (ident u m)
             ∙ ·-self (val s₂ u))
  , (val-⋆ s₂ s₁ t ∙ ·-distinct (val s₁ t) (val s₂ t) sep)

-- The transported Lean iff, proved on this side of the dictionary.
annihilator-iff : (ts : List Test) (t : Test)
                → (AgreeSeparate ts t → ShrinksAnnihilator ts t)
                × (ShrinksAnnihilator ts t → AgreeSeparate ts t)
annihilator-iff ts t = agreeSeparate→shrinks ts t , shrinks→agreeSeparate ts t

------------------------------------------------------------------------
-- §4  CHARGE IS THAT IFF AT ONE GROUP ELEMENT — and the audit runs.
--
-- Specialise §3's witness to τ = τ₋, the diagonal element (−1,−1,…)
-- whose character is the parity grading (`GaugeOrbitClasses.val-τ₋`).
-- Then `ShrinksAnnihilator` becomes, coordinate by coordinate:
--
--     AllNeutral τ₋ qs   ⟺  AllEven qs        (`ParitySeparator`)
--     val τ₋ t ≡ false   ⟺  sgn (Ω t) ≡ false (`ChargeCriterion.HasOdd`
--                                              at a single query)
--
-- so `Charged` below is `ChargeCriterion`'s criterion arrived at as an
-- instance rather than posited — which is what W2's adapter was for.
-- `charged?` decides it, and that is where the audit stops being manual.
--
-- `ChargeCriterion`'s own worked instances show the manual step:
--
--     probe-2-separates = odd⇒separator probe-2 (inl refl)
--     probe-6-cannot    = neutral⇒no-separator probe-6 (refl , tt)
--
-- `inl refl` and `(refl , tt)` are the reader performing the audit —
-- invisible on a one-element list, and the whole job on a real one.
-- `audit` is total: query list in, verdict-with-proof out.
------------------------------------------------------------------------

Charged : List Test → Test → Type
Charged ts t = AllNeutral τ₋ ts × (val τ₋ t ≡ false)

charged? : Test → Bool
charged? t = not (sgn (Ω t))

-- Charge is a special case of strict informativeness (§5: strictly so).
Charged→AgreeSeparate : (ts : List Test) (t : Test)
                      → Charged ts t → AgreeSeparate ts t
Charged→AgreeSeparate ts t (neutral , c) =
  shrinks→agreeSeparate ts t (τ₋ , neutral , c)

-- The two coordinate translations, both directions.
allEven→τ₋neutral : (ts : List Test) → AllEven ts → AllNeutral τ₋ ts
allEven→τ₋neutral []       tt         = tt
allEven→τ₋neutral (u ∷ ts) (e , rest) =
  val-τ₋ u ∙ e , allEven→τ₋neutral ts rest

τ₋neutral→allEven : (ts : List Test) → AllNeutral τ₋ ts → AllEven ts
τ₋neutral→allEven []       tt         = tt
τ₋neutral→allEven (u ∷ ts) (e , rest) =
  sym (val-τ₋ u) ∙ e , τ₋neutral→allEven ts rest

odd→τ₋charged : (t : Test) → sgn (Ω t) ≡ false → val τ₋ t ≡ false
odd→τ₋charged t o = val-τ₋ t ∙ o

τ₋charged→odd : (t : Test) → val τ₋ t ≡ false → sgn (Ω t) ≡ false
τ₋charged→odd t c = sym (val-τ₋ t) ∙ c

-- The adapter, as one statement: charge is the τ₋-instance of §3, and it
-- is the odd-Ω criterion.
charge-is-odd-Ω : (ts : List Test) (t : Test)
                → (Charged ts t → (AllEven ts × (sgn (Ω t) ≡ false)))
                × ((AllEven ts × (sgn (Ω t) ≡ false)) → Charged ts t)
charge-is-odd-Ω ts t =
    (λ (n , c) → τ₋neutral→allEven ts n , τ₋charged→odd t c)
  , λ (e , o) → allEven→τ₋neutral ts e , odd→τ₋charged t o

charged?-sound : (t : Test) → val τ₋ t ≡ false → charged? t ≡ true
charged?-sound t c = cong not (τ₋charged→odd t c)

charged?-complete : (t : Test) → charged? t ≡ true → val τ₋ t ≡ false
charged?-complete t p = odd→τ₋charged t (notTrue→false (sgn (Ω t)) p)

------------------------------------------------------------------------
-- §4.1  The audit, total.
------------------------------------------------------------------------

anyCharged : List Test → Bool
anyCharged []       = false
anyCharged (t ∷ ts) = charged? t or anyCharged ts

-- The computed verdict, reflected back into the indices
-- `ChargeCriterion` asks for.
reflect-true : (ts : List Test) → anyCharged ts ≡ true → HasOdd ts
reflect-true []       p = ⊥.rec (false≢true p)
reflect-true (t ∷ ts) p with orTrue (charged? t) (anyCharged ts) p
... | inl q = inl (notTrue→false (sgn (Ω t)) q)
... | inr q = inr (reflect-true ts q)

reflect-false : (ts : List Test) → anyCharged ts ≡ false → AllEven ts
reflect-false []       p = tt
reflect-false (t ∷ ts) p =
    notFalse→true (sgn (Ω t)) (orFalse-l (charged? t) (anyCharged ts) p)
  , reflect-false ts (orFalse-r (charged? t) (anyCharged ts) p)

-- THE DELIVERABLE.  `Separates` is `ChargeCriterion`'s: a decision
-- procedure accepting σ₊ and rejecting its gauge flip.  Nothing about
-- the query list has to be known in advance, and no index is supplied.
private
  auditOn : (ts : List Test) (b : Bool) → anyCharged ts ≡ b
          → Separates ts ⊎ (¬ (Separates ts))
  auditOn ts true  p = inl (odd⇒separator ts (reflect-true ts p))
  auditOn ts false p = inr (neutral⇒no-separator ts (reflect-false ts p))

audit : (ts : List Test) → Separates ts ⊎ (¬ (Separates ts))
audit ts = auditOn ts (anyCharged ts) refl

-- Likewise for a single probe against an installed set, which is the
-- form the Lean statement is in.
private
  probeAuditOn : (ts : List Test) (t : Test) (b : Bool) → anyCharged ts ≡ b
               → Charged ts t ⊎ (¬ (Charged ts t))
  probeAuditOn ts t true  p =
    inr (λ (n , _) →
      neutral-not-charged τ₋ ts n
        (chargeOf ts (reflect-true ts p)))
    where
      -- an odd installed query is a charged one for τ₋, so the
      -- installed set does not annihilate τ₋ and no probe is strictly
      -- informative about that orbit any more.
      chargeOf : (qs : List Test) → HasOdd qs → HasCharge τ₋ qs
      chargeOf (u ∷ qs) (inl o) = inl (odd→τ₋charged u o)
      chargeOf (u ∷ qs) (inr h) = inr (chargeOf qs h)
  probeAuditOn ts t false p = helper (charged? t) refl
    where
      helper : (b : Bool) → charged? t ≡ b → Charged ts t ⊎ (¬ (Charged ts t))
      helper true  q = inl (allEven→τ₋neutral ts (reflect-false ts p)
                           , charged?-complete t q)
      helper false q = inr (λ (_ , c) →
        true≢false (sym (notFalse→true (sgn (Ω t)) q) ∙ τ₋charged→odd t c))

probeAudit : (ts : List Test) (t : Test) → Charged ts t ⊎ (¬ (Charged ts t))
probeAudit ts t = probeAuditOn ts t (anyCharged ts) refl

------------------------------------------------------------------------
-- §4.2  Worked instances, with the index supplied by `refl`.
--
-- In each of these the only input is the list.  The odd query in `mixed`
-- is the second of three; `reflect-true mixed refl` finds it.
------------------------------------------------------------------------

mixed : List Test                -- {p₀p₁ , p₀²p₁ , p₀p₁p₂p₃} — Ω = 2,3,4
mixed = (0 ∷ 1 ∷ []) ∷ (0 ∷ 0 ∷ 1 ∷ []) ∷ (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷ []

mixed-verdict : anyCharged mixed ≡ true
mixed-verdict = refl

mixed-separates : Separates mixed
mixed-separates = odd⇒separator mixed (reflect-true mixed refl)

neutralSet : List Test           -- Ω = 2,2,4: every query parity-neutral
neutralSet = (0 ∷ 1 ∷ []) ∷ (2 ∷ 2 ∷ []) ∷ (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷ []

neutralSet-verdict : anyCharged neutralSet ≡ false
neutralSet-verdict = refl

neutralSet-blind : ¬ (Separates neutralSet)
neutralSet-blind = neutral⇒no-separator neutralSet (reflect-false neutralSet refl)

-- The single-probe form: charge, decided, with no orbit reasoning by
-- hand.  `[]` is vacuously neutral, so both verdicts are about the probe.
probe-charged : Charged [] (0 ∷ [])
probe-charged = tt , refl

probe-neutral-not-charged : ¬ (Charged [] (0 ∷ 1 ∷ []))
probe-neutral-not-charged (_ , c) = true≢false (τ₋charged→odd (0 ∷ 1 ∷ []) c)

------------------------------------------------------------------------
-- §5  THE TYPED LIMIT ON §3.
--
-- checked term of ¬P at a stated locus, with the refuting instance
-- exhibited).  THE WITNESS IS NOT NEW — it is `GaugeOrbitClasses` §6's
-- τ₀, the single-prime flip, and that module already draws the
-- distinction it certifies.  What is stated here is only its
-- consequence for this transport, which is the thing a successor could
-- otherwise assume the Lean term already supplies.
--
-- The tempting reading of "transport the Lean iff and the charge
-- criterion is DEFINITIONAL" is: charge = strict refinement of the
-- experiment partition.  It is not.  By §3 the transported iff says the
-- ANNIHILATOR SUBGROUP shrinks — a statement about all of qs^⊥ — while
-- charge is that statement's value at the single element τ₋.  A probe
-- can shrink the annihilator without touching τ₋.
--
-- Locus: `Signs = ℕ → Bool` with the full gauge group acting, i.e. the
-- free state space of `TARGET.md` (absent from this repository) §3.  Instance: t = p₀p₁ (Ω = 2, hence
-- parity-neutral) and τ = τ₀.
--
-- WHAT EXACTLY FAILS TO TRANSPORT, named.  In Lean, `State M` is the
-- residual state space of the automaton under study — canonical,
-- `Fintype`, determined by the object.  On the parity side the states
-- are a torsor under a gauge group, and "is this probe informative?"
-- has no answer until a SUBGROUP of that gauge group is named.  The
-- gauge group is the structure with no counterpart in the Lean
-- statement; §4's restriction to τ₋ is where it enters, and it is not a
-- convenience but the entire specificity of W2.
--
-- CONSEQUENCE, stated so it can be checked against.  The adapter of
-- §3–§4 is real and its scope is the subgroup ⟨τ₋⟩.  A charge criterion
-- phrased as strict refinement over the full state space is refuted
-- below; anyone extending this to W3 must carry the subgroup with them.
------------------------------------------------------------------------

neutralProbe : Test              -- p₀p₁: Ω = 2
neutralProbe = 0 ∷ 1 ∷ []

neutralProbe-is-neutral : sgn (Ω neutralProbe) ≡ true
neutralProbe-is-neutral = refl

-- τ₀ is `GaugeOrbitClasses`' single-prime flip, and it is not
-- annihilated by a query the parity grading cannot see.
τ₀-charged-here : val τ₀ neutralProbe ≡ false
τ₀-charged-here = refl

-- So the probe shrinks the annihilator with nothing installed…
neutral-but-strictly-informative : ShrinksAnnihilator [] neutralProbe
neutral-but-strictly-informative = τ₀ , tt , τ₀-charged-here

-- …hence is strictly informative in the transported Lean sense…
neutral-but-agreeSeparating : AgreeSeparate [] neutralProbe
neutral-but-agreeSeparating =
  shrinks→agreeSeparate [] neutralProbe neutral-but-strictly-informative

-- …while carrying no parity charge.
T1-strict-refinement-is-not-charge :
  ¬ ((ts : List Test) (t : Test) → AgreeSeparate ts t → sgn (Ω t) ≡ false)
T1-strict-refinement-is-not-charge h =
  true≢false (sym neutralProbe-is-neutral
              ∙ h [] neutralProbe neutral-but-agreeSeparating)

-- The inclusion of §4 is therefore strict: charge ⊊ strict
-- informativeness, with the gap exhibited.
Charged⊊AgreeSeparate :
  Σ[ t ∈ Test ] (AgreeSeparate [] t × (¬ (Charged [] t)))
Charged⊊AgreeSeparate =
  neutralProbe , neutral-but-agreeSeparating , probe-neutral-not-charged
