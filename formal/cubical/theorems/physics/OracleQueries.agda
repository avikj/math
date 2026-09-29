{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- OracleQueries
--
-- TARGET.md (absent from this repository) §6 item 2, answered — and answered in the negative.
--
-- THE QUESTION.  `ChargeCriterion` proves: a query set separates the
-- all-plus sign assignment from its gauge flip IFF it contains a query
-- of odd Ω.  `notes/BARRIER.md` (absent from this repository) §3 Problem 2 asks for an oracle model
-- distinguishing VALUE queries ("what is a(n)?") from FUNCTIONAL-EQUATION
-- queries ("a(mn)=a(m)a(n), used as a constraint and not as a value").
-- TARGET.md (absent from this repository) §6 predicts these are "the same distinction stated twice",
-- and says that if they are not, the difference is the finding.
--
-- THEY ARE NOT THE SAME, AND THE DIFFERENCE IS EXACT.  A
-- functional-equation query carries NO charge — not "usually none", not
-- "none unless its arguments are odd": none, unconditionally, at every
-- pair of arguments, including maximally charged ones.  Its answer is
-- the constant `true` on the entire class of completely multiplicative
-- ±1 functions (`fe-const`), so it is simulated exactly by post-processing
-- that ignores the oracle.  Functional-equation access therefore lies
-- strictly INSIDE the blind side of the charge criterion; the two axes are
-- orthogonal, not identical.
--
-- The one-line witness is `p-two-ways`: the SAME odd-Ω argument p
-- separates when read as a value and does not separate when read through
-- the functional equation.  Charge is a property of the READING, not of
-- the argument — which is the sharper form of ChargeCriterion's own
-- "charge lives in what a method reads".
--
-- WHY, STRUCTURALLY (the reason the counterexample had to exist).  The
-- parity charge is the map χ = sgn ∘ Ω, and χ is a MONOID CHARACTER of the
-- factorization monoid: χ(mn) = χ(m)χ(n) (`charge-++`).  The functional
-- equation is precisely the monoid law that χ is a character FOR.  A
-- character cannot be moved by the law it respects, so the kernel of χ —
-- the neutral sector — is closed under everything the functional equation
-- licenses.  That is `Gen-neutral`: the deductive closure of a neutral
-- query set under multiplication AND division is still neutral, hence by
-- `ChargeCriterion.neutral⇒no-separator` still non-separating.  This is
-- the conservation law behind the counterexample: symmetry and conserved
-- quantity are the same statement, and here the symmetry is the gauge
-- flip, the conserved quantity is χ, and the functional equation is a
-- gauge-invariant relation, so it conserves χ identically.
--
-- WHAT THIS SAYS ABOUT `BARRIER.md` (absent from this repository).  That note's §2 visibility table
-- credits row 3, "functional-equation access", with being "the one known
-- access to Chowla-grade (bulk) content", and its own honesty ledger §4
-- says row 3 rests on "reading Tao's published argument through this lens
-- (no new analysis of it here)".  This module supplies the missing
-- analysis for the parity axis, and it inverts the attribution: the
-- entropy-decrement step uses λ(pn) = −λ(n), which is the functional
-- equation SPECIALIZED AT A KNOWN VALUE λ(p) = −1 — a value query at
-- Ω = 1, i.e. the single maximally charged reading there is.  By the
-- charge criterion that value is what puts the method on the separating
-- side.  The equation contributes exactly zero charge; the value
-- contributes all of it.  So "functional-equation access" is not a third
-- interface with more parity power — it is the neutral monoid law plus a
-- charged value query, and only the second half is doing work.
--
-- CONSEQUENCE FOR W3 (BARRIER Problem 1 / TARGET §2 W3).  W3 asks to prove
-- that no post-processing of value queries simulates functional-equation
-- queries.  On the parity axis that is FALSE and this module refutes it:
-- FE queries are simulated by the constant `true`, using no queries at
-- all (`fe-simulated-by-constant`).  The separation, if there is one,
-- must run the other way and must be about the functional equation as an
-- INFERENCE RULE applied to a charged seed — not about it as a query type.
--
-- Contents (no holes, no postulates, --safe):
--
--   val-++, Ω-++, sgn-+       val and Ω are monoid homomorphisms
--   charge-++                 χ = sgn ∘ Ω is a monoid CHARACTER
--   Query, ans                the two-interface oracle of BARRIER §3(2)
--   fe-const                  every FE answer is `true`, for every σ
--   fe-simulated-by-constant  hence FE queries have a query-free simulator
--   Neutral, AllNeutral       charge of a query; FE queries: always neutral
--   neutralQ⇒no-separator     neutral transcripts are equal, so no decision
--   fe-blind                  an ALL-FE query set never separates, however
--                             charged its arguments
--   p-two-ways                THE FINDING: one odd-Ω argument, two
--                             readings, opposite verdicts
--   Gen, Gen-sound            the FE deductive closure, and that it really
--                             is a closure (it determines values)
--   Gen-neutral               CONSERVATION: closure of neutral is neutral
--   closure-no-separator      hence FE inference cannot manufacture a
--                             separator from neutral readings
--
-- RELATION TO `InterfaceSeparation` (W3, BARRIER Problem 1),
-- which arrives at the same core facts from the other assignment: its
-- `fe-promised-constant` is `fe-const` here, its `fe-simulated-by-nothing`
-- is `fe-simulated-by-constant`, its `sgn-++` is `charge-++`, and its
-- `fe-closure-cannot-separate` is the `mul` half of `Gen-neutral`.
-- Its W3 dichotomy (FE access is nonconstant on
-- ARBITRARY ±1 sequences, hence its content is the multiplicativity promise
-- itself) is proved there.
--
-- WHAT IS ONLY HERE:
--   * `Gen` carries a DIVISION rule (`quo`) as well as multiplication.  Its
--     `Deriv` is `var`/`unit`/`mul` only.  Division is exactly the rule a
--     hostile reader reaches for — "divide a known argument by a known
--     divisor and land on an odd one" — and it is the only rule whose
--     neutrality needs cancellation in F₂ rather than closure under the
--     product (`·-cancel`).  Closing that case is what makes the
--     conservation law a statement about the GROUP the functional equation
--     generates, not just the monoid.
--   * `Gen-sound`: the closure really is a closure — two sign assignments
--     agreeing on the basis agree on everything derived, division included —
--     so `quo` is a licensed inference and not an extra assumption.
--   * `p-two-ways`: the orthogonality witness that answers TARGET §6 item 2,
--     which is a different question from W3.
------------------------------------------------------------------------

module OracleQueries where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Relation.Nullary using (¬_)

open import ParitySeparator
open import ChargeCriterion

------------------------------------------------------------------------
-- §1  The two homomorphisms, and the character.
--
-- `val σ` and `Ω` are both monoid homomorphisms out of the factorization
-- monoid (Number, ++).  The first IS the functional equation; the second,
-- composed with the parity character of ℕ, IS the charge.  Everything in
-- this module is the interaction of these two facts, so they are proved
-- first and separately.
------------------------------------------------------------------------

·-idem : (b : Bool) → b · b ≡ true
·-idem true  = refl
·-idem false = refl

-- Cancellation in ℤ/2, in the only form used below.
·-cancel : {a b : Bool} → a ≡ true → a · b ≡ true → b ≡ true
·-cancel {a} {b} ea eab = sym (cong (λ z → z · b) ea) ∙ eab

-- THE FUNCTIONAL EQUATION.  This is not an auxiliary lemma: it is the
-- object BARRIER §3(2) proposes to give an oracle interface to.
val-++ : (σ : Signs) (m n : Number) → val σ (m ++ n) ≡ val σ m · val σ n
val-++ σ []       n = refl
val-++ σ (p ∷ ms) n =
    cong (λ z → σ p · z) (val-++ σ ms n)
  ∙ sym (·-assoc (σ p) (val σ ms) (val σ n))

Ω-++ : (m n : Number) → Ω (m ++ n) ≡ Ω m + Ω n
Ω-++ []       n = refl
Ω-++ (p ∷ ms) n = cong suc (Ω-++ ms n)

not-·ˡ : (a b : Bool) → not (a · b) ≡ (not a) · b
not-·ˡ true  true  = refl
not-·ˡ true  false = refl
not-·ˡ false true  = refl
not-·ˡ false false = refl

sgn-+ : (a b : ℕ) → sgn (a + b) ≡ sgn a · sgn b
sgn-+ zero    b = refl
sgn-+ (suc a) b = cong not (sgn-+ a b) ∙ not-·ˡ (sgn a) (sgn b)

-- THE CHARACTER.  χ = sgn ∘ Ω is multiplicative.  This single line is the
-- reason the finding below is not an accident of the encoding: a
-- character is by definition the thing the monoid law cannot move.
charge-++ : (m n : Number) → sgn (Ω (m ++ n)) ≡ sgn (Ω m) · sgn (Ω n)
charge-++ m n = cong sgn (Ω-++ m n) ∙ sgn-+ (Ω m) (Ω n)

-- Immediate: every square is neutral AND its value is pinned, for every σ.
-- The smallest instance of "the functional equation returns a constant".
square-const : (σ : Signs) (n : Number) → val σ (n ++ n) ≡ true
square-const σ n = val-++ σ n n ∙ ·-idem (val σ n)

------------------------------------------------------------------------
-- §2  The oracle of BARRIER.md (absent from this repository) §3 Problem 2.
--
--   `value n`   — "what is a(n)?"           (a value query)
--   `fequ m n`  — "is a(mn) = a(m)a(n)?"    (a functional-equation query,
--                                            the equation consumed as a
--                                            constraint and not as a value,
--                                            which is BARRIER §2's own
--                                            wording for row 3)
--
-- Answers are ±1 = Bool.  The FE answer is encoded as the product
-- a(mn)·a(m)·a(n), which is +1 exactly when the constraint holds — in the
-- sign group, "equal" and "product is the unit" are the same predicate,
-- so no extra machinery is needed to say what the oracle returns.
------------------------------------------------------------------------

data Query : Type where
  value : Number → Query
  fequ  : Number → Number → Query

ans : Signs → Query → Bool
ans σ (value n)  = val σ n
ans σ (fequ m n) = val σ (m ++ n) · (val σ m · val σ n)

obsQ : Signs → List Query → List Bool
obsQ σ qs = map (ans σ) qs

------------------------------------------------------------------------
-- §3  The functional-equation interface is constant.
--
-- Every FE query returns `true` on every completely multiplicative ±1
-- function, at every pair of arguments.  So the FE oracle is not merely
-- parity-blind: it is blind to EVERYTHING, distinguishing no two members
-- of the class at all.  This is the strongest possible failure of
-- the predicted identification — the FE side of BARRIER's
-- distinction is not the charged side, it is a degenerate sub-case of the
-- neutral side.
------------------------------------------------------------------------

fe-const : (σ : Signs) (m n : Number) → ans σ (fequ m n) ≡ true
fe-const σ m n =
    cong (λ z → z · (val σ m · val σ n)) (val-++ σ m n)
  ∙ ·-idem (val σ m · val σ n)

-- …and therefore the FE interface has an exact simulator that makes no
-- query whatsoever.  This is the direct refutation of BARRIER Problem 1 /
-- TARGET W3 *on the parity axis*: not only does value-query
-- post-processing simulate FE queries, the EMPTY query set does.
fe-simulated-by-constant :
    (σ : Signs) (m n : Number) → ans σ (fequ m n) ≡ (λ (_ : List Bool) → true) []
fe-simulated-by-constant = fe-const

------------------------------------------------------------------------
-- §4  Charge of a query, and the transcript collision.
--
-- The charge of a value query is the charge of its argument, exactly as
-- in `ChargeCriterion`.  The charge of an FE query is zero — with no
-- hypothesis on its arguments.  `Neutral (fequ m n) = Unit` is the whole
-- finding, compressed into a definition that §3 justifies.
------------------------------------------------------------------------

Neutral : Query → Type
Neutral (value n)  = sgn (Ω n) ≡ true
Neutral (fequ _ _) = Unit

AllNeutral : List Query → Type
AllNeutral []       = Unit
AllNeutral (q ∷ qs) = Neutral q × AllNeutral qs

ans-agree : (σ : Signs) (q : Query) → Neutral q → ans σ q ≡ ans (flip σ) q
ans-agree σ (value n)  e  = sym (neutral-blind σ n e)
ans-agree σ (fequ m n) tt = fe-const σ m n ∙ sym (fe-const (flip σ) m n)

obsQ-agree : (σ : Signs) (qs : List Query) → AllNeutral qs
           → obsQ σ qs ≡ obsQ (flip σ) qs
obsQ-agree σ []       tt         = refl
obsQ-agree σ (q ∷ qs) (e , rest) =
  cong₂ _∷_ (ans-agree σ q e) (obsQ-agree σ qs rest)

SeparatesQ : List Query → Type
SeparatesQ qs =
  Σ[ decide ∈ (List Bool → Bool) ]
    ((decide (obsQ σ₊ qs) ≡ true) × (decide (obsQ (flip σ₊) qs) ≡ false))

neutralQ⇒no-separator : (qs : List Query) → AllNeutral qs → ¬ (SeparatesQ qs)
neutralQ⇒no-separator qs all (decide , yes , no) =
  true≢false (sym yes ∙ cong decide (obsQ-agree σ₊ qs all) ∙ no)

------------------------------------------------------------------------
-- §5  An all-FE query set is blind, at arbitrarily charged arguments.
------------------------------------------------------------------------

FEonly : List Query → Type
FEonly []                = Unit
FEonly (value _   ∷ _)   = ⊥
FEonly (fequ  _ _ ∷ qs)  = FEonly qs

FEonly⇒AllNeutral : (qs : List Query) → FEonly qs → AllNeutral qs
FEonly⇒AllNeutral []               tt = tt
FEonly⇒AllNeutral (fequ m n ∷ qs)  f  = tt , FEonly⇒AllNeutral qs f

fe-blind : (qs : List Query) → FEonly qs → ¬ (SeparatesQ qs)
fe-blind qs f = neutralQ⇒no-separator qs (FEonly⇒AllNeutral qs f)

------------------------------------------------------------------------
-- §6  THE FINDING, as one pair of terms.
--
-- Let p be a prime: Ω(p) = 1, the maximal charge a query can carry.
-- Read as a VALUE, p separates.  Read through the FUNCTIONAL EQUATION —
-- the same p, twice over, plus a second FE query mentioning it again —
-- it does not.  Same argument, opposite verdicts.
--
-- So the value/FE axis of BARRIER §3(2) is NOT the odd-Ω/even-Ω axis of
-- `charge-criterion`.  It is orthogonal to it, and one of its two sides
-- is entirely contained in the blind half.
------------------------------------------------------------------------

p : Number
p = 0 ∷ []                       -- one prime; Ω = 1; sgn (Ω p) = false

read-p : List Query
read-p = value p ∷ []

fe-at-p : List Query
fe-at-p = fequ p p ∷ fequ p [] ∷ []

read-p-separates : SeparatesQ read-p
read-p-separates = hd , val-σ₊ p , val-σ₋ p

fe-at-p-cannot : ¬ (SeparatesQ fe-at-p)
fe-at-p-cannot = fe-blind fe-at-p tt

p-two-ways : SeparatesQ read-p × (¬ (SeparatesQ fe-at-p))
p-two-ways = read-p-separates , fe-at-p-cannot

-- And FE queries do not even help a neutral value query along: a mixed
-- transcript of one neutral value reading and two charged-argument FE
-- readings is still blind.
mixed : List Query
mixed = value (p ++ p) ∷ fequ p p ∷ fequ p (p ++ p) ∷ []

mixed-cannot : ¬ (SeparatesQ mixed)
mixed-cannot = neutralQ⇒no-separator mixed (refl , tt , tt , tt)

------------------------------------------------------------------------
-- §7  The conservation law: why §6 is structural and not a trick.
--
-- The objection to §6 is that an FE query is a bad model of "using the
-- functional equation": one does not ASK whether a(mn) = a(m)a(n), one
-- USES it to deduce new values from old.  So model that instead.
--
-- `Gen S` is the deductive closure of a set S of known arguments under
-- everything the functional equation licenses in the sign group:
-- multiply two known arguments, or divide a known argument by a known
-- divisor.  `Gen-sound` checks this really is a closure — two sign
-- assignments agreeing on S agree on all of `Gen S`, so the values there
-- are genuinely determined and nothing is being assumed.
--
-- `Gen-neutral` is then the conservation law: the closure of a neutral
-- set is neutral.  Charge cannot be manufactured by inference, only read.
-- The proof is that χ is a character (§1) and its kernel is a subgroup.
------------------------------------------------------------------------

data Gen (S : Number → Type) : Number → Type where
  gen : {n : Number}   → S n                        → Gen S n
  mul : {m n : Number} → Gen S m → Gen S n          → Gen S (m ++ n)
  quo : {m n : Number} → Gen S m → Gen S (m ++ n)   → Gen S n

-- a(n) = a(m)·a(mn): the division rule, as an identity.
recover : (σ : Signs) (m n : Number) → val σ m · val σ (m ++ n) ≡ val σ n
recover σ m n =
    cong (λ z → val σ m · z) (val-++ σ m n)
  ∙ sym (·-assoc (val σ m) (val σ m) (val σ n))
  ∙ cong (λ z → z · val σ n) (·-idem (val σ m))

Gen-sound : (S : Number → Type) (σ τ : Signs)
          → ((k : Number) → S k → val σ k ≡ val τ k)
          → (k : Number) → Gen S k → val σ k ≡ val τ k
Gen-sound S σ τ h k (gen s) = h k s
Gen-sound S σ τ h _ (mul {m} {n} gm gn) =
    val-++ σ m n
  ∙ cong₂ _·_ (Gen-sound S σ τ h m gm) (Gen-sound S σ τ h n gn)
  ∙ sym (val-++ τ m n)
Gen-sound S σ τ h n (quo {m} gm gmn) =
    sym (recover σ m n)
  ∙ cong₂ _·_ (Gen-sound S σ τ h m gm) (Gen-sound S σ τ h (m ++ n) gmn)
  ∙ recover τ m n

NeutralSet : (Number → Type) → Type
NeutralSet S = (k : Number) → S k → sgn (Ω k) ≡ true

-- CONSERVATION.  Functional-equation inference is charge-preserving.
Gen-neutral : (S : Number → Type) → NeutralSet S → NeutralSet (Gen S)
Gen-neutral S hS k (gen s) = hS k s
Gen-neutral S hS _ (mul {m} {n} gm gn) =
    charge-++ m n
  ∙ cong₂ _·_ (Gen-neutral S hS m gm) (Gen-neutral S hS n gn)
Gen-neutral S hS n (quo {m} gm gmn) =
  ·-cancel (Gen-neutral S hS m gm)
           (sym (charge-++ m n) ∙ Gen-neutral S hS (m ++ n) gmn)

------------------------------------------------------------------------
-- §8  …hence FE inference on a neutral basis still cannot separate.
--
-- Joining §7 back to `ChargeCriterion`: a method that starts from neutral
-- readings and closes them under the functional equation ends with a
-- neutral query set, so `neutral⇒no-separator` applies unchanged.  The
-- barrier is not merely unbroken by functional-equation access; it is
-- untouched by it.
------------------------------------------------------------------------

AllGen : (Number → Type) → List Number → Type
AllGen S []       = Unit
AllGen S (n ∷ qs) = Gen S n × AllGen S qs

AllGen⇒AllEven : (S : Number → Type) → NeutralSet S
               → (qs : List Number) → AllGen S qs → AllEven qs
AllGen⇒AllEven S hS []       tt         = tt
AllGen⇒AllEven S hS (n ∷ qs) (g , rest) =
  Gen-neutral S hS n g , AllGen⇒AllEven S hS qs rest

closure-no-separator : (S : Number → Type) → NeutralSet S
                     → (qs : List Number) → AllGen S qs → ¬ (Separates qs)
closure-no-separator S hS qs ag =
  neutral⇒no-separator qs (AllGen⇒AllEven S hS qs ag)

-- The contrast that keeps §8 from being vacuous: a CHARGED basis of course
-- separates, and it does so through its value, not through the closure —
-- one reading at p, no inference at all.
charged-basis-separates : Separates (p ∷ [])
charged-basis-separates = odd⇒separator (p ∷ []) (inl refl)
