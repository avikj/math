{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.InterfaceSeparation
--
-- W3 of `TARGET.md` (absent from this repository) §2 = `notes/BARRIER.md` (absent from this repository) §2's closing demand:
--
--     "a proof that no WL post-processing Φ can simulate that interface
--      — i.e., a separation, not just a classification."
--
-- The interface in question is `BARRIER.md` (absent from this repository)'s third presentation:
-- FUNCTIONAL-EQUATION ACCESS, "a(np) = a(n)a(p) used as a *constraint*,
-- not a value", which is the interface Tao's entropy decrement consumes
-- and which the windowed-linear class WL declines by construction —
-- WL "treats a as a black-box sequence".
--
-- THE ANSWER IS A DICHOTOMY, AND THE DICHOTOMY IS THE RESULT.  W3 is not
-- one question.  It is two, with OPPOSITE answers, and which one you are
-- asking is fixed by a single modelling choice that `BARRIER.md` (absent from this repository) makes
-- silently:
--
--   * PROMISED MODEL — the hidden object is a completely multiplicative
--     ±1 function (a sign assignment on the primes; `ParitySeparator`'s
--     `Signs`).  Then **W3 IS FALSE**: functional-equation access is
--     exactly simulated by post-processing of value queries, and the
--     simulator is CONSTRUCTED here (`compile`, `derived-simulated`).
--     The functional equation is an identity on this class, so an
--     FE CHECK carries zero bits (`fe-promised-constant`), and an
--     FE REWRITE — deriving a(mn) from a(m), a(n) — is a computation on
--     the transcript and nothing more.  Whatever entropy decrement's
--     advantage over WL is, it is NOT that it queries a channel the
--     value oracle lacks.
--
--   * UNPROMISED MODEL — the hidden object is an arbitrary ±1 sequence,
--     which is what "black-box sequence" literally says.  Then **W3 IS
--     TRUE**, and provably so at the smallest nontrivial scale: no
--     post-processing of ANY value-query set that misses the product
--     point determines even one FE bit (`value-cannot-simulate-fe`),
--     however many queries it makes and however non-computable the
--     post-processing is.  Three value queries AT the right points do
--     simulate it (`fe-simulated-when-product-queried`).
--
-- So the content of the functional-equation interface is exactly THE
-- PROMISE (`fe-content-is-the-promise`): it is nonconstant on sequences
-- and constant on multiplicative ones.  A separation theorem for it is
-- available, but it separates "may I assume multiplicativity?" from
-- "must I verify it?", not "value channel" from "constraint channel".
--
-- WHY THIS IS NOT A MODEL CHOSEN TO MAKE A THEOREM EASY.  Both models
-- are formalised here and both theorems are proved; neither is assumed.
-- The hostile reader's move is named in `notes/INTERFACE_SEPARATION.md` (absent from this repository)
-- §6 and it is the right one: attack the claim that a finite-query
-- oracle model is the right home for entropy decrement at all, since
-- that argument's actual input is an AVERAGED statement over all n at
-- once.  This module proves what a query model can decide and says so.
--
-- WHAT IS NEW HERE relative to the two modules it builds on.
-- `ParitySeparator` proves neutral observers cannot separate
-- σ from its gauge flip; `ChargeCriterion` upgrades that to
-- an iff on the query set.  Both fix the interface and vary the object.
-- This module fixes the object and VARIES THE INTERFACE, which is what
-- an oracle separation is, and adds the one arithmetic corollary that
-- matters to the barrier program:
--
--     `fe-closure-cannot-separate` — closing a parity-neutral query set
--     under the functional equation NEVER produces a charged query.
--
-- That is "no post-processing manufactures charge" upgraded from a slogan
-- to a structural induction over the syntax of derivations, in the same
-- shape as `NaturalMachine.FlipObservable`'s grammar-blindness theorem.
--
-- Contents (no holes, no postulates, --safe):
--
--   Simulates                     I simulates J iff some (arbitrary,
--                                 even non-computable) f post-processes
--                                 I's transcript into J's answer
--   collision⇒no-simulation       the only way to refute simulation:
--                                 one collision in I, split by J
--   val-++                        complete multiplicativity, as the
--                                 concatenation law on factor multisets
--   defect                        the functional-equation query, a(mn)·a(m)·a(n)
--   fe-promised-constant          it is ≡ true on every multiplicative a
--   fe-simulated-by-nothing       hence simulated by the EMPTY transcript
--   Deriv, target, post, compile  the FE-rewriting calculus, and its
--                                 compilation into post-processing
--   derived-simulated             ⇒ W3 refuted in the promised model
--   sgn-++, target-even           charge is F₂-linear along derivations
--   fe-closure-cannot-separate    ⇒ neutral stays neutral under FE closure
--   a₀, a₁, unpromised-agree      the constructed separating pair
--   value-cannot-simulate-fe      ⇒ W3 proved in the unpromised model
--   fe-simulated-when-product-queried
--                                 …and the exact converse: the obstruction
--                                 is SUPPORT, not power
--   fe-content-is-the-promise     the two halves in one statement
------------------------------------------------------------------------

module NaturalMachine.InterfaceSeparation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map ; _++_)
open import Cubical.Relation.Nullary using (¬_)

open import NaturalMachine.ParitySeparator
open import NaturalMachine.ChargeCriterion using (Separates ; neutral⇒no-separator)

------------------------------------------------------------------------
-- §0  What an oracle separation IS, once post-processing is arbitrary.
--
-- An interface on a hidden object of type O is a map O → A: the whole
-- transcript it produces.  Post-processing is any function A → B, with
-- no computability, continuity or measurability demanded — this is
-- `BARRIER.md` (absent from this repository) Proposition B3's "arbitrary, even non-computable Φ",
-- taken literally, and it is the strongest form of the hypothesis.
--
-- Hence simulation is not a complexity statement; it is a statement
-- about PARTITIONS.  I simulates J exactly when I's transcript refines
-- J's, and the only way to refute it is to exhibit a COLLISION of I
-- that J splits.  Because the object space here is free — arbitrary
-- sign assignments on the primes, `TARGET.md` (absent from this repository) §3's whole reason to
-- attack parity rather than ζ — collisions can be constructed, not
-- hunted for.  That is the diagonalisation, and §4 performs it.
------------------------------------------------------------------------

Simulates : {O A B : Type} → (O → A) → (O → B) → Type
Simulates {O} {A} {B} I J = Σ[ f ∈ (A → B) ] ((o : O) → f (I o) ≡ J o)

collision⇒no-simulation :
    {O A B : Type} (I : O → A) (J : O → B) (o₁ o₂ : O)
  → I o₁ ≡ I o₂ → ¬ (J o₁ ≡ J o₂) → ¬ (Simulates I J)
collision⇒no-simulation I J o₁ o₂ same split (f , correct) =
  split (sym (correct o₁) ∙ cong f same ∙ correct o₂)

-- Trivially, an interface simulates itself; recorded so that "simulates"
-- is visibly a preorder and not a hedge.
self-simulates : {O A : Type} (I : O → A) → Simulates I I
self-simulates I = (λ a → a) , λ _ → refl

------------------------------------------------------------------------
-- §1  Sequences, and the functional-equation query.
--
-- A number is its multiset of prime factors (`ParitySeparator.Number` =
-- List ℕ), so MULTIPLICATION IS CONCATENATION and the functional
-- equation a(mn) = a(m)a(n) reads a(m ++ n) = a m · a n.  The FE query
-- is the DEFECT of that identity — the same triple (x, y, x+y) the
-- Blum–Luby–Rubinfeld linearity test reads, which is where a reader
-- should look for prior art on this interface (see the note, §5).
------------------------------------------------------------------------

Seq : Type
Seq = Number → Bool               -- an arbitrary ±1 sequence: NO promise

defect : Seq → Number → Number → Bool
defect a m n = a (m ++ n) · a m · a n

-- Complete multiplicativity of `val σ`, which is what makes `Signs` the
-- promised class: the value of a product is the product of the values.
val-++ : (σ : Signs) (m n : Number) → val σ (m ++ n) ≡ val σ m · val σ n
val-++ σ []       n = refl
val-++ σ (p ∷ ms) n =
    cong (λ z → σ p · z) (val-++ σ ms n)
  ∙ sym (·-assoc (σ p) (val σ ms) (val σ n))

-- FE DIVISION is FE multiplication here, and this is the lemma that says
-- so: recovering a(n) from a(mn) and a(m) is `mul`, because {±1} has
-- exponent two.  Stated because "your calculus only multiplies" is the
-- first objection to §3, and it is answered by the group, not by fiat.
·-cancel : (a b : Bool) → a · (a · b) ≡ b
·-cancel true  b     = refl
·-cancel false true  = refl
·-cancel false false = refl

cancel : (σ : Signs) (m n : Number) → val σ (m ++ (m ++ n)) ≡ val σ n
cancel σ m n =
    val-++ σ m (m ++ n)
  ∙ cong (λ z → val σ m · z) (val-++ σ m n)
  ∙ ·-cancel (val σ m) (val σ n)

------------------------------------------------------------------------
-- §2  PROMISED MODEL, first half: an FE CHECK carries zero bits.
--
-- On the promised class the functional equation is an identity, so its
-- defect is constantly +1 and the empty transcript simulates it.  This
-- is the trivial half and it is stated because it is the half a reader
-- of `BARRIER.md` (absent from this repository) §2 will assume away: the note's third presentation is
-- described as accessing "a(np) = a(n)a(p) … as a constraint", and a
-- constraint that always holds is not an access.
------------------------------------------------------------------------

-- (a·b)·a·b = 1 in the group {±1}: exponent two and abelian, four cases.
abab : (a b : Bool) → ((a · b) · a) · b ≡ true
abab true  true  = refl
abab true  false = refl
abab false true  = refl
abab false false = refl

fe-promised-constant : (σ : Signs) (m n : Number) → defect (val σ) m n ≡ true
fe-promised-constant σ m n =
    cong (λ z → z · val σ m · val σ n) (val-++ σ m n)
  ∙ abab (val σ m) (val σ n)

fe-simulated-by-nothing :
    (m n : Number)
  → Simulates {Signs} (λ _ → tt) (λ σ → defect (val σ) m n)
fe-simulated-by-nothing m n = (λ _ → true) , λ σ → sym (fe-promised-constant σ m n)

-- …and not just one instance.  The FULL functional-equation oracle —
-- answering every instance (m,n) simultaneously, an infinite object, no
-- query budget — is still simulated by the empty transcript.  This is
-- the statement that closes "you only modelled finitely many FE queries"
-- for the CHECK reading of the interface.
fe-oracle-simulated-by-nothing :
  Simulates {Signs} (λ _ → tt) (λ σ → λ (m n : Number) → defect (val σ) m n)
fe-oracle-simulated-by-nothing =
    (λ _ _ _ → true)
  , λ σ → funExt (λ m → funExt (λ n → sym (fe-promised-constant σ m n)))

------------------------------------------------------------------------
-- §3  PROMISED MODEL, second half: FE REWRITING IS POST-PROCESSING.
--
-- This is the half that decides W3, and the trivial reading of §2 does
-- not settle it.  The substantive use of the functional equation is not
-- to CHECK it but to REWRITE with it: to obtain a(mn) from a(m) and
-- a(n) — which is exactly how entropy decrement moves information from
-- a scale to a dilate of that scale, and exactly what the windowed class
-- cannot do, since a window [1,X] is not closed under multiplication.
--
-- The theorem is that this buys nothing over the value queries already
-- made.  `Deriv` is the syntax of FE rewriting: a query already asked
-- (`var i`), the empty product (`unit`), or the product of two
-- derivations (`mul`).  `target` says which number a derivation names;
-- `post` is the post-processing that computes its value FROM THE
-- TRANSCRIPT ALONE, by structural recursion on the same syntax; and
-- `compile` proves them equal for every σ.
--
-- So every value the FE interface can derive is a function of the value
-- transcript.  `derived-simulated` states that as a simulation.  W3 is
-- FALSE in the promised model, and not narrowly: the simulator is
-- explicit, total, and computes.
------------------------------------------------------------------------

data Deriv : Type where
  var  : ℕ → Deriv
  unit : Deriv
  mul  : Deriv → Deriv → Deriv

-- Safe lookups.  The defaults are chosen to agree: out of range, the
-- named number is the empty product and the recorded answer is its
-- value, +1.  Nothing below depends on that choice being meaningful —
-- it only has to be consistent, which is what keeps `compile` total.
nthQ : ℕ → List Number → Number
nthQ _       []       = []
nthQ zero    (q ∷ _)  = q
nthQ (suc i) (_ ∷ qs) = nthQ i qs

nthB : ℕ → List Bool → Bool
nthB _       []       = true
nthB zero    (b ∷ _)  = b
nthB (suc i) (_ ∷ bs) = nthB i bs

target : List Number → Deriv → Number
target qs (var i)   = nthQ i qs
target qs unit      = []
target qs (mul d e) = target qs d ++ target qs e

post : Deriv → List Bool → Bool
post (var i)   bs = nthB i bs
post unit      bs = true
post (mul d e) bs = post d bs · post e bs

nth-obs : (σ : Signs) (i : ℕ) (qs : List Number)
        → nthB i (obs σ qs) ≡ val σ (nthQ i qs)
nth-obs σ i       []       = refl
nth-obs σ zero    (q ∷ qs) = refl
nth-obs σ (suc i) (q ∷ qs) = nth-obs σ i qs

compile : (σ : Signs) (qs : List Number) (d : Deriv)
        → post d (obs σ qs) ≡ val σ (target qs d)
compile σ qs (var i)   = nth-obs σ i qs
compile σ qs unit      = refl
compile σ qs (mul d e) =
    cong₂ _·_ (compile σ qs d) (compile σ qs e)
  ∙ sym (val-++ σ (target qs d) (target qs e))

-- W3, refuted in the promised model.
derived-simulated :
    (qs : List Number) (d : Deriv)
  → Simulates (λ σ → obs σ qs) (λ σ → val σ (target qs d))
derived-simulated qs d = post d , λ σ → compile σ qs d

-- Again the unbudgeted form: the whole FE-REWRITING oracle, answering
-- every derivation at once, is a single post-processing of the value
-- transcript.  Together with `fe-oracle-simulated-by-nothing` this is
-- the refutation of W3 in the promised model in its strongest available
-- form — no finiteness, no computability, no budget anywhere.
derived-oracle-simulated :
    (qs : List Number)
  → Simulates (λ σ → obs σ qs) (λ σ → λ (d : Deriv) → val σ (target qs d))
derived-oracle-simulated qs =
  (λ bs d → post d bs) , λ σ → funExt (λ d → compile σ qs d)

------------------------------------------------------------------------
-- §4  The arithmetic corollary: FE closure never manufactures charge.
--
-- `ChargeCriterion` says a query set separates the reference pair iff it
-- contains an odd-Ω query.  Ω mod 2 is additive along products — that is
-- `sgn-++`, and it is the whole reason the parity character is a
-- character — so a derivation from even-Ω queries has even-Ω target.
-- Therefore the FE closure of a parity-neutral query set is parity-
-- neutral, and by `ChargeCriterion.neutral⇒no-separator` still admits no
-- separator at all.
--
-- This is the sharp form of `TARGET.md` (absent from this repository) §4b's asymmetry ("charge lives
-- in what a method reads, and no amount of computation on neutral
-- readings manufactures it"): the functional equation is a computation
-- on neutral readings, and it is now proved not to manufacture charge.
------------------------------------------------------------------------

not-·ʳ : (a b : Bool) → not (a · b) ≡ (not a) · b
not-·ʳ true  b     = refl
not-·ʳ false true  = refl
not-·ʳ false false = refl

sgn-++ : (m n : Number) → sgn (Ω (m ++ n)) ≡ sgn (Ω m) · sgn (Ω n)
sgn-++ []       n = refl
sgn-++ (p ∷ ms) n = cong not (sgn-++ ms n) ∙ not-·ʳ (sgn (Ω ms)) (sgn (Ω n))

nthQ-even : (i : ℕ) (qs : List Number) → AllEven qs → sgn (Ω (nthQ i qs)) ≡ true
nthQ-even i       []       tt        = refl
nthQ-even zero    (q ∷ qs) (e , _)   = e
nthQ-even (suc i) (q ∷ qs) (_ , rest) = nthQ-even i qs rest

target-even : (qs : List Number) → AllEven qs → (d : Deriv)
            → sgn (Ω (target qs d)) ≡ true
target-even qs all (var i)   = nthQ-even i qs all
target-even qs all unit      = refl
target-even qs all (mul d e) =
    sgn-++ (target qs d) (target qs e)
  ∙ cong₂ _·_ (target-even qs all d) (target-even qs all e)

derived-AllEven : (qs : List Number) → AllEven qs → (ds : List Deriv)
                → AllEven (map (target qs) ds)
derived-AllEven qs all []       = tt
derived-AllEven qs all (d ∷ ds) = target-even qs all d , derived-AllEven qs all ds

-- No functional-equation closure of a neutral query set separates.
fe-closure-cannot-separate :
    (qs : List Number) → AllEven qs → (ds : List Deriv)
  → ¬ (Separates (map (target qs) ds))
fe-closure-cannot-separate qs all ds =
  neutral⇒no-separator (map (target qs) ds) (derived-AllEven qs all ds)

------------------------------------------------------------------------
-- §5  UNPROMISED MODEL: the separation, proved by construction.
--
-- Drop the promise — take the hidden object to be an arbitrary ±1
-- sequence, which is what `BARRIER.md` (absent from this repository)'s "black-box sequence" says
-- verbatim — and the FE query stops being an identity.  Now it is one
-- honest bit, and the value interface cannot get it unless it reads the
-- product point.
--
-- The separating pair is CONSTRUCTED, not found: `a₀` is constantly +1,
-- `a₁` is +1 except at arguments with exactly two prime factors.  They
-- agree on every query of Ω ≠ 2 — an unbounded set, containing every
-- prime, every prime power of odd exponent, every window [1,X] read
-- through Ω-graded probes — and disagree on the single FE instance
-- (p, q).  This is `TARGET.md` (absent from this repository) §3's point cashed: the object space is
-- free, so the diagonalisation that is unavailable against ζ is
-- available here.
------------------------------------------------------------------------

a₀ : Seq
a₀ _ = true

-- +1 unless the argument has exactly two prime factors.
isNot2 : ℕ → Bool
isNot2 zero                = true
isNot2 (suc zero)          = true
isNot2 (suc (suc zero))    = false
isNot2 (suc (suc (suc k))) = true

a₁ : Seq
a₁ n = isNot2 (Ω n)

obsS : Seq → List Number → List Bool
obsS a qs = map a qs

-- "the value-query set never reads a product of exactly two primes".
AvoidsTwo : List Number → Type
AvoidsTwo []       = Unit
AvoidsTwo (n ∷ qs) = (isNot2 (Ω n) ≡ true) × AvoidsTwo qs

unpromised-agree : (qs : List Number) → AvoidsTwo qs → obsS a₀ qs ≡ obsS a₁ qs
unpromised-agree []       tt         = refl
unpromised-agree (n ∷ qs) (e , rest) =
  cong₂ _∷_ (sym e) (unpromised-agree qs rest)

-- The FE instance: two distinct primes, indices 0 and 1.
p₀ p₁ : Number
p₀ = 0 ∷ []
p₁ = 1 ∷ []

defect-a₀ : defect a₀ p₀ p₁ ≡ true
defect-a₀ = refl

defect-a₁ : defect a₁ p₀ p₁ ≡ false
defect-a₁ = refl

-- W3, PROVED in the unpromised model: for EVERY value-query set that
-- misses the product point, and EVERY post-processing whatsoever, the
-- functional-equation bit is not recoverable.
value-cannot-simulate-fe :
    (qs : List Number) → AvoidsTwo qs
  → ¬ (Simulates (λ a → obsS a qs) (λ a → defect a p₀ p₁))
value-cannot-simulate-fe qs av =
  collision⇒no-simulation (λ a → obsS a qs) (λ a → defect a p₀ p₁) a₀ a₁
    (unpromised-agree qs av)
    (λ same → true≢false (sym defect-a₀ ∙ same ∙ defect-a₁))

-- The instance at the smallest nontrivial scale: read both primes, learn
-- nothing about their product.
two-primes-query : List Number
two-primes-query = p₀ ∷ p₁ ∷ []

smallest-separation :
  ¬ (Simulates (λ a → obsS a two-primes-query) (λ a → defect a p₀ p₁))
smallest-separation = value-cannot-simulate-fe two-primes-query (refl , refl , tt)

------------------------------------------------------------------------
-- §6  …and the exact converse, which is what makes §5 a SUPPORT
--     condition rather than a power gap.
--
-- Three value queries — at mn, at m, at n — simulate the FE query
-- exactly, with the post-processing being the same product.  So the
-- interfaces are not separated by strength: they are separated by WHICH
-- ARGUMENTS THEY TOUCH.  That is the same verdict `ChargeCriterion`
-- reached from the other side ("about the QUERY SET and not the
-- post-processing"), reached here against a different adversary, and it
-- is the reason the arithmetic reading in the note is about the window
-- failing to be multiplicatively closed and not about Φ being weak.
------------------------------------------------------------------------

fe-simulated-when-product-queried :
    (m n : Number)
  → Simulates (λ a → obsS a ((m ++ n) ∷ m ∷ n ∷ [])) (λ a → defect a m n)
fe-simulated-when-product-queried m n =
  (λ bs → nthB 0 bs · nthB 1 bs · nthB 2 bs) , λ a → refl

------------------------------------------------------------------------
-- §7  The dichotomy in one statement.
--
-- The functional-equation query is nonconstant on sequences and constant
-- on multiplicative ones.  Hence its entire information content is the
-- promise, and any separation theorem built on it separates hypotheses,
-- not channels.  This is the sentence the note argues `BARRIER.md` (absent from this repository) §2
-- should carry in place of "outside the interface of WL by construction".
------------------------------------------------------------------------

fe-content-is-the-promise :
    (Σ[ a ∈ Seq ] (¬ (defect a p₀ p₁ ≡ true)))
  × ((σ : Signs) → defect (val σ) p₀ p₁ ≡ true)
fe-content-is-the-promise =
    (a₁ , λ q → true≢false (sym q ∙ defect-a₁))
  , λ σ → fe-promised-constant σ p₀ p₁

-- Corollary worth naming: `a₁` is not the value function of ANY sign
-- assignment.  The separating adversary of §5 is genuinely outside the
-- promised class — which is not a defect of the construction, it is the
-- theorem.
a₁-not-multiplicative : (σ : Signs) → ¬ ((n : Number) → a₁ n ≡ val σ n)
a₁-not-multiplicative σ h =
  true≢false (sym (fe-promised-constant σ p₀ p₁)
             ∙ sym (cong (λ a → defect a p₀ p₁) (funExt h))
             ∙ defect-a₁)
