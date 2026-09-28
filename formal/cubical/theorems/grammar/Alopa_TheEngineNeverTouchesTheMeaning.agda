{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अलोपः — यन्त्रम् अर्थं न स्पृशति ।
--
-- (nothing dropped: the engine never touches the meaning.)
--
-- THE JOIN.  `Calana_TheRunAndTheInvariantForAllN` proves शेषः invariant
-- under the whole run — for EVERY n, by structural recursion, nothing
-- sampled:
--
--     अलोपः : (n : ℕ) (v : विवेक) → शेषः (क्रम n (बुन v)) ≡ शेषः v
--
-- `interactive/MathMachine.hs` (absent from this repository) makes a claim of the same shape and has no
-- such theorem.  Its round installs proved equations as rewrite rules and
-- re-normalises its whole term space with them; its entire argument for
-- why that is safe is per-rule — each rule passed a kernel.  Nothing says
-- the RUN preserves anything.  §4 says it, in अलोपः's form.
--
-- AND IT REMOVES THE SAMPLING.  The engine's conjecture step is "these
-- two terms agreed on forty random assignments, so guess they are equal".
-- That step is answering a question normalisation answers exactly.
--
--   §5  two terms with the same normal form are equal under EVERY
--       environment.  No environment is inspected in the proof.
--   §6  a single disagreeing assignment refutes.  One point is enough,
--       and one point is all it can ever do.
--   §7  and the sampler cannot be fixed by sampling more: `var 0` and
--       `var 1` agree on every CONSTANT environment — infinitely many
--       samples, all confirming — and they are not equal.  What a sample
--       confirms is a property of the distribution it was drawn from.
--
-- THE FIELD IS THE OWNER'S MOVE.  `VivekaPramana_TheUpadhiIsCarriedAsA
-- Field` carries the defeating condition as a field instead of asserting
-- an equivalence that is false; the third pass sharpens the field to
-- प्रमाण : दक्षिण ≡ सम + वाम, which makes the record the graph of + and
-- the equivalence contentful.  `Rule` below is that move applied to the
-- engine: a rewrite rule is not two terms with a certificate recorded in
-- a log elsewhere, it is two terms CARRYING their certificate as a
-- field.  Soundness of the run then is not an audit; it falls out of the
-- type.
------------------------------------------------------------------------

module Alopa_TheEngineNeverTouchesTheMeaning where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; znots)
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

private
  Code : Bool → Type₀
  Code true  = ⊥
  Code false = Unit

  ¬false≡true : ¬ (false ≡ true)
  ¬false≡true p = subst Code p tt

--------------------------------------------------------------------------
-- 1.  Terms, environments, meaning
--------------------------------------------------------------------------

data Term : Type₀ where
  var : ℕ → Term
  op  : Term → Term → Term

Env : Type₀
Env = ℕ → ℕ

eval : Env → Term → ℕ
eval ρ (var i)  = ρ i
eval ρ (op a b) = eval ρ a + eval ρ b

--------------------------------------------------------------------------
-- 2.  A rule carries its certificate.  उपाधिः क्षेत्रम् एव.
--------------------------------------------------------------------------

record Rule : Type₀ where
  constructor rule
  field
    lhs rhs : Term
    प्रमाण   : (ρ : Env) → eval ρ lhs ≡ eval ρ rhs

open Rule public

--------------------------------------------------------------------------
-- 3.  Structural equality, sound by construction
--------------------------------------------------------------------------

eqℕ : ℕ → ℕ → Bool
eqℕ zero zero       = true
eqℕ zero (suc _)    = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

eqℕ-sound : (m n : ℕ) → eqℕ m n ≡ true → m ≡ n
eqℕ-sound zero zero _ = refl
eqℕ-sound zero (suc _) p = ⊥.rec (¬false≡true p)
eqℕ-sound (suc _) zero p = ⊥.rec (¬false≡true p)
eqℕ-sound (suc m) (suc n) p = cong suc (eqℕ-sound m n p)

and-true : (x y : Bool) → x and y ≡ true → (x ≡ true) × (y ≡ true)
and-true true true _ = refl , refl
and-true true false p = ⊥.rec (¬false≡true p)
and-true false _ p = ⊥.rec (¬false≡true p)

eqT : Term → Term → Bool
eqT (var i) (var j)   = eqℕ i j
eqT (op a b) (op c d) = eqT a c and eqT b d
eqT (var _) (op _ _)  = false
eqT (op _ _) (var _)  = false

eqT-sound : (s t : Term) → eqT s t ≡ true → s ≡ t
eqT-sound (var i) (var j) p = cong var (eqℕ-sound i j p)
eqT-sound (op a b) (op c d) p =
  cong₂ op (eqT-sound a c (fst q)) (eqT-sound b d (snd q))
  where q = and-true (eqT a c) (eqT b d) p
eqT-sound (var _) (op _ _) p = ⊥.rec (¬false≡true p)
eqT-sound (op _ _) (var _) p = ⊥.rec (¬false≡true p)

--------------------------------------------------------------------------
-- 4.  The run
--------------------------------------------------------------------------

pick : Bool → Rule → List Rule → Term → Term
fire : List Rule → Term → Term

pick true  r _    _ = rhs r
pick false _ rest t = fire rest t

fire []          t = t
fire (r ∷ rest)  t = pick (eqT t (lhs r)) r rest t

step : List Rule → Term → Term
step rs (var i)  = fire rs (var i)
step rs (op a b) = fire rs (op (step rs a) (step rs b))

normalize : ℕ → List Rule → Term → Term
normalize zero    _  t = t
normalize (suc n) rs t = normalize n rs (step rs t)

--------------------------------------------------------------------------
-- 5.  अलोपः : for every n, the run leaves every meaning where it was
--------------------------------------------------------------------------

pick-sound : (b : Bool) (r : Rule) (rest : List Rule) (ρ : Env) (t : Term)
           → (b ≡ true → t ≡ lhs r)
           → eval ρ (pick b r rest t) ≡ eval ρ t
fire-sound : (rs : List Rule) (ρ : Env) (t : Term)
           → eval ρ (fire rs t) ≡ eval ρ t

pick-sound true r rest ρ t h =
  sym (प्रमाण r ρ) ∙ cong (eval ρ) (sym (h refl))
pick-sound false _ rest ρ t _ = fire-sound rest ρ t

fire-sound [] ρ t = refl
fire-sound (r ∷ rest) ρ t =
  pick-sound (eqT t (lhs r)) r rest ρ t (eqT-sound t (lhs r))

step-sound : (rs : List Rule) (ρ : Env) (t : Term)
           → eval ρ (step rs t) ≡ eval ρ t
step-sound rs ρ (var i) = fire-sound rs ρ (var i)
step-sound rs ρ (op a b) =
    fire-sound rs ρ (op (step rs a) (step rs b))
  ∙ cong₂ _+_ (step-sound rs ρ a) (step-sound rs ρ b)

अलोपः : (n : ℕ) (rs : List Rule) (ρ : Env) (t : Term)
      → eval ρ (normalize n rs t) ≡ eval ρ t
अलोपः zero    _  _ _ = refl
अलोपः (suc n) rs ρ t = अलोपः n rs ρ (step rs t) ∙ step-sound rs ρ t

--------------------------------------------------------------------------
-- 6.  What the sampler was for, done exactly
--------------------------------------------------------------------------

-- Same normal form ⟹ equal under EVERY environment.  Nothing is sampled;
-- no environment appears in the proof except the one being asked about.
same-normal-form→equal :
    (n : ℕ) (rs : List Rule) (s t : Term)
  → normalize n rs s ≡ normalize n rs t
  → (ρ : Env) → eval ρ s ≡ eval ρ t
same-normal-form→equal n rs s t p ρ =
  sym (अलोपः n rs ρ s) ∙ cong (eval ρ) p ∙ अलोपः n rs ρ t

--------------------------------------------------------------------------
-- 7.  And the other direction is where a sample belongs
--------------------------------------------------------------------------

-- one disagreeing assignment kills the claim outright
one-witness-refutes :
    (s t : Term) (ρ : Env)
  → ¬ (eval ρ s ≡ eval ρ t)
  → ¬ ((σ : Env) → eval σ s ≡ eval σ t)
one-witness-refutes s t ρ h k = h (k ρ)

--------------------------------------------------------------------------
-- 8.  Why more samples do not help: the confirmation is about the draw
--------------------------------------------------------------------------

constEnv : ℕ → Env
constEnv c _ = c

-- infinitely many samples, every one of them agreeing …
agree-on-every-constant-environment :
    (c : ℕ) → eval (constEnv c) (var 0) ≡ eval (constEnv c) (var 1)
agree-on-every-constant-environment _ = refl

-- … and the two terms are not equal.
not-equal : ¬ ((σ : Env) → eval σ (var 0) ≡ eval σ (var 1))
not-equal k = znots (k (λ i → i))

-- So a confirmation from sampling is a statement about the distribution
-- the samples came from, never about the terms.  Forty is not the
-- problem, and four hundred would not be either.
sampling-confirms-the-draw-not-the-terms :
    ((c : ℕ) → eval (constEnv c) (var 0) ≡ eval (constEnv c) (var 1))
  × (¬ ((σ : Env) → eval σ (var 0) ≡ eval σ (var 1)))
sampling-confirms-the-draw-not-the-terms =
  agree-on-every-constant-environment , not-equal
