{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FiniteWorldMaximizer
--
-- NONVANISHING HYPOTHESIS MADE PART OF THE TYPE.
--
--   **Theorem.** For every integral polynomial `f`, every finite `E`
--   with `f != 0` on `E` has a point that fails to transport: any point
--   maximizing `v_p(f)`.
--
-- A summary
-- restates it as "For **every** integral polynomial, every finite `E`
-- has a point that cannot transport — any maximizer of `v_p(f)`",
-- dropping the clause "with `f != 0` on `E`".  Like §C2 (instrumented
-- by `LineWorldTransport` / `Control/QuantifierDrop`) the drop has no
-- lexical signature: the shortened sentence contains no wrong word,
-- only a missing clause.
--
-- WHAT KIND OF DEFECT THIS IS — stated because it differs from C2's and
-- the difference bounds what the instrument shows.  C2's dropped
-- hypothesis leaves a sentence that is FALSE.  C1's leaves one the
-- audit calls "not even well formed": with `f ≡ 0` on `E` every point
-- has `v_p(f) = ∞`, so "any maximizer of `v_p(f)`" — the message's
-- entire proof — denotes nothing.  Ill-formedness is not directly a
-- type-checkable falsehood, so it is TRANSLATED here, by one modelling
-- decision that must be stated openly: `MaxAt W m` requires the
-- maximizer `m` to be a point where the observable does not vanish
-- (`IsFin (W m)`), which is what "the point maximizing `v_p(f)`" has to
-- mean if it means anything.  Under that reading the dropped-clause
-- statement becomes false — `vanishing-world` has no maximizer at all —
-- and `dropped-hypothesis-false` proves it.  A reader who rejects that
-- reading is left with the weaker but still true claim that the term
-- cannot be built; the control below exhibits both, since Agda's error
-- is a MISSING-ARGUMENT error naming the clause.
--
-- THIS IS A MODEL, NOT THE FULL SETTING.  Formalized here is the
-- smallest world that carries the distinction:
--
--   * `E` is a two-point set `Pt`; a world is a valuation
--     `W : Pt → Val` with `Val = fin ℕ ⊎ ∞`, where `∞` is `v_p(0)`,
--     the valuation at a point where `f` vanishes;
--   * `NonVanishing W` is the note's clause "`f != 0` on `E`", i.e.
--     every point has finite valuation;
--   * `maximizer` produces, from a world AND that certificate, a point
--     together with a proof that no point of `E` exceeds it — the
--     "point maximizing `v_p(f)`" the theorem's proof names.
--
-- Everything below is a closed computation or a two-case induction on
-- ℕ; there is no fitting and no sampling (CLAUDE.md (absent from this repository)).
-- It contains exactly the step the summary broke — that
-- the maximizer exists — and nothing else.
--
-- HEADLINE TERMS
--   maximizer               the theorem's witness, hypothesis in the type
--   vanishing-world         the world `f ≡ 0` on `E`
--   vanishing-has-no-certificate   it satisfies no nonvanishing hypothesis
--   vanishing-world-has-no-maximizer  and has no maximizer either
--   dropped-hypothesis-false        the clause-dropped reading implies ⊥
------------------------------------------------------------------------

module FiniteWorldMaximizer where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Bool.Properties using (true≢false)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)

------------------------------------------------------------------------
-- 0.  Order on ℕ, as a computed Bool, with the two facts needed.

le : ℕ → ℕ → Bool
le zero    _       = true
le (suc _) zero    = false
le (suc a) (suc b) = le a b

le-refl : (a : ℕ) → le a a ≡ true
le-refl zero    = refl
le-refl (suc a) = le-refl a

le-flip : (a b : ℕ) → le a b ≡ false → le b a ≡ true
le-flip zero    b       q = ⊥-rec (true≢false q)
le-flip (suc a) zero    _ = refl
le-flip (suc a) (suc b) q = le-flip a b q

dich : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
dich true  = inl refl
dich false = inr refl

------------------------------------------------------------------------
-- 1.  Worlds.  `E = {x₁,x₂}`; `Val` is ℕ ∪ {∞}, and `∞ = v_p(0)` is the
--     valuation at a point where the observable vanishes.

data Pt : Type where
  x₁ x₂ : Pt

data Val : Type where
  fin : ℕ → Val
  ∞   : Val

World : Type
World = Pt → Val

-- The note's clause "`f != 0` on `E`", pointwise.
IsFin : Val → Type
IsFin (fin _) = Unit
IsFin ∞       = ⊥

NonVanishing : World → Type
NonVanishing W = (q : Pt) → IsFin (W q)

-- The valuation as a number — available only where `f` does not vanish.
num : (v : Val) → IsFin v → ℕ
num (fin n) _ = n

------------------------------------------------------------------------
-- 2.  The theorem's witness: a point no other point exceeds.  The
--     nonvanishing certificate is an argument, so the term cannot be
--     written without it — which is the whole content of the clause the
--     summary dropped.

-- The valuation does not depend on which nonvanishing certificate is
-- offered (`IsFin v` is `Unit` or `⊥`).
num-irr : (v : Val) (p q : IsFin v) → num v p ≡ num v q
num-irr (fin n) _ _ = refl
num-irr ∞       p _ = ⊥-rec p

-- "m maximizes v_p(f)": the observable does not vanish at m, and no
-- point of E has larger valuation.  Note this does NOT mention a global
-- certificate — it is statable for an arbitrary world, which is what
-- lets the dropped-hypothesis reading be stated and refuted rather than
-- merely left unbuildable.
MaxAt : World → Pt → Type
MaxAt W m =
  Σ[ fm ∈ IsFin (W m) ]
    ((q : Pt) (fq : IsFin (W q)) → le (num (W q) fq) (num (W m) fm) ≡ true)

maximizer : (W : World) (h : NonVanishing W) → Σ[ m ∈ Pt ] MaxAt W m
maximizer W h = go (dich (le a b))
  where
  a = num (W x₁) (h x₁)
  b = num (W x₂) (h x₂)

  lift₂ : ((q : Pt) → le (num (W q) (h q)) (num (W x₂) (h x₂)) ≡ true) → MaxAt W x₂
  lift₂ base = h x₂ , λ q fq → cong (λ n → le n b) (num-irr (W q) fq (h q)) ∙ base q

  lift₁ : ((q : Pt) → le (num (W q) (h q)) (num (W x₁) (h x₁)) ≡ true) → MaxAt W x₁
  lift₁ base = h x₁ , λ q fq → cong (λ n → le n a) (num-irr (W q) fq (h q)) ∙ base q

  go : (le a b ≡ true) ⊎ (le a b ≡ false) → Σ[ m ∈ Pt ] MaxAt W m
  go (inl q) = x₂ , lift₂ (λ { x₁ → q ; x₂ → le-refl b })
  go (inr q) = x₁ , lift₁ (λ { x₁ → le-refl a ; x₂ → le-flip a b q })

------------------------------------------------------------------------
-- 3.  The degenerate world the dropped clause was excluding: `f ≡ 0` on
--     `E`, where every point has valuation ∞ and no maximizer exists.

vanishing-world : World
vanishing-world _ = ∞

vanishing-has-no-certificate : NonVanishing vanishing-world → ⊥
vanishing-has-no-certificate h = h x₁

-- Vanishing at a single point is already enough.
half-vanishing-world : World
half-vanishing-world x₁ = fin 3
half-vanishing-world x₂ = ∞

half-vanishing-has-no-certificate : NonVanishing half-vanishing-world → ⊥
half-vanishing-has-no-certificate h = h x₂

------------------------------------------------------------------------
-- 4.  Therefore the hypothesis-dropped reading — "EVERY finite world
--     has a point maximizing v_p(f)" — is false on this model, since
--     `vanishing-world` has no such point at all: the maximizer would
--     have to be a point where the observable does not vanish, and
--     there is none.  `NaturalMachine/Control/MaximizerWithoutNonvanishing.agda`
--     asserts exactly the antecedent below and must fail to type-check.

vanishing-world-has-no-maximizer : (m : Pt) → MaxAt vanishing-world m → ⊥
vanishing-world-has-no-maximizer _ (fm , _) = fm

dropped-hypothesis-false :
  ((W : World) → Σ[ m ∈ Pt ] MaxAt W m) → ⊥
dropped-hypothesis-false g =
  vanishing-world-has-no-maximizer (fst (g vanishing-world))
                                   (snd (g vanishing-world))
