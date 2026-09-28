{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- आसन्न — आसन्नो वृत्तपरिणाहः ।
--
-- (this is the APPROXIMATE circumference of a circle.)
--
-- ────────────────────────────────────────────────────────────────────
-- The BARRIER Structure Proposition states that WL observables factor
-- through the blurred spectral measure, hence no post-processing
-- recovers what the blur merged.
--
-- One might split it in two: the analytic half (that WL
-- observables do factor through the blur), and the second
-- half (that once they do, no refinement recovers the fibre) is already
-- available in general form from
-- `Vaidharmya_TheObstructionWasNeverClassicalAndTheAnswerTypeNeedOnlyBeApart`,
-- which drops `Bool` from `QuotientFiberLaw` and leaves
-- the negative half standing over an arbitrary answer type with an
-- arbitrary irreflexive separation.
--
-- **THE SPLIT IS NOT VALID, AND THIS MODULE IS WHY.**
--
-- `Vaidharmya`'s `AllBlind` demands that blind queries return EQUAL
-- answers — its own header says "not close, equal" — because its whole
-- proof is `cong decide` applied to an equality of transcripts.  An
-- analytic barrier lemma does not deliver equality.  It delivers
-- agreement to within ε: `BARRIER.md` (absent from this repository)'s own Corollary B2 asks only that
-- σ_k − σ_k′ be "annihilated at that resolution", with mismatch
-- O((δL)^{2p−1}), and `BARRIER_ERROR_WINDOW.md` (absent from this repository) Theorem U1 puts the
-- window's error term E at C_E X₀^{−1/2} Θ_φ(L/2), a NONZERO quantity
-- that depends on the configuration through the (k−1)-fold wave layer
-- 𝒵_{k−1}.  Two configurations agreeing under the blur therefore give
-- transcripts that are CLOSE, never equal, and `cong` fires on nothing.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED HERE.  Three statements, no analysis, no numerics.
--
--   §२  **The near-law.**  Replace equality of answers by an arbitrary
--       tolerance relation `_≈_` and the law survives — PROVIDED the
--       decoder respects the tolerance and the tolerance excludes the
--       separation.  Proof is four lines and mentions no constructor.
--
--   §३  **Where the exact case got its hypothesis for free.**  Take
--       `_≈_ := _≡_` and `Respects decide` is inhabited for EVERY
--       decoder, by `cong`.  That is precisely the hypothesis
--       `Vaidharmya` never had to state, and precisely the one the
--       analytic setting must now pay for.
--
--   §४  **The gap is real, and here is a counterexample.**  Near
--       blindness ALONE — with the arbitrary post-processing that
--       `BARRIER.md` (absent from this repository)'s Proposition B3 explicitly insists on ("even
--       non-computable") — implies NO obstruction whatever.  One state
--       space of two points, one query, answers 1 and 0, tolerance
--       "differ by at most one": the pair is near-blind and the head
--       decoder separates it.  Checked, not argued.
--
-- ────────────────────────────────────────────────────────────────────
-- SO WHAT MUST THE ANALYTIC BARRIER LEMMA SUPPLY?  Exactly one of two
-- things, and this module's content is that there is no third:
--
--   (a) EXACT agreement of the full observable, not of the blur — which
--       is `BARRIER_SMOOTH_TERM.md` (absent from this repository)'s corrected B2′ (every lower-arity
--       layer, at precision εX^{−r/2}), and is a strictly stronger
--       demand than B2 as `BARRIER.md` (absent from this repository) still states it; or
--
--   (b) a MODULUS on Φ — a bound on how far a WL post-processing may
--       amplify a sub-resolution difference.  §२'s `Respects` is the
--       weakest form of that hypothesis.
--
-- And (b) is in direct contradiction with Proposition B3 as written,
-- whose entire force is that Φ is arbitrary.  **B3's generality is what
-- kills the ε-version of its own corollary.**  That collision is the
-- finding; it is a missing distinction in the WL definition.
--
-- ────────────────────────────────────────────────────────────────────
--
-- ────────────────────────────────────────────────────────────────────
-- TERM.  आसन्न — "approached", hence approximate — is the tradition's
-- own word for a value given AS an approximation and marked so in the
-- statement itself.  ryabhaa, *ryabhaya*, Gaitapda 10 (499):
-- the ratio 62832/20000 is introduced with आसन्नो वृत्तपरिणाहः, "this is
-- the approximate circumference" — the approximation declared in the
-- verse rather than left for a reader to discover.  That declaration is
-- the whole subject of this module: a quantity known to within a
-- tolerance is a different object from a quantity known, and a theorem
-- proved for the second does not transfer to the first.
--
-- LIMIT.  The term is used here for an arbitrary tolerance relation on
-- an answer type.  No text states a tolerance relation, ryabhaa
-- proved nothing below, and the connection asserted is only that both
-- name the same job — marking, in the statement, that what is in hand
-- is near and not equal.
------------------------------------------------------------------------

module Asanna_TheNearIsNotTheEqualAndTheBarrierDiesInTheGap where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥* ; rec*)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz)
open import Cubical.Relation.Nullary using (¬_)

private variable ℓ : Level

------------------------------------------------------------------------
-- १ · The observation class, with a tolerance in place of equality.
--
-- `V` is what a query returns; `_≈_` is "indistinguishable to within the
-- window"; `_#_` is "told apart".  Nothing is assumed of either — not
-- reflexivity, not symmetry, not transitivity, not irreflexivity.  The
-- hypotheses arrive at the theorems that need them, so it is visible
-- which theorem pays for what.
------------------------------------------------------------------------

module Def (X : Type ℓ) (V : Type ℓ)
           (_≈_ : V → V → Type ℓ)
           (_#_ : V → V → Type ℓ) where

  Query : Type ℓ
  Query = X → V

  obs : List Query → X → List V
  obs []       x = []
  obs (o ∷ os) x = o x ∷ obs os x

  -- Transcripts within tolerance, pointwise.
  _≈ᴸ_ : List V → List V → Type ℓ
  []      ≈ᴸ []      = Unit*
  []      ≈ᴸ (_ ∷ _) = ⊥*
  (_ ∷ _) ≈ᴸ []      = ⊥*
  (a ∷ s) ≈ᴸ (b ∷ t) = (a ≈ b) × (s ≈ᴸ t)

  -- Every query fails to resolve the pair — to within the tolerance.
  -- This, and not equality, is what a windowed observable delivers.
  NearBlind : List Query → X → X → Type ℓ
  NearBlind []       x y = Unit*
  NearBlind (o ∷ os) x y = (o x ≈ o y) × NearBlind os x y

  -- Post-processing, arbitrary: `BARRIER.md` (absent from this repository) Prop. B3's Φ.
  Separates : List Query → X → X → Type ℓ
  Separates os x y =
    Σ[ decide ∈ (List V → V) ] (decide (obs os x) # decide (obs os y))

  -- A decoder carrying a modulus: it may not turn a within-tolerance
  -- difference into an out-of-tolerance one.
  Respects : (List V → V) → Type ℓ
  Respects decide = (s t : List V) → s ≈ᴸ t → decide s ≈ decide t

  SeparatesRespectfully : List Query → X → X → Type ℓ
  SeparatesRespectfully os x y =
    Σ[ decide ∈ (List V → V) ]
      (Respects decide × (decide (obs os x) # decide (obs os y)))

------------------------------------------------------------------------
-- २ · The near-law.  Two hypotheses, both stated, neither free.
--
--   (i)  the decoder respects the tolerance;
--   (ii) the tolerance excludes the separation — being within tolerance
--        is incompatible with being told apart.
--
-- Given those, near-blindness obstructs, and the proof never mentions a
-- constructor, a decidability, or an h-level, exactly as in §२ of
-- `Vaidharmya`.  The `cong` there has become the hypothesis here; that
-- substitution IS the content of this module.
------------------------------------------------------------------------

  obs-near : (os : List Query) (x y : X)
           → NearBlind os x y → obs os x ≈ᴸ obs os y
  obs-near []       x y _        = tt*
  obs-near (o ∷ os) x y (b , bs) = b , obs-near os x y bs

  near-no-decision :
      ((a b : V) → a ≈ b → ¬ (a # b))
    → (os : List Query) (x y : X)
    → NearBlind os x y → ¬ SeparatesRespectfully os x y
  near-no-decision excl os x y nb (decide , resp , sep) =
    excl (decide (obs os x)) (decide (obs os y))
         (resp (obs os x) (obs os y) (obs-near os x y nb))
         sep

  -- Non-vacuity: respectful decoders exist, so the conclusion of
  -- `near-no-decision` is not a statement about the empty class.
  const-respects : (v : V) → ((w : V) → w ≈ w) → Respects (λ _ → v)
  const-respects v ≈refl s t _ = ≈refl v

------------------------------------------------------------------------
-- ३ · Where the exact law got its hypothesis for free.
--
-- Instantiate the tolerance at equality.  Then `Respects` is inhabited
-- for EVERY decoder — that is `cong` — so `SeparatesRespectfully` and
-- `Separates` coincide and §२ collapses to `Vaidharmya`'s
-- `no-decision`, hypothesis (i) having cost nothing.
--
-- The point is negative and it is the whole reason the split fails:
-- hypothesis (i) is invisible at `_≡_` and load-bearing anywhere else.
------------------------------------------------------------------------

module समता (X : Type ℓ) (V : Type ℓ) (_#_ : V → V → Type ℓ) where

  open Def X V _≡_ _#_ public

  ≈ᴸ→≡ : (s t : List V) → s ≈ᴸ t → s ≡ t
  ≈ᴸ→≡ []      []      _       = refl
  ≈ᴸ→≡ []      (_ ∷ _) e       = rec* e
  ≈ᴸ→≡ (_ ∷ _) []      e       = rec* e
  ≈ᴸ→≡ (a ∷ s) (b ∷ t) (p , q) = cong₂ _∷_ p (≈ᴸ→≡ s t q)

  -- The hypothesis that costs nothing at equality.
  every-decoder-respects : (decide : List V → V) → Respects decide
  every-decoder-respects decide s t e = cong decide (≈ᴸ→≡ s t e)

  -- …hence the arbitrary-decoder statement follows, with irreflexivity
  -- as the only surviving hypothesis: `Vaidharmya` §२, recovered.
  exact-no-decision : ((v : V) → ¬ (v # v))
                    → (os : List Query) (x y : X)
                    → NearBlind os x y → ¬ Separates os x y
  exact-no-decision irr os x y nb (decide , sep) =
    near-no-decision (λ a b p → subst (λ z → ¬ (z # b)) (sym p) (irr b))
                     os x y nb
                     (decide , every-decoder-respects decide , sep)

------------------------------------------------------------------------
-- ४ · The gap, as a checked counterexample.
--
-- Drop hypothesis (i) — which is exactly what `BARRIER.md` (absent from this repository) Prop. B3
-- does when it insists Φ be arbitrary and even non-computable — and
-- near-blindness implies nothing at all.
--
-- Two states.  One query.  Answers 1 and 0.  Tolerance: differ by at
-- most one.  Separation: inequality.  The pair is near-blind; the head
-- decoder tells it apart.
--
-- The tolerance here is deliberately NOT excluded by the separation
-- (adjacent naturals are within tolerance and unequal), which is
-- precisely the analytic situation: two configurations agreeing under
-- the blur have observable values that are close and different.
------------------------------------------------------------------------

_≈₁_ : ℕ → ℕ → Type₀
m ≈₁ n = (m ≡ n) ⊎ ((suc m ≡ n) ⊎ (m ≡ suc n))

_≠₁_ : ℕ → ℕ → Type₀
m ≠₁ n = ¬ (m ≡ n)

open Def Bool ℕ _≈₁_ _≠₁_

-- The one query: it reads 1 on the first state and 0 on the second.
मापः : Query
मापः true  = 1
मापः false = 0

शिरः : List ℕ → ℕ
शिरः []      = 0
शिरः (n ∷ _) = n

आसन्न-अन्धत्वम् : NearBlind (मापः ∷ []) true false
आसन्न-अन्धत्वम् = inr (inr refl) , tt*

-- …and yet it is separated, by a decoder as tame as they come.
आसन्न-न-बाधा : Separates (मापः ∷ []) true false
आसन्न-न-बाधा = शिरः , snotz

-- Stated as the refutation it is: near-blindness plus arbitrary
-- post-processing does NOT obstruct.  Any barrier claim of that shape
-- is false, and the two admissible repairs are §२'s hypotheses.
गापः : NearBlind (मापः ∷ []) true false × Separates (मापः ∷ []) true false
गापः = आसन्न-अन्धत्वम् , आसन्न-न-बाधा

------------------------------------------------------------------------
-- ५ · शेषः — what this leaves standing, and what it hands back.
--
-- Standing: `Vaidharmya` is untouched.  Over an answer type with EXACT
-- blindness the obstruction holds for any irreflexive separation and
-- any decoder whatever, and §३ re-derives it from §२.
--
-- `METHOD.md` (absent from this repository) §3 item 1 does not reduce to a formal half plus an
-- analytic half.  The analytic half must additionally produce ONE of
--
--   (a) exact layerwise agreement — B2′ of `BARRIER_SMOOTH_TERM.md` (absent from this repository),
--       which `BARRIER.md` (absent from this repository)'s Corollary B2 does not state; or
--   (b) a modulus on WL post-processing — which `BARRIER.md` (absent from this repository)'s
--       Proposition B3 currently rules out by construction.
------------------------------------------------------------------------
