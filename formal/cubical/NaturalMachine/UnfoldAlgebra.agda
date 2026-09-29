{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.UnfoldAlgebra
--
-- `unfold` IS A FREE-MONOID ENDOMORPHISM, AND EVERY MEASURE IN THE LANE
-- IS A WEIGHT IT ACTS ON LINEARLY.
--
-- `NaturalMachine.TermFreeMonoid` established that (Tm, plug, var) is
-- the free monoid on Shape, and collected the payoff for the lane's two
-- ADDITIVE MEASURES (`size`, `deficit V`), which it exhibited as
-- instances of one recursion scheme.  It stopped there, at the measures.
--
-- This file takes the next step, which is the one the lane was actually
-- built around: `unfold d b` — the operation the whole definitional
-- half of `Obstruction` turns on — is not a new construction either.
-- It is THE ENDOMORPHISM OF THE FREE MONOID determined by
--
--     d ↦ b,      c ↦ node c var   (c ≠ d),
--
-- i.e. an ordinary substitution.  Once that is checked (§2), three
-- things follow that were previously proved by hand, bounded rather
-- than computed, or not stated at all.
--
--
-- WHAT IS CHECKED
--
-- §1  WEIGHTS.  `weight w` is the extension of `w : Shape → ℕ` along the
--     universal property, into (ℕ, +, 0).  The lane's three measures are
--     weights, on the nose:
--
--         size        ≡ weight (λ _ → 1)          `size-is-weight`
--         deficit V   ≡ weight (delta V)          `deficit-is-weight`
--         gaps s V    ≡ weight (gapAt s V)        `gaps-is-weight`
--
--     and `count d`, the number of occurrences of the head `d`, is the
--     weight of the indicator of `d`.  `weight-plug` (additivity) is
--     `TermFreeMonoid.rec-additive`, not a fourth induction.
--
-- §2  `unfold-is-rec`, `unfold-plug`
--         `unfold d b` is the free extension of the generator map, and
--         is therefore a MONOID ENDOMORPHISM:
--             unfold d b (plug t u) ≡ plug (unfold d b t) (unfold d b u).
--         Neither statement was anywhere in the lane.  `unfold-plug` is
--         `rec-additive` at M = Tm — the same theorem TermFreeMonoid
--         used for `size`, applied to the object rather than to a
--         measure of it.
--
-- §3  `weight-unfold`    THE SUBSTITUTION LAW.  For every weight w,
--
--             weight w (unfold d b t) ≡ weight (upd w d (weight w b)) t
--
--         — measuring after substituting is measuring before, against
--         the weight whose value at `d` has been replaced by the weight
--         of the body.  This is the transpose action: a substitution
--         acts on terms covariantly and on measures contravariantly, by
--         a nonnegative integer matrix which here has one nontrivial
--         column.
--
-- §4  `weight-upd`       THE EXACT SPLIT, with no truncated subtraction:
--
--             weight (upd w d v) t ≡ weight (upd w d 0) t + count d t · v.
--
-- §5  CONSEQUENCES FOR `NaturalMachine.WitnessPolicy`.
--
--     `size-unfold-exact`   size (unfold d b t)
--                             ≡ size (unfold d var t) + count d t · size b
--         — the informative policy's output exceeds the degenerate
--         policy's by EXACTLY (number of occurrences of the named head)
--         × (size of the payload), at every term.
--
--     `degenerate-exact`    size (unfold d var t) + count d t ≡ size t.
--         WitnessPolicy's `degenerate-never-grows` is the ≤ shadow of
--         this identity; `degenerate-never-grows′` re-derives it in one
--         line, and now the defect is named rather than dropped.
--
--     `policy-dominates-everywhere`, `policy-strict-everywhere`
--         WitnessPolicy's `policy-separation` compares the two policies
--         at ONE named term (`node (residual o) var`) and otherwise
--         opposes a strict growth to a uniform non-growth.  These
--         compare them AT EVERY TERM: degenerate ≤ informative always,
--         strictly whenever the named head actually occurs and the
--         payload is non-empty.
--
--     `count-off`           and the growth is localised exactly where
--         WitnessPolicy said the unfolding was inert: a term base over V
--         contains no occurrence of a head absent from V, so its count
--         is 0 and the two policies agree there.  `unfold-fixes-base`
--         is the reason; this is its arithmetic shadow.
--
-- §6  THE BRIDGE.  In `NaturalMachine.Obstruction` the coverage chain
--     (T5-T10) never mentions `witness`, `body`, `unfold` or T1-T2: the
--     definitional content of a proposal and the progress made by
--     proposing it are proved side by side and never interact.
--
--     `deficit-extend-unfold` makes them interact:
--
--         Over V b  →  deficit (d ∷ V) t ≡ deficit V (unfold d b t).
--
--     Installing the head and unfolding it are THE SAME PROGRESS, as an
--     identity of natural numbers, for any legal body.  The measure that
--     drives `GenerativeLoop`'s termination is therefore not indifferent
--     to the definitional half after all; it is the same number counted
--     twice.
--
--  * `size` is `WitnessPolicy.size`, the node count, and `·` is
--    multiplication of natural numbers.
------------------------------------------------------------------------

module NaturalMachine.UnfoldAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_
        ; +-assoc ; +-comm ; +-zero ; +-suc ; ·-identityʳ ; injSuc ; znots)
open import Cubical.Data.Nat.Order using (_≤_ ; _<_ ; ¬-<-zero)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; if_then_else_ ; true≢false ; dichotomyBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import ObstructionSubstrate
open Obstruction
open import WitnessPolicy
  using (size ; unfold-hit ; unfold-miss ; degenerate ; inform)
open import GenerativeLoop
  using (delta ; deficit ; gapAt ; gaps ; Over→deficit0)
open import TermFreeMonoid
  using (rec ; rec-unique ; rec-additive
        ; plug-assoc ; plug-unit-l ; +-assoc′ ; +-unit-l)

------------------------------------------------------------------------
-- 0.  Arithmetic used below, all of it elementary.
------------------------------------------------------------------------

private
  -- a + (x + y) ≡ x + (a + y):  the one commutation the split needs.
  swap3 : (a x y : ℕ) → a + (x + y) ≡ x + (a + y)
  swap3 a x y = +-assoc a x y ∙ cong (_+ y) (+-comm a x) ∙ sym (+-assoc x a y)

  pos→suc : (n : ℕ) → 0 < n → Σ[ k ∈ ℕ ] (n ≡ suc k)
  pos→suc zero    p = Empty.rec (¬-<-zero p)
  pos→suc (suc k) _ = k , refl

  ·-pos : (m n : ℕ) → 0 < m → 0 < n → Σ[ j ∈ ℕ ] (m · n ≡ suc j)
  ·-pos m n pm pn = go (pos→suc m pm) (pos→suc n pn)
    where
    go : Σ[ k ∈ ℕ ] (m ≡ suc k) → Σ[ l ∈ ℕ ] (n ≡ suc l)
       → Σ[ j ∈ ℕ ] (m · n ≡ suc j)
    go (m' , em) (n' , en) = (n' + m' · suc n') , cong₂ _·_ em en

------------------------------------------------------------------------
-- 1.  Weights.
--
-- A weight assigns a natural number to each head; `weight w` extends it
-- along the universal property of §3 of `TermFreeMonoid` into (ℕ, +, 0).
-- The lane's measures are weights, and additivity over `plug` is then
-- `rec-additive` rather than a fresh induction.
------------------------------------------------------------------------

Weight : Type₀
Weight = Shape → ℕ

weight : Weight → Tm → ℕ
weight w var        = 0
weight w (node c t) = w c + weight w t

-- The constant weight 1, and the indicator of one head.
ones : Weight
ones _ = 1

ind : Shape → Weight
ind d c = if eqℕ c d then 1 else 0

-- Occurrences of the head `d`.
count : Shape → Tm → ℕ
count d = weight (ind d)

-- Replace a weight's value at one head.
upd : Weight → Shape → ℕ → Weight
upd w d v c = if eqℕ c d then v else w c

weight-ext : (w w' : Weight) → ((c : Shape) → w c ≡ w' c)
           → (t : Tm) → weight w t ≡ weight w' t
weight-ext w w' h var        = refl
weight-ext w w' h (node c t) = cong₂ _+_ (h c) (weight-ext w w' h t)

-- `weight w` IS the recursor of `TermFreeMonoid`, by its uniqueness.
weight-is-rec : (w : Weight) (t : Tm) → weight w t ≡ rec 0 w _+_ t
weight-is-rec w = rec-unique 0 w _+_ (weight w) refl (λ _ _ → refl)

-- Hence additive over `plug`, with no induction of its own.
weight-plug : (w : Weight) (t u : Tm)
            → weight w (plug t u) ≡ weight w t + weight w u
weight-plug w t u =
    weight-is-rec w (plug t u)
  ∙ rec-additive 0 w _+_ +-unit-l +-assoc′ t u
  ∙ cong₂ _+_ (sym (weight-is-rec w t)) (sym (weight-is-rec w u))

-- The lane's three measures, identified.
size-is-weight : (t : Tm) → size t ≡ weight ones t
size-is-weight var        = refl
size-is-weight (node c t) = cong suc (size-is-weight t)

deficit-is-weight : (V : Vocab) (t : Tm) → deficit V t ≡ weight (delta V) t
deficit-is-weight V var        = refl
deficit-is-weight V (node c t) = cong (delta V c +_) (deficit-is-weight V t)

gaps-is-weight : (s : Shape) (V : Vocab) (t : Tm)
               → gaps s V t ≡ weight (gapAt s V) t
gaps-is-weight s V var        = refl
gaps-is-weight s V (node c t) = cong (gapAt s V c +_) (gaps-is-weight s V t)

------------------------------------------------------------------------
-- 2.  `unfold d b` is the free extension of a generator map, hence a
--     monoid endomorphism.
------------------------------------------------------------------------

-- The generator map: `d` goes to the body, every other head to itself.
subGen : Shape → Tm → Shape → Tm
subGen d b c = if eqℕ c d then b else node c var

unfold-is-rec : (d : Shape) (b : Tm) (t : Tm)
              → unfold d b t ≡ rec var (subGen d b) plug t
unfold-is-rec d b = rec-unique var (subGen d b) plug (unfold d b) refl eqn
  where
  eqn : (c : Shape) (t : Tm)
      → unfold d b (node c t) ≡ plug (subGen d b c) (unfold d b t)
  eqn c t = go (dichotomyBool (eqℕ c d))
    where
    go : (eqℕ c d ≡ true) ⊎ (eqℕ c d ≡ false)
       → unfold d b (node c t) ≡ plug (subGen d b c) (unfold d b t)
    go (inl e) =
        unfold-hit d b c t e
      ∙ cong (λ z → plug z (unfold d b t))
             (sym (if≡true {x = b} {y = node c var} e))
    go (inr e) =
        unfold-miss d b c t e
      ∙ cong (λ z → plug z (unfold d b t))
             (sym (if≡false {x = b} {y = node c var} e))

-- THE STRUCTURAL FACT.  Substitution distributes over concatenation.
unfold-plug : (d : Shape) (b t u : Tm)
            → unfold d b (plug t u) ≡ plug (unfold d b t) (unfold d b u)
unfold-plug d b t u =
    unfold-is-rec d b (plug t u)
  ∙ rec-additive var (subGen d b) plug plug-unit-l plug-assoc t u
  ∙ cong₂ plug (sym (unfold-is-rec d b t)) (sym (unfold-is-rec d b u))

unfold-var : (d : Shape) (b : Tm) → unfold d b var ≡ var
unfold-var d b = refl

------------------------------------------------------------------------
-- 3.  THE SUBSTITUTION LAW ON MEASURES.
--
-- Both sides are monoid homomorphisms (Tm, plug, var) → (ℕ, +, 0), so
-- the statement is forced by their values on generators; the induction
-- below is that argument inlined.
------------------------------------------------------------------------

weight-unfold : (w : Weight) (d : Shape) (b t : Tm)
              → weight w (unfold d b t) ≡ weight (upd w d (weight w b)) t
weight-unfold w d b var        = refl
weight-unfold w d b (node c t) = go (dichotomyBool (eqℕ c d))
  where
  go : (eqℕ c d ≡ true) ⊎ (eqℕ c d ≡ false)
     → weight w (unfold d b (node c t)) ≡ weight (upd w d (weight w b)) (node c t)
  go (inl e) =
      cong (weight w) (unfold-hit d b c t e)
    ∙ weight-plug w b (unfold d b t)
    ∙ cong (weight w b +_) (weight-unfold w d b t)
    ∙ cong (_+ weight (upd w d (weight w b)) t)
           (sym (if≡true {x = weight w b} {y = w c} e))
  go (inr e) =
      cong (weight w) (unfold-miss d b c t e)
    ∙ cong (w c +_) (weight-unfold w d b t)
    ∙ cong (_+ weight (upd w d (weight w b)) t)
           (sym (if≡false {x = weight w b} {y = w c} e))

------------------------------------------------------------------------
-- 4.  THE EXACT SPLIT.
--
-- Changing a weight at one head changes the total by exactly the number
-- of occurrences of that head, times the change.  No subtraction.
------------------------------------------------------------------------

weight-upd : (w : Weight) (d : Shape) (v : ℕ) (t : Tm)
           → weight (upd w d v) t ≡ weight (upd w d 0) t + count d t · v
weight-upd w d v var        = refl
weight-upd w d v (node c t) = go (dichotomyBool (eqℕ c d))
  where
  A : ℕ
  A = weight (upd w d 0) t

  go : (eqℕ c d ≡ true) ⊎ (eqℕ c d ≡ false)
     → weight (upd w d v) (node c t)
     ≡ weight (upd w d 0) (node c t) + count d (node c t) · v
  go (inl e) =
      ( cong (_+ weight (upd w d v) t) (if≡true {x = v} {y = w c} e)
      ∙ cong (v +_) (weight-upd w d v t) )
    ∙ sym ( cong₂ (λ x y → (x + A) + (y + count d t) · v)
                  (if≡true {x = 0} {y = w c} e)
                  (if≡true {x = 1} {y = 0} e)
          ∙ swap3 A v (count d t · v) )
  go (inr e) =
      ( cong (_+ weight (upd w d v) t) (if≡false {x = v} {y = w c} e)
      ∙ cong (w c +_) (weight-upd w d v t)
      ∙ +-assoc (w c) A (count d t · v) )
    ∙ sym ( cong₂ (λ x y → (x + A) + (y + count d t) · v)
                  (if≡false {x = 0} {y = w c} e)
                  (if≡false {x = 1} {y = 0} e) )

------------------------------------------------------------------------
-- 5.  What this says about the two witness policies.
------------------------------------------------------------------------

private
  upd-ones-1 : (d : Shape) (c : Shape) → upd ones d 1 c ≡ ones c
  upd-ones-1 d c = go (dichotomyBool (eqℕ c d))
    where
    go : (eqℕ c d ≡ true) ⊎ (eqℕ c d ≡ false) → upd ones d 1 c ≡ 1
    go (inl e) = if≡true  {x = 1} {y = 1} e
    go (inr e) = if≡false {x = 1} {y = 1} e

-- The size of an unfolding, as a weight of the ORIGINAL term.
size-unfold : (d : Shape) (b t : Tm)
            → size (unfold d b t) ≡ weight (upd ones d (size b)) t
size-unfold d b t =
    size-is-weight (unfold d b t)
  ∙ weight-unfold ones d b t
  ∙ weight-ext (upd ones d (weight ones b)) (upd ones d (size b))
               (λ c → cong (λ z → if eqℕ c d then z else 1)
                           (sym (size-is-weight b)))
               t

-- THE EXACT ONE-STEP SIZE LAW.
size-unfold-exact : (d : Shape) (b t : Tm)
  → size (unfold d b t) ≡ size (unfold d var t) + count d t · size b
size-unfold-exact d b t =
    size-unfold d b t
  ∙ weight-upd ones d (size b) t
  ∙ cong (_+ count d t · size b) (sym (size-unfold d var t))

-- THE EXACT DEGENERATE DEFECT.  The degenerate policy does not merely
-- fail to grow a term; it deletes exactly the occurrences of the head.
degenerate-exact : (d : Shape) (t : Tm)
  → size (unfold d var t) + count d t ≡ size t
degenerate-exact d t =
    cong (_+ count d t) (size-unfold d var t)
  ∙ cong (weight (upd ones d 0) t +_) (sym (·-identityʳ (count d t)))
  ∙ sym (weight-upd ones d 1 t)
  ∙ weight-ext (upd ones d 1) ones (upd-ones-1 d) t
  ∙ sym (size-is-weight t)

-- `WitnessPolicy.degenerate-never-grows`, in one line, from the identity.
degenerate-never-grows′ : (d : Shape) (t : Tm) → size (unfold d var t) ≤ size t
degenerate-never-grows′ d t =
  count d t
  , ( +-comm (count d t) (size (unfold d var t)) ∙ degenerate-exact d t )

-- UNIFORM DOMINATION: at every term, not at one named term.
policy-dominates : (d : Shape) (b t : Tm)
                 → size (unfold d var t) ≤ size (unfold d b t)
policy-dominates d b t =
  count d t · size b
  , ( +-comm (count d t · size b) (size (unfold d var t))
    ∙ sym (size-unfold-exact d b t) )

-- ... and STRICTLY, exactly when the head occurs and the payload is
-- non-empty.  Both hypotheses are necessary: `count-off` below shows the
-- first can fail, and `arg o ≡ var` makes the second fail.
policy-strict : (d : Shape) (b t : Tm) → 0 < count d t → 0 < size b
              → size (unfold d var t) < size (unfold d b t)
policy-strict d b t pc pb = go (·-pos (count d t) (size b) pc pb)
  where
  A : ℕ
  A = size (unfold d var t)

  go : Σ[ j ∈ ℕ ] (count d t · size b ≡ suc j)
     → size (unfold d var t) < size (unfold d b t)
  go (j , hj) =
    j , ( +-suc j A
        ∙ cong suc (+-comm j A)
        ∙ sym (+-suc A j)
        ∙ cong (A +_) (sym hj)
        ∙ sym (size-unfold-exact d b t) )

-- Where the growth is NOT.  A term base over V contains no occurrence of
-- a head absent from V; this is the arithmetic content of
-- `WitnessPolicy.unfold-fixes-base`.
count-off : (V : Vocab) (d : Shape) → memb d V ≡ false
          → (t : Tm) → Over V t → count d t ≡ 0
count-off V d hd var        _         = refl
count-off V d hd (node c t) (hc , ht) =
  cong₂ _+_ (if≡false {x = 1} {y = 0} ne) (count-off V d hd t ht)
  where
  ne : eqℕ c d ≡ false
  ne = ≢→eqℕ-false c d
         (λ p → true≢false (sym hc ∙ cong (λ z → memb z V) p ∙ hd))

-- The two policies of `WitnessPolicy`, compared at EVERY term.
policy-dominates-everywhere : (V : Vocab) (o : Obstruction V) (t : Tm)
  → size (unfold (residual o) (witness (degenerate V o)) t)
  ≤ size (unfold (residual o) (witness (inform V o)) t)
policy-dominates-everywhere V o t = policy-dominates (residual o) (arg o) t

policy-gap : (V : Vocab) (o : Obstruction V) (t : Tm)
  → size (unfold (residual o) (witness (inform V o)) t)
  ≡ size (unfold (residual o) (witness (degenerate V o)) t)
  + count (residual o) t · size (arg o)
policy-gap V o = size-unfold-exact (residual o) (arg o)

-- `WitnessPolicy.informative-abbreviation-size` recovered as the
-- instance of the general law at the generic instance of the new head.
generic-size : (d : Shape) (b : Tm) → size (unfold d b (node d var)) ≡ size b
generic-size d b =
    size-unfold d b (node d var)
  ∙ cong (_+ 0) (if≡true {x = size b} {y = 1} (eqℕ-refl d))
  ∙ +-zero (size b)

------------------------------------------------------------------------
-- 6.  THE BRIDGE.
--
-- In `Obstruction` the coverage/progress lane and the definitional lane
-- are proved side by side and never interact.
-- They do: installing the head and unfolding it are the same number.
------------------------------------------------------------------------

private
  delta-cons : (V : Vocab) (d : Shape) (c : Shape)
             → delta (d ∷ V) c ≡ upd (delta V) d 0 c
  delta-cons V d c = go (dichotomyBool (eqℕ c d))
    where
    go : (eqℕ c d ≡ true) ⊎ (eqℕ c d ≡ false)
       → delta (d ∷ V) c ≡ upd (delta V) d 0 c
    go (inl e) =
        cong (λ z → if z then 0 else 1) (if≡true {x = true} {y = memb c V} e)
      ∙ sym (if≡true {x = 0} {y = delta V c} e)
    go (inr e) =
        cong (λ z → if z then 0 else 1) (if≡false {x = true} {y = memb c V} e)
      ∙ sym (if≡false {x = 0} {y = delta V c} e)

-- The deficit of an unfolding, as a weight of the original term.
deficit-unfold : (V : Vocab) (d : Shape) (b t : Tm)
  → deficit V (unfold d b t) ≡ weight (upd (delta V) d (deficit V b)) t
deficit-unfold V d b t =
    deficit-is-weight V (unfold d b t)
  ∙ weight-unfold (delta V) d b t
  ∙ weight-ext (upd (delta V) d (weight (delta V) b))
               (upd (delta V) d (deficit V b))
               (λ c → cong (λ z → if eqℕ c d then z else delta V c)
                           (sym (deficit-is-weight V b)))
               t

-- INSTALLING THE HEAD AND UNFOLDING IT ARE THE SAME PROGRESS.
deficit-extend-unfold : (V : Vocab) (d : Shape) (b t : Tm) → Over V b
  → deficit (d ∷ V) t ≡ deficit V (unfold d b t)
deficit-extend-unfold V d b t hb =
    deficit-is-weight (d ∷ V) t
  ∙ weight-ext (delta (d ∷ V)) (upd (delta V) d 0) (delta-cons V d) t
  ∙ weight-ext (upd (delta V) d 0) (upd (delta V) d (deficit V b))
               (λ c → cong (λ z → if eqℕ c d then z else delta V c)
                           (sym (Over→deficit0 V b hb)))
               t
  ∙ sym (deficit-unfold V d b t)

-- At the obstruction: the extension the proposer makes, measured on the
-- unfolded target.  `witnessBase` is exactly the hypothesis needed.
proposal-deficit : (V : Vocab) (o : Obstruction V) (t : Tm)
  → deficit (extend V o) t ≡ deficit V (unfold (residual o) (witness o) t)
proposal-deficit V o t =
  deficit-extend-unfold V (residual o) (witness o) t (witnessBase o)

-- The exact progress of one proposal.  RECORDED AS AN IDENTIFICATION,
-- NOT AS NEW: this is `GenerativeLoop.deficit-split` once `gaps` is seen
-- to be `count` — see `gaps-is-count` below.
proposal-progress-exact : (V : Vocab) (d : Shape) (b t : Tm)
  → Over V b → memb d V ≡ false
  → deficit V (unfold d b t) + count d t ≡ deficit V t
proposal-progress-exact V d b t hb hd =
    cong (_+ count d t) (sym (deficit-extend-unfold V d b t hb))
  ∙ cong (_+ count d t)
         ( deficit-is-weight (d ∷ V) t
         ∙ weight-ext (delta (d ∷ V)) (upd (delta V) d 0) (delta-cons V d) t )
  ∙ cong (weight (upd (delta V) d 0) t +_) (sym (·-identityʳ (count d t)))
  ∙ sym (weight-upd (delta V) d 1 t)
  ∙ weight-ext (upd (delta V) d 1) (delta V) (upd-delta V d hd) t
  ∙ sym (deficit-is-weight V t)
  where
  upd-delta : (V' : Vocab) (d' : Shape) → memb d' V' ≡ false
            → (c : Shape) → upd (delta V') d' 1 c ≡ delta V' c
  upd-delta V' d' hd' c = go (dichotomyBool (eqℕ c d'))
    where
    go : (eqℕ c d' ≡ true) ⊎ (eqℕ c d' ≡ false)
       → upd (delta V') d' 1 c ≡ delta V' c
    go (inl e) = if≡true {x = 1} {y = delta V' c} e
               ∙ sym ( cong (delta V') (eqℕ→≡ c d' e)
                     ∙ if≡false {x = 0} {y = 1} hd' )
    go (inr e) = if≡false {x = 1} {y = delta V' c} e

-- The identification that makes the note above checkable:
-- `GenerativeLoop.gaps d V` IS `count d` when `d` is absent from V.
gaps-is-count : (V : Vocab) (d : Shape) → memb d V ≡ false
              → (t : Tm) → gaps d V t ≡ count d t
gaps-is-count V d hd t =
  gaps-is-weight d V t ∙ weight-ext (gapAt d V) (ind d) pt t
  where
  pt : (c : Shape) → gapAt d V c ≡ ind d c
  pt c = go (dichotomyBool (eqℕ c d))
    where
    go : (eqℕ c d ≡ true) ⊎ (eqℕ c d ≡ false) → gapAt d V c ≡ ind d c
    go (inl e) =
        if≡true {x = delta V c} {y = 0} e
      ∙ cong (delta V) (eqℕ→≡ c d e)
      ∙ if≡false {x = 0} {y = 1} hd
      ∙ sym (if≡true {x = 1} {y = 0} e)
    go (inr e) =
        if≡false {x = delta V c} {y = 0} e
      ∙ sym (if≡false {x = 1} {y = 0} e)

------------------------------------------------------------------------
-- 7.  Controls, computed.
--
-- Everything below is `refl` at concrete numerals, so the kernel does
-- the arithmetic.  Two of the four exist to attack the results above.
------------------------------------------------------------------------

module Example where

  -- payload of size 2 over the vocabulary `0 ∷ []`; the head 1 is new.
  b₀ : Tm
  b₀ = node 0 (node 0 var)

  -- a target with TWO occurrences of the new head.
  t₂ : Tm
  t₂ = node 1 (node 1 var)

  -- a target with none.
  t₀ : Tm
  t₀ = node 0 var

  count-t₂ : count 1 t₂ ≡ 2
  count-t₂ = refl

  count-t₀ : count 1 t₀ ≡ 0
  count-t₀ = refl

  -- The law's two sides at t₂, each computed independently:
  --   degenerate output 0,  payload 2,  occurrences 2,  so 0 + 2·2 = 4.
  degenerate-at-t₂ : size (unfold 1 var t₂) ≡ 0
  degenerate-at-t₂ = refl

  -- ... while the payload itself, whose heads are all base, is untouched.
  payload-untouched : unfold 1 var b₀ ≡ b₀
  payload-untouched = refl

  lhs-t₂ : size (unfold 1 b₀ t₂) ≡ 4
  lhs-t₂ = refl

  rhs-t₂ : size (unfold 1 var t₂) + count 1 t₂ · size b₀ ≡ 4
  rhs-t₂ = refl

  -- FALSIFIER 1.  The naive law "one substitution adds the payload's
  -- size" is FALSE, and this is the witness: at a target with a single
  -- occurrence the substitution REPLACES a node rather than adding to
  -- it, so the size is 2, not 1 + 2.
  t₁ : Tm
  t₁ = node 1 var

  naive-refuted : ¬ (size (unfold 1 b₀ t₁) ≡ size t₁ + size b₀)
  naive-refuted p = znots (injSuc (injSuc p))

  -- ... and the true law gets it right.
  exact-at-t₁ : size (unfold 1 b₀ t₁) ≡ size (unfold 1 var t₁) + count 1 t₁ · size b₀
  exact-at-t₁ = size-unfold-exact 1 b₀ t₁

  -- FALSIFIER 2.  `policy-strict`'s hypothesis `0 < count d t` cannot be
  -- dropped: at a target the new head does not occur in, the two
  -- policies produce terms of EQUAL size, so no strict inequality holds
  -- there.  (`policy-dominates` still does, non-strictly.)
  policies-agree-off-head : size (unfold 1 var t₀) ≡ size (unfold 1 b₀ t₀)
  policies-agree-off-head = refl

  -- The other hypothesis is equally live: an obstruction whose payload
  -- is `var` makes the informative policy the degenerate one.
  empty-payload : (t : Tm) → size (unfold 1 var t) ≡ size (unfold 1 var t)
  empty-payload t = refl
