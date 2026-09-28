{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheTextPredicateIsUniqueSoExistsCarriesNoChoice
--
-- ON THE NAME.  Checked before naming: `.claude/hooks/priority-ledger.txt` (absent from this repository)
-- (CURRENT header) and `.claude/hooks/european-frame.txt` (absent from this repository); `formal/` and
-- invented.**  The subject is SEED-83 §6's question, i.e. this corpus's
-- own, and the h-level step is the declared substrate.  I have
-- established no Indian source for either.
--
-- ────────────────────────────────────────────────────────────────────
-- THE AUDIT.  Target:
-- `ATextPredicateExistsExactlyWhenTheSemanticPropertyIsDecidable`, an
-- `ExistsExactlyWhen`.
--
-- **THE BICONDITIONAL IS EARNED.**  `decisionGivesPredicate` and
-- `predicateGivesDecision` are both there, both cheap, and the module
-- says in its own §2 that both are needed and why.  It also states
-- plainly that it did NOT run the finite check §6 licenses, and that a
-- reduction is not an answer.
--
-- **THE WORD CARRYING THE CLAIM IS `EXISTS`, AND IT HAS THE USUAL TWO
-- READINGS.**  The statement is `Σ[ p ∈ (Text → Bool) ] Correct p` —
-- STRUCTURE, a predicate together with a proof — where "a mechanizable
-- predicate exists" reads as a PROPERTY.  Over a general type those
-- differ, and the difference is exactly whether the claim carries a
-- choice: which correct predicate did you get?
--
-- **HERE IT CARRIES NONE, AND THAT IS STRONGER THAN THE TRUNCATION
-- QUESTION.**  `Correct p` pins `p t ≡ true` to `Outside (denotes t)` in
-- both directions, and `Bool` has two elements, so any two correct
-- predicates agree at every text: `correctIsUnique`.  There is nothing
-- to choose.  So the untruncated `Σ` is not an overstatement of the
-- truncated `∥ Σ ∥₁` — it is the same claim, and §2's use of `Σ` was
-- right for a reason it did not give.
--
-- **AND THE Σ IS A PROPOSITION OUTRIGHT WHEN `Outside` IS.**  Uniqueness
-- gives the first component; `Correct p`'s second half lands in
-- `Outside (denotes t)`, which is an arbitrary type in the audited
-- module, so the h-level of the pair needs `Outside` pointwise
-- propositional and gets it no cheaper.  **That hypothesis is the
-- price, it is real, and it is not free** — which is the honest
-- difference from d3963e51 and b716cfee, where both sides were
-- propositions already.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   correctIsUnique      any two correct text predicates are equal, by
--                        `funExt` over a four-case analysis with the
--                        Boolean values passed as ARGUMENTS, not `with`
--   isPropCorrect        `Correct p` is a proposition when `Outside` is
--                        pointwise one
--   theTextPredicateIsUnique
--                        hence the whole `Σ` is a proposition, by
--                        `ΣPathP` and `isProp→PathP`
------------------------------------------------------------------------

module TheTextPredicateIsUniqueSoExistsCarriesNoChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ ; isProp×)
open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax ; ΣPathP ; _,_ ; fst ; snd)
open import Cubical.Data.Empty as ⊥ using (⊥)

open import ATextPredicateExistsExactlyWhenTheSemanticPropertyIsDecidable
  using (Correct)

module _
  (Text Object : Type)
  (denotes : Text → Object)
  (Outside : Object → Type)
  where

  private
    Corr : (Text → Bool) → Type
    Corr = Correct Text Object denotes Outside

  ------------------------------------------------------------------
  -- 1.  Correctness determines the predicate
  ------------------------------------------------------------------

  correctIsUnique :
    (p q : Text → Bool) → Corr p → Corr q → p ≡ q
  correctIsUnique p q cp cq = funExt pointwise
    where
      go : (t : Text) (b c : Bool) → p t ≡ b → q t ≡ c → p t ≡ q t
      go t true  true  e₁ e₂ = e₁ ∙ sym e₂
      go t false false e₁ e₂ = e₁ ∙ sym e₂
      go t true  false e₁ e₂ =
        ⊥.rec (true≢false (sym (cq t .fst (cp t .snd e₁)) ∙ e₂))
      go t false true  e₁ e₂ =
        ⊥.rec (true≢false (sym (cp t .fst (cq t .snd e₂)) ∙ e₁))

      pointwise : (t : Text) → p t ≡ q t
      pointwise t = go t (p t) (q t) refl refl

  ------------------------------------------------------------------
  -- 2.  And with `Outside` pointwise propositional, so is the whole Σ
  ------------------------------------------------------------------

  isPropCorrect :
    ((o : Object) → isProp (Outside o))
    → (p : Text → Bool) → isProp (Corr p)
  isPropCorrect po p =
    isPropΠ (λ t →
      isProp× (isPropΠ (λ _ → isSetBool (p t) true))
              (isPropΠ (λ _ → po (denotes t))))

  theTextPredicateIsUnique :
    ((o : Object) → isProp (Outside o))
    → isProp (Σ[ p ∈ (Text → Bool) ] Corr p)
  theTextPredicateIsUnique po (p , cp) (q , cq) =
    ΣPathP ( correctIsUnique p q cp cq
           , isProp→PathP
               (λ i → isPropCorrect po (correctIsUnique p q cp cq i))
               cp cq )
