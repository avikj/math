{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Baddha — what the calculus binds and cannot release.
--
-- TERM.  बद्ध, bound / held fast.  Used here in its plain sense, and the
-- compound is chosen here: no text is cited for it and nothing below is
-- anyone's theorem.  (The corpus uses बद्धम् for the karma-count in
-- `Karma_…`; that is a different object and no connection is claimed.)
--
-- THIS MODULE REFUTES A CONJECTURE STATED IN TWO OTHER MODULES.
-- `Anupurvi_….NormalisationConjecture` and
-- `Samkhyana_….CompleteInvariantConjecture` both propose that the word of
-- variable occurrences together with the count of successors is a COMPLETE
-- invariant for derivability — that two terms agreeing on both are joined
-- by some derivation.  They are not.  There is a third conservation law,
-- it is independent of the other two, and it separates a pair on which
-- they agree.
--
-- WHY IT EXISTS, before the proof, because the reason is the design fact.
-- The calculus has NO ASSOCIATIVITY.  Read the rules: `add-zero` deletes an
-- `add` whose right child is `zero`; `add-suc` lifts a successor out of a
-- right child to the front; the three congruences descend; `reverse`
-- undoes.  Nothing re-brackets.  So a successor sitting in the LEFT operand
-- of an `add` can never reach the front — unless that `add` is itself
-- deleted, and `add-zero` deletes it only when its right child is `zero`.
-- A right child that carries a variable can never become `zero`, because
-- `Anupurvi_…` proves the word is conserved.  Hence:
--
--     A SUCCESSOR IN A LEFT OPERAND WHOSE SIBLING CARRIES A VARIABLE IS
--     PERMANENTLY TRAPPED.
--
-- §1 counts exactly those, §2 proves the count is conserved by every rule,
-- and §3 exhibits the pair.
--
-- THE ENTANGLEMENT, which is the part worth reading twice.  The proof that
-- `trapped` is conserved CANNOT be done alone.  The congruence on the left
-- needs `constPart` to be conserved (a successor moved inside the left
-- operand must not change how many are trapped), and the congruence on the
-- right needs the WORD to be conserved (the sibling must not stop carrying
-- a variable).  So the third law is provable only in the presence of the
-- first two, and the three stand or fall together — which is why the
-- earlier conjecture was reasonable and why it is nonetheless false.
--
-- WHAT THE REFUTATION LEAVES STANDING.  Everything in the other modules.
-- The word is conserved; the constant is conserved; the meaning is their
-- function; soundness follows.  What falls is only the CONVERSE — that the
-- two suffice — and it fell to a third invariant rather than to an error.
-- The corrected statement, with no conjecture attached to it: derivability
-- implies agreement on word, constant AND trapped count, and whether those
-- three suffice is §4's conjecture.
------------------------------------------------------------------------

module NaturalMachine.Baddha_TheTrappedSuccessorIsAThirdConservationLawAndItRefutesTheCompleteInvariantConjecture where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ) renaming (zero to nzero ; suc to nsuc ; _+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-zero ; snotz)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

open import Kernel.RewriteCertificate
open import NaturalMachine.Anupurvi_TheVariableWordIsInvariantSoTheKernelsSoundnessIsNotCompleteness
  using (VarName ; word ; step-preserves-word ; derivation-preserves-word)
open import NaturalMachine.Samkhyana_TheCountingSemanticsIsTheAbelianisationOfTheWordAndSoundnessIsTwoConservationLaws
  using (constPart ; step-preserves-const ; derivation-preserves-const)

------------------------------------------------------------------------
-- §1.  THE TRAPPED COUNT.
--
-- `guard w c` is `c` when the word `w` is non-empty and `nzero` otherwise:
-- a sibling that carries no variable is a sibling that may yet be deleted,
-- so it traps nothing.
------------------------------------------------------------------------

guard : List VarName → ℕ → ℕ
guard []      c = nzero
guard (_ ∷ _) c = c

trapped : Tm → ℕ
trapped var       = nzero
trapped yvar      = nzero
trapped zvar      = nzero
trapped uvar      = nzero
trapped vvar      = nzero
trapped wvar      = nzero
trapped zero      = nzero
trapped (suc t)   = trapped t
trapped (add l r) = (trapped l +ℕ trapped r) +ℕ guard (word r) (constPart l)

------------------------------------------------------------------------
-- §2.  IT IS CONSERVED — AND THE PROOF NEEDS BOTH OTHER LAWS.
------------------------------------------------------------------------

step-preserves-trapped : {a b : Tm} → Step a b → trapped a ≡ trapped b
step-preserves-trapped (add-zero t) =
  cong (_+ℕ nzero) (+-zero (trapped t)) ∙ +-zero (trapped t)
step-preserves-trapped (add-suc l r) = refl
step-preserves-trapped (suc-step p)  = step-preserves-trapped p
step-preserves-trapped (add-left {x} {y} p z) =
  cong₂ _+ℕ_
    (cong (_+ℕ trapped z) (step-preserves-trapped p))
    (cong (guard (word z)) (step-preserves-const p))
step-preserves-trapped (add-right z {x} {y} p) =
  cong₂ _+ℕ_
    (cong (trapped z +ℕ_) (step-preserves-trapped p))
    (cong (λ q → guard q (constPart z)) (step-preserves-word p))
step-preserves-trapped (reverse p) = sym (step-preserves-trapped p)

derivation-preserves-trapped : {a b : Tm} → Derivation a b → trapped a ≡ trapped b
derivation-preserves-trapped (done t)        = refl
derivation-preserves-trapped (then-step p d) =
  step-preserves-trapped p ∙ derivation-preserves-trapped d

------------------------------------------------------------------------
-- §3.  THE SEPARATED PAIR.  Same word, same constant, different trapping.
--
--   add (suc var) yvar     the successor sits in a left operand whose
--                          sibling carries a variable: trapped.
--   suc (add var yvar)     the successor is at the front: free.
------------------------------------------------------------------------

private
  A B : Tm
  A = add (suc var) yvar
  B = suc (add var yvar)

same-word     : word A ≡ word B
same-word     = refl

same-constant : constPart A ≡ constPart B
same-constant = refl

trapping-differs : trapped A ≡ nsuc nzero
trapping-differs = refl

trapping-differs' : trapped B ≡ nzero
trapping-differs' = refl

-- THE REFUTATION.
not-derivable : ¬ Derivation A B
not-derivable d = snotz (sym trapping-differs ∙ derivation-preserves-trapped d)

-- and stated as the refutation of the conjecture's shape, so that no reader
-- has to reconstruct which sentence died.
the-complete-invariant-conjecture-is-false :
  ((a b : Tm) → word a ≡ word b → constPart a ≡ constPart b → Derivation a b) → ⊥
the-complete-invariant-conjecture-is-false conj =
  not-derivable (conj A B same-word same-constant)

------------------------------------------------------------------------
-- §4.  THE THREE-LAW CONJECTURE.
------------------------------------------------------------------------

ThreeLawInvariantConjecture : Type₀
ThreeLawInvariantConjecture =
  (a b : Tm)
  → word a ≡ word b
  → constPart a ≡ constPart b
  → trapped a ≡ trapped b
  → Derivation a b
