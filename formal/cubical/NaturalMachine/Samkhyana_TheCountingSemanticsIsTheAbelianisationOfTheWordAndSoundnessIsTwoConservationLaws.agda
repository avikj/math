{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Saṃkhyāna — the counting, and exactly what it is the count OF.
--
-- TERM.  संख्यान, enumeration / reckoning; the ordinary word for counting
-- as an act, as against संख्या, the number reached.  Used here in that
-- plain sense and cited to no text: the compound is not being claimed from
-- a source, and nothing below is anyone's theorem.  (`Ankapasa_…` names the
-- same phenomenon from the other side; the two headers do not compete.)
--
-- WHAT THIS MODULE ESTABLISHES, and it finishes a triangle whose other two
-- corners are already in the corpus.
--
--   `Anupurvi_…`  the calculus preserves the left-to-right WORD of variable
--                 occurrences, so it cannot transpose two variables, so
--                 soundness is not completeness.
--   `Ankapasa_…`  the counting semantics cannot SEE a transposition: at
--                 `add var var` commutativity is a loop ℕ must call `refl`,
--                 while `ua` of the corresponding equivalence is not `refl`.
--
-- Neither says what `eval` IS in terms of the word.  This one does:
--
--   §3  `eval-decomposes` — for every term and every environment,
--
--          eval t ρ  ≡  sumWord (word t) ρ  +  constPart t ,
--
--       where `constPart` counts the `suc`s structurally.  So the meaning
--       of a term is determined by two combinatorial data and nothing else,
--       and `sumWord` reads the word only through the MULTISET of its
--       letters, because addition on ℕ is commutative.
--
--   §2  `step-preserves-const` — the constant is invariant under every
--       `Step`, exactly as the word is.
--
--   §4  `soundness-via-invariants` — therefore soundness is a COROLLARY of
--       two conservation laws, and is here re-proved without touching
--       `step-sound`.  The kernel's original proof discharges each rule
--       against `+-zero` and `+-suc`; this one observes that every rule
--       conserves a word and a constant, and that the meaning is a function
--       of those two.  Two proofs of one theorem, by different means.
--
-- THE PICTURE THE THREE MODULES MAKE, stated once:
--
--       Tm ──word──▸ List VarName ──abelianise──▸ ℕ⁶ , plus a constant
--            ▲                          ▲
--            │                          └── this is all `eval` sees
--            └── this is what every derivation conserves
--
-- The gap between what the calculus conserves and what the semantics reads
-- is exactly the quotient of the free monoid by commutativity — the
-- transpositions.  That single fact explains, at once, why derivations
-- cannot permute (`Anupurvi_…`), why the count cannot see a permutation
-- (`Ankapasa_…`), and why `add-comm` both completes the calculus toward its
-- ℕ-semantics and introduces the ℤ/2 of holonomy: it is the generator of
-- precisely that quotient.
--
--   §5  `derivable-invariants` — the forward half of a complete invariant:
--       a derivation implies equal words AND equal constants.  The converse
--       is refuted in §5.
------------------------------------------------------------------------

module NaturalMachine.Samkhyana_TheCountingSemanticsIsTheAbelianisationOfTheWordAndSoundnessIsTwoConservationLaws where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ) renaming (zero to nzero ; suc to nsuc ; _+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-assoc ; +-comm ; +-suc ; +-zero)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import Kernel.RewriteCertificate
open import NaturalMachine.Anupurvi_TheVariableWordIsInvariantSoTheKernelsSoundnessIsNotCompleteness
  using (VarName ; vx ; vy ; vz ; vu ; vv ; vw ; word ; derivation-preserves-word)

------------------------------------------------------------------------
-- §1.  THE CONSTANT.  How many successors the term carries, structurally.
------------------------------------------------------------------------

constPart : Tm → ℕ
constPart var       = nzero
constPart yvar      = nzero
constPart zvar      = nzero
constPart uvar      = nzero
constPart vvar      = nzero
constPart wvar      = nzero
constPart zero      = nzero
constPart (suc t)   = nsuc (constPart t)
constPart (add l r) = constPart l +ℕ constPart r

------------------------------------------------------------------------
-- §2.  IT IS CONSERVED, RULE BY RULE.
------------------------------------------------------------------------

step-preserves-const : {a b : Tm} → Step a b → constPart a ≡ constPart b
step-preserves-const (add-zero t)    = +-zero (constPart t)
step-preserves-const (add-suc l r)   = +-suc (constPart l) (constPart r)
step-preserves-const (suc-step p)    = cong nsuc (step-preserves-const p)
step-preserves-const (add-left p z)  = cong (_+ℕ constPart z) (step-preserves-const p)
step-preserves-const (add-right z p) = cong (constPart z +ℕ_) (step-preserves-const p)
step-preserves-const (reverse p)     = sym (step-preserves-const p)

derivation-preserves-const : {a b : Tm} → Derivation a b → constPart a ≡ constPart b
derivation-preserves-const (done t)        = refl
derivation-preserves-const (then-step p d) =
  step-preserves-const p ∙ derivation-preserves-const d

------------------------------------------------------------------------
-- §3.  THE DECOMPOSITION.  The meaning is the word plus the constant.
------------------------------------------------------------------------

open Env

lookupρ : VarName → Env → ℕ
lookupρ vx ρ = x ρ
lookupρ vy ρ = y ρ
lookupρ vz ρ = z ρ
lookupρ vu ρ = u ρ
lookupρ vv ρ = v ρ
lookupρ vw ρ = w ρ

sumWord : List VarName → Env → ℕ
sumWord []       ρ = nzero
sumWord (n ∷ ns) ρ = lookupρ n ρ +ℕ sumWord ns ρ

-- `sumWord` is a monoid map out of the free monoid.  This is the line at
-- which the word's ORDER stops mattering: concatenation goes to addition,
-- and addition is commutative.
sumWord-++ : (m n : List VarName) (ρ : Env)
           → sumWord (m ++ n) ρ ≡ sumWord m ρ +ℕ sumWord n ρ
sumWord-++ []       n ρ = refl
sumWord-++ (a ∷ m)  n ρ =
    cong (lookupρ a ρ +ℕ_) (sumWord-++ m n ρ)
  ∙ +-assoc (lookupρ a ρ) (sumWord m ρ) (sumWord n ρ)

private
  swapMid : (a b c d : ℕ) → (a +ℕ b) +ℕ (c +ℕ d) ≡ (a +ℕ c) +ℕ (b +ℕ d)
  swapMid a b c d =
      sym (+-assoc a b (c +ℕ d))
    ∙ cong (a +ℕ_) (+-assoc b c d)
    ∙ cong (λ q → a +ℕ (q +ℕ d)) (+-comm b c)
    ∙ cong (a +ℕ_) (sym (+-assoc c b d))
    ∙ +-assoc a c (b +ℕ d)

eval-decomposes : (t : Tm) (ρ : Env)
                → eval t ρ ≡ sumWord (word t) ρ +ℕ constPart t
eval-decomposes var       ρ = sym (cong (_+ℕ nzero) (+-zero (x ρ)) ∙ +-zero (x ρ))
eval-decomposes yvar      ρ = sym (cong (_+ℕ nzero) (+-zero (y ρ)) ∙ +-zero (y ρ))
eval-decomposes zvar      ρ = sym (cong (_+ℕ nzero) (+-zero (z ρ)) ∙ +-zero (z ρ))
eval-decomposes uvar      ρ = sym (cong (_+ℕ nzero) (+-zero (u ρ)) ∙ +-zero (u ρ))
eval-decomposes vvar      ρ = sym (cong (_+ℕ nzero) (+-zero (v ρ)) ∙ +-zero (v ρ))
eval-decomposes wvar      ρ = sym (cong (_+ℕ nzero) (+-zero (w ρ)) ∙ +-zero (w ρ))
eval-decomposes zero      ρ = refl
eval-decomposes (suc t)   ρ =
    cong nsuc (eval-decomposes t ρ)
  ∙ sym (+-suc (sumWord (word t) ρ) (constPart t))
eval-decomposes (add l r) ρ =
    cong₂ _+ℕ_ (eval-decomposes l ρ) (eval-decomposes r ρ)
  ∙ swapMid (sumWord (word l) ρ) (constPart l) (sumWord (word r) ρ) (constPart r)
  ∙ cong (_+ℕ (constPart l +ℕ constPart r)) (sym (sumWord-++ (word l) (word r) ρ))

------------------------------------------------------------------------
-- §4.  SOUNDNESS, RE-PROVED FROM THE TWO CONSERVATION LAWS.
--
-- `step-sound` is not used.  What is used is that a derivation conserves
-- the word and the constant, and that §3 makes the meaning a function of
-- exactly those two.
------------------------------------------------------------------------

meaning-from-invariants :
  (a b : Tm) → word a ≡ word b → constPart a ≡ constPart b
  → (ρ : Env) → eval a ρ ≡ eval b ρ
meaning-from-invariants a b pw pc ρ =
    eval-decomposes a ρ
  ∙ cong₂ _+ℕ_ (cong (λ q → sumWord q ρ) pw) pc
  ∙ sym (eval-decomposes b ρ)

soundness-via-invariants :
  {a b : Tm} → Derivation a b → (ρ : Env) → eval a ρ ≡ eval b ρ
soundness-via-invariants {a} {b} d =
  meaning-from-invariants a b
    (derivation-preserves-word d)
    (derivation-preserves-const d)

------------------------------------------------------------------------
-- §5.  THE FORWARD HALF OF A COMPLETE INVARIANT, AND THE CONVERSE.
------------------------------------------------------------------------

derivable-invariants :
  {a b : Tm} → Derivation a b → (word a ≡ word b) × (constPart a ≡ constPart b)
derivable-invariants d =
  derivation-preserves-word d , derivation-preserves-const d

-- The sharp conjecture, and it is FALSE.
-- `Baddha_…` proves a third conservation law — the count of successors
-- trapped in a left operand whose sibling carries a variable — and
-- separates `add (suc var) yvar` from `suc (add var yvar)`, which agree on
-- word and on constant.  The cause is that the calculus has no
-- associativity, so such a successor can never reach the front.  The type
-- is kept so the refutation has something to name; the sharper conjecture
-- is `Baddha_….ThreeLawInvariantConjecture`.
CompleteInvariantConjecture : Type₀
CompleteInvariantConjecture =
  (a b : Tm) → word a ≡ word b → constPart a ≡ constPart b → Derivation a b
