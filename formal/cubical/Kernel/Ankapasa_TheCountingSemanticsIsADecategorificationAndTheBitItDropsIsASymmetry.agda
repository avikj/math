{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Ankapasa_TheCountingSemanticsIsADecategorification
--                        AndTheBitItDropsIsASymmetry
--
-- TERM.  अङ्कपाश · aṅkapāśa -- "the net of digits", the traditional name for
-- the combinatorics of PERMUTATIONS: how many arrangements a given multiset
-- of digits admits, and how to enumerate them in order.  Bhskara II,
-- *Llvat*, the akapa section (~1150).
--
-- What is borrowed is the section's OBJECT: an arrangement, as distinct from the
-- count of arrangements.  §4 shows the kernel's semantics keeps the count
-- and provably cannot keep the arrangement, and that the missing datum is
-- exactly a transposition.
--
------------------------------------------------------------------------
-- THE THIRD READING OF THE SAME LINE, AND THE ONE THAT BUILDS.
--
-- `Vyapti_…` read `NativeOperation.control-sound`: the kernel memorises.
-- `Residue_⟦`   read `Kernel.RewriteCertificate.derivation-sound`: the derivation
--            carries no meaning, so all of it is remainder.
--
-- Both are one fact.  Each soundness field lands in an identity type of a
-- SET (`Tm` for control, `ℕ` for meaning), hence in a proposition, hence
-- carries zero bits.  So the diagnosis is not "the proofs are weak" but:
--
--     THE KERNEL'S SEMANTICS IS DECATEGORIFIED.
--     `eval : Tm → Env → ℕ` keeps a cardinality and drops the bijection.
--
-- This module builds the categorified semantics and measures the gap.
--
--   §1  ⟦_⟧ : Tm → TEnv → Type₀.  zero ↦ ⊥, suc ↦ Unit ⊎ −, add ↦ ⊎.
--       The six variable coordinates stay distinct, as in `Env`.
--   §2  step-equiv, derivation-equiv.  EVERY constructor of `Step` becomes
--       an EQUIVALENCE and every `Derivation` a composite of them --
--       `add-zero` the right unitor, `add-suc` a shuffle, the congruences
--       `⊎-equiv`, and `reverse` `invEquiv`.  So the kernel's existing
--       calculus already had a univalent semantics.
--   §3  Step⁺ / Derivation⁺: the calculus extended by ONE constructor,
--       `add-comm`.  It is sound for the counting semantics (`+-comm`), so
--       this is a legitimate extension of the kernel and not a rigged one.
--   §4  THE SEPARATION.  Let σ interpret `var` by `Unit`, and let
--       `comm-loop : Derivation⁺ (add var var) (add var var)` be the single
--       commutation.  Then:
--
--         counting-semantics-cannot-see-it
--           its ℕ-meaning is equal to `refl`, forced, and by `Residue_⟦` §4 NO
--           function of that meaning distinguishes it from `done⁺`;
--         univalent-semantics-does-see-it
--           its interpretation sends `inl tt` to `inr tt`, so it is not the
--           identity map;
--         comm-loop-is-a-nontrivial-loop-in-the-universe
--           and `ua` of it is not `refl` -- via `uaβ`, i.e. by the univalence
--           β-rule COMPUTING, which is the whole reason this substrate was
--           chosen.
--
--       The bit the counting semantics provably cannot hold is a
--       transposition of a two element type.  Commutativity of addition is
--       not free information: it is a ℤ/2 of holonomy, and every readout
--       valued in a set annihilates it (नय-निरोधः).
--
-- WHY THIS IS THE LANGUAGE-MODEL STATEMENT.  `install` makes a proved
-- theorem a next-move, so the operation library is a learned policy.  A
-- policy scored by a count-valued readout is scored by a decategorification,
-- and §4 exhibits the exact datum such a score cannot represent: which
-- arrangement, as opposed to how many.  Order information is not an
-- inefficiency of a bag-of-counts semantics; it is provably absent from it.
------------------------------------------------------------------------

module Kernel.Ankapasa_TheCountingSemanticsIsADecategorificationAndTheBitItDropsIsASymmetry where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; idEquiv ; invEquiv ; compEquiv)
open import Cubical.Foundations.Univalence using (ua ; uaβ)
open import Cubical.Data.Nat using (ℕ ; isSetℕ ; +-comm)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sum.Properties
  using (⊎-equiv ; ⊎-swap-≃ ; ⊎-assoc-≃ ; ⊎-IdR-⊥-≃)

open import Kernel.RewriteCertificate

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1.  THE CATEGORIFIED INTERPRETATION.
--
-- `Env` sends the six variable coordinates to numbers.  `TEnv` sends them to
-- TYPES.  Keeping all six distinct matters for the same reason it does in
-- `RewriteCertificate`: identifying them would prove things only on the
-- diagonal.
------------------------------------------------------------------------

record TEnv : Type₁ where
  constructor tenv
  field X Y Z U V W : Type₀

open TEnv

⟦_⟧ : Tm → TEnv → Type₀
⟦ var ⟧     σ = X σ
⟦ yvar ⟧    σ = Y σ
⟦ zvar ⟧    σ = Z σ
⟦ uvar ⟧    σ = U σ
⟦ vvar ⟧    σ = V σ
⟦ wvar ⟧    σ = W σ
⟦ zero ⟧    σ = ⊥
⟦ suc t ⟧   σ = Unit ⊎ ⟦ t ⟧ σ
⟦ add l r ⟧ σ = ⟦ l ⟧ σ ⊎ ⟦ r ⟧ σ

------------------------------------------------------------------------
-- §2.  EVERY STEP IS AN EQUIVALENCE.
--
-- This is the semantics the kernel's calculus always admitted.  `add-zero`
-- is the right unitor; `add-suc` is the shuffle that moves a successor out
-- of the right summand and to the front; the three congruence constructors
-- are `⊎-equiv`; and `reverse`, which in the counting semantics was `sym`,
-- is `invEquiv` -- the constructor that makes the derivation space a
-- groupoid rather than a rewriting order.
------------------------------------------------------------------------

shuffle : {A B : Type₀} → A ⊎ (Unit ⊎ B) ≃ Unit ⊎ (A ⊎ B)
shuffle {A} {B} =
  compEquiv (invEquiv ⊎-assoc-≃)
 (compEquiv (⊎-equiv ⊎-swap-≃ (idEquiv B))
            ⊎-assoc-≃)

step-equiv : {a b : Tm} → Step a b → (σ : TEnv) → ⟦ a ⟧ σ ≃ ⟦ b ⟧ σ
step-equiv (add-zero x)     σ = ⊎-IdR-⊥-≃
step-equiv (add-suc x y)    σ = shuffle
step-equiv (suc-step p)     σ = ⊎-equiv (idEquiv Unit) (step-equiv p σ)
step-equiv (add-left p z)   σ = ⊎-equiv (step-equiv p σ) (idEquiv (⟦ z ⟧ σ))
step-equiv (add-right z p)  σ = ⊎-equiv (idEquiv (⟦ z ⟧ σ)) (step-equiv p σ)
step-equiv (reverse p)      σ = invEquiv (step-equiv p σ)

derivation-equiv : {a b : Tm} → Derivation a b → (σ : TEnv) → ⟦ a ⟧ σ ≃ ⟦ b ⟧ σ
derivation-equiv (done x)        σ = idEquiv (⟦ x ⟧ σ)
derivation-equiv (then-step p d) σ = compEquiv (step-equiv p σ) (derivation-equiv d σ)

-- Univalence turns each derivation into a PATH BETWEEN TYPES, and the path
-- acts by transport.  This is the kernel's own `install`-able content, read
-- one level up.
derivation-path : {a b : Tm} → Derivation a b → (σ : TEnv) → ⟦ a ⟧ σ ≡ ⟦ b ⟧ σ
derivation-path d σ = ua (derivation-equiv d σ)

------------------------------------------------------------------------
-- §3.  ONE MORE CONSTRUCTOR, AND IT IS SOUND.
--
-- `Step` has no commutativity.  Adding it does not break the counting
-- semantics -- `+-comm` discharges it -- so this is a legitimate extension
-- of the kernel and the separation in §4 is not obtained by cheating.
------------------------------------------------------------------------

data Step⁺ : Tm → Tm → Type₀ where
  base     : {x y : Tm} → Step x y → Step⁺ x y
  add-comm : (x y : Tm) → Step⁺ (add x y) (add y x)

data Derivation⁺ : Tm → Tm → Type₀ where
  done⁺ : (x : Tm) → Derivation⁺ x x
  then⁺ : {x y z : Tm} → Step⁺ x y → Derivation⁺ y z → Derivation⁺ x z

step⁺-sound : {a b : Tm} → Step⁺ a b → (ρ : Env) → eval a ρ ≡ eval b ρ
step⁺-sound (base p)       ρ = step-sound p ρ
step⁺-sound (add-comm x y) ρ = +-comm (eval x ρ) (eval y ρ)

derivation⁺-sound : {a b : Tm} → Derivation⁺ a b → (ρ : Env) → eval a ρ ≡ eval b ρ
derivation⁺-sound (done⁺ x)     ρ = refl
derivation⁺-sound (then⁺ p d)   ρ = step⁺-sound p ρ ∙ derivation⁺-sound d ρ

step⁺-equiv : {a b : Tm} → Step⁺ a b → (σ : TEnv) → ⟦ a ⟧ σ ≃ ⟦ b ⟧ σ
step⁺-equiv (base p)       σ = step-equiv p σ
step⁺-equiv (add-comm x y) σ = ⊎-swap-≃

derivation⁺-equiv : {a b : Tm} → Derivation⁺ a b → (σ : TEnv) → ⟦ a ⟧ σ ≃ ⟦ b ⟧ σ
derivation⁺-equiv (done⁺ x)   σ = idEquiv (⟦ x ⟧ σ)
derivation⁺-equiv (then⁺ p d) σ = compEquiv (step⁺-equiv p σ) (derivation⁺-equiv d σ)

------------------------------------------------------------------------
-- §4.  THE SEPARATION.
--
-- One commutation, at a term where both summands are the same, is a LOOP:
-- its endpoints are literally the same term.  The counting semantics is
-- forced to call it `refl`.  The univalent semantics calls it a swap.
------------------------------------------------------------------------

σ₁ : TEnv
σ₁ = tenv Unit Unit Unit Unit Unit Unit

comm-loop : Derivation⁺ (add var var) (add var var)
comm-loop = then⁺ (add-comm var var) (done⁺ (add var var))

-- (a) THE COUNTING SEMANTICS IS BLIND, and it is not a matter of `eval`
-- being coarse: `eval`'s codomain is a set, so the meaning of the loop is
-- EQUAL to the meaning of doing nothing, as a term.
counting-semantics-cannot-see-it :
  (ρ : Env) → derivation⁺-sound comm-loop ρ ≡ derivation⁺-sound (done⁺ (add var var)) ρ
counting-semantics-cannot-see-it ρ =
  isSetℕ (eval (add var var) ρ) (eval (add var var) ρ) _ _

-- and therefore, by the general no-go of `Residue_⟦` §4 restated here at Step⁺,
-- no function whatsoever of the counting meaning separates them.
no-counting-criterion-separates :
  {C : Type ℓ} (φ : ((ρ : Env) → eval (add var var) ρ ≡ eval (add var var) ρ) → C)
  → φ (derivation⁺-sound comm-loop) ≡ φ (derivation⁺-sound (done⁺ (add var var)))
no-counting-criterion-separates φ = cong φ (funExt counting-semantics-cannot-see-it)

-- (b) THE UNIVALENT SEMANTICS SEES IT.  The loop moves the left copy to the
-- right; the identity does not.
swaps : equivFun (derivation⁺-equiv comm-loop σ₁) (inl tt) ≡ inr tt
swaps = refl

fixes : equivFun (derivation⁺-equiv (done⁺ (add var var)) σ₁) (inl tt) ≡ inl tt
fixes = refl

isLeft : Unit ⊎ Unit → Bool
isLeft (inl _) = true
isLeft (inr _) = false

univalent-semantics-does-see-it :
  derivation⁺-equiv comm-loop σ₁ ≡ derivation⁺-equiv (done⁺ (add var var)) σ₁ → ⊥
univalent-semantics-does-see-it p =
  true≢false (sym (cong (λ e → isLeft (equivFun e (inl tt))) p))

-- (c) AND IT IS A NONTRIVIAL LOOP IN THE UNIVERSE.  The proof runs through
-- `uaβ`: transport along `ua e` COMPUTES to `e`'s function.  That is the
-- executable half of univalence, and it is what makes this a calculation
-- rather than a citation -- the loop is not asserted to be nontrivial, it is
-- transported along and the answer comes back `inr tt`.
comm-path : ⟦ add var var ⟧ σ₁ ≡ ⟦ add var var ⟧ σ₁
comm-path = ua (derivation⁺-equiv comm-loop σ₁)

comm-loop-is-a-nontrivial-loop-in-the-universe : comm-path ≡ refl → ⊥
comm-loop-is-a-nontrivial-loop-in-the-universe p =
  true≢false (sym (cong isLeft chain))
  where
    chain : inr tt ≡ inl tt
    chain = sym (uaβ (derivation⁺-equiv comm-loop σ₁) (inl tt))
          ∙ cong (λ q → transport q (inl tt)) p
          ∙ transportRefl (inl tt)
