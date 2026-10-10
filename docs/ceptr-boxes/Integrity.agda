{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Integrity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-zero ; +-suc ; isSetℕ ; znots ; injSuc)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr) renaming (rec to ⊎rec)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁)

-- the kernel again, so this box checks on its own.
data Tm : Type where
  var zero : Tm
  suc  : Tm → Tm
  add  : Tm → Tm → Tm

data Step : Tm → Tm → Type where
  add-zero  : (x : Tm) → Step (add x zero) x
  add-suc   : (x y : Tm) → Step (add x (suc y)) (suc (add x y))
  suc-step  : {x y : Tm} → Step x y → Step (suc x) (suc y)
  reverse   : {x y : Tm} → Step x y → Step y x

data Derivation : Tm → Tm → Type where
  done      : (x : Tm) → Derivation x x
  then-step : {x y z : Tm} → Step x y → Derivation y z → Derivation x z

eval : Tm → ℕ → ℕ
eval var       ρ = ρ
eval zero      ρ = 0
eval (suc t)   ρ = suc (eval t ρ)
eval (add l r) ρ = eval l ρ + eval r ρ

step-sound : {a b : Tm} → Step a b → (ρ : ℕ) → eval a ρ ≡ eval b ρ
step-sound (add-zero t)    ρ = +-zero (eval t ρ)
step-sound (add-suc l r)   ρ = +-suc (eval l ρ) (eval r ρ)
step-sound (suc-step p)    ρ = cong suc (step-sound p ρ)
step-sound (reverse p)     ρ = sym (step-sound p ρ)

derivation-sound : {a b : Tm} → Derivation a b → (ρ : ℕ) → eval a ρ ≡ eval b ρ
derivation-sound (done t)        ρ = refl
derivation-sound (then-step p d) ρ = step-sound p ρ ∙ derivation-sound d ρ

record NativeOperation : Type₁ where
  field
    source target : Tm
    checked       : Derivation source target
    Control       : Tm → Type
    control-sound : {t : Tm} → Control t → t ≡ source

-- 1 · the chain.  Entries concatenate, and every entry reverses: a
--     round trip is invisible to the meaning.

infixr 5 _⊕_
_⊕_ : {a b c : Tm} → Derivation a b → Derivation b c → Derivation a c
done _        ⊕ e = e
then-step p d ⊕ e = then-step p (d ⊕ e)

rev : {a b : Tm} → Derivation a b → Derivation b a
rev (done a)                = done a
rev (then-step {x = x} p d) = rev d ⊕ then-step (reverse p) (done x)

roundTripIsTheIdentity :
  {a b : Tm} (d : Derivation a b) (ρ : ℕ) → derivation-sound (d ⊕ rev d) ρ ≡ refl
roundTripIsTheIdentity {a} d ρ = isSetℕ (eval a ρ) (eval a ρ) _ _

-- 2 · THE VERDICT.  The meaning of an entry lives in an identity type of ℕ,
--     a proposition: two validators of one entry reach EQUAL verdicts,
--     as terms.  There is nothing to vote on.

twoNodesCannotDisagree :
  {a b : Tm} (d e : Derivation a b) (ρ : ℕ)
  → derivation-sound d ρ ≡ derivation-sound e ρ
twoNodesCannotDisagree {a} {b} d e ρ = isSetℕ (eval a ρ) (eval b ρ) _ _

-- and the semantics never needed the entry, only that one exists.
soundnessFactorsThroughExistence :
  {a b : Tm} (ρ : ℕ) → ∥ Derivation a b ∥₁ → eval a ρ ≡ eval b ρ
soundnessFactorsThroughExistence {a} {b} ρ =
  PT.rec (isSetℕ (eval a ρ) (eval b ρ)) (λ d → derivation-sound d ρ)
  where import Cubical.HITs.PropositionalTruncation as PT

-- 3 · intrinsic integrity.  An operation cannot be constructed without
--     its checked derivation, so validity travels with the operation:
--     there is nothing for access control to protect and nothing for
--     a merge to verify.

everyOperationIsSound :
  (op : NativeOperation) (ρ : ℕ)
  → eval (NativeOperation.source op) ρ ≡ eval (NativeOperation.target op) ρ
everyOperationIsSound op ρ = derivation-sound (NativeOperation.checked op) ρ

-- 4 · the join.  A library is a list; merging is concatenation, total,
--     with no failure mode; and what a merge enables is exactly the
--     union — order-independent, idempotent, grow-only.

Library : Type₁
Library = List NativeOperation

Enabled : Library → Tm → Type
Enabled []       t = ⊥
Enabled (op ∷ L) t = NativeOperation.Control op t ⊎ Enabled L t

merge : Library → Library → Library
merge = _++_

keepsTheLeft : (L M : Library) (t : Tm) → Enabled L t → Enabled (merge L M) t
keepsTheLeft []       M t e       = Empty.rec e
keepsTheLeft (op ∷ L) M t (inl c) = inl c
keepsTheLeft (op ∷ L) M t (inr s) = inr (keepsTheLeft L M t s)

keepsTheRight : (L M : Library) (t : Tm) → Enabled M t → Enabled (merge L M) t
keepsTheRight []       M t e = e
keepsTheRight (op ∷ L) M t e = inr (keepsTheRight L M t e)

inventsNothing : (L M : Library) (t : Tm) → Enabled (merge L M) t → Enabled L t ⊎ Enabled M t
inventsNothing []       M t e       = inr e
inventsNothing (op ∷ L) M t (inl c) = inl (inl c)
inventsNothing (op ∷ L) M t (inr s) = ⊎rec (λ x → inl (inr x)) inr (inventsNothing L M t s)

mergeIsOrderIndependent :
  (L M : Library) (t : Tm) → Enabled (merge L M) t → Enabled (merge M L) t
mergeIsOrderIndependent L M t e =
  ⊎rec (keepsTheRight M L t) (keepsTheLeft M L t) (inventsNothing L M t e)

mergeIsIdempotent : (L : Library) (t : Tm) → Enabled (merge L L) t → Enabled L t
mergeIsIdempotent L t e = ⊎rec (λ x → x) (λ x → x) (inventsNothing L L t e)

-- 5 · THE FORK.  What two nodes genuinely differ on is the route, and
--     the route is kept.  Two entries of one fact, lengths 2 and 4;
--     the meaning identifies them, and no function of the meaning
--     recovers their cost.

len : {a b : Tm} → Derivation a b → ℕ
len (done _)        = zero
len (then-step _ d) = suc (len d)

direct detour : Derivation (add var (suc zero)) (suc var)
direct =
  then-step (add-suc var zero) (then-step (suc-step (add-zero var)) (done (suc var)))
detour =
  then-step (add-suc var zero)
    (then-step (reverse (add-suc var zero))
      (then-step (add-suc var zero)
        (then-step (suc-step (add-zero var)) (done (suc var)))))

two≢four : suc (suc zero) ≡ suc (suc (suc (suc zero))) → ⊥
two≢four p = znots (injSuc (injSuc p))

routesGenuinelyDiffer : ¬ direct ≡ detour
routesGenuinelyDiffer p = two≢four (cong len p)

meaningsAreEqual : (ρ : ℕ) → derivation-sound direct ρ ≡ derivation-sound detour ρ
meaningsAreEqual = twoNodesCannotDisagree direct detour

costDoesNotFactor :
  ¬ (Σ[ g ∈ (∥ Derivation (add var (suc zero)) (suc var) ∥₁ → ℕ) ]
       ((d : Derivation (add var (suc zero)) (suc var)) → g ∣ d ∣₁ ≡ len d))
costDoesNotFactor (g , agrees) =
  two≢four (sym (agrees direct) ∙ cong g (squash₁ ∣ direct ∣₁ ∣ detour ∣₁) ∙ agrees detour)

-- 6 · a warrant.  An invalid entry is not an entry anyone must be
--     stopped from writing; it is a type with no inhabitant, and the
--     refutation is a term one node computes alone and every node can
--     re-run.

warrant : ¬ Derivation zero (suc zero)
warrant d = znots (derivation-sound d 0)
