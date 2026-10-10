{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Install where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-zero ; +-suc)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)

-- 1 · the semantic tree, its rewrite steps, and their meaning.

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

-- 2 · a native operation: a protocol the receptor can run, carrying
--     its checked derivation and the control under which it fires.

record NativeOperation : Type₁ where
  field
    source target : Tm
    checked       : Derivation source target
    Control       : Tm → Type
    control-sound : {t : Tm} → Control t → t ≡ source

  apply : (t : Tm) → Control t → Tm
  apply _ _ = target

  apply-checked : (t : Tm) (c : Control t) → Derivation t (apply t c)
  apply-checked t c =
    subst (λ q → Derivation q target) (sym (control-sound c)) checked

-- INSTALL.  A proven derivation becomes a capability of the receptor.
install : {lhs rhs : Tm} → Derivation lhs rhs → NativeOperation
NativeOperation.source        (install {lhs} d)       = lhs
NativeOperation.target        (install {rhs = rhs} d) = rhs
NativeOperation.checked       (install d)             = d
NativeOperation.Control       (install {lhs} d) t     = t ≡ lhs
NativeOperation.control-sound (install d) c           = c

-- install forgets nothing: the derivation is read back by refl, so the
-- step that learns it is reversible and erases no input.
installForgetsNothing : {l r : Tm} (d : Derivation l r) → NativeOperation.checked (install d) ≡ d
installForgetsNothing d = refl

-- 3 · the applicability locus of an installed capability is a point:
--     capability grows by one, not by a class.

Locus : NativeOperation → Type
Locus op = Σ[ t ∈ Tm ] NativeOperation.Control op t

installLocusIsAPoint : {l r : Tm} (d : Derivation l r) → isContr (Locus (install d))
installLocusIsAPoint {l} d .fst = l , refl
installLocusIsAPoint {l} d .snd (t , p) i = p (~ i) , λ j → p (~ i ∨ j)

-- 4 · the open slot.  A receptor may demand any further evidence R
--     before firing — a receipt, a role, a signature — and whatever R
--     is, the demand can only make the operation harder to fire,
--     never fire it anywhere new.

demand : {lhs rhs : Tm} (R : Type) → Derivation lhs rhs → NativeOperation
NativeOperation.source        (demand {lhs} R d)       = lhs
NativeOperation.target        (demand {rhs = rhs} R d) = rhs
NativeOperation.checked       (demand R d)             = d
NativeOperation.Control       (demand {lhs} R d) t     = (t ≡ lhs) × R
NativeOperation.control-sound (demand R d) c           = fst c

enabledSetIsSubsingleton :
  (op : NativeOperation) {s t : Tm}
  → NativeOperation.Control op s → NativeOperation.Control op t → s ≡ t
enabledSetIsSubsingleton op cs ct =
  NativeOperation.control-sound op cs ∙ sym (NativeOperation.control-sound op ct)

anyDemandIsSafe :
  {lhs rhs : Tm} (R : Type) (d : Derivation lhs rhs) {s t : Tm}
  → NativeOperation.Control (demand R d) s
  → NativeOperation.Control (demand R d) t
  → s ≡ t
anyDemandIsSafe R d = enabledSetIsSubsingleton (demand R d)

theDemandIsReal :
  {lhs rhs : Tm} {R : Type} (d : Derivation lhs rhs) (t : Tm)
  → NativeOperation.Control (demand R d) t → R
theDemandIsReal d t c = snd c

-- 5 · nothing unproven can be installed: an operation cannot be
--     constructed without its checked derivation, so every operation
--     that exists means what it says.

everyOperationIsSound :
  (op : NativeOperation) (ρ : ℕ)
  → eval (NativeOperation.source op) ρ ≡ eval (NativeOperation.target op) ρ
everyOperationIsSound op ρ = derivation-sound (NativeOperation.checked op) ρ

-- the kernel's own first theorem, installed.
accepted : Derivation (add var (suc zero)) (suc var)
accepted =
  then-step (add-suc var zero)
    (then-step (suc-step (add-zero var)) (done (suc var)))

plusOne : NativeOperation
plusOne = install accepted
