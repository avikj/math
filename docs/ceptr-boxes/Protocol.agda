{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Protocol where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-zero ; +-suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)

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
  apply : (t : Tm) → Control t → Tm
  apply _ _ = target
  apply-checked : (t : Tm) (c : Control t) → Derivation t (apply t c)
  apply-checked t c =
    subst (λ q → Derivation q target) (sym (control-sound c)) checked

install : {lhs rhs : Tm} → Derivation lhs rhs → NativeOperation
NativeOperation.source        (install {lhs} d)       = lhs
NativeOperation.target        (install {rhs = rhs} d) = rhs
NativeOperation.checked       (install d)             = d
NativeOperation.Control       (install {lhs} d) t     = t ≡ lhs
NativeOperation.control-sound (install d) c           = c

-- 1 · the offer and the choice.  An enabled future is an operation
--     with the control that fires it here; executing it keeps only the
--     new term and the derivation that reached it — small, replayable,
--     free of who asked.  Advancing a list of futures keeps them all.

record EnabledFuture (seed : Tm) : Type₁ where
  field
    operation : NativeOperation
    control   : NativeOperation.Control operation seed
  target : Tm
  target = NativeOperation.apply operation seed control
  derivation : Derivation seed target
  derivation = NativeOperation.apply-checked operation seed control

record CheckedFuture (seed : Tm) : Type where
  field
    target     : Tm
    derivation : Derivation seed target

execute : {seed : Tm} → EnabledFuture seed → CheckedFuture seed
CheckedFuture.target     (execute f) = EnabledFuture.target f
CheckedFuture.derivation (execute f) = EnabledFuture.derivation f

-- 2 · the loop closes: what was just done becomes a capability.

learn : {s : Tm} → CheckedFuture s → NativeOperation
learn f = install (CheckedFuture.derivation f)

-- 3 · protocols compose; the composition is strict.

infixr 5 _⊕_
_⊕_ : {a b c : Tm} → Derivation a b → Derivation b c → Derivation a c
done _        ⊕ e = e
then-step p d ⊕ e = then-step p (d ⊕ e)

⊕-assoc : {a b c z : Tm} (d : Derivation a b) (e : Derivation b c) (f : Derivation c z)
  → (d ⊕ e) ⊕ f ≡ d ⊕ (e ⊕ f)
⊕-assoc (done a)        e f = refl
⊕-assoc (then-step p d) e f = cong (then-step p) (⊕-assoc d e f)

-- 4 · a session: where it began, where it stands, the whole transcript,
--     and what it has learned.  One turn advances all four together.

record Session : Type₁ where
  constructor session
  field
    origin  : Tm
    here    : Tm
    trace   : Derivation origin here
    library : List NativeOperation
open Session

begin : Tm → Session
begin t = session t t (done t) []

turn : (S : Session) → EnabledFuture (here S) → Session
turn S f = session (origin S) (EnabledFuture.target f)
                   (trace S ⊕ EnabledFuture.derivation f)
                   (learn (execute f) ∷ library S)

turnGrowsTheLibrary :
  (S : Session) (f : EnabledFuture (here S))
  → length (library (turn S f)) ≡ suc (length (library S))
turnGrowsTheLibrary S f = refl

-- 5 · THE RETIREMENT.  The whole conversation is one theorem, hence one
--     protocol the receptor can thereafter run in a single step, and
--     that protocol means what the conversation meant.

sessionSound : (S : Session) (ρ : ℕ) → eval (origin S) ρ ≡ eval (here S) ρ
sessionSound S ρ = derivation-sound (trace S) ρ

retire : Session → NativeOperation
retire S = install (trace S)

retireSpansTheSession :
  (S : Session)
  → (NativeOperation.source (retire S) ≡ origin S)
  × (NativeOperation.target (retire S) ≡ here S)
retireSpansTheSession S = refl , refl

retireIsSound :
  (S : Session) (ρ : ℕ)
  → eval (NativeOperation.source (retire S)) ρ ≡ eval (NativeOperation.target (retire S)) ρ
retireIsSound S = sessionSound S

-- 6 · THE TEMPLATE WITH A SLOT.  An installed operation fires at one
--     term.  A schema is a template whose control carries the filler
--     of its slot, and it fires at every instance — soundly, for free,
--     because the meaning already held at every environment.

subVar : Tm → Tm → Tm
subVar u var       = u
subVar u zero      = zero
subVar u (suc t)   = suc (subVar u t)
subVar u (add l r) = add (subVar u l) (subVar u r)

eval-subVar : (u body : Tm) (ρ : ℕ) → eval (subVar u body) ρ ≡ eval body (eval u ρ)
eval-subVar u var       ρ = refl
eval-subVar u zero      ρ = refl
eval-subVar u (suc b)   ρ = cong suc (eval-subVar u b ρ)
eval-subVar u (add l r) ρ = cong₂ _+_ (eval-subVar u l ρ) (eval-subVar u r ρ)

record Schema : Type where
  field
    lhs rhs : Tm
    meaning : (ρ : ℕ) → eval lhs ρ ≡ eval rhs ρ

  Slot : Tm → Type
  Slot t = Σ[ u ∈ Tm ] (t ≡ subVar u lhs)

  instantiate : (t : Tm) → Slot t → Tm
  instantiate _ (u , _) = subVar u rhs

  instantiateSound : (t : Tm) (c : Slot t) (ρ : ℕ) → eval t ρ ≡ eval (instantiate t c) ρ
  instantiateSound t (u , p) ρ =
      cong (λ q → eval q ρ) p
    ∙ eval-subVar u lhs ρ
    ∙ meaning (eval u ρ)
    ∙ sym (eval-subVar u rhs ρ)

accepted : Derivation (add var (suc zero)) (suc var)
accepted =
  then-step (add-suc var zero)
    (then-step (suc-step (add-zero var)) (done (suc var)))

plusOneSchema : Schema
Schema.lhs     plusOneSchema = add var (suc zero)
Schema.rhs     plusOneSchema = suc var
Schema.meaning plusOneSchema = derivation-sound accepted

-- one template, two contexts
ctx₀ ctx₁ : Tm
ctx₀ = add zero (suc zero)
ctx₁ = add (suc zero) (suc zero)

ctx₀-filled : Schema.Slot plusOneSchema ctx₀
ctx₀-filled = zero , refl

ctx₁-filled : Schema.Slot plusOneSchema ctx₁
ctx₁-filled = suc zero , refl

leftIsZero : Tm → Bool
leftIsZero (add zero _) = true
leftIsZero _            = false

ctx₀≢ctx₁ : ctx₀ ≡ ctx₁ → ⊥
ctx₀≢ctx₁ p = true≢false (cong leftIsZero p)

-- and no installed operation whatsoever fires at both: the slot is what
-- the template has and the instance lacks.
noOperationFiresAtBoth :
  (op : NativeOperation)
  → NativeOperation.Control op ctx₀ → NativeOperation.Control op ctx₁ → ⊥
noOperationFiresAtBoth op c₀ c₁ =
  ctx₀≢ctx₁ (NativeOperation.control-sound op c₀ ∙ sym (NativeOperation.control-sound op c₁))
