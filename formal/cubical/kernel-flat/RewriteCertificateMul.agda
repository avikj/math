{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- The certificate language, widened to multiplication.
--
-- WHY THIS IS A SEPARATE MODULE.  `RewriteCertificate` is
-- the live soundness perimeter of the Haskell gate: `MathMachine.hs` (absent from this repository) →
-- `Certificate.hs` (absent from this repository) → (S1) `InductionSearch.hs` (absent from this repository) emit modules that import it,
-- and `induction-sound` there is the semantic warrant for installing a
-- rewrite rule.  `Tm` is a closed datatype,
-- so a constructor cannot be added from outside; the only conservative move
-- is to MIRROR the module with the constructor added, and then to PROVE the
-- mirroring is conservative rather than to assert it.  That is what §6 does:
-- an embedding `embed : A.Tm → Tm` which
--
--   * commutes with evaluation           (`embed-eval`),
--   * carries every additive Step, Derivation, HypStep, HypDerivation and
--     InductionCertificate to one of the same shape here
--     (`embed-step` … `embed-certificate`).
--
-- Consequence, and the reason it is worth the lines: every certificate the
-- additive kernel ever accepted is accepted here with the same meaning, so
-- widening the language cannot retroactively unsay anything the machine has
-- already installed.  S2's boot replay does not have to re-litigate the
-- library across a language epoch change; only S3's `mUnspeakable` entries
-- (things the kernel could NOT say) are the ones the widening reopens.
--
-- EVERY NAME HERE MATCHES ITS ADDITIVE COUNTERPART EXACTLY.  That is a
-- deliberate interface constraint, not an accident: the Haskell renderer
-- (`renderModuleNamed`, S1.0) then differs by one import string plus the
-- new constructors, so the S1 extraction stays valid.
--
-- WHY MULTIPLICATION FIRST.  Its two defining equations are already in
-- `MathMachine.vocabulary`'s `symDefs` —
--
--     x * 0     = 0                x * s(y)  = (x * y) + x
--
-- — and both are already checked against ℕ in
-- `HaskellDefinitionBoundary` (`haskell-mul-zero`,
-- `haskell-mul-suc`).  So `mul-zero`/`mul-suc` below introduce NO new
-- trusted input: they are the machine's own axioms, re-indexed by their
-- endpoints.  `mod`, `div`, `Omega`, `omega`, `musq` — the demands standing
-- in `machine/thoughts.math` (absent from this repository) — have no `symSem` and no `symDefs` at all;
-- each would be a new trusted input, and each is strictly downstream of a
-- comparison/remainder primitive.  See `machine/patches/S4-certificate-
-- vocabulary.md` (absent from this repository) §3 for the dependency chain.
--
-- SCOPE FENCE ON THE LIBRARY LEMMAS.  `+-comm`, `0≡m·0` and `·-suc` are
-- imported and used ONLY in `step-sound`, i.e. only to interpret the
-- calculus in ℕ.  They are NOT steps of the calculus: `Step` has no
-- commutation constructor, so an emitted certificate still cannot cite
-- them.  This is exactly the boundary `machine/CERTIFICATE_REACH.md` (absent from this repository) §2
-- insists on — the engine's contribution must not collapse from proof to
-- discovery because the library already knew the theorem.
------------------------------------------------------------------------

module RewriteCertificateMul where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-zero ; +-suc ; +-comm ; 0≡m·0 ; ·-suc)

import Kernel.RewriteCertificate as A

------------------------------------------------------------------------
-- 1. Syntax
------------------------------------------------------------------------

data Tm : Type₀ where
  var yvar zvar uvar vvar wvar : Tm
  zero : Tm
  suc  : Tm → Tm
  add  : Tm → Tm → Tm
  mul  : Tm → Tm → Tm

-- The step calculus.  `mul-zero`/`mul-suc` are MathMachine's `symDefs` for
-- `*`, oriented left-to-right exactly as its LPO orients them (precedence
-- `* > + > s > 0`, positional in `vocabulary`); `mul-left`/`mul-right` are
-- the congruence closure, matching the `add-left`/`add-right` pattern
-- argument for argument; `reverse` supplies the other direction, so the
-- calculus is a congruence, not a reduction relation, and termination of
-- SEARCH is the bounded BFS's job rather than the orientation's.
data Step : Tm → Tm → Type₀ where
  add-zero : (x : Tm) → Step (add x zero) x
  add-suc  : (x y : Tm) → Step (add x (suc y)) (suc (add x y))
  mul-zero : (x : Tm) → Step (mul x zero) zero
  mul-suc  : (x y : Tm) → Step (mul x (suc y)) (add (mul x y) x)
  suc-step : {x y : Tm} → Step x y → Step (suc x) (suc y)
  add-left : {x y : Tm} → Step x y → (z : Tm) → Step (add x z) (add y z)
  add-right : (z : Tm) → {x y : Tm} → Step x y → Step (add z x) (add z y)
  mul-left : {x y : Tm} → Step x y → (z : Tm) → Step (mul x z) (mul y z)
  mul-right : (z : Tm) → {x y : Tm} → Step x y → Step (mul z x) (mul z y)
  reverse : {x y : Tm} → Step x y → Step y x

data Derivation : Tm → Tm → Type₀ where
  done : (x : Tm) → Derivation x x
  then-step : {x y z : Tm} → Step x y → Derivation y z → Derivation x z

subVar : Tm → Tm → Tm
subVar u var = u
subVar u yvar = yvar
subVar u zvar = zvar
subVar u uvar = uvar
subVar u vvar = vvar
subVar u wvar = wvar
subVar u zero = zero
subVar u (suc t) = suc (subVar u t)
subVar u (add l r) = add (subVar u l) (subVar u r)
subVar u (mul l r) = mul (subVar u l) (subVar u r)

-- A rewrite system parameterized by exactly one induction hypothesis.
-- The hypothesis is conclusion-indexed and may be used under contexts.
data HypStep (ihL ihR : Tm) : Tm → Tm → Type₀ where
  lift-step : {x y : Tm} → Step x y → HypStep ihL ihR x y
  hypothesis : HypStep ihL ihR ihL ihR
  reverse-hypothesis : HypStep ihL ihR ihR ihL
  hyp-suc : {x y : Tm} → HypStep ihL ihR x y
          → HypStep ihL ihR (suc x) (suc y)
  hyp-add-left : {x y : Tm} → HypStep ihL ihR x y → (z : Tm)
               → HypStep ihL ihR (add x z) (add y z)
  hyp-add-right : (z : Tm) → {x y : Tm} → HypStep ihL ihR x y
                → HypStep ihL ihR (add z x) (add z y)
  hyp-mul-left : {x y : Tm} → HypStep ihL ihR x y → (z : Tm)
               → HypStep ihL ihR (mul x z) (mul y z)
  hyp-mul-right : (z : Tm) → {x y : Tm} → HypStep ihL ihR x y
                → HypStep ihL ihR (mul z x) (mul z y)

data HypDerivation (ihL ihR : Tm) : Tm → Tm → Type₀ where
  hyp-done : (x : Tm) → HypDerivation ihL ihR x x
  hyp-then : {x y z : Tm} → HypStep ihL ihR x y
           → HypDerivation ihL ihR y z → HypDerivation ihL ihR x z

record InductionCertificate (lhs rhs : Tm) : Type₀ where
  field
    base : Derivation (subVar zero lhs) (subVar zero rhs)
    step : HypDerivation lhs rhs
      (subVar (suc var) lhs) (subVar (suc var) rhs)

------------------------------------------------------------------------
-- 2. Semantics
------------------------------------------------------------------------

-- The executable meaning of the syntax.  `var` is interpreted by one
-- environment; the remaining constructors are the actual natural zero,
-- successor, addition, and multiplication.  Keeping all six coordinates
-- distinct matters: identifying them would prove only equality on the
-- diagonal.
record Env : Type₀ where
  constructor env
  field x y z u v w : ℕ

open Env

eval : Tm → Env → ℕ
eval var       ρ = x ρ
eval yvar      ρ = y ρ
eval zvar      ρ = z ρ
eval uvar      ρ = u ρ
eval vvar      ρ = v ρ
eval wvar      ρ = w ρ
eval zero      ρ = 0
eval (suc t)   ρ = suc (eval t ρ)
eval (add l r) ρ = eval l ρ + eval r ρ
eval (mul l r) ρ = eval l ρ · eval r ρ

------------------------------------------------------------------------
-- 3. Soundness
--
-- Every certificate step preserves that meaning.  Therefore the Haskell
-- gate cannot install a rule merely because it inhabits an uninterpreted
-- rewrite calculus: its exact checked endpoints are pointwise equal on ℕ.
--
-- The two multiplicative base cases are the only place the argument-order
-- mismatch of `machine/CERTIFICATE_REACH.md` (absent from this repository) §1 is paid for.  Cubical's
-- `_·_` recurses on its FIRST argument and states its laws as `0 ≡ m · 0`
-- and `m · suc n ≡ m + m · n`; MathMachine's `*` recurses on its SECOND and
-- writes `x * 0 = 0`, `x * s y = x * y + x`.  The whole cost of that is one
-- `sym` and one `∙ +-comm`, and it is paid here, once, in the perimeter —
-- never inside a certificate.  (These are `haskell-mul-zero` and
-- `haskell-mul-suc` of `HaskellDefinitionBoundary`, reused
-- pointwise rather than re-derived.)
------------------------------------------------------------------------

step-sound : {a b : Tm} → Step a b → (ρ : Env) → eval a ρ ≡ eval b ρ
step-sound (add-zero t)    ρ = +-zero (eval t ρ)
step-sound (add-suc l r)   ρ = +-suc (eval l ρ) (eval r ρ)
step-sound (mul-zero t)    ρ = sym (0≡m·0 (eval t ρ))
step-sound (mul-suc l r)   ρ =
  ·-suc (eval l ρ) (eval r ρ) ∙ +-comm (eval l ρ) (eval l ρ · eval r ρ)
step-sound (suc-step p)    ρ = cong suc (step-sound p ρ)
step-sound (add-left p t)  ρ = cong (_+ eval t ρ) (step-sound p ρ)
step-sound (add-right t p) ρ = cong (eval t ρ +_) (step-sound p ρ)
step-sound (mul-left p t)  ρ = cong (_· eval t ρ) (step-sound p ρ)
step-sound (mul-right t p) ρ = cong (eval t ρ ·_) (step-sound p ρ)
step-sound (reverse p)     ρ = sym (step-sound p ρ)

derivation-sound : {a b : Tm} → Derivation a b → (ρ : Env) → eval a ρ ≡ eval b ρ
derivation-sound (done t)        ρ = refl
derivation-sound (then-step p d) ρ = step-sound p ρ ∙ derivation-sound d ρ

setX : ℕ → Env → Env
setX n ρ = env n (y ρ) (z ρ) (u ρ) (v ρ) (w ρ)

eval-subVar : (t body : Tm) (ρ : Env) →
  eval (subVar t body) ρ ≡ eval body (setX (eval t ρ) ρ)
eval-subVar t var       ρ = refl
eval-subVar t yvar      ρ = refl
eval-subVar t zvar      ρ = refl
eval-subVar t uvar      ρ = refl
eval-subVar t vvar      ρ = refl
eval-subVar t wvar      ρ = refl
eval-subVar t zero      ρ = refl
eval-subVar t (suc b)   ρ = cong suc (eval-subVar t b ρ)
eval-subVar t (add l r) ρ = cong₂ _+_ (eval-subVar t l ρ) (eval-subVar t r ρ)
eval-subVar t (mul l r) ρ = cong₂ _·_ (eval-subVar t l ρ) (eval-subVar t r ρ)

hyp-step-sound : {ihL ihR a b : Tm} → HypStep ihL ihR a b →
  (ρ : Env) → eval ihL ρ ≡ eval ihR ρ → eval a ρ ≡ eval b ρ
hyp-step-sound (lift-step p)          ρ ih = step-sound p ρ
hyp-step-sound hypothesis             ρ ih = ih
hyp-step-sound reverse-hypothesis     ρ ih = sym ih
hyp-step-sound (hyp-suc p)            ρ ih = cong suc (hyp-step-sound p ρ ih)
hyp-step-sound (hyp-add-left p t)     ρ ih =
  cong (_+ eval t ρ) (hyp-step-sound p ρ ih)
hyp-step-sound (hyp-add-right t p)    ρ ih =
  cong (eval t ρ +_) (hyp-step-sound p ρ ih)
hyp-step-sound (hyp-mul-left p t)     ρ ih =
  cong (_· eval t ρ) (hyp-step-sound p ρ ih)
hyp-step-sound (hyp-mul-right t p)    ρ ih =
  cong (eval t ρ ·_) (hyp-step-sound p ρ ih)

hyp-derivation-sound : {ihL ihR a b : Tm} → HypDerivation ihL ihR a b →
  (ρ : Env) → eval ihL ρ ≡ eval ihR ρ → eval a ρ ≡ eval b ρ
hyp-derivation-sound (hyp-done t)     ρ ih = refl
hyp-derivation-sound (hyp-then p d)   ρ ih =
  hyp-step-sound p ρ ih ∙ hyp-derivation-sound d ρ ih

-- A checked base trace and checked successor trace, with the hypothesis
-- available only at the predecessor, entail the advertised equation for
-- every environment.  This is the semantic reason an accepted induction
-- certificate may become an executable rewrite rule.
induction-sound : {lhs rhs : Tm} → InductionCertificate lhs rhs →
  (ρ : Env) → eval lhs ρ ≡ eval rhs ρ
induction-sound {lhs} {rhs} cert (env n y₀ z₀ u₀ v₀ w₀) = go n
  where
  ρ : ℕ → Env
  ρ k = env k y₀ z₀ u₀ v₀ w₀

  go : (k : ℕ) → eval lhs (ρ k) ≡ eval rhs (ρ k)
  go zero =
    sym (eval-subVar zero lhs (ρ zero))
    ∙ derivation-sound (InductionCertificate.base cert) (ρ zero)
    ∙ eval-subVar zero rhs (ρ zero)
  go (suc k) =
    sym (eval-subVar (suc var) lhs (ρ k))
    ∙ hyp-derivation-sound (InductionCertificate.step cert) (ρ k) (go k)
    ∙ eval-subVar (suc var) rhs (ρ k)

------------------------------------------------------------------------
-- 4. The additive certificate, re-checked in the wider language
--
-- The old worked example still closes, constructor for constructor.  This
-- is the cheap half of conservativity; §6 proves the general statement.
------------------------------------------------------------------------

accepted : Derivation (add var (suc zero)) (suc var)
accepted =
  then-step (add-suc var zero)
    (then-step (suc-step (add-zero var)) (done (suc var)))

accepted-sound : (ρ : Env) → eval (add var (suc zero)) ρ ≡ eval (suc var) ρ
accepted-sound = derivation-sound accepted

------------------------------------------------------------------------
-- 5. What the widening actually closes
--
-- 5a.  A ground multiplicative computation, no induction: 1 * 1 = 1.
--      Not deep, but it is the smallest witness that `mul-zero`/`mul-suc`
--      and the add-rules interlock rather than merely coexist.
------------------------------------------------------------------------

-- 1 * 1 → 1 * 0 + 1 → 0 + 1 → s (0 + 0) → s 0.
-- Note the second move: the redex `mul (s 0) 0` sits in the LEFT argument
-- of an `add`, so the congruence that carries it is `add-left`.  Getting
-- this wrong is the standing hazard of a two-operator congruence calculus,
-- and it is exactly what the indexing catches.
one-times-one : Derivation (mul (suc zero) (suc zero)) (suc zero)
one-times-one =
  then-step (mul-suc (suc zero) zero)
  (then-step (add-left (mul-zero (suc zero)) (suc zero))
  (then-step (add-suc zero zero)
  (then-step (suc-step (add-zero zero))
    (done (suc zero)))))

one-times-one-sound :
  (ρ : Env) → eval (mul (suc zero) (suc zero)) ρ ≡ eval (suc zero) ρ
one-times-one-sound = derivation-sound one-times-one

------------------------------------------------------------------------
-- 5b.  x * 1 = x, as a full induction certificate.
--
-- THIS IS THE LOAD-BEARING EXAMPLE, and it is worth saying why it is not
-- trivial.  In MathMachine's orientation `*` recurses on the right, so
--
--     x * 1  =  x * s 0  →  x * 0 + x  →  0 + x
--
-- and `0 + x` is IRREDUCIBLE in this calculus: `add-zero` strips a zero on
-- the RIGHT (`x + 0 → x`), and `add-suc` needs a successor on the right.
-- Left-identity of `+` is itself an induction here.  So `x * 1 = x` cannot
-- be closed by any single-step skeleton; the successor branch has to run a
-- SIX-step trace which (i) uses `mul-zero` forwards, (ii) uses `mul-zero`
-- and `mul-suc` BACKWARDS to refold `0 + x` into `x * 1`, and (iii) applies
-- the induction hypothesis under a `suc` context.
--
-- That is precisely the class `Certificate.hs` (absent from this repository)'s eleven-shape skeleton
-- (`refl`, `ih`, `cong suc`, `cong (_+ k)`, …) cannot express.
-- The additive calculus
-- could not state this theorem at all.
------------------------------------------------------------------------

x-times-one : InductionCertificate (mul var (suc zero)) var
x-times-one = record
  { base =
      -- 0 * 1 → 0 * 0 + 0 → 0 + 0 → 0
      then-step (mul-suc zero zero)
      (then-step (add-left (mul-zero zero) zero)
      (then-step (add-zero zero)
        (done zero)))
  ; step =
      -- s x * 1 → s x * 0 + s x → 0 + s x → s (0 + x)
      --         → s (x * 0 + x) → s (x * 1) → s x
      hyp-then (lift-step (mul-suc (suc var) zero))
      (hyp-then (lift-step (add-left (mul-zero (suc var)) (suc var)))
      (hyp-then (lift-step (add-suc zero var))
      (hyp-then (hyp-suc (lift-step (reverse (add-left (mul-zero var) var))))
      (hyp-then (hyp-suc (lift-step (reverse (mul-suc var zero))))
      (hyp-then (hyp-suc hypothesis)
        (hyp-done (suc var)))))))
  }

-- The advertised equation, for every environment.  `x · 1 ≡ x` is now a
-- theorem OF THE MACHINE'S CALCULUS, obtained from the machine's own two
-- defining equations for `*` by a checked trace — not cited from
-- `Cubical.Data.Nat.Properties`.
x-times-one-sound :
  (ρ : Env) → eval (mul var (suc zero)) ρ ≡ eval var ρ
x-times-one-sound = induction-sound x-times-one

------------------------------------------------------------------------
-- 6. Conservativity, proved
--
-- `embed` is the inclusion of the additive language.  Everything below is
-- structural; the content is the statement, not the proofs.
------------------------------------------------------------------------

embed : A.Tm → Tm
embed A.var  = var
embed A.yvar = yvar
embed A.zvar = zvar
embed A.uvar = uvar
embed A.vvar = vvar
embed A.wvar = wvar
embed A.zero = zero
embed (A.suc t)   = suc (embed t)
embed (A.add l r) = add (embed l) (embed r)

toBase : Env → A.Env
toBase ρ = A.env (x ρ) (y ρ) (z ρ) (u ρ) (v ρ) (w ρ)

-- Meaning is preserved: the widening adds vocabulary, not reinterpretation.
embed-eval : (t : A.Tm) (ρ : Env) → eval (embed t) ρ ≡ A.eval t (toBase ρ)
embed-eval A.var  ρ = refl
embed-eval A.yvar ρ = refl
embed-eval A.zvar ρ = refl
embed-eval A.uvar ρ = refl
embed-eval A.vvar ρ = refl
embed-eval A.wvar ρ = refl
embed-eval A.zero ρ = refl
embed-eval (A.suc t)   ρ = cong suc (embed-eval t ρ)
embed-eval (A.add l r) ρ = cong₂ _+_ (embed-eval l ρ) (embed-eval r ρ)

embed-step : {a b : A.Tm} → A.Step a b → Step (embed a) (embed b)
embed-step (A.add-zero t)    = add-zero (embed t)
embed-step (A.add-suc l r)   = add-suc (embed l) (embed r)
embed-step (A.suc-step p)    = suc-step (embed-step p)
embed-step (A.add-left p t)  = add-left (embed-step p) (embed t)
embed-step (A.add-right t p) = add-right (embed t) (embed-step p)
embed-step (A.reverse p)     = reverse (embed-step p)

embed-derivation : {a b : A.Tm} → A.Derivation a b
                 → Derivation (embed a) (embed b)
embed-derivation (A.done t)          = done (embed t)
embed-derivation (A.then-step p d)   = then-step (embed-step p) (embed-derivation d)

embed-hyp-step : {ihL ihR a b : A.Tm} → A.HypStep ihL ihR a b
               → HypStep (embed ihL) (embed ihR) (embed a) (embed b)
embed-hyp-step (A.lift-step p)          = lift-step (embed-step p)
embed-hyp-step A.hypothesis             = hypothesis
embed-hyp-step A.reverse-hypothesis     = reverse-hypothesis
embed-hyp-step (A.hyp-suc p)            = hyp-suc (embed-hyp-step p)
embed-hyp-step (A.hyp-add-left p t)     = hyp-add-left (embed-hyp-step p) (embed t)
embed-hyp-step (A.hyp-add-right t p)    = hyp-add-right (embed t) (embed-hyp-step p)

embed-hyp-derivation : {ihL ihR a b : A.Tm} → A.HypDerivation ihL ihR a b
                     → HypDerivation (embed ihL) (embed ihR) (embed a) (embed b)
embed-hyp-derivation (A.hyp-done t)   = hyp-done (embed t)
embed-hyp-derivation (A.hyp-then p d) =
  hyp-then (embed-hyp-step p) (embed-hyp-derivation d)

embed-subVar : (u t : A.Tm) → embed (A.subVar u t) ≡ subVar (embed u) (embed t)
embed-subVar u A.var  = refl
embed-subVar u A.yvar = refl
embed-subVar u A.zvar = refl
embed-subVar u A.uvar = refl
embed-subVar u A.vvar = refl
embed-subVar u A.wvar = refl
embed-subVar u A.zero = refl
embed-subVar u (A.suc t)   = cong suc (embed-subVar u t)
embed-subVar u (A.add l r) = cong₂ add (embed-subVar u l) (embed-subVar u r)

-- THE CONSERVATIVITY STATEMENT.  Every induction certificate the additive
-- kernel accepts is an induction certificate here, over the embedded
-- endpoints.  Nothing already installed can be unsaid by the widening; only
-- the REJECTIONS (S3's `mUnspeakable`) are reopened by it.
embed-certificate : {lhs rhs : A.Tm} → A.InductionCertificate lhs rhs
                  → InductionCertificate (embed lhs) (embed rhs)
embed-certificate {lhs} {rhs} cert = record
  { base =
      subst2 Derivation
        (embed-subVar A.zero lhs) (embed-subVar A.zero rhs)
        (embed-derivation (A.InductionCertificate.base cert))
  ; step =
      subst2 (HypDerivation (embed lhs) (embed rhs))
        (embed-subVar (A.suc A.var) lhs) (embed-subVar (A.suc A.var) rhs)
        (embed-hyp-derivation (A.InductionCertificate.step cert))
  }

-- …and it means there what it meant here.
embed-certificate-sound : {lhs rhs : A.Tm} → A.InductionCertificate lhs rhs
  → (ρ : Env) → A.eval lhs (toBase ρ) ≡ A.eval rhs (toBase ρ)
embed-certificate-sound {lhs} {rhs} cert ρ =
  sym (embed-eval lhs ρ)
  ∙ induction-sound (embed-certificate cert) ρ
  ∙ embed-eval rhs ρ
