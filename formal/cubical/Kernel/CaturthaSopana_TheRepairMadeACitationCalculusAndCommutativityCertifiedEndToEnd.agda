{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Kernel.CaturthaSopana_TheRepairMadeACitationCalculusAnd
--                                    CommutativityCertifiedEndToEnd
--
-- -  the fourth step of the stair.
--
-- WHERE THIS STANDS.  `TrtiyaSopana_…` proved the induction certificate
-- does not reach commutativity: the wall is the type of the `base`
-- field, which demands a bare `Derivation`, and named the repair without
-- making it.  This module makes the repair
-- in the kernel's own philosophy: `install` turns a
-- theorem into a move, so let the certificate layer do the same — a step
-- may CITE a lemma that was itself CERTIFIED BELOW this level, carrying the
-- lower certificate (an `InductionCertificate` on `var` or an
-- `InductionCertificateY` on `yvar`) as the constructor's argument.  The
-- citation is object-level data, so a `CCert` is replayable and is checked
-- by the kernel's own soundness theorems, not only by Agda's meta-level.
-- (A citation constructor accepting an arbitrary meta-level proof of the
-- pointwise equation would make the citation closure coincide with truth
-- in ℕ, and the third rung of the stair below would say nothing.)
--
-- THREE PIECES, then the prize:
--
--   §1  induction on the SECOND coordinate: `subY`, `eval-subY`, the
--       Y-certificate, its soundness — the mirror the kernel never
--       needed until commutativity asked for it;
--   §2  the citation calculus: `CStep`/`CDeriv` (hypothesis-free) and
--       `CHypStep`/`CHypDeriv` (hypothesis at the predecessor), each
--       sound; a citation carries a LOWER-LEVEL CERTIFICATE, never a
--       bare pointwise proof; a `CCert` whose base and step live in these;
--   §3  the two lemmas, each certified BELOW this level:
--         0 + y = y            by a Y-certificate       (underivable)
--         (suc x) + y = suc (x + y)   by a Y-certificate
--   §4  COMMUTATIVITY, certified end to end: base cites §3's first
--       lemma, step cites the second and uses the hypothesis once under
--       suc.  `ccert-sound` discharges it at every environment.
--
-- Together with `Naya_…` and `TrtiyaSopana_…` the stair now reads:
--
--   rewrite closure  ⊊  induction closure  ⊊  citation closure ∋ comm
--
-- with the first strictness at 0 + x = x, the second at x + y = y + x,
-- and the third level exhibited INHABITED at commutativity — reached,
-- not merely true.
------------------------------------------------------------------------

module Kernel.CaturthaSopana_TheRepairMadeACitationCalculusAndCommutativityCertifiedEndToEnd where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import Kernel.RewriteCertificate

------------------------------------------------------------------------
-- §1.  Induction on the second coordinate.
------------------------------------------------------------------------

subY : Tm → Tm → Tm
subY u var       = var
subY u yvar      = u
subY u zvar      = zvar
subY u uvar      = uvar
subY u vvar      = vvar
subY u wvar      = wvar
subY u zero      = zero
subY u (suc t)   = suc (subY u t)
subY u (add l r) = add (subY u l) (subY u r)

setY : ℕ → Env → Env
setY n ρ = env (Env.x ρ) n (Env.z ρ) (Env.u ρ) (Env.v ρ) (Env.w ρ)

eval-subY : (t body : Tm) (ρ : Env) →
  eval (subY t body) ρ ≡ eval body (setY (eval t ρ) ρ)
eval-subY t var       ρ = refl
eval-subY t yvar      ρ = refl
eval-subY t zvar      ρ = refl
eval-subY t uvar      ρ = refl
eval-subY t vvar      ρ = refl
eval-subY t wvar      ρ = refl
eval-subY t zero      ρ = refl
eval-subY t (suc b)   ρ = cong suc (eval-subY t b ρ)
eval-subY t (add l r) ρ = cong₂ _+_ (eval-subY t l ρ) (eval-subY t r ρ)

record InductionCertificateY (lhs rhs : Tm) : Type₀ where
  field
    baseY : Derivation (subY zero lhs) (subY zero rhs)
    stepY : HypDerivation lhs rhs
      (subY (suc yvar) lhs) (subY (suc yvar) rhs)

inductionY-sound : {lhs rhs : Tm} → InductionCertificateY lhs rhs →
  (ρ : Env) → eval lhs ρ ≡ eval rhs ρ
inductionY-sound {lhs} {rhs} cert (env x₀ n z₀ u₀ v₀ w₀) = go n
  where
  ρ : ℕ → Env
  ρ k = env x₀ k z₀ u₀ v₀ w₀

  go : (k : ℕ) → eval lhs (ρ k) ≡ eval rhs (ρ k)
  go zero =
    sym (eval-subY zero lhs (ρ zero))
    ∙ derivation-sound (InductionCertificateY.baseY cert) (ρ zero)
    ∙ eval-subY zero rhs (ρ zero)
  go (suc k) =
    sym (eval-subY (suc yvar) lhs (ρ k))
    ∙ hyp-derivation-sound (InductionCertificateY.stepY cert) (ρ k) (go k)
    ∙ eval-subY (suc yvar) rhs (ρ k)

------------------------------------------------------------------------
-- §2.  The citation calculus.  A step is a rewrite, a citation carrying
--      its own pointwise proof, or a congruence; the hypothesis variant
--      adds the predecessor's equation, exactly as `HypStep` does.
------------------------------------------------------------------------

data CStep : Tm → Tm → Type₀ where
  c-lift : {x y : Tm} → Step x y → CStep x y
  c-citeX : {l r : Tm} → InductionCertificate l r → CStep l r
  c-citeY : {l r : Tm} → InductionCertificateY l r → CStep l r
  c-suc  : {x y : Tm} → CStep x y → CStep (suc x) (suc y)
  c-addL : {x y : Tm} → CStep x y → (z : Tm) → CStep (add x z) (add y z)
  c-addR : (z : Tm) → {x y : Tm} → CStep x y → CStep (add z x) (add z y)

data CDeriv : Tm → Tm → Type₀ where
  c-done : (x : Tm) → CDeriv x x
  c-then : {x y z : Tm} → CStep x y → CDeriv y z → CDeriv x z

cstep-sound : {a b : Tm} → CStep a b → (ρ : Env) → eval a ρ ≡ eval b ρ
cstep-sound (c-lift p)     ρ = step-sound p ρ
cstep-sound (c-citeX cert)  ρ = induction-sound cert ρ
cstep-sound (c-citeY cert)  ρ = inductionY-sound cert ρ
cstep-sound (c-suc p)      ρ = cong suc (cstep-sound p ρ)
cstep-sound (c-addL p t)   ρ = cong (_+ eval t ρ) (cstep-sound p ρ)
cstep-sound (c-addR t p)   ρ = cong (eval t ρ +_) (cstep-sound p ρ)

cderiv-sound : {a b : Tm} → CDeriv a b → (ρ : Env) → eval a ρ ≡ eval b ρ
cderiv-sound (c-done _)     ρ = refl
cderiv-sound (c-then p d)   ρ = cstep-sound p ρ ∙ cderiv-sound d ρ

data CHypStep (ihL ihR : Tm) : Tm → Tm → Type₀ where
  ch-lift : {x y : Tm} → CStep x y → CHypStep ihL ihR x y
  ch-hyp  : CHypStep ihL ihR ihL ihR
  ch-suc  : {x y : Tm} → CHypStep ihL ihR x y
          → CHypStep ihL ihR (suc x) (suc y)
  ch-addL : {x y : Tm} → CHypStep ihL ihR x y → (z : Tm)
          → CHypStep ihL ihR (add x z) (add y z)
  ch-addR : (z : Tm) → {x y : Tm} → CHypStep ihL ihR x y
          → CHypStep ihL ihR (add z x) (add z y)

data CHypDeriv (ihL ihR : Tm) : Tm → Tm → Type₀ where
  ch-done : (x : Tm) → CHypDeriv ihL ihR x x
  ch-then : {x y z : Tm} → CHypStep ihL ihR x y
          → CHypDeriv ihL ihR y z → CHypDeriv ihL ihR x z

chstep-sound : {ihL ihR a b : Tm} → CHypStep ihL ihR a b →
  (ρ : Env) → eval ihL ρ ≡ eval ihR ρ → eval a ρ ≡ eval b ρ
chstep-sound (ch-lift p)   ρ ih = cstep-sound p ρ
chstep-sound ch-hyp        ρ ih = ih
chstep-sound (ch-suc p)    ρ ih = cong suc (chstep-sound p ρ ih)
chstep-sound (ch-addL p t) ρ ih = cong (_+ eval t ρ) (chstep-sound p ρ ih)
chstep-sound (ch-addR t p) ρ ih = cong (eval t ρ +_) (chstep-sound p ρ ih)

chderiv-sound : {ihL ihR a b : Tm} → CHypDeriv ihL ihR a b →
  (ρ : Env) → eval ihL ρ ≡ eval ihR ρ → eval a ρ ≡ eval b ρ
chderiv-sound (ch-done _)   ρ ih = refl
chderiv-sound (ch-then p d) ρ ih =
  chstep-sound p ρ ih ∙ chderiv-sound d ρ ih

record CCert (lhs rhs : Tm) : Type₀ where
  field
    baseC : CDeriv (subVar zero lhs) (subVar zero rhs)
    stepC : CHypDeriv lhs rhs
      (subVar (suc var) lhs) (subVar (suc var) rhs)

ccert-sound : {lhs rhs : Tm} → CCert lhs rhs →
  (ρ : Env) → eval lhs ρ ≡ eval rhs ρ
ccert-sound {lhs} {rhs} cert (env n y₀ z₀ u₀ v₀ w₀) = go n
  where
  ρ : ℕ → Env
  ρ k = env k y₀ z₀ u₀ v₀ w₀

  go : (k : ℕ) → eval lhs (ρ k) ≡ eval rhs (ρ k)
  go zero =
    sym (eval-subVar zero lhs (ρ zero))
    ∙ cderiv-sound (CCert.baseC cert) (ρ zero)
    ∙ eval-subVar zero rhs (ρ zero)
  go (suc k) =
    sym (eval-subVar (suc var) lhs (ρ k))
    ∙ chderiv-sound (CCert.stepC cert) (ρ k) (go k)
    ∙ eval-subVar (suc var) rhs (ρ k)

------------------------------------------------------------------------
-- §3.  The two lemmas, certified below this level.
------------------------------------------------------------------------

-- 0 + y = y, by Y-induction (underivable as a Derivation: Naya_… §3).
zero-left-certY : InductionCertificateY (add zero yvar) yvar
InductionCertificateY.baseY zero-left-certY =
  then-step (add-zero zero) (done zero)
InductionCertificateY.stepY zero-left-certY =
  hyp-then (lift-step (add-suc zero yvar))
    (hyp-then (hyp-suc hypothesis) (hyp-done (suc yvar)))

zero-left-everywhere : (ρ : Env) → eval (add zero yvar) ρ ≡ eval yvar ρ
zero-left-everywhere = inductionY-sound zero-left-certY

-- (suc x) + y = suc (x + y), by Y-induction.
suc-left-certY : InductionCertificateY (add (suc var) yvar) (suc (add var yvar))
InductionCertificateY.baseY suc-left-certY =
  then-step (add-zero (suc var))
    (then-step (reverse (suc-step (add-zero var))) (done (suc (add var zero))))
InductionCertificateY.stepY suc-left-certY =
  hyp-then (lift-step (add-suc (suc var) yvar))
    (hyp-then (hyp-suc hypothesis)
      (hyp-then (reverse-hypothesis-under-suc)
        (hyp-done _)))
  where
  -- suc (suc (add var yvar)) → suc (add var (suc yvar)) is the reverse
  -- of add-suc under one suc; spelled out because the target of the
  -- walk is subY (suc yvar) applied to suc (add var yvar).
  reverse-hypothesis-under-suc :
    HypStep (add (suc var) yvar) (suc (add var yvar))
      (suc (suc (add var yvar))) (suc (add var (suc yvar)))
  reverse-hypothesis-under-suc =
    hyp-suc (lift-step (reverse (add-suc var yvar)))

suc-left-everywhere :
  (ρ : Env) → eval (add (suc var) yvar) ρ ≡ eval (suc (add var yvar)) ρ
suc-left-everywhere = inductionY-sound suc-left-certY

------------------------------------------------------------------------
-- §4.  COMMUTATIVITY, certified end to end.
--
--   base :  0 + y  --cite zero-left-->  y  --reverse add-zero-->  y + 0
--   step :  (suc x) + y  --cite suc-left-->  suc (x + y)
--                        --hypothesis under suc-->  suc (y + x)
--                        --reverse add-suc-->  y + suc x
------------------------------------------------------------------------

comm-cert : CCert (add var yvar) (add yvar var)
CCert.baseC comm-cert =
  c-then (c-citeY zero-left-certY)
    (c-then (c-lift (reverse (add-zero yvar))) (c-done (add yvar zero)))
CCert.stepC comm-cert =
  ch-then (ch-lift (c-citeY suc-left-certY))
    (ch-then (ch-suc ch-hyp)
      (ch-then (ch-lift (c-lift (reverse (add-suc yvar var))))
        (ch-done (add yvar (suc var)))))

commutativity-certified :
  (ρ : Env) → eval (add var yvar) ρ ≡ eval (add yvar var) ρ
commutativity-certified = ccert-sound comm-cert
