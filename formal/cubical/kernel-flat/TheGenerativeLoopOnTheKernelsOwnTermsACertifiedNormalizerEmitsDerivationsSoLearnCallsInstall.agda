{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheGenerativeLoopOnTheKernelsOwnTerms.  The proved-terminating generative learner runs on
-- `ObstructionSubstrate.Tm`, a DIFFERENT datatype from the metacircular
-- kernel's `Kernel.RewriteCertificate.Tm`, with no `Tm`-morphism sending
-- `propose ↦ install`.
--
-- WHY NOT A MORPHISM.  A total faithful `Tm`-morphism is blocked twice:
--   (arity)   Obstruction's `node : Shape(=ℕ) → Tm → Tm` is one unary
--             constructor over a countably-infinite head alphabet; the
--             kernel's `Tm` is a CLOSED signature with one unary symbol
--             (`suc`), so ℕ-many heads have no arity-faithful image.
--   (witness) `propose` outputs a purely SYNTACTIC proposal (a fresh head
--             + body, no rewrite witness), while `install` consumes a
--             CHECKED `Derivation`.  The object that strictly decreases the
--             generative loop's `deficit` carries no equational content.
-- So the loop cannot be TRANSPORTED into the kernel.  Instead it is
-- RE-EXPRESSED on the kernel's own terms: a certified normalizer whose
-- every step is a real `Step`, so the discovered reduction IS a checked
-- `Derivation`, and `install` is called on it literally.  That makes
-- "learning = discovery becoming native capability" —
-- one checked pipeline `learn = install ∘ normalize`.
--
-- WHAT IS PROVEN, --safe, no postulates, structurally terminating:
--   addNorm       for all l r, a term and a Derivation (add l r) ⇝ it,
--                 eliminating additions against a numeral right argument
--                 (add x zero ⇝ x; add x (suc y) ⇝ suc (add x y)),
--                 structural on r.
--   normalize     for every term t, a Derivation t ⇝ normalForm t, built
--                 from real Step constructors under congruence — the
--                 discovery, as a checked object.
--   normalize-sound
--                 normalization preserves ℕ-meaning at every environment
--                 (free, from derivation-sound): the discovered move is
--                 SOUND, so nothing false can be learned.
--   learn         learn t = install (normalize t) : NativeOperation — the
--                 discovered derivation becomes an installed, executable
--                 kernel move.  `propose ↦ install`, literal, on one Tm.
--   run-example   normalForm (add var (suc zero)) ≡ suc var, by refl — the
--                 normalizer COMPUTES; the derivation it emits is the
--                 kernel's own `accepted`.
--
-- The kernel's REACH is unchanged (Siddhasadhana: self-installation is a
-- plateau); what closes is the
-- DISCOVERY→INSTALLATION loop on one language.
------------------------------------------------------------------------

module TheGenerativeLoopOnTheKernelsOwnTermsACertifiedNormalizerEmitsDerivationsSoLearnCallsInstall where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd)

open import Kernel.RewriteCertificate
open import Kernel.ControlledGrammar using (NativeOperation ; install)

------------------------------------------------------------------------
-- Derivation transitivity and the three congruences — each structural on
-- its Derivation argument, so every step below is a real `Step`.
------------------------------------------------------------------------

_▸_ : {a b c : Tm} → Derivation a b → Derivation b c → Derivation a c
done a        ▸ e = e
then-step s d ▸ e = then-step s (d ▸ e)

infixr 5 _▸_

sucD : {a b : Tm} → Derivation a b → Derivation (suc a) (suc b)
sucD (done a)        = done (suc a)
sucD (then-step s d) = then-step (suc-step s) (sucD d)

addLD : {a b : Tm} → Derivation a b → (z : Tm) → Derivation (add a z) (add b z)
addLD (done a)        z = done (add a z)
addLD (then-step s d) z = then-step (add-left s z) (addLD d z)

addRD : (z : Tm) → {a b : Tm} → Derivation a b → Derivation (add z a) (add z b)
addRD z (done a)        = done (add z a)
addRD z (then-step s d) = then-step (add-right z s) (addRD z d)

------------------------------------------------------------------------
-- addNorm — eliminate an addition against its right argument, structural
-- on that argument.  add x zero ⇝ x; add x (suc y) ⇝ suc (add x y),
-- recursing on y; otherwise (variable / nested add on the right) it is
-- irreducible and left as-is (a `done`).
------------------------------------------------------------------------

addNorm : (l r : Tm) → Σ Tm (λ t → Derivation (add l r) t)
addNorm l zero    = l , then-step (add-zero l) (done l)
addNorm l (suc y) =
  let t = fst (addNorm l y)
      d = snd (addNorm l y)
  in suc t , then-step (add-suc l y) (sucD d)
addNorm l r       = add l r , done (add l r)

------------------------------------------------------------------------
-- normalize — normalize any term, structural on the term.  Under an add,
-- normalize both arguments (congruence), then eliminate the addition.
------------------------------------------------------------------------

norm : (t : Tm) → Σ Tm (λ s → Derivation t s)
norm var        = var , done var
norm yvar       = yvar , done yvar
norm zvar       = zvar , done zvar
norm uvar       = uvar , done uvar
norm vvar       = vvar , done vvar
norm wvar       = wvar , done wvar
norm zero       = zero , done zero
norm (suc t)    = suc (fst (norm t)) , sucD (snd (norm t))
norm (add l r)  =
  let l' = fst (norm l) ; dl = snd (norm l)
      r' = fst (norm r) ; dr = snd (norm r)
      t  = fst (addNorm l' r') ; da = snd (addNorm l' r')
  in t , (addLD dl r ▸ addRD l' dr) ▸ da

normalForm : Tm → Tm
normalForm t = fst (norm t)

normalize : (t : Tm) → Derivation t (normalForm t)
normalize t = snd (norm t)

------------------------------------------------------------------------
-- Soundness is free: the discovered move preserves ℕ-meaning everywhere,
-- so nothing false can be learned.
------------------------------------------------------------------------

normalize-sound : (t : Tm) (ρ : Env) → eval t ρ ≡ eval (normalForm t) ρ
normalize-sound t = derivation-sound (normalize t)

------------------------------------------------------------------------
-- THE CLOSURE.  The discovered derivation becomes an installed kernel
-- operation: learning = discovery becoming native capability, literally.
------------------------------------------------------------------------

learn : (t : Tm) → NativeOperation
learn t = install (normalize t)

------------------------------------------------------------------------
-- The normalizer COMPUTES, and on the kernel's canonical seed it emits the
-- kernel's own `accepted` derivation add var (suc zero) ⇝ suc var.
------------------------------------------------------------------------

run-example : normalForm (add var (suc zero)) ≡ suc var
run-example = refl
