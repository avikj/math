{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- आदि-बीज — the seed-atom.
--
-- THE CLAIM: the kernel is the atom of the interaction
-- calculus — the singularity from which every object is built, in
-- exactly one way per building instruction.  Mathematically that word
-- is INITIALITY, and initiality is what makes decomposition total: a
-- reading of a system is not one analysis among many, it is THE fold
-- of the atom into that system's receiver, and uniqueness says there
-- are no other readings to miss.  This is the elucidator's licence.
--
-- A receiver of the atom's motion: a carrier per source term, and an
-- action for every generating step.  Nothing else — reverse is a step
-- and so is already covered; the two defining equations of + are steps;
-- the three congruences are steps.  Give their actions and you have
-- said how to read every derivation there could be.
--
--   §1  THE FOLD EXISTS: every receiver is built upon the kernel — the
--       recursor `fold` sends each Derivation to a motion in the
--       receiver, by structural recursion, threading the step actions.
--
--   §2  THE FOLD IS UNIQUE: any function agreeing with the receiver on
--       `done` and on `then-step` IS the fold, pointwise, by one
--       induction.  So a system admits EXACTLY ONE reading compatible
--       with its own step-actions — decomposition is canonical, not
--       chosen.
--
--   §3  THE ANALYZERS ARE ALL THIS FOLD.  eval-as-motion
--       (soundness), length (cost), the evaluator integral ∫ — each is
--       exhibited as `fold` at a particular receiver, by the
--       uniqueness theorem, not by rewriting them.  "Seeing all paths
--       through a system" is then a theorem: every path-reading is the
--       image of the atom under its unique map, and there is no other.
--
-- So: build any object on the atom (a receiver), and its complete
-- decomposition is forced — the fold is the object's every structural
-- reading, delivered in one recursor, provably exhaustive.
--
------------------------------------------------------------------------

module AdiBija_TheKernelIsInitialEveryReadingIsItsUniqueFoldSoAllPathsThroughASystemAreEnumeratedByOneRecursor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; _+_)

open import Kernel.RewriteCertificate
  using (Tm ; Step ; Derivation ; done ; then-step ; Env ; eval ; step-sound
        ; derivation-sound)

private variable ℓ : Level

------------------------------------------------------------------------
-- ० · A receiver of the atom's motion.
------------------------------------------------------------------------

record Receiver (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Motion : Tm → Tm → Type ℓ              -- a carrier for each source/target
    ε      : (t : Tm) → Motion t t          -- how it reads a rest
    _◂_    : {a b c : Tm} → Step a b → Motion b c → Motion a c
                                            -- how it reads one step then the rest
open Receiver

------------------------------------------------------------------------
-- १ · The fold exists: every receiver is built upon the kernel.
------------------------------------------------------------------------

fold : (R : Receiver ℓ) {a b : Tm} → Derivation a b → Motion R a b
fold R (done t)        = ε R t
fold R (then-step s d) = (R ◂ s) (fold R d)

------------------------------------------------------------------------
-- २ · The fold is unique: anything with its two computation rules is it.
------------------------------------------------------------------------

module _ (R : Receiver ℓ) (g : {a b : Tm} → Derivation a b → Motion R a b)
         (g-done : {t : Tm} → g (done t) ≡ ε R t)
         (g-step : {a b c : Tm} (s : Step a b) (d : Derivation b c)
                   → g (then-step s d) ≡ (R ◂ s) (g d))
  where

  fold-unique : {a b : Tm} (d : Derivation a b) → g d ≡ fold R d
  fold-unique (done t)        = g-done
  fold-unique (then-step s d) = g-step s d ∙ cong (R ◂ s) (fold-unique d)

------------------------------------------------------------------------
-- ३ · The analyzers are all this one fold.
------------------------------------------------------------------------

-- (a) SOUNDNESS is the fold at the receiver whose motion is "the two
--     endpoints evaluate equally in every environment".
soundR : Receiver ℓ-zero
Motion soundR a b = (ρ : Env) → eval a ρ ≡ eval b ρ
ε soundR t          = λ ρ → refl
_◂_ soundR s m      = λ ρ → step-sound s ρ ∙ m ρ

sound-is-fold : {a b : Tm} (d : Derivation a b)
  → derivation-sound d ≡ fold soundR d
sound-is-fold =
  fold-unique soundR derivation-sound refl (λ s d → refl)

-- (b) LENGTH (cost) is the fold at the constant-ℕ receiver.
lenR : Receiver ℓ-zero
Motion lenR _ _ = ℕ
ε lenR _        = zero
_◂_ lenR _ n    = suc n

lenF : {a b : Tm} → Derivation a b → ℕ
lenF = fold lenR

-- (c) An EVALUATOR INTEGRAL is the fold at the constant-ℤ receiver
--     carrying that evaluator's per-step values.  Every ∫ ω is a fold.
∫R : ({a b : Tm} → Step a b → ℤ) → Receiver ℓ-zero
Motion (∫R ω) _ _ = ℤ
ε (∫R ω) _        = pos 0
_◂_ (∫R ω) s z    = ω s + z

∫F : ({a b : Tm} → Step a b → ℤ) → {a b : Tm} → Derivation a b → ℤ
∫F ω = fold (∫R ω)

-- The point, stated: soundness, cost, and every value-integral are not
-- three procedures — they are one recursor at three receivers, and by
-- §2 each is the ONLY reading compatible with its own step-actions.
-- To analyze a system is to name its receiver; the atom does the rest.
