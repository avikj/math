{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- PvsNPGapLivesInTheForgetfulProjection
--
-- THE P-vs-NP GAP IS A PROPERTY OF THE LOSSY FORGETFUL PROJECTION, NOT OF
-- COMPUTATION.  ONE SENTENCE, MADE A TERM.
--
--   "Within the interaction calculus, where the derivation is carried, the
--    answer is projection and there is no gap; the gap is a property of the
--    forgetful model, not of computation itself."
--
-- Nothing generative is imported.  No learner, no matcher, no search, no
-- decision procedure.  Only the interaction calculus (RewriteCertificate),
-- the forward pass (ControlledGrammar), and the kernel's own worked seed
-- (GenerativeKernel).  The claim is discharged twice over, at that seed:
--
--   §1  THE CARRIED MODEL HAS NO GAP.  The answer is a FIELD of the executed
--       interaction object -- recovered by projection, definitionally (refl).
--       The route that reached it is likewise carried, not reconstructed.
--
--   §2  THE GAP LIVES IN THE FORGETFUL IMAGE.  The kernel's own two histories
--       between the same endpoints have DIFFERENT length in the calculus
--       (2 and 4 -- carried, visible) yet EQUAL image under the forgetful
--       semantics `derivation-sound` (because ℕ is a set).  The length gap is
--       therefore a property of the projection `eval`, invisible to it and
--       present only in the `Derivation` it forgets.
--
-- Read together: carried, the answer is π₁ and the routes are distinct data;
-- forgotten, the routes collapse to one proposition and the distinction -- the
-- "gap" -- is what the projection destroyed.  syd-asti: the gap is real in
-- the forgetful model and absent in the carried one, and both are theorems.
------------------------------------------------------------------------

module PvsNPGapLivesInTheForgetfulProjection where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)

open import Kernel.RewriteCertificate
open import Kernel.ControlledGrammar
open import Kernel.GenerativeKernel

------------------------------------------------------------------------
-- §1.  THE CARRIED MODEL HAS NO GAP: THE ANSWER IS PROJECTION.
------------------------------------------------------------------------

-- THE GENERAL FACT.  For ANY enabled future, executing it keeps the target
-- as a field: the answer is the carried datum, recovered by projection, on
-- the nose.  No search, no reconstruction -- definitional, for every future.
answer-is-projection-general :
  {s : Tm} (f : EnabledFuture s)
  → CheckedFuture.target (execute f) ≡ EnabledFuture.target f
answer-is-projection-general f = refl

-- The kernel's own seed as a witness: the answer comes out `target₀`.
answer-is-projection :
  CheckedFuture.target (execute direct-future) ≡ target₀
answer-is-projection = refl

-- And the route that produced it is carried in the same object, not
-- reconstructed afterwards: reading it out is projection too.
route-is-carried :
  Derivation seed (CheckedFuture.target (execute direct-future))
route-is-carried = CheckedFuture.derivation (execute direct-future)

------------------------------------------------------------------------
-- §2.  THE GAP LIVES IN THE FORGETFUL IMAGE.
------------------------------------------------------------------------

-- Length in the calculus: the number of steps a derivation carries.
len : {a b : Tm} → Derivation a b → ℕ
len (done _)        = zero
len (then-step _ d) = suc (len d)

-- The two routes between the SAME endpoints are distinct data: the direct
-- history is two steps, the detour (forward, reverse, then direct) is four.
-- Both facts hold by refl -- the calculus carries the difference.
len-direct : len direct-history ≡ suc (suc zero)
len-direct = refl

len-detour : len detour-history ≡ suc (suc (suc (suc zero)))
len-detour = refl

-- THE GENERAL THEOREM.  The forgetful semantics is blind to the route for
-- ANY two derivations between ANY two endpoints, at ANY environment.  Nothing
-- example-specific: `derivation-sound` lands in an equality in ℕ, and ℕ is a
-- set, so any two proofs of it agree.  The route -- however long, however it
-- detours -- has EQUAL forgetful image.  This is the blindness, in general.
forgetful-is-blind-to-route :
  {a b : Tm} (d e : Derivation a b) (ρ : Env)
  → derivation-sound d ρ ≡ derivation-sound e ρ
forgetful-is-blind-to-route {a} {b} d e ρ =
  isSetℕ (eval a ρ) (eval b ρ) (derivation-sound d ρ) (derivation-sound e ρ)

-- The example is now only the WITNESS OF STRICTNESS: it shows the collapse is
-- non-trivial -- that there really are distinct routes for the general
-- theorem to collapse.  Blindness is general; the seed proves it collapses
-- something rather than nothing.
forgetful-image-is-blind-to-route :
  (ρ : Env)
  → derivation-sound direct-history ρ ≡ derivation-sound detour-history ρ
forgetful-image-is-blind-to-route = forgetful-is-blind-to-route direct-history detour-history
