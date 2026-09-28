{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- एकभाषा — one language.  Compound built here (एक, one;
-- भाषा, language); not a source term.
--
-- THE DIRECTIVE THIS ANSWERS, the owner's: the machine must not
-- look at two sources.  The Haskell body / Agda truth-store split IS the
-- lossy implementation of the core ideas — Certificate.hs (absent from this repository)'s entire
-- "FAITHFULNESS" header is an apology for translating between them, and
-- every copy of the term code (MathMachine's, Sanghatta's, Siddhi's) is
-- a seam where meaning leaks.  Agda is already code (MAlonzo compiles
-- it); so the machine's own world — terms, rules, store, normalizer,
-- prover — moves INTO the one language, and the split retires.
--
-- THE ONE STRUCTURAL MOVE, and it changes what "gate" means:
--
--     record नियमः : rule = { lhs ; rhs ; साक्षी : ⊨ (lhs , rhs) }
--
-- A store entry CARRIES ITS PROOF AS A FIELD.  An unproven rule is not
-- refused by a gate — it is UNCONSTRUCTIBLE.  The gate is the type.
-- Certificate's watched controls guard a boundary between two worlds;
-- here there is no boundary to guard.  What the kernel checks, once,
-- at this module, is the SOUNDNESS OF THE PROVER ITSELF (नि-साक्षी
-- below); every rule it ever mints thereafter is born proven.
--
-- WHAT THIS SLICE CONTAINS, all checked, no holes:
--   §1  the machine's own vocabulary as one datatype (the SAME clause
--       order as machine/library.terms' world: max and le in the
--       machine's own recursion, stated at the definitions);
--   §2  truth: ⊨ e  =  ∀ρ → eval l ρ ≡ eval r ρ, over the standard model;
--   §3  the store type whose entries cannot exist unproven;
--   §4  the internal prover, norm-and-compare, WITH its soundness
--       theorem — a proof-producing function, no Bool verdict anywhere
--       on the wire (the Uttara discipline arriving at the type level);
--   §5  real members of the machine's own non-joining list (Sanghatta,
--       this container), proven by the internal prover and
--       installed as नियम values — the store growing as typed truth.
--
-- NOVELTY CLAIMED: none of the mathematics (normalization-by-
-- simplification and its soundness are classical).  The composition —
-- the machine's OWN store re-founded so proof is a field and the
-- prover is internal — is the contribution.
------------------------------------------------------------------------

module NaturalMachine.EkaBhasha_TheStoreCarriesItsProofsTheGateIsTheTypeAndTheProverLivesInside where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-zero ; +-suc ; ·-suc ; 0≡m·0)
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)

------------------------------------------------------------------------
-- §1  The vocabulary, one datatype — IMPORTED, not restated.  The
--     machine's vocabulary, evaluator and normalizer live ONCE, in the act-portion (formal/karma/KarmaKanda…, checked
--     --cubical-compatible --safe), which both worlds import with full
--     use: this --cubical body proves paths about the very definitions
--     the compiled mouth runs.  The Veda's two portions read one text.
--     Variables are names over ℕ; an environment is total, so no
--     finite-context bureaucracy.  The machine's own max and le, ITS
--     clause order (library.terms' world):
--       max x 0 = x ; max 0 x = x ; max (s x)(s y) = s (max x y)
--       le 0 x = 1  ; le (s x) 0 = 0 ; le (s x)(s y) = le x y
------------------------------------------------------------------------

import PramanaKanda_TheOneKnowingItselfCrossesTheBoundaryCertificatesAndAllInTheSharedTongue as प्र
import Agda.Builtin.Maybe as निजमा
open import Cubical.Data.Equality using (eqToPath)
open import KarmaKanda_TheActPortionOfTheBodyPathFreeAndCompiled public
  using ( Tm ; var ; ze ; su ; _⊕_ ; _⊗_ ; _⊖_ ; mx ; lq ; gc
        ; mxℕ ; lqℕ ; sbℕ ; eval
        ; plus' ; times' ; sub' ; mx' ; lq' ; gc' ; norm ; गच्छℕ )

------------------------------------------------------------------------
-- §2  Truth over the standard model.
------------------------------------------------------------------------

Eq' : Type
Eq' = Tm × Tm

⊨_ : Eq' → Type
⊨ (l , r) = (ρ : ℕ → ℕ) → eval l ρ ≡ eval r ρ

------------------------------------------------------------------------
-- §3  THE STORE.  An entry carries its proof; the gate is the type.
------------------------------------------------------------------------

record नियमः : Type where
  constructor niyama
  field
    lhs rhs : Tm
    साक्षी  : ⊨ (lhs , rhs)

------------------------------------------------------------------------
-- §4  The internal prover: symbolic simplification in the machine's own
--     clause order, each simplifier WITH its soundness, then compare.
------------------------------------------------------------------------

-- (the simplifiers and norm are imported from the act-portion in §1)

-- The soundness of the simplifiers and of norm is
-- proven ONCE, in the shared tongue (PramanaKanda), where the compiled
-- mouth runs the same theorem; this body LIFTS it to a path.  One
-- proof, two worlds.
norm-sound : ∀ t ρ → eval (norm t) ρ ≡ eval t ρ
norm-sound t ρ = eqToPath (प्र.norm-sound t ρ)

-- syntactic equality that RETURNS THE PATH — no Bool on any wire, no
-- separate soundness lemma: the test and its witness are one value.
mmap : {A B : Type} → (A → B) → Maybe A → Maybe B
mmap f (just a) = just (f a)
mmap f nothing  = nothing

mmap2 : {A B C : Type} → (A → B → C) → Maybe A → Maybe B → Maybe C
mmap2 f (just a) (just b) = just (f a b)
mmap2 f _        _        = nothing

-- the shared-tongue verdict, lifted: same decision, path certificate
उद्धार-मा : {A : Type} {B : Type} → (A → B) → निजमा.Maybe A → Maybe B
उद्धार-मा f (निजमा.just a) = just (f a)
उद्धार-मा f निजमा.nothing  = nothing

_≟ℕ_ : (i j : ℕ) → Maybe (i ≡ j)
i ≟ℕ j = उद्धार-मा eqToPath (i प्र.≟ℕ j)

_≟T_ : (a b : Tm) → Maybe (a ≡ b)
a ≟T b = उद्धार-मा eqToPath (a प्र.≟T b)

-- THE PROVER.  Returns a proof or nothing — the two roads, at the type.
साधनम् : (e : Eq') → Maybe (⊨ e)
साधनम् (l , r) = mmap witness (norm l ≟T norm r)
  where
  witness : norm l ≡ norm r → ⊨ (l , r)
  witness p ρ =
    sym (norm-sound l ρ) ∙ cong (λ t → eval t ρ) p ∙ norm-sound r ρ

------------------------------------------------------------------------
-- §5  The machine's own missing theorems, proven internally and
--     installed as typed store values.  Each pair below is a member of
--     Sanghatta's non-joining list, this container (the सिद्धि
--     runs' ledger).  `fromJust … tt` compiles exactly when the prover
--     succeeds — a failed proof is a TYPE ERROR here, not a log line.
------------------------------------------------------------------------

inJust : {A : Type} → Maybe A → Type
inJust (just _) = Unit
inJust nothing  = ⊥

fromJust : {A : Type} (m : Maybe A) → inJust m → A
fromJust (just a) _ = a

private
  x₀ : Tm
  x₀ = var 0

-- le(s(s(x)), s(0)) = 0
नियम₁ : नियमः
नियम₁ = niyama (lq (su (su x₀)) (su ze)) ze
               (fromJust (साधनम् (lq (su (su x₀)) (su ze) , ze)) tt)

-- max(s(x), s(0)) = s(x)
नियम₂ : नियमः
नियम₂ = niyama (mx (su x₀) (su ze)) (su x₀)
               (fromJust (साधनम् (mx (su x₀) (su ze) , su x₀)) tt)

-- -(s(0), s(s(x))) = 0
नियम₃ : नियमः
नियम₃ = niyama ((su ze) ⊖ (su (su x₀))) ze
               (fromJust (साधनम् ((su ze) ⊖ (su (su x₀)) , ze)) tt)

-- le(0, s(x)) = le(0, x)   (both sides normalize to s(0))
नियम₄ : नियमः
नियम₄ = niyama (lq ze (su x₀)) (lq ze x₀)
               (fromJust (साधनम् (lq ze (su x₀) , lq ze x₀)) tt)
