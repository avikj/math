{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.CertificateFibration
--
-- THE CERTIFICATE IS THE FIBRE COORDINATE.
--
-- `notes/ONLINE_SMITH_CERTIFICATE_REVERSIBILITY.md` (absent from this repository) proves, of a map
-- `f : X → Y` between finite sets:
--
--     "The fiber bound is elementary.  Basis inputs with the same
--      declared output must be distinguished by orthogonal environment
--      states.  Conversely, label the environment by the input's
--      position inside its output fiber.  Hence the minimum environment
--      dimension of a finite classical basis map is its maximum fiber
--      cardinality."
--
-- Two directions, two arguments, one finiteness hypothesis, one
-- appeal to orthogonality.  This module replaces all of that by a
-- re-bracketing that Agda accepts as `refl`, and then reads the
-- corpus's numbers off it.
--
-- THE STRUCTURE THAT MAKES IT INEVITABLE.  Fix `f : X → Y` and a
-- certificate `c : X → E`.  The recorded update is
-- `⟨f,c⟩ : X → Y × E`.  Then for every `y : Y` and `e : E`
--
--     fiber ⟨f,c⟩ (y , e)  ≅  fiber (c ↾ fiber f y) e            (§1)
--
-- and BOTH round trips of that Iso are `refl`: it is Σ-eta, nothing
-- more.  Everything the note proves follows by transporting
-- `isProp` across it (§2), because `isEmbedding` IS `hasPropFibers`
-- (`Cubical.Functions.Embedding.isEmbedding≡hasPropFibers`).
--
-- Consequences, in the order the note states them:
--
--   * (note, item 2 — the lower bound)  a certificate that restores
--     injectivity embeds EVERY fiber of `f` into `E`     (`fiber↪cert`).
--     No finiteness, no orthogonality, no counting.
--   * (note, items 3 and 5 — attainment)  conversely a fiberwise
--     family of embeddings IS a certificate  (`triv→isEmbedding`), and
--     the two data are the same data: `certIso` (§3) is an Iso
--     `(X → E) ≅ ((y : Y) → fiber f y → E)`, one of whose round trips
--     is again `refl`.
--   * the numerical statement, once the fibres happen to be finite
--     (§4, `fiberCard≤`): `card (fiber f y) ≤ card E`.
--
-- The note's sentence is
-- symmetric — "the minimum … IS the maximum fiber cardinality" — and
-- §3 shows the two halves are not symmetric.  The lower bound is a
-- theorem about `f` alone.  The attainment is a DATUM: a family
-- `(y : Y) → fiber f y ↪ E`, uniform in `y`.  A pointwise cardinality
-- bound `∀ y → card (fiber f y) ≤ n` does NOT produce that family;
-- producing it is choosing an enumeration of each fibre, i.e. choosing
-- a trivialisation of the fibration `f`.  In the
-- corpus's own instance the trivialisation is canonical — the emitted
-- row coefficient `-q` IS the fibre coordinate — which is exactly why
-- that example works and why it proves nothing about the general case.
--
-- §5 lands that instance: for the Smith family
-- `A_q = ((2,0),(2q+1,7))`, whose post-state `B = ((1,7),(2,0))` is
-- independent of `q` (`collab/messages/workers/
-- 20260812T161511.752509Z--codex_quantum_process--0004.md` (absent from this repository)), the fibre
-- over the single post-state is `ℕ`, so ANY certificate alphabet `E`
-- admits `ℕ ↪ E`.  That is the broadcast's "no finite global
-- controller factors through (kind,pivot,remainder)", with the
-- unbounded family replaced by one embedding and the limit removed
-- rather than controlled.
--
-- The same §2 statement, at the map "ternary history `{0,1,2}^k` ↦
-- common nominal endpoint" of `collab/messages/
-- 0285-codex-quantum-process-fixed-domain-memory-result.md` (absent from this repository), is that
-- message's `3^k` lower bound; §4 is the step that turns the embedding
-- into the number.
--
-- `NaturalMachine.FiniteInformation` (ported from the Lean lane) already
-- has `Completes q c` = injectivity of `⟨q,c⟩`, and
-- `completes→separates` / `separates→completes` reducing it to fibres.
-- That is §2 at h-level 0 for a SET, stated element-wise.  §6 below
-- bridges to it in both directions rather than restating it, and the
-- bridge is where the h-level hypotheses become visible: `Completes`
-- needs `isSet Y`, `isSet E` to imply `isEmbedding`, while §1–§3 need
-- none.  `FiniteInformation`'s cardinality corollary
-- `targetFiber-card≤` bounds `card C` below by the TARGET values alive
-- in a fibre, relative to a decoder; `fiberCard≤` here bounds it below
-- by the fibre itself, with no target and no decoder.  Neither implies
-- the other as stated.
--
-- `Cubical.Functions.Fibration.totalEquiv` (HoTT Lemma 4.8.2) is the
-- universal property doing the work in §3: `certIso` is precisely
-- currying `X → E` along `X ≃ Σ Y (fiber f)`.  It is written out
-- directly because in that form one round trip is definitional, which
-- is the point being made.
--
-- PRIOR ART.  `Cubical.Foundations.Equiv.Fiberwise.fibers-total` is HoTT
-- Thm 4.7.6:
--
--     fiber (λ (a , p) → a , g a p) (a , q)  ≅  fiber (g a) q
--
-- for a fibrewise map `g : ∀ a → P a → Q a`.  §1 IS that theorem, at
-- `P = fiber f`, `Q = λ _ → E`, transported along
-- `X ≃ Σ Y (fiber f)`.  What §1 adds is exactly what the transport
-- costs: `fibers-total`'s four components are `J`/`JRefl` arguments,
-- while §1's source is `X` itself and its target family is CONSTANT, so
-- both round trips are `refl` and `fiberIso` computes.  The derived
-- version is available and is strictly weaker in computational
-- content.
------------------------------------------------------------------------

module NaturalMachine.CertificateFibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber ; invIsEq)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; invIso ; isoToEquiv)
open import Cubical.Foundations.HLevels using (isOfHLevelRetractFromIso ; isSet×)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.FinSet using (isFinSet ; card)
open import Cubical.Data.FinSet.Cardinality using (card↪Inequality')
open import Cubical.Functions.Embedding
  using (isEmbedding ; hasPropFibers ; _↪_ ; injEmbedding
        ; isEmbedding→hasPropFibers ; hasPropFibers→isEmbedding
        ; Equiv→Embedding ; compEmbedding)

open import NaturalMachine.FiniteInformation using (Completes)

private
  variable
    ℓx ℓy ℓe : Level

module _ {X : Type ℓx} {Y : Type ℓy} {E : Type ℓe} (f : X → Y) where

  ------------------------------------------------------------------
  -- 1.  THE RE-BRACKETING
  --
  -- `recorded c` is the note's "recorded update"
  -- `A_q ↦ (B , -q)`; `onFiber c y` is the certificate read on one
  -- fibre of the state map.  The Iso between their fibres is Σ-eta.
  ------------------------------------------------------------------

  recorded : (X → E) → X → Y × E
  recorded c x = (f x , c x)

  onFiber : (c : X → E) (y : Y) → fiber f y → E
  onFiber c y u = c (fst u)

  fiberIso : (c : X → E) (y : Y) (e : E)
           → Iso (fiber (recorded c) (y , e)) (fiber (onFiber c y) e)
  Iso.fun      (fiberIso c y e) (x , p)       = (x , cong fst p) , cong snd p
  Iso.inv      (fiberIso c y e) ((x , p) , q) = x , ΣPathP (p , q)
  Iso.rightInv (fiberIso c y e) _             = refl
  Iso.leftInv  (fiberIso c y e) _             = refl

  ------------------------------------------------------------------
  -- 2.  THE TRANSFER
  --
  -- `isEmbedding` is `hasPropFibers`; §1 is a fibrewise Iso; so the
  -- two statements are the same statement.  Both directions of the
  -- note's argument, with the orthogonality appeal deleted.
  ------------------------------------------------------------------

  recorded→onFiber : (c : X → E)
                   → isEmbedding (recorded c)
                   → (y : Y) → isEmbedding (onFiber c y)
  recorded→onFiber c emb y =
    hasPropFibers→isEmbedding
      (λ e → isOfHLevelRetractFromIso 1 (invIso (fiberIso c y e))
               (isEmbedding→hasPropFibers emb (y , e)))

  onFiber→recorded : (c : X → E)
                   → ((y : Y) → isEmbedding (onFiber c y))
                   → isEmbedding (recorded c)
  onFiber→recorded c h =
    hasPropFibers→isEmbedding
      (λ ye → isOfHLevelRetractFromIso 1 (fiberIso c (fst ye) (snd ye))
                (isEmbedding→hasPropFibers (h (fst ye)) (snd ye)))

  -- The note's item 2, in full generality: a certificate that makes the
  -- recorded update injective embeds every fibre of the state map.
  fiber↪cert : (c : X → E) → isEmbedding (recorded c) → (y : Y) → fiber f y ↪ E
  fiber↪cert c emb y = onFiber c y , recorded→onFiber c emb y

  ------------------------------------------------------------------
  -- 3.  A CERTIFICATE IS A TRIVIALISATION
  --
  -- Currying along `X ≃ Σ Y (fiber f)` (HoTT 4.8.2).  Written out so
  -- that `leftInv` is `refl`: recovering `c` from its fibrewise
  -- restrictions is not a theorem, it is η.
  ------------------------------------------------------------------

  toTriv : (X → E) → ((y : Y) → fiber f y → E)
  toTriv c = onFiber c

  fromTriv : ((y : Y) → fiber f y → E) → (X → E)
  fromTriv t x = t (f x) (x , refl)

  toTriv-fromTriv : (t : (y : Y) → fiber f y → E) (y : Y) (u : fiber f y)
                  → toTriv (fromTriv t) y u ≡ t y u
  toTriv-fromTriv t y (x , p) =
    J (λ y' p' → t (f x) (x , refl) ≡ t y' (x , p')) refl p

  certIso : Iso (X → E) ((y : Y) → fiber f y → E)
  Iso.fun      certIso = toTriv
  Iso.inv      certIso = fromTriv
  Iso.rightInv certIso t = funExt (λ y → funExt (toTriv-fromTriv t y))
  Iso.leftInv  certIso c = refl

  -- Attainment, and the honest shape of it: the input is a FAMILY of
  -- embeddings indexed by `Y`, not a bound on their sizes.
  triv→isEmbedding : (t : (y : Y) → fiber f y ↪ E)
                   → isEmbedding (recorded (fromTriv (λ y → fst (t y))))
  triv→isEmbedding t =
    onFiber→recorded (fromTriv (λ y → fst (t y)))
      (λ y → subst isEmbedding
               (sym (funExt (toTriv-fromTriv (λ y' → fst (t y')) y)))
               (snd (t y)))

  ------------------------------------------------------------------
  -- 4.  THE NUMBER, WHERE THE NUMBER EXISTS
  --
  -- Everything above is finiteness-free.  This is the only place a
  -- cardinality appears, and it is a corollary of §2, not a separate
  -- argument.  It is the note's "minimum environment dimension ≥
  -- maximum fibre cardinality" — the ≥ half, which is the half that is
  -- a theorem.
  ------------------------------------------------------------------

  fiberCard≤ : (c : X → E) → isEmbedding (recorded c)
             → (y : Y) (finFib : isFinSet (fiber f y)) (finE : isFinSet E)
             → card (fiber f y , finFib) ≤ card (E , finE)
  fiberCard≤ c emb y finFib finE =
    card↪Inequality' (fiber f y , finFib) (E , finE)
      (onFiber c y) (recorded→onFiber c emb y)

  ------------------------------------------------------------------
  -- 6.  BRIDGE TO `NaturalMachine.FiniteInformation`
  --
  -- `Completes f c` is the element-wise injectivity of `recorded c`.
  -- One direction is free; the other buys `isEmbedding` from
  -- injectivity and must pay `isSet` for it.  Stated here so that the
  -- two modules are visibly the same subject at two h-levels, and so
  -- that nothing above silently re-proves `FiniteInformation`.
  ------------------------------------------------------------------

  isEmbedding→Completes : (c : X → E) → isEmbedding (recorded c) → Completes f c
  isEmbedding→Completes c emb x x' p = invIsEq (emb x x') p

  Completes→isEmbedding : (c : X → E) → isSet Y → isSet E
                        → Completes f c → isEmbedding (recorded c)
  Completes→isEmbedding c isSetY isSetE comp =
    injEmbedding (isSet× isSetY isSetE) (λ {w} {x} p → comp w x p)

------------------------------------------------------------------------
-- 5.  THE CORPUS INSTANCE: THE SMITH QUOTIENT NO-GO
--
-- `A_q = ((2,0),(2q+1,7))` for `q : ℕ`.  Every source reaches the same
-- post-state `B`, so the state map is constant and its single fibre is
-- `ℕ`.  Therefore every certificate alphabet that restores injectivity
-- admits `ℕ ↪ E`.
------------------------------------------------------------------------

module SmithQuotientNoGo where

  post : ℕ → Unit
  post _ = tt

  fiberPostIso : Iso (fiber post tt) ℕ
  Iso.fun      fiberPostIso (q , _) = q
  Iso.inv      fiberPostIso q       = q , refl
  Iso.rightInv fiberPostIso _       = refl
  Iso.leftInv  fiberPostIso _       = refl

  no-finite-controller :
    {E : Type ℓe} (c : ℕ → E) → isEmbedding (recorded post c) → ℕ ↪ E
  no-finite-controller {E = E} c emb =
    compEmbedding
      (fiber↪cert post c emb tt)
      (Equiv→Embedding (isoToEquiv (invIso fiberPostIso)))
