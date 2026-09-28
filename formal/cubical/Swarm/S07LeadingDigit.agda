{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S07LeadingDigit
--
-- `notes/REFINING_DILATION.md` (absent from this repository) (Theorem Q) prices the coherent
-- environment register of a refining organism at
--
--     d_E(t) = ⌈ t / p^D(t) ⌉ ,   D(t) = ⌊ log_p t ⌋ ,
--
-- and squeezes it:  1 ≤ d_E(t) ≤ p  for every t (Archimedes' lens).
--
-- This module isolates what d_E actually IS, with no division, no
-- logarithm and no floating point anywhere:
--
--   `Bracket q t e`  says   e·q < t ≤ (e+1)·q ,  i.e.  ⌈t/q⌉ = e+1.
--
--   * `bracket-unique`  — the index e is unique, so `Bracket` really is
--                         a function of (q,t): the ceiling quotient.
--   * `dE-squeeze`      — from q ≤ t < p·q,  1 ≤ e+1 ≤ p.  (Theorem Q.)
--   * `bracket-exact`   — t = a·q  ⇒  index a-1, i.e. d_E = a.
--   * `bracket-roundup` — t = a·q+s, 0<s≤q  ⇒  index a, i.e. d_E = a+1.
--     Together: WITH q = p^D, d_E(t) is the leading base-p digit of t,
--     rounded up by one iff any lower digit is nonzero.
--   * `bracket-reset`   — at t = q (a power of p) the index is 0, so
--                         d_E = 1: the register is empty.
--   * `scale-inv`       — Bracket q t e → Bracket (q·p) (t·p) e.
--                         d_E is invariant under t ↦ p·t.  This is the
--                         bubble (Uhlenbeck's lens): the statistic is a
--                         function on the multiplicative scale circle
--                         ℝ/(log p)ℤ, which is exactly why its NATURAL
--                         density does not converge and its LOGARITHMIC
--                         density does (Benford in base p).
--
-- No postulates, no holes.
------------------------------------------------------------------------

module Swarm.S07LeadingDigit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)

private
  variable
    p q t a s e e' : ℕ

------------------------------------------------------------------------
-- 0.  The bracket:  ⌈ t / q ⌉ = e + 1, stated without division.
------------------------------------------------------------------------

Bracket : ℕ → ℕ → ℕ → Type
Bracket q t e = (e · q < t) × (t ≤ suc e · q)

------------------------------------------------------------------------
-- 1.  Right cancellation for < .  (Everything below runs on this.)
------------------------------------------------------------------------

cancelʳ< : a · q < e · q → a < e
cancelʳ< {a} {q} {e} h with a ≟ e
... | lt r = r
... | eq r = ⊥rec (¬m<m (subst (λ z → z · q < e · q) r h))
... | gt r = ⊥rec (¬m<m (<≤-trans h (≤-·k (<-weaken r))))

------------------------------------------------------------------------
-- 2.  Uniqueness:  Bracket is single-valued, hence a function.
------------------------------------------------------------------------

bracket-unique : Bracket q t e → Bracket q t e' → e ≡ e'
bracket-unique {q} {t} {e} {e'} (lo , hi) (lo' , hi') with e ≟ e'
... | eq r = r
... | lt r = ⊥rec (¬m<m (≤<-trans (≤-trans hi (≤-·k r)) lo'))
... | gt r = ⊥rec (¬m<m (≤<-trans (≤-trans hi' (≤-·k r)) lo))

------------------------------------------------------------------------
-- 3.  Theorem Q, exactly:  q ≤ t < p·q  ⇒  1 ≤ d_E ≤ p, d_E = e+1.
--     (Only the upper hypothesis is needed; q ≤ t is what makes the
--      leading digit nonzero, recorded separately as `digit-lower`.)
------------------------------------------------------------------------

dE-upper : Bracket q t e → t < p · q → suc e ≤ p
dE-upper (lo , _) h = cancelʳ< (<-trans lo h)

dE-lower : 1 ≤ suc e
dE-lower = suc-≤-suc zero-≤

dE-squeeze : Bracket q t e → t < p · q → (1 ≤ suc e) × (suc e ≤ p)
dE-squeeze b h = dE-lower , dE-upper b h

------------------------------------------------------------------------
-- 4.  d_E is the leading base-p digit, rounded up iff the tail is ≠ 0.
--     Write t = a·q + s with s < q and q = p^D.
------------------------------------------------------------------------

·-lt-suc : 0 < q → a · q < suc a · q
·-lt-suc {q} {a} h =
  subst2 _<_ (+-zero (a · q)) (+-comm (a · q) q) (<-k+ h)

-- exact multiple of the scale: no rounding, index a-1, so d_E = a
bracket-exact : 0 < q → t ≡ suc a · q → Bracket q t a
bracket-exact {q} {t} {a} h teq =
    subst (λ z → a · q < z) (sym teq) (·-lt-suc {q} {a} h)
  , subst (_≤ suc a · q) (sym teq) ≤-refl

-- nonzero tail: index a, so d_E = a+1
bracket-roundup : 0 < s → s ≤ q → t ≡ a · q + s → Bracket q t a
bracket-roundup {s} {q} {t} {a} h0 hq teq =
    subst (λ z → a · q < z) (sym teq)
      (subst (_< a · q + s) (+-zero (a · q)) (<-k+ h0))
  , subst (_≤ suc a · q) (sym teq)
      (subst (a · q + s ≤_) (+-comm (a · q) q) (≤-k+ hq))

-- the leading digit really is a digit: q ≤ t < p·q and t = a·q+s give 1 ≤ a < p
digit-lower : 0 < q → q ≤ t → t ≡ a · q + s → s < q → 0 < a
digit-lower {q} {t} {a} {s} hq hqt teq hs with a ≟ 0
... | eq r = ⊥rec (¬m<m (≤<-trans hqt
      (subst (_< q) (sym (teq ∙ cong (λ z → z · q + s) r)) hs)))
... | lt r = ⊥rec (¬-<-zero r)
... | gt r = r

digit-upper : t < p · q → t ≡ a · q + s → a < p
digit-upper {t} {p} {q} {a} {s} h teq =
  cancelʳ< (≤<-trans (subst (a · q ≤_) (sym teq) (_ , +-comm s (a · q))) h)

------------------------------------------------------------------------
-- 5.  The reset:  at a power of p the environment register is empty.
------------------------------------------------------------------------

bracket-reset : 0 < q → Bracket q q 0
bracket-reset {q} h = h , subst (q ≤_) (sym (+-zero q)) ≤-refl

------------------------------------------------------------------------
-- 6.  THE BUBBLE.  d_E is invariant under the scaling t ↦ p·t.
--     Hence d_E is a function on the scale circle, its empirical
--     distribution over {1..N} depends on N only through {log_p N},
--     and no natural density exists (p ≥ 3).  The logarithmic density
--     is the Haar average over this invariance — that is Theorem 3 of
--     collab/swarm/2026-08-14/swarm-0814-07-leading-digit-bubble.md (absent from this repository).
------------------------------------------------------------------------

scale-inv : ∀ {p'} → Bracket q t e → Bracket (q · suc p') (t · suc p') e
scale-inv {q} {t} {e} {p'} (lo , hi) =
    subst (_< t · suc p') (sym (·-assoc e q (suc p'))) (<-·sk lo)
  , subst (t · suc p' ≤_) (sym (·-assoc (suc e) q (suc p'))) (≤-·k hi)
