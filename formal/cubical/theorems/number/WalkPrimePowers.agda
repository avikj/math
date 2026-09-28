{-# OPTIONS --cubical --safe --no-import-sorts #-}

-- WALK_FORCING_LAW.md (absent from this repository) STATEMENT (2), composed:
--
--     the walk installs exactly the prime powers, in increasing order.
--
-- The three pieces:
--
--   §(b)   WalkBridge     the installs are the jump points, in order
--   §(c)⇐  WalkJumps      a prime power is a jump point
--   §(c)⇒  CoprimeSplitting  a least non-divisor is a prime power
--
-- This file composes them.  Two things worth noting:
--
--   * `installs-are-prime-powers` really is three lines, and -- worth
--     noting -- it does not use §(b) at all.  It is §(c)⇒ applied
--     directly to `next-lnd`.  The ordering theorem is not needed to
--     know each install is a prime power.
--
--   * `prime-powers-are-installed` is NOT renaming.  §(c)⇐ gives that a
--     prime power is a jump point, and §(b) gives that the walk skips no
--     jump point BETWEEN CONSECUTIVE INSTALLS -- a local statement.
--     Getting from "no jump is skipped locally" to "every jump is hit"
--     needs an induction that locates a given jump point in the stream,
--     which in turn needs `install-grows` (n < install n) to bound the
--     search.  That is `locate` below, and it is the only genuinely new
--     argument in the file.
--
-- Together with `WalkBridge.install-mono` (strictly increasing), the two
-- theorems below are statement (2) with no residue.

module WalkPrimePowers where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import WalkCapacity using (range1)
open import LCMExists using (lcmList-isLCM)
open import WalkUnconditional using (cap)
open import WalkJumps
  using (IsPrime ; prime-0< ; prime-power-not-covered)
open import CoprimeSplitting
  using (IsPrimePower ; leastNonDivisor-isPrimePower)
open import WalkBridge
  using ( Jump ; next ; next-2≤ ; next-lnd ; install ; install-1≤
        ; install-mono ; install-exhaustive ; below-first ; ·-pos )

------------------------------------------------------------------------
-- §(c)⇒ ON THE STREAM: every install is a prime power.
--
-- Three lines, and no §(b): the walk's step already carries a
-- `LeastNonDivisor` certificate (`next-lnd`), which is exactly the
-- hypothesis CoprimeSplitting's theorem consumes.
------------------------------------------------------------------------

installs-are-prime-powers : (n : ℕ) → IsPrimePower (install n)
installs-are-prime-powers zero =
  leastNonDivisor-isPrimePower (cap 1) (next 1) (next-2≤ 1) (next-lnd 1)
installs-are-prime-powers (suc n) =
  leastNonDivisor-isPrimePower
    (cap (install n)) (next (install n))
    (next-2≤ (install n)) (next-lnd (install n))

------------------------------------------------------------------------
-- §(c)⇐ ON THE STREAM: every prime power is a jump point.
------------------------------------------------------------------------

pos-form : (a : ℕ) → 0 < a → Σ[ b ∈ ℕ ] a ≡ suc b
pos-form zero    0<a = Empty.rec (¬-<-zero 0<a)
pos-form (suc b) _   = b , refl

^-pos : (p a : ℕ) → 0 < p → 0 < (p ^ a)
^-pos p zero    _   = suc-≤-suc zero-≤
^-pos p (suc a) 0<p = ·-pos p (p ^ a) 0<p (^-pos p a 0<p)

prime-power-is-jump : (k : ℕ) → IsPrimePower (suc k) → Jump k
prime-power-is-jump k (p , a , pp , 0<a , pa≡sk) =
  subst (λ z → ¬ (z ∣ cap k)) pb≡sk
    (prime-power-not-covered p b k (cap k) pp (sym pb≡sk)
      (lcmList-isLCM (range1 k)))
  where
  b : ℕ
  b = pos-form a 0<a .fst

  pb≡sk : (p ^ suc b) ≡ suc k
  pb≡sk = subst (λ x → (p ^ x) ≡ suc k) (pos-form a 0<a .snd) pa≡sk

------------------------------------------------------------------------
-- FROM LOCAL EXHAUSTIVENESS TO GLOBAL: every jump point is installed.
--
-- `install-exhaustive` says nothing is skipped BETWEEN
-- install n and install (suc n); to conclude that a given jump point k
-- is hit, one must first locate k in the stream, and that needs the
-- stream to outrun the index.
------------------------------------------------------------------------

install-grows : (n : ℕ) → n < install n
install-grows zero    = ≤-trans (suc-≤-suc zero-≤) (install-1≤ zero)
install-grows (suc n) = ≤<-trans (install-grows n) (install-mono n)

-- search downward from a stage that has already overshot
locate : (k b : ℕ) → suc k < install b → Jump k → Σ[ n ∈ ℕ ] install n ≡ suc k
locate k zero    sk<i0  jk = Empty.rec (below-first k sk<i0 jk)
locate k (suc b) sk<isb jk with splitℕ-< (suc k) (install b)
... | inl sk<ib  = locate k b sk<ib jk
... | inr ib≤sk with ≤-split ib≤sk
...   | inr ib≡sk = b , ib≡sk
...   | inl ib<sk =
  Empty.rec (install-exhaustive b k (pred-≤-pred ib<sk) sk<isb jk)

jump-is-installed : (k : ℕ) → Jump k → Σ[ n ∈ ℕ ] install n ≡ suc k
jump-is-installed k = locate k (suc k) (install-grows (suc k))

------------------------------------------------------------------------
-- STATEMENT (2), both directions.
------------------------------------------------------------------------

prime-powers-are-installed :
  (q : ℕ) → IsPrimePower q → Σ[ n ∈ ℕ ] install n ≡ q
prime-powers-are-installed q ipp@(p , a , pp , 0<a , pa≡q) =
  subst (λ z → Σ[ n ∈ ℕ ] install n ≡ z) (sym q≡sk)
    (jump-is-installed k (prime-power-is-jump k (subst IsPrimePower q≡sk ipp)))
  where
  0<q : 0 < q
  0<q = subst (0 <_) pa≡q (^-pos p a (prime-0< p pp))

  k : ℕ
  k = pos-form q 0<q .fst

  q≡sk : q ≡ suc k
  q≡sk = pos-form q 0<q .snd

------------------------------------------------------------------------
-- What the two of them, plus WalkBridge.install-mono, say together:
--
--   install : ℕ → ℕ is strictly increasing            (install-mono)
--   its image lands in the prime powers               (installs-are-prime-powers)
--   its image contains every prime power              (prime-powers-are-installed)
--
-- i.e. `install` is the increasing enumeration of the prime powers, and
-- it is the walk's own execution.  Statement (2) of WALK_FORCING_LAW.md (absent from this repository),
-- as a term.
--
-- It also COMPUTES, through WalkBridge's `next-1 .. next-5`: the stream
-- begins 2, 3, 4, 5, 7 -- kernel-evaluated, with 6 skipped because 6 is
-- not a prime power, which is `CoprimeSplitting.6-not-prime-power`
-- rather than a coincidence of the search.
------------------------------------------------------------------------
