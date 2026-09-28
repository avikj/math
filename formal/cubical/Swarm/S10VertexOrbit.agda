{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S10VertexOrbit
--
-- THE FEASIBLE VERTEX OF A ROOT CAGE IS ESSENTIALLY UNIQUE.
--
-- Context.  `notes/SHARP_CAGE_DOES_NOT_MAKE_DEGREE_TEN_TRACTABLE.md` (absent from this repository) and
-- `natural_machine_cpu_loop_rust/cage.rs` bound the Vieta coefficients of a
-- totally nonreal degree-2m divisor with unit constant term by maximizing
-- each elementary symmetric function e_k over the LOG-POLYTOPE
--
--     Δ = { x ∈ [β, α]^m  :  Σ x_k = 0 },      β = log B ≤ 0 ≤ α = log A.
--
-- The note's argument is: e_k is a symmetric convex function of the log
-- radii, hence maximized at a VERTEX.  The program instead computes ONE
-- vertex (the first feasible index s in its loop) and reads off EVERY
-- coefficient bound from that single vertex.  Those are different claims:
-- distinct convex functions may be maximized at distinct vertices, so
-- "maximized at a vertex" does not licence "maximized at THIS vertex".
--
-- This module closes that gap.  Up to the S_m-action permuting coordinates
-- (under which every e_k is invariant), Δ has at most two vertex indices,
-- they are adjacent, and in the two-index case both indices name the SAME
-- multiset of radii.  So there is exactly one vertex orbit, one maximizer
-- for all k simultaneously, and the program's shortcut is sound.
--
-- Encoding.  A vertex pins m-1 = n coordinates at bounds: s of them at α,
-- u = n - s of them at β, with compensator c = -sα - uβ.  Writing a = α ≥ 0
-- and b = -β ≥ 0 (both naturals in any common additive scale) the vertex is
-- feasible, i.e. β ≤ c ≤ α, exactly when
--
--     s·a ≤ (u+1)·b       (that is  c ≤ α)
--     u·b ≤ (s+1)·a       (that is  β ≤ c)
--
-- which is `Feas s u` below.  Only the ordered-abelian-group structure of
-- the exponents is used, so ℕ is not a restriction on the argument, only on
-- the scale in which α and β are expressed.  No real analysis enters: the
-- whole content is that the sequence s ↦ c_s is arithmetic with common
-- difference exactly the width α - β of the feasibility window, so it
-- cannot step over the window, and cannot land in it twice except by
-- hitting both endpoints at once.
--
-- Nothing here is postulated and nothing is left open.
------------------------------------------------------------------------

module Swarm.S10VertexOrbit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥

-- a = α  (the upper log-radius, ≥ 0),  b = -β  (minus the lower one, ≥ 0)
module Cage (a b : ℕ) where

  ----------------------------------------------------------------------
  -- feasibility of the vertex index s, with u = n - s
  ----------------------------------------------------------------------

  Feas : ℕ → ℕ → Type₀
  Feas s u = (s · a ≤ suc u · b) × (u · b ≤ suc s · a)

  ≡→≤ : {m n : ℕ} → m ≡ n → m ≤ n
  ≡→≤ p = 0 , p

  stepA : (s : ℕ) → s · a ≤ suc s · a
  stepA s = ≤-·k {s} {suc s} {a} ≤-sucℕ

  stepB : (u : ℕ) → u · b ≤ suc u · b
  stepB u = ≤-·k {u} {suc u} {b} ≤-sucℕ

  ----------------------------------------------------------------------
  -- (1) EXISTENCE.  Some vertex index is feasible, for every n.
  --
  -- Induction on n.  At n = 0 the single coordinate is the compensator and
  -- it is 0 ∈ [β, α].  At the step, comparing (u+1)·b with (s+1)·a decides
  -- whether the new pinned coordinate goes to the lower or the upper bound;
  -- ℕ's order is total, so one of the two always works.  This is the exact
  -- content of "the sequence cannot step over the window".
  ----------------------------------------------------------------------

  exists : (n : ℕ) → Σ[ s ∈ ℕ ] Σ[ u ∈ ℕ ] ((s + u ≡ n) × Feas s u)
  exists zero = 0 , 0 , refl , (zero-≤ , zero-≤)
  exists (suc n) with exists n
  ... | (s , u , p , (f1 , f2)) with splitℕ-≤ (suc u · b) (suc s · a)
  ...   | inl q = s , suc u , (+-suc s u ∙ cong suc p)
                , (≤-trans f1 (stepB (suc u)) , q)
  ...   | inr q = suc s , u , cong suc p
                , (<-weaken q , ≤-trans f2 (stepA (suc s)))

  ----------------------------------------------------------------------
  -- (2) DEGENERACY IS FORCED.  If two distinct indices over the same n are
  -- both feasible then the compensator of the lower one sits exactly on the
  -- upper bound:  c_s = α,  i.e.  (s+1)·a = u·b.
  ----------------------------------------------------------------------

  -- s + u ≡ s' + u' and s < s' force u' < u
  shrink : (s u s' u' : ℕ) → s + u ≡ s' + u' → suc s ≤ s' → suc u' ≤ u
  shrink s u s' u' e le =
    ≤-k+-cancel
      (subst (_≤ s + u) (sym (+-suc s u'))
        (subst (suc s + u' ≤_) (sym e) (≤-+k le)))

  degen : (s u s' u' : ℕ) → s + u ≡ s' + u' → suc s ≤ s'
        → Feas s u → Feas s' u' → suc s · a ≡ u · b
  degen s u s' u' e le (_ , f2) (g1 , _) =
    ≤-antisym (≤-trans (≤-·k le)
                       (≤-trans g1 (≤-·k (shrink s u s' u' e le))))
              f2

  ----------------------------------------------------------------------
  -- (3) THE CONVERSE.  That single equation is not merely necessary; when
  -- it holds, both s and s+1 really are feasible.  So "two feasible
  -- indices" is *equivalent* to  (s+1)·a = (u'+1)·b,  which pins the
  -- degeneracy down exactly rather than bounding it.
  ----------------------------------------------------------------------

  degen→both : (s u' : ℕ) → suc s · a ≡ suc u' · b
             → Feas s (suc u') × Feas (suc s) u'
  degen→both s u' q =
      ( ≤-trans (stepA s) (≤-trans (≡→≤ q) (stepB (suc u')))
      , ≡→≤ (sym q) )
    , ( ≡→≤ q
      , ≤-trans (stepB u') (≤-trans (≡→≤ (sym q)) (stepA (suc s))) )

  ----------------------------------------------------------------------
  -- (4) THE DICHOTOMY.  Any two feasible indices over the same n either
  -- coincide, or one of them is degenerate in the sense of (2)/(3).
  -- Contrapositive: no degeneracy ⇒ the feasible index is unique.
  ----------------------------------------------------------------------

  dichotomy : (s u s' u' : ℕ) → s + u ≡ s' + u' → Feas s u → Feas s' u'
            → (s ≡ s') ⊎ ((suc s · a ≡ u · b) ⊎ (suc s' · a ≡ u' · b))
  dichotomy s u s' u' e F F' with s ≟ s'
  ... | lt p = inr (inl (degen s u s' u' e p F F'))
  ... | eq p = inl p
  ... | gt p = inr (inr (degen s' u' s u (sym e) p F' F))

  ----------------------------------------------------------------------
  -- (5) AT MOST TWO, AND ADJACENT.  When the cage is nondegenerate in the
  -- upper direction (α > 0, i.e. A > 1) a second feasible index can only
  -- be the immediate successor of the first.  With (2) this is the full
  -- statement: the feasible set is {s} or {s, s+1}.
  ----------------------------------------------------------------------

  zeroFactor : (d : ℕ) → 0 < a → d · a ≡ 0 → d ≡ 0
  zeroFactor zero _ _ = refl
  zeroFactor (suc d) pa p =
    ⊥.rec (¬-<-zero (subst (0 <_) (fst (m+n≡0→m≡0×n≡0 p)) pa))

  adjacent : (s u s' u' : ℕ) → s + u ≡ s' + u' → suc s ≤ s'
           → Feas s u → Feas s' u' → 0 < a → s' ≡ suc s
  adjacent s u s' u' e le F@(_ , f2) F'@(g1 , _) pa =
    sym pd ∙ cong (_+ suc s) d≡0
    where
      pd : fst le + suc s ≡ s'
      pd = snd le

      chainB : s' · a ≤ suc s · a
      chainB = ≤-trans g1 (≤-trans (≤-·k (shrink s u s' u' e le)) f2)

      eqa : fst le · a + suc s · a ≡ 0 + suc s · a
      eqa = ·-distribʳ (fst le) (suc s) a
          ∙ cong (_· a) pd
          ∙ ≤-antisym chainB (≤-·k le)

      d≡0 : fst le ≡ 0
      d≡0 = zeroFactor (fst le) pa (inj-+m eqa)

------------------------------------------------------------------------
-- (6) RECIPROCATION BUYS NOTHING.
--
-- If q is admissible then so are the root radii of its reversal
-- q*(x) = x^{2m} q(1/x), which lie in [1/A, 1/B] with product 1 and give
-- |a_{2m-k}(q)| = |a_k(q*)| ≤ (majorant for the cage (1/B, 1/A)).  That is
-- a second, free bound on every coefficient, and the obvious question is
-- whether the coordinatewise minimum of the two is sharper.
--
-- It is not, and the reason is (1)-(5).  Reciprocation sends log-radii
-- x ↦ -x, so the cage (A, B) with (α, β) = (a, -b) becomes the cage
-- (1/B, 1/A) with (α', β') = (b, -a): the SAME module with a and b
-- swapped.  Under that swap the feasibility conditions exchange places
-- verbatim, so the feasible indices correspond by (s, u) ↦ (u, s) and the
-- reciprocal cage's vertex orbit is exactly the reciprocal of the original
-- one.  Hence its majorants are b'_k = b_{2m-k}, the minimum is the
-- original bound, and nothing is gained.
--
-- The proof is the identity on the pair, with its components exchanged.
------------------------------------------------------------------------

reciprocal : (a b s u : ℕ) → Cage.Feas a b s u → Cage.Feas b a u s
reciprocal a b s u (p , q) = q , p

reciprocal-involutive : (a b s u : ℕ) (F : Cage.Feas a b s u)
                      → reciprocal b a u s (reciprocal a b s u F) ≡ F
reciprocal-involutive a b s u F = refl

------------------------------------------------------------------------
-- What this buys, stated outside the module.
--
-- Fix a cage (A, B) with B ≤ 1 ≤ A and write a = log A, b = -log B in a
-- common scale.  Combining (1), (2), (3), (5):
--
--   * a feasible vertex index always exists;
--   * the feasible set is {s} or {s, s+1};
--   * it is {s, s+1} exactly when (s+1)·a = u·b with u = n - s, i.e. when
--     A^{s+1} B^{n-s} = 1;
--   * in that case c_s = α and c_{s+1} = β, so the two indices name the
--     radius multisets  {α^s, β^u, α}  and  {α^{s+1}, β^{u-1}, β},  which
--     are the same multiset  {α^{s+1}, β^{u}}.
--
-- Hence Δ has exactly ONE vertex orbit under S_m, every symmetric convex
-- function on Δ attains its maximum there, and reading all the Vieta
-- majorants off a single feasible vertex is valid.
--
-- Two instances, both exact:
--
--   sharp cage  (A, B) = (√2, φ⁻¹):  A^{s+1} B^{n-s} = 1 would need
--     2^{s+1} = φ^{2(n-s)} with s+1 ≥ 1.  If n = s the right side is 1 and
--     the left is ≥ 2.  If n > s then φ^{2k} = (L_{2k} + F_{2k}√5)/2 with
--     F_{2k} ≠ 0 is irrational while 2^{s+1} is not.  So the feasible index
--     is unique at every degree and cage.rs's loop never had a choice.
--
--   generic cage (A, B) = (2, ½):  the condition reads s+1 = n-s, so the
--     feasible set has TWO indices exactly when n = m-1 is odd, i.e. at
--     degrees 4, 8, 12, ....  cage.rs takes the first and never remarks on
--     it; the multiset identity above is what makes that harmless.
------------------------------------------------------------------------
