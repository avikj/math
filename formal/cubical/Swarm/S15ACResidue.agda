{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S15ACResidue
--
-- WHAT THIS SETTLES
--
-- `runtime/execute/acmatch.py` (absent from this repository) opens with a 113-line docstring headed
-- "THE SEMANTICS, STATED BEFORE THE CODE".  It permits an AC residue at
-- the ROOT of a pattern and forbids one at every INNER AC node, and it
-- gives this reason:
--
--     an inner residue would make the instantiated left side a
--     *different term* from the subject ((#0+#1) matched against a+b+c
--     with residue c claims the subject is a+b, which it is not), so an
--     inner residue is unsound for a rewrite, not merely expensive.
--
-- That reason is false, and provably so *by the module's own root
-- construction*.  At the root the instantiated base left side is also a
-- different term from the subject -- `mul ?a ?a` against `mul x y x z`
-- is not `mul x x` -- and the module repairs exactly that by building a
-- DERIVED LEMMA whose left side is the pattern EXTENDED by fresh residue
-- variables (`_ac_try` -> `derive_ac_lemma`, gates G1-G5).  The same
-- extension is available verbatim at an inner node: replace the inner
-- node `q` by `q` with the residue variables appended.  Gate G3
-- (`ac_canonical` agreement) and gate G4 (`poly_equal`) both still make
-- sense there.  So "different term from the subject" cannot be what
-- separates the two cases.
--
-- What actually separates them is UNIFORMITY of the derived RIGHT side.
-- The module's root construction is
--
--     rhs' = mk(lhs.kind, (base.rhs,) + rvars)                (sec. 4)
--
-- a function of the base RIGHT side and the residue ALONE -- it never
-- inspects `base.lhs`.  This file proves:
--
--   * `ACRoot.rootSound` / `ACRoot.rootUniform` -- at the root that
--     construction IS sound, for any associative-commutative operator,
--     any arity, any permutation, any residue; and it is uniform, i.e.
--     two base lemmas with the same right side and the same residue
--     force the same derived value.  Gates G3 and G4 are exactly the
--     two hypotheses.
--
--   * `noUniformInner` -- at an inner node NO such function exists.
--     Not "the module has not implemented one": none exists.  ONE base
--     lemma, ONE syntactically identical inner AC node occurring at two
--     positions, ONE residue, TWO correct and unequal derived right
--     sides (`ext₁-correct`, `ext₂-correct`, `7≢8`).
--
-- So the docstring forbids the right thing for the wrong reason.  The
-- correct statement of the obstruction is:
--
--     Root residue is an instance of CONGRUENCE: the derived left side
--     is C[base.lhs] for the context C = (·) ⊕ Z, so the derived right
--     side is C[base.rhs], uniformly.  Inner residue is not a
--     congruence instance at all: the derived left side is
--     base.lhs[p := q ⊕ Z], a SUBSTITUTION INTO the pattern rather than
--     a context around it.  Nothing in equational logic sends
--     base.lhs = base.rhs to a statement about base.lhs[p := q ⊕ Z],
--     and the required right side depends on how the surrounding
--     context acts on position p -- additively at one occurrence,
--     multiplicatively at another, in the single witness below.
--
-- METHOD NOTE (two lenses, which disagree here).  Poincare:
-- the AC matcher is an exponential search with no closed form, so study
-- the qualitative flow -- which is what the docstring does, and it
-- misidentifies the invariant.  Gauss: build the scaffolding, publish
-- the theorem.  The theorem is `rootUniform` + `noUniformInner`; the
-- scaffolding is the 1040-line matcher.
--
-- No postulates, no holes.
------------------------------------------------------------------------

module Swarm.S15ACResidue where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Nat

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- PART 1.  The root: residue extension is congruence, and it is uniform
------------------------------------------------------------------------
--
-- An AC node is its argument LIST modulo permutation; `⊙` is the fold
-- that gives it a value.  This is exactly `crystallize.derivation`'s flat
-- n-ary `Sum`/`Prod` together with `poly_equal`'s semantics, with no
-- commitment to which operator it is.

module ACRoot
  {A : Type ℓ}
  (_⊕_ : A → A → A)
  (e : A)
  (⊕-assoc : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z))
  (⊕-comm  : (x y : A) → x ⊕ y ≡ y ⊕ x)
  (⊕-unitˡ : (x : A) → e ⊕ x ≡ x)
  where

  ⊙ : List A → A
  ⊙ []       = e
  ⊙ (x ∷ xs) = x ⊕ ⊙ xs

  ⊙-++ : (xs ys : List A) → ⊙ (xs ++ ys) ≡ (⊙ xs) ⊕ (⊙ ys)
  ⊙-++ []       ys = sym (⊕-unitˡ (⊙ ys))
  ⊙-++ (x ∷ xs) ys =
    cong (x ⊕_) (⊙-++ xs ys) ∙ sym (⊕-assoc x (⊙ xs) (⊙ ys))

  -- `Ins a xs ys` : ys is xs with a inserted somewhere.
  data Ins (a : A) : List A → List A → Type ℓ where
    ins-here  : {xs : List A} → Ins a xs (a ∷ xs)
    ins-there : {b : A} {xs ys : List A} → Ins a xs ys → Ins a (b ∷ xs) (b ∷ ys)

  -- The AC-rearrangement relation on argument lists.  This is what gate
  -- G3 (`ac_canonical(lhs') == ac_canonical(base_lhs ++ residue vars)`)
  -- decides.
  data Perm : List A → List A → Type ℓ where
    perm-nil  : Perm [] []
    perm-cons : {a : A} {xs ys zs : List A}
              → Perm xs ys → Ins a ys zs → Perm (a ∷ xs) zs

  ins-sound : {a : A} {xs ys : List A} → Ins a xs ys → ⊙ ys ≡ a ⊕ (⊙ xs)
  ins-sound ins-here = refl
  ins-sound {a = a} (ins-there {b = b} {xs = xs} p) =
      cong (b ⊕_) (ins-sound p)
    ∙ sym (⊕-assoc b a (⊙ xs))
    ∙ cong (_⊕ (⊙ xs)) (⊕-comm b a)
    ∙ ⊕-assoc a b (⊙ xs)

  perm-sound : {xs ys : List A} → Perm xs ys → ⊙ xs ≡ ⊙ ys
  perm-sound perm-nil = refl
  perm-sound (perm-cons {a = a} p q) =
    cong (a ⊕_) (perm-sound p) ∙ sym (ins-sound q)

  -- THE ROOT CONSTRUCTION, `mk(lhs.kind, (base.rhs,) + rvars)`:
  -- a function of the base RIGHT side and the residue only.
  Ψroot : A → List A → A
  Ψroot r zs = r ⊕ (⊙ zs)

  -- Soundness.  `base` is gate G4 on the base lemma; `g3` is gate G3.
  -- Note the conclusion does not mention `ps`.
  rootSound : (ps rs zs ts : List A)
            → (⊙ ps) ≡ (⊙ rs)
            → Perm (ps ++ zs) ts
            → ⊙ ts ≡ Ψroot (⊙ rs) zs
  rootSound ps rs zs ts base g3 =
      sym (perm-sound g3)
    ∙ ⊙-++ ps zs
    ∙ cong (_⊕ (⊙ zs)) base

  -- Uniformity, stated so that Part 2 can refute its inner analogue:
  -- two DIFFERENT base left sides with the SAME right side and the SAME
  -- residue produce the same derived value.
  rootUniform : (ps ps' rs zs ts ts' : List A)
              → (⊙ ps)  ≡ (⊙ rs)
              → (⊙ ps') ≡ (⊙ rs)
              → Perm (ps  ++ zs) ts
              → Perm (ps' ++ zs) ts'
              → ⊙ ts ≡ ⊙ ts'
  rootUniform ps ps' rs zs ts ts' b b' g g' =
    rootSound ps rs zs ts b g ∙ sym (rootSound ps' rs zs ts' b' g')

-- The additive AC node of the substrate, as an instance.
module ACRootPlus =
  ACRoot {A = ℕ} _+_ zero (λ x y z → sym (+-assoc x y z)) +-comm (λ _ → refl)

------------------------------------------------------------------------
-- PART 2.  The inner node: no uniform derived right side exists
------------------------------------------------------------------------
--
-- One base lemma.  Its left side contains the AC node (x + y) twice,
-- as literally the same subterm, under two different contexts: bare
-- (additive) at the first occurrence, and under `_· x` at the second.

one two : ℕ
one = suc zero
two = suc one

baseLhs : ℕ → ℕ → ℕ
baseLhs x y = (x + y) + ((x + y) · x)

baseRhs : ℕ → ℕ → ℕ
baseRhs x y = (x + y) + ((x · x) + (y · x))

baseLemma : (x y : ℕ) → baseLhs x y ≡ baseRhs x y
baseLemma x y = cong ((x + y) +_) (sym (·-distribʳ x y x))

-- The two inner extensions: the residue z appended to the FIRST
-- occurrence of the node, and to the SECOND.  Both are legitimate inner
-- AC matches of the node (x + y) against (x + y + z) with residue z --
-- gate G3's `ac_canonical` test passes for each, since each derived left
-- side is an AC rearrangement of the pattern extended by one fresh
-- variable at that position.
ext₁ ext₂ : ℕ → ℕ → ℕ → ℕ
ext₁ x y z = ((x + y) + z) + ((x + y) · x)
ext₂ x y z = (x + y) + (((x + y) + z) · x)

-- Each extension DOES have a correct derived right side: derivability is
-- not the obstruction.
ext₁-correct : (x y z : ℕ) → ext₁ x y z ≡ ((x + y) + z) + ((x · x) + (y · x))
ext₁-correct x y z = cong (((x + y) + z) +_) (sym (·-distribʳ x y x))

ext₂-correct : (x y z : ℕ)
             → ext₂ x y z ≡ (x + y) + (((x · x) + (y · x)) + (z · x))
ext₂-correct x y z =
    cong ((x + y) +_) (sym (·-distribʳ (x + y) z x))
  ∙ cong (λ w → (x + y) + (w + (z · x))) (sym (·-distribʳ x y x))

-- The residue enters ADDITIVELY at one occurrence and SCALED BY x at the
-- other.  At (x,y,z) = (2,0,1) the two derived values are 7 and 8.
7≢8 : ext₁ two zero one ≡ ext₂ two zero one → ⊥
7≢8 p =
  znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc p)))))))

-- THE OBSTRUCTION.  Ψ is an arbitrary candidate derived right side
-- computed from the data the root construction uses -- the base right
-- side (here fixed: `baseRhs`), the residue, and the ambient variables.
-- Since both extensions arise from the SAME base lemma, the SAME node,
-- and the SAME residue, any construction uniform in that data must
-- return the same Ψ for both.  It cannot.
noUniformInner :
    (Ψ : ℕ → ℕ → ℕ → ℕ)
  → ((x y z : ℕ) → ext₁ x y z ≡ Ψ x y z)
  → ((x y z : ℕ) → ext₂ x y z ≡ Ψ x y z)
  → ⊥
noUniformInner Ψ h₁ h₂ = 7≢8 (h₁ two zero one ∙ sym (h₂ two zero one))

-- Corollary in the shape of `rootUniform`, for direct comparison: the
-- inner analogue of `rootUniform` is false.
innerNotUniform : ((x y z : ℕ) → ext₁ x y z ≡ ext₂ x y z) → ⊥
innerNotUniform h = 7≢8 (h two zero one)
