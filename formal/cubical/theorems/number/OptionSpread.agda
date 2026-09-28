{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- OptionSpread
--
-- THE OPTION-SPREAD DICHOTOMY: exposed-point rigidity, and the
-- completeness of two-point separation certificates.
--
-- Two documents in this corpus make opposite claims about
-- when a numerical summary of a state determines that state's future:
--
--   * collab/discovery/claims/R0019-exposed-point-rigidity.md (absent from this repository), statement
--     (E): weights w_n > 0 summable, |c_n| ≤ 1, and Σ w_n c_n = Σ w_n
--     forces c_n = 1 for EVERY n.  One scalar pins down an infinite
--     object.  Its proof obligation 1 reads, in full, "E by termwise
--     nonnegativity after taking real parts".
--
--   * collab/messages/0249-codex-formation-cache-option-result.md (absent from this repository): the
--     caches {1,2,4,5} and {1,2,3,6} have the SAME scalar summary
--     (queries, additions, retained-count) = (·,3,4) yet marginal costs
--     (1,0) and (0,1) on the declared targets (3,4).  "A router merging
--     these states necessarily misprices at least one future request."
--
-- Both are statements about a fibre of a summary map σ, ordered by the
-- pointwise order on marginal-cost vectors.  R0019 is the case where the
-- fibre is a single point; 0249 exhibits a fibre with no ≼-least member.
-- 0249 gives a counterexample but never states the inequality that the
-- counterexample violates.  This module states it, and proves that a
-- violation is always witnessed by exactly two states:
--
--   THEOREM (`dichotomy`).  For every inhabited finite fibre F of cost
--   vectors, one may CONSTRUCT either
--     (R) a member m ∈ F with m ≼ y for all y ∈ F — merging F to m
--         misprices nothing; or
--     (S) two members u,v ∈ F and two targets i, j with u_i < v_i and
--         v_j < u_j.
--   The certificate in (S) always has size TWO: no three-state or
--   higher-order witness is ever needed.  (The branches are not
--   exclusive in general — a fibre may have a least element and an
--   incomparable pair further up — but on a two-element fibre the (S)
--   certificate does refute (R): `sep-pair-noLeast`.)
--
-- Rigidity end: `sum-rigid` / `exposed-point`, the discrete form of
-- R0019 (E), proved by exactly its termwise argument.
-- Separation end: `cacheSep` / `cacheNoLeast`, message 0249's pair.
--
-- Nothing here is measured.  Every ℕ is a literal; every step is a term.
------------------------------------------------------------------------

module OptionSpread where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (Σ; _×_; _,_; Σ-syntax)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Data.Empty as ⊥

------------------------------------------------------------------------
-- 1.  Cost vectors: the pointwise order, and strict advantage
--
-- A cost vector lists the marginal cost of each declared future target,
-- in a fixed order.  Both relations are defined by RECURSION on the
-- lists rather than as indexed families: Cubical Agda cannot invert the
-- length index of `Vec` without losing computation under transport, and
-- a definition that does not compute is not the object we want.
--
-- Vectors of different arity are declared separated (`◃` holds both
-- ways, `≼` neither way).  In every use below one arity is fixed by the
-- declared target family, so the convention is never exercised; it is
-- chosen so that `≼-or-◃` is total without a shape hypothesis.
------------------------------------------------------------------------

-- x ≼ y : x is no more expensive than y on EVERY target.
_≼_ : List ℕ → List ℕ → Type₀
[]       ≼ []       = Unit
[]       ≼ (_ ∷ _)  = ⊥.⊥
(_ ∷ _)  ≼ []       = ⊥.⊥
(a ∷ xs) ≼ (b ∷ ys) = (a ≤ b) × (xs ≼ ys)

-- x ◃ y : x is STRICTLY cheaper than y on at least one target.  The
-- inl/inr address names that target.  This is the atom of the
-- separating inequality.
_◃_ : List ℕ → List ℕ → Type₀
[]       ◃ []       = ⊥.⊥
[]       ◃ (_ ∷ _)  = Unit
(_ ∷ _)  ◃ []       = Unit
(a ∷ xs) ◃ (b ∷ ys) = (a < b) ⊎ (xs ◃ ys)

≼-refl : (x : List ℕ) → x ≼ x
≼-refl []       = tt
≼-refl (a ∷ xs) = ≤-refl , ≼-refl xs

≼-trans : (x y z : List ℕ) → x ≼ y → y ≼ z → x ≼ z
≼-trans []       []       []       _        _        = tt
≼-trans (a ∷ xs) (b ∷ ys) (c ∷ zs) (p , ps) (q , qs) =
  ≤-trans p q , ≼-trans xs ys zs ps qs

-- A strict advantage refutes the reverse dominance.  This is what makes
-- (S) an obstruction and not merely a difference.
◃→¬≼ : (x y : List ℕ) → x ◃ y → ¬ (y ≼ x)
◃→¬≼ []       (b ∷ ys) _          e        = e
◃→¬≼ (a ∷ xs) []       _          e        = e
◃→¬≼ (a ∷ xs) (b ∷ ys) (inl a<b) (b≤a , _) = <-asym a<b b≤a
◃→¬≼ (a ∷ xs) (b ∷ ys) (inr t)   (_ , r)   = ◃→¬≼ xs ys t r

------------------------------------------------------------------------
-- 2.  The decision step (Julia Robinson's lens: it is arithmetic)
--
-- Either x dominates y everywhere, or y is strictly cheaper somewhere.
-- Constructive: this IS the algorithm, target by target.
------------------------------------------------------------------------

≼-or-◃ : (x y : List ℕ) → (x ≼ y) ⊎ (y ◃ x)
≼-or-◃ []       []       = inl tt
≼-or-◃ []       (b ∷ ys) = inr tt
≼-or-◃ (a ∷ xs) []       = inr tt
≼-or-◃ (a ∷ xs) (b ∷ ys) = go (a ≟ b) (≼-or-◃ xs ys)
  where
    go : Trichotomy a b
       → (xs ≼ ys) ⊎ (ys ◃ xs)
       → ((a ∷ xs) ≼ (b ∷ ys)) ⊎ ((b ∷ ys) ◃ (a ∷ xs))
    go (lt a<b) (inl t) = inl (<-weaken a<b , t)
    go (lt a<b) (inr t) = inr (inr t)
    go (eq e)   (inl t) = inl (subst (a ≤_) e ≤-refl , t)
    go (eq e)   (inr t) = inr (inr t)
    go (gt b<a) _       = inr (inl b<a)

------------------------------------------------------------------------
-- 3.  Fibres of a summary map: an inhabited finite family of states
------------------------------------------------------------------------

_∈_ : List ℕ → List (List ℕ) → Type₀
a ∈ []      = ⊥.⊥
a ∈ (x ∷ F) = (a ≡ x) ⊎ (a ∈ F)

_≼all_ : List ℕ → List (List ℕ) → Type₀
u ≼all []      = Unit
u ≼all (x ∷ F) = (u ≼ x) × (u ≼all F)

≼all-∈ : (u v : List ℕ) (F : List (List ℕ)) → u ≼all F → v ∈ F → u ≼ v
≼all-∈ u v []      _       ()
≼all-∈ u v (x ∷ F) (p , r) (inl e) = subst (u ≼_) (sym e) p
≼all-∈ u v (x ∷ F) (p , r) (inr i) = ≼all-∈ u v F r i

≼all-mono : (x u : List ℕ) (F : List (List ℕ)) → x ≼ u → u ≼all F → x ≼all F
≼all-mono x u []      p _       = tt
≼all-mono x u (y ∷ F) p (q , r) = ≼-trans x u y p q , ≼all-mono x u F p r

-- (R) the merge representative;  (S) the two-point separating certificate.
Least : List (List ℕ) → Type₀
Least F = Σ[ u ∈ List ℕ ] ((u ∈ F) × (u ≼all F))

Sep : List (List ℕ) → Type₀
Sep F = Σ[ u ∈ List ℕ ] Σ[ v ∈ List ℕ ]
          ((u ∈ F) × (v ∈ F) × (u ◃ v) × (v ◃ u))

------------------------------------------------------------------------
-- 4.  THE DICHOTOMY
------------------------------------------------------------------------

consLeast : (x u : List ℕ) (G : List (List ℕ))
          → u ∈ G → u ≼all G
          → Least (x ∷ G) ⊎ Sep (x ∷ G)
consLeast x u G u∈ dom with ≼-or-◃ x u
... | inl x≼u = inl (x , inl refl , (≼-refl x , ≼all-mono x u G x≼u dom))
... | inr u◃x with ≼-or-◃ u x
...   | inl u≼x = inl (u , inr u∈ , (u≼x , dom))
...   | inr x◃u = inr (u , x , (inr u∈ , inl refl , u◃x , x◃u))

-- For every inhabited finite fibre, EITHER a sound merge representative
-- OR a two-point separation.  Constructive, hence decidable.  An
-- inhabited fibre is presented as a distinguished member x and the rest G.
dichotomy : (x : List ℕ) (G : List (List ℕ)) → Least (x ∷ G) ⊎ Sep (x ∷ G)
dichotomy x []      = inl (x , inl refl , (≼-refl x , tt))
dichotomy x (y ∷ G) with dichotomy y G
... | inl (u , u∈ , dom)            = consLeast x u (y ∷ G) u∈ dom
... | inr (u , v , u∈ , v∈ , p , q) =
        inr (u , v , (inr u∈ , inr v∈ , p , q))

-- On a two-element fibre the separating certificate really is a no-go:
-- no member of the fibre dominates the other, so any merged report
-- misprices at least one declared target.
sep-pair-noLeast : (u v : List ℕ) → u ◃ v → v ◃ u → ¬ Least (u ∷ v ∷ [])
sep-pair-noLeast u v u◃v v◃u (m , inl e , (_ , q , _)) =
  ◃→¬≼ v u v◃u (subst (_≼ v) e q)
sep-pair-noLeast u v u◃v v◃u (m , inr (inl e) , (p , _)) =
  ◃→¬≼ u v u◃v (subst (_≼ u) e p)
sep-pair-noLeast u v u◃v v◃u (m , inr (inr ()) , _)

-- A singleton fibre is always sound.  This is the router-side reading of
-- exposed-point rigidity (§5): rigidity ⇒ soundness.
singleton-least : (x : List ℕ) → Least (x ∷ [])
singleton-least x = x , inl refl , (≼-refl x , tt)

------------------------------------------------------------------------
-- 5.  The rigidity end: R0019 (E), discretely
------------------------------------------------------------------------

sum : List ℕ → ℕ
sum []       = 0
sum (a ∷ xs) = a + sum xs

sum-mono : (x y : List ℕ) → x ≼ y → sum x ≤ sum y
sum-mono []       []       _        = ≤-refl
sum-mono (a ∷ xs) (b ∷ ys) (p , ps) = ≤-+-≤ p (sum-mono xs ys ps)

head-eq : {a b sx sy : ℕ} → a ≤ b → sx ≤ sy → a + sx ≡ b + sy → a ≡ b
head-eq {a} {b} {sx} {sy} a≤b sx≤sy p with a ≟ b
... | lt a<b = ⊥.rec (¬m<m (subst (_< (b + sy)) p
                            (<≤-trans (<-+k a<b) (≤-k+ sx≤sy))))
... | eq e   = e
... | gt b<a = ⊥.rec (<-asym b<a a≤b)

-- THE EXPOSED-POINT LEMMA.  Termwise domination together with equality
-- of the aggregate forces termwise equality: the aggregate map has a
-- singleton fibre at its maximum.  This is R0019's proof obligation 1,
-- over ℕ, by exactly the stated argument.
sum-rigid : (x y : List ℕ) → x ≼ y → sum x ≡ sum y → x ≡ y
sum-rigid []       []       _        _ = refl
sum-rigid (a ∷ xs) (b ∷ ys) (a≤b , t) p =
  cong₂ _∷_ a≡b (sum-rigid xs ys t (inj-m+ (p ∙ cong (_+ sum ys) (sym a≡b))))
  where
    a≡b : a ≡ b
    a≡b = head-eq a≤b (sum-mono xs ys t) p

ones : ℕ → List ℕ
ones zero    = []
ones (suc m) = 1 ∷ ones m

-- R0019 (E) in its own shape: unit-bounded coordinates whose aggregate
-- attains the maximum are all 1.
exposed-point : (m : ℕ) (c : List ℕ)
              → c ≼ ones m → sum c ≡ sum (ones m) → c ≡ ones m
exposed-point m c = sum-rigid c (ones m)

------------------------------------------------------------------------
-- 6.  The separation end: message 0249's cache pair, checked
--
-- Declared future targets, in order: (3, 4).
-- Cache C₅ = {1,2,4,5} holds 4 and reaches 3 in one addition: (1,0).
-- Cache C₆ = {1,2,3,6} holds 3 and reaches 4 in one addition: (0,1).
-- Scalar summary σ = (additions, retained-count) = (3,4) for both.
------------------------------------------------------------------------

μ₅ μ₆ : List ℕ
μ₅ = 1 ∷ 0 ∷ []
μ₆ = 0 ∷ 1 ∷ []

σ₅ σ₆ : List ℕ
σ₅ = 3 ∷ 4 ∷ []
σ₆ = 3 ∷ 4 ∷ []

-- The two states lie in the SAME fibre of the scalar summary.
same-summary : σ₅ ≡ σ₆
same-summary = refl

0<1 : 0 < 1
0<1 = 0 , refl

cacheFibre : List (List ℕ)
cacheFibre = μ₅ ∷ μ₆ ∷ []

μ₅◃μ₆ : μ₅ ◃ μ₆     -- C₅ strictly cheaper on target 4
μ₅◃μ₆ = inr (inl 0<1)

μ₆◃μ₅ : μ₆ ◃ μ₅     -- C₆ strictly cheaper on target 3
μ₆◃μ₅ = inl 0<1

cacheSep : Sep cacheFibre
cacheSep = μ₅ , μ₆ , (inl refl , inr (inl refl) , μ₅◃μ₆ , μ₆◃μ₅)

-- Hence no merge representative exists: message 0249's no-go, as a term.
cacheNoLeast : ¬ Least cacheFibre
cacheNoLeast = sep-pair-noLeast μ₅ μ₆ μ₅◃μ₆ μ₆◃μ₅

-- Contrast.  Equality of summaries is NOT itself the obstruction: a
-- fibre whose members are comparable does have a representative.
chainFibre : List (List ℕ)
chainFibre = (0 ∷ 0 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ []

chainLeast : Least chainFibre
chainLeast = (0 ∷ 0 ∷ []) , inl refl
           , (≼-refl (0 ∷ 0 ∷ []) , (zero-≤ , ≤-refl , tt) , tt)
