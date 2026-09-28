{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- SimplicialDefectFailure
--
-- the defect family σ ↦ δ_σ of a charted Chu space is a functor on the
-- DEGENERACY half of the simplex category and on no more.
--
-- HEADLINE STATEMENTS:
--
--  1. holonomy-dup      Prop. 2, degeneracy invariance, BY EQUALITY.
--     defect-dup        s_j preserves the first and the last vertex and
--                       inserts one factor ρ_{i_j i_j} = e, so
--                       𝔥_{s_j σ} ≡ 𝔥_σ and hence δ_{s_j σ} ≡ δ_σ.
--                       Unconditional on ρ: the only law used is a
--                       RIGHT UNIT for the composition.  No inverses,
--                       no associativity, no cocycle condition, no
--                       hypothesis on X, 𝒯 or Q.
--
--  2. faces-fail-covariantly     Prop. 3, the single counterexample, in
--     faces-fail-contravariantly which BOTH variances fail at once, on
--                       the same face operator d₀ at adjacent
--                       dimensions.  X = {a,b}, |𝒯| = 1, I = {0,1,2,3},
--                       ρ₁₃ = ρ₃₁ = sw and every other ρ = id.  The
--                       holonomies are computed by the kernel (refl);
--                       the two failures of inclusion are decided, not
--                       asserted.  Exhaustive as a negative because
--                       Q_α = (𝒫(X), ⊆) is a POSET: a morphism exists
--                       iff the inclusion holds, so "no inclusion" IS
--                       "no functorial relation" (note §1).
--
--  3. cocycle⇒trivial   Prop. 4, the sharp form, forward direction:
--     cocycle⇒defect-const  a cocycle ρ forces 𝔥_σ ≡ e for every σ and
--     cocycle⇒faces-act     hence δ constant, hence functorial along
--                       every face in both variances.
--
--  4. covariant⇒trivial          §4, THE CONVERSE, and it holds in ONE
--     covariant⇒holonomy-trivial variance only.  If δ_σ ⊑ δ_{d₀σ} for
--                       every σ (the SIMPLICIAL variance, and only d₀ is
--                       assumed) then δ_σ ⊑ δ_e for every σ — in
--                       (𝒫(X),⊆) that is δ_σ = ∅.  Iterating d₀ reaches
--                       a 0-simplex, whose holonomy is cap(ρ_ii)·e = e.
--                       With separating tests this gives 𝔥 ≡ e, and
--                       CocycleExtraction.Corpus.trivial⇒cocycle then
--                       gives ρ_jk ρ_ij = ρ_ik.  So in the simplicial
--                       variance the note's slogan is a THEOREM:
--                       face-functorial ⟺ δ = 0 ⟺ ρ a cocycle.
--
--  5. Cosimplicial-sharp-fails-corpus   §5, and this AMENDS the note.
--     Cosimplicial-sharp-fails-archive  In the COSIMPLICIAL variance
--                       (δ_{d_jσ} ⊑ δ_σ) the slogan is FALSE.  Chart:
--                       X = ℤ with Aut(X) ⊇ ℤ acting by translation,
--                       I = {0,1}, ρ_ij = 1 for i ≠ j, ρ_ii = 0,
--                       separating tests.  ρ is NOT a cocycle and
--                       δ_{(0,1,0)} ≠ ∅, yet δ_{d_jσ} ⊆ δ_σ for EVERY σ
--                       and EVERY j.  Q_α is thin, so the inequalities
--                       ARE a functor: the face half of note (O6) is
--                       satisfiable off the cocycle locus.  Proved for
--                       BOTH readings on the same chart — the good locus
--                       is the block simplices under the corpus reading
--                       and the constant simplices under the archive
--                       one, and both are closed under vertex deletion.
--
--  6. shadow-support-infinite   §7 (note §5.3 / Cor. 5.3).  If one
--                       simplex has nonempty defect then its iterated
--                       degeneracies are pairwise distinct and all carry
--                       the SAME defect, so Σ_σ |δ_σ| is 0 or infinite:
--                       the scalar shadow of
--                       SHRINKING_TESTS_LOWER_CURVATURE.md (absent from this repository) Def. 1.5 is a
--                       two-valued predicate, not a count.
--
-- THE TWO READINGS OF THE HOLONOMY (note §0.3) — load-bearing for this
-- encoding.  D0016 §B reads 𝔥_σ = ρ_{i₀iₙ} ρ_{i_{n-1}iₙ} ⋯ ρ_{i₀i₁},
-- with NO inverse on the long edge; SHRINKING_TESTS_LOWER_CURVATURE.md (absent from this repository)
-- Def. 1.4 reads 𝔥_σ = ρ_{i₀iₙ}⁻¹ ρ_{i_{n-1}iₙ} ⋯ ρ_{i₀i₁}, and only
-- the latter is the descent obstruction.  This module is AGNOSTIC
-- between them, deliberately, in two separate ways:
--
--   * §1 abstracts the long-edge factor as an arbitrary `cap : G → G`.
--     Both readings are instances (cap = idfun, cap = inverse), and the
--     degeneracy theorem is proved once for all caps.
--   * §2's counterexample lives in Aut(X) ≅ ℤ/2, encoded as (Bool, _⊕_),
--     where g⁻¹ = g, so the two formulas literally coincide.  The
--     instance below takes cap = idfun, and `cap-irrelevant-in-ℤ/2`
--     records that any cap whatsoever with cap false ≡ false and
--     cap true ≡ true — in particular both readings — gives the same
--     numbers.
--
-- §3 is the one place where the readings differ, and the module says so
-- in its hypothesis rather than hiding it: Prop. 4 is proved under
-- `cap-inv : ∀ g → cap g · g ≡ e`, which holds for the corpus reading
-- and fails for the archive one.  §4 needs only `cap e ≡ e`, true of
-- both; §4′ proves SEPARATELY what each reading yields (cocycle for the
-- corpus one; ρ² = e plus a closure identity for the archive one — the
-- note's "a 1-simplex carries ρ²", now a checked term); §5's chart
-- refutes the cosimplicial sharp form under BOTH readings at once.
------------------------------------------------------------------------

module SimplicialDefectFailure where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _⊕_ ; ⊕-identityʳ)
open import Cubical.Data.Bool using (false≢true)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Empty as ⊥Mod
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat
  using (snotz ; injSuc ; inj-+m ; m+n≡0→m≡0×n≡0 ; +-zero)
  renaming (_+_ to _+ℕ_ ; +-comm to +ℕ-comm)
open import Cubical.Data.Int
  using (ℤ ; pos ; _+_ ; -_ ; _-_ ; injPos ; pos+ ; pos0+ ; plusMinus
        ; -Cancel ; -Cancel' ; +Assoc)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------
-- §0.  Simplices of the indiscrete (ech) nerve
--
-- N_n = I^{n+1}, note §1.  An n-simplex is a NON-EMPTY list of
-- vertices, encoded as a head together with a tail, so that "first
-- vertex" is total.  The face and degeneracy operators are the ones of
-- note §1:
--   d_j (i₀,…,iₙ) = (i₀,…,î_j,…,iₙ)      s_j (i₀,…,iₙ) = (i₀,…,i_j,i_j,…,iₙ)
------------------------------------------------------------------------

record Simplex (I : Type ℓ) : Type ℓ where
  constructor _◂_
  field
    head : I
    tail : List I

open Simplex public

infixr 5 _◂_

module _ {I : Type ℓ} where

  -- last vertex iₙ
  lastL : I → List I → I
  lastL i []       = i
  lastL i (x ∷ xs) = lastL x xs

  lastV : Simplex I → I
  lastV (i ◂ t) = lastL i t

  -- s_j, as a duplication of the j-th vertex.  For j > n it is the
  -- identity; the theorem below is then vacuously true there, and for
  -- 0 ≤ j ≤ n it is exactly s_j.
  dupL : ℕ → List I → List I
  dupL j       []       = []
  dupL zero    (x ∷ xs) = x ∷ x ∷ xs
  dupL (suc j) (x ∷ xs) = x ∷ dupL j xs

  degen : ℕ → Simplex I → Simplex I
  degen zero    (i ◂ t) = i ◂ (i ∷ t)
  degen (suc j) (i ◂ t) = i ◂ dupL j t

  -- d₀, the only face operator §3.2 needs.  On a 0-simplex it is the
  -- identity (there is no (-1)-simplex); the counterexample never uses
  -- that branch.
  face₀ : Simplex I → Simplex I
  face₀ (i ◂ [])      = i ◂ []
  face₀ (i ◂ (x ∷ t)) = x ◂ t

  -- d_j for every j, added for §5–§6: deletion of the j-th vertex.  For
  -- j greater than the dimension it is the identity, so a hypothesis
  -- quantified over all j is no stronger there than at the real faces.
  delL : ℕ → List I → List I
  delL j       []       = []
  delL zero    (x ∷ xs) = xs
  delL (suc j) (x ∷ xs) = x ∷ delL j xs

  face : ℕ → Simplex I → Simplex I
  face zero    σ       = face₀ σ
  face (suc j) (i ◂ t) = i ◂ delL j t

  -- Iterated degeneracy at 0, and the vertex count, for §7.
  iterDegen : ℕ → Simplex I → Simplex I
  iterDegen zero    σ = σ
  iterDegen (suc n) σ = degen zero (iterDegen n σ)

  lengthS : Simplex I → ℕ
  lengthS (i ◂ t) = suc (length t)

  lengthS-iter : (n : ℕ) (σ : Simplex I) → lengthS (iterDegen n σ) ≡ n +ℕ lengthS σ
  lengthS-iter zero    σ       = refl
  lengthS-iter (suc n) σ       = cong suc (lengthS-iter n σ)

  iterDegen-inj : (σ : Simplex I) (m n : ℕ) → iterDegen m σ ≡ iterDegen n σ → m ≡ n
  iterDegen-inj σ m n p =
    inj-+m (sym (lengthS-iter m σ) ∙ cong lengthS p ∙ lengthS-iter n σ)

------------------------------------------------------------------------
-- §1.  Proposition 2 — degeneracy invariance, unconditional
--
-- Structure assumed: a composition with a RIGHT unit, a chart ρ with
-- ρ_{ii} = e, and an arbitrary long-edge cap.  That is all the proof of
-- note §3.1 uses, so that is all the module assumes.  In particular
-- neither associativity nor invertibility appears, and both readings of
-- 𝔥 are instances of `cap`.
------------------------------------------------------------------------

module Holonomy
  {I : Type ℓ} {G : Type ℓ'}
  (_·_ : G → G → G) (e : G)
  (·IdR : (g : G) → g · e ≡ g)
  (ρ : I → I → G)
  (ρ-refl : (i : I) → ρ i i ≡ e)
  (cap : G → G)
  where

  -- consecutive-edge product ρ_{i_{n-1}iₙ} ⋯ ρ_{i₀i₁}
  pathL : I → List I → G
  pathL i []       = e
  pathL i (x ∷ xs) = pathL x xs · ρ i x

  -- 𝔥_σ = cap(ρ_{i₀iₙ}) · (consecutive-edge product)
  𝔥 : Simplex I → G
  𝔥 σ = cap (ρ (head σ) (lastV σ)) · pathL (head σ) (tail σ)

  -- The last vertex is untouched by a degeneracy.
  lastL-dup : (j : ℕ) (i : I) (t : List I) → lastL i (dupL j t) ≡ lastL i t
  lastL-dup j       i []       = refl
  lastL-dup zero    i (x ∷ xs) = refl
  lastL-dup (suc j) i (x ∷ xs) = lastL-dup j x xs

  -- The consecutive-edge product is untouched: one factor ρ_{i_j i_j}
  -- = e is inserted, and a right unit absorbs it.
  pathL-dup : (j : ℕ) (i : I) (t : List I) → pathL i (dupL j t) ≡ pathL i t
  pathL-dup j       i []       = refl
  pathL-dup zero    i (x ∷ xs) =
    cong (λ g → (pathL x xs · g) · ρ i x) (ρ-refl x)
      ∙ cong (_· ρ i x) (·IdR (pathL x xs))
  pathL-dup (suc j) i (x ∷ xs) = cong (_· ρ i x) (pathL-dup j x xs)

  -- The j = 0 branch of `degen` prepends the head to itself.
  lastL-head : (i : I) (t : List I) → lastL i (i ∷ t) ≡ lastL i t
  lastL-head i t = refl

  pathL-head : (i : I) (t : List I) → pathL i (i ∷ t) ≡ pathL i t
  pathL-head i t = cong (pathL i t ·_) (ρ-refl i) ∙ ·IdR (pathL i t)

  -- PROPOSITION 2.  𝔥_{s_j σ} ≡ 𝔥_σ, for every j and every σ.
  holonomy-dup : (j : ℕ) (σ : Simplex I) → 𝔥 (degen j σ) ≡ 𝔥 σ
  holonomy-dup zero (i ◂ t) =
    cong (cap (ρ i (lastL i t)) ·_) (pathL-head i t)
  holonomy-dup (suc j) (i ◂ t) =
    cong₂ (λ a b → cap (ρ i a) · b) (lastL-dup j i t) (pathL-dup j i t)

  -- COROLLARY.  δ is a function of 𝔥 and S alone (note Def. 1.5), so it
  -- inherits the equality for ANY defect assignment whatsoever.
  module _ {D : Type ℓ'} (δ𝔥 : G → D) where

    δ : Simplex I → D
    δ σ = δ𝔥 (𝔥 σ)

    defect-dup : (j : ℕ) (σ : Simplex I) → δ (degen j σ) ≡ δ σ
    defect-dup j σ = cong δ𝔥 (holonomy-dup j σ)

    -- §7 (see the header): the scalar shadow of
    -- SHRINKING_TESTS_LOWER_CURVATURE.md (absent from this repository) Def. 1.5 is two-valued in
    -- {0, ∞} rather than a count.  ONE simplex with nonempty defect
    -- forces an ℕ-indexed family of PAIRWISE DISTINCT simplices with the
    -- SAME defect: the iterated degeneracies of that simplex.
    defect-iter : (n : ℕ) (σ : Simplex I) → δ (iterDegen n σ) ≡ δ σ
    defect-iter zero    σ = refl
    defect-iter (suc n) σ = defect-dup zero (iterDegen n σ) ∙ defect-iter n σ

    shadow-support-infinite :
        (σ : Simplex I)
      → ((n : ℕ) → δ (iterDegen n σ) ≡ δ σ)
      × ((m n : ℕ) → iterDegen m σ ≡ iterDegen n σ → m ≡ n)
    shadow-support-infinite σ = (λ n → defect-iter n σ) , iterDegen-inj σ

------------------------------------------------------------------------
-- §2.  Proposition 3 — the face counterexample
--
-- X = {a,b} = Bool; Aut(X) ≅ ℤ/2 written additively as (Bool, _⊕_, false)
-- with id = false, sw = true.  𝒯 = S = {t}, e(a,t) = 0, e(b,t) = 1, so
-- ∼_S is equality and
--        δ_σ = X  if 𝔥_σ = sw,        δ_σ = ∅  if 𝔥_σ = id.
-- Subsets of X are their characteristic functions X → Bool; A ⊆ B is
-- the (unique, if it exists) morphism of the poset Q_α = (𝒫(X), ⊆).
------------------------------------------------------------------------

data Idx : Type₀ where
  ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ : Idx

-- ρ₁₃ = ρ₃₁ = sw, every other ρ_{ij} = id (including every ρ_{ii}).
ρX : Idx → Idx → Bool
ρX ⟨1⟩ ⟨3⟩ = true
ρX ⟨3⟩ ⟨1⟩ = true
ρX _   _   = false

ρX-refl : (i : Idx) → ρX i i ≡ false
ρX-refl ⟨0⟩ = refl
ρX-refl ⟨1⟩ = refl
ρX-refl ⟨2⟩ = refl
ρX-refl ⟨3⟩ = refl

-- ℤ/2 has g⁻¹ = g, so the archive reading (cap = id) and the corpus
-- reading (cap = inverse) are the SAME function here; cap = idfun below
-- is therefore not a choice between them.  `cap-irrelevant-in-ℤ/2`
-- makes that precise.
capX : Bool → Bool
capX b = b

cap-irrelevant-in-ℤ/2 : (c : Bool → Bool) → c false ≡ false → c true ≡ true
                      → (b : Bool) → c b ≡ capX b
cap-irrelevant-in-ℤ/2 c p q false = p
cap-irrelevant-in-ℤ/2 c p q true  = q

open Holonomy {I = Idx} _⊕_ false ⊕-identityʳ ρX ρX-refl capX
  renaming (𝔥 to 𝔥X ; pathL to pathX)

-- Subsets of X = Bool, and the poset structure of Q_α.
Psub : Type₀
Psub = Bool → Bool

∅ : Psub
∅ _ = false

full : Psub
full _ = true

_⊆_ : Psub → Psub → Type₀
A ⊆ B = (x : Bool) → A x ≡ true → B x ≡ true

infix 4 _⊆_

-- δ_σ = X when 𝔥_σ = sw, ∅ when 𝔥_σ = id.
δ𝔥X : Bool → Psub
δ𝔥X h _ = h

δX : Simplex Idx → Psub
δX σ = δ𝔥X (𝔥X σ)

-- The two simplices of note §3.2: σ = (0,1,2,3) and τ = (1,2,3) = d₀σ.
σ₃ : Simplex Idx
σ₃ = ⟨0⟩ ◂ (⟨1⟩ ∷ ⟨2⟩ ∷ ⟨3⟩ ∷ [])

τ₂ : Simplex Idx
τ₂ = ⟨1⟩ ◂ (⟨2⟩ ∷ ⟨3⟩ ∷ [])

-- d₀σ IS τ, on the nose.
d₀σ≡τ : face₀ σ₃ ≡ τ₂
d₀σ≡τ = refl

-- The holonomy table of note §3.2, decided by the kernel.
𝔥σ₃ : 𝔥X σ₃ ≡ false                         -- ρ₀₃+ρ₀₁+ρ₁₂+ρ₂₃ = 0
𝔥σ₃ = refl

𝔥τ₂ : 𝔥X τ₂ ≡ true                          -- ρ₁₃+ρ₁₂+ρ₂₃ = 1
𝔥τ₂ = refl

𝔥d₁σ : 𝔥X (⟨0⟩ ◂ (⟨2⟩ ∷ ⟨3⟩ ∷ [])) ≡ false   -- d₁σ = (0,2,3)
𝔥d₁σ = refl

𝔥d₂σ : 𝔥X (⟨0⟩ ◂ (⟨1⟩ ∷ ⟨3⟩ ∷ [])) ≡ true    -- d₂σ = (0,1,3)
𝔥d₂σ = refl

𝔥d₃σ : 𝔥X (⟨0⟩ ◂ (⟨1⟩ ∷ ⟨2⟩ ∷ [])) ≡ false   -- d₃σ = (0,1,2)
𝔥d₃σ = refl

𝔥d₀τ : 𝔥X (⟨2⟩ ◂ (⟨3⟩ ∷ [])) ≡ false         -- d₀τ = (2,3)
𝔥d₀τ = refl

𝔥d₁τ : 𝔥X (⟨1⟩ ◂ (⟨3⟩ ∷ [])) ≡ false         -- d₁τ = (1,3)
𝔥d₁τ = refl

𝔥d₂τ : 𝔥X (⟨1⟩ ◂ (⟨2⟩ ∷ [])) ≡ false         -- d₂τ = (1,2)
𝔥d₂τ = refl

-- Hence the defects: δ_σ = ∅, δ_τ = X, δ_{d₀τ} = ∅.
δσ₃ : δX σ₃ ≡ ∅
δσ₃ = refl

δτ₂ : δX τ₂ ≡ full
δτ₂ = refl

δd₀τ : δX (face₀ τ₂) ≡ ∅
δd₀τ = refl

-- The single inclusion failure that both directions reduce to.
full⊄∅ : ¬ (full ⊆ ∅)
full⊄∅ p = false≢true (p false refl)

-- CONTRAVARIANT (cosimplicial) DIRECTION FAILS, at σ:
--   a cosimplicial structure would give δ_{d₀σ} ⊆ δ_σ, i.e. X ⊆ ∅.
faces-fail-contravariantly : ¬ (δX (face₀ σ₃) ⊆ δX σ₃)
faces-fail-contravariantly = full⊄∅

-- COVARIANT (simplicial) DIRECTION FAILS, at τ, same operator d₀:
--   a simplicial structure would give δ_τ ⊆ δ_{d₀τ}, i.e. X ⊆ ∅.
faces-fail-covariantly : ¬ (δX τ₂ ⊆ δX (face₀ τ₂))
faces-fail-covariantly = full⊄∅

-- PROPOSITION 3, assembled: one charted Chu space, both failures, the
-- same face operator, adjacent dimensions.  Since Q_α is a poset, this
-- is exhaustive: it is not "no map was found" but "no map exists".
Proposition3 : (¬ (δX (face₀ σ₃) ⊆ δX σ₃)) × (¬ (δX τ₂ ⊆ δX (face₀ τ₂)))
Proposition3 = faces-fail-contravariantly , faces-fail-covariantly

-- Degeneracy invariance holds here too, as it must (§1 is unconditional).
degeneracy-still-acts : (j : ℕ) (σ : Simplex Idx) → δX (degen j σ) ≡ δX σ
degeneracy-still-acts j σ = cong δ𝔥X (holonomy-dup j σ)

------------------------------------------------------------------------
-- §3.  Proposition 4 — the sharp form, forward direction
--
-- If ρ is a cocycle then 𝔥 ≡ e and δ is constant, hence functorial
-- along every face in both variances — the case in which the apparatus
-- has nothing to measure.
--
-- HYPOTHESIS `cap-inv`.  This is the one statement in the module that
-- distinguishes the two readings of §0.3, and it is exposed as a
-- hypothesis rather than baked in: cap g · g ≡ e holds for the corpus
-- reading (cap = inverse, Def. 1.4) and FAILS for the archive reading
-- (cap = idfun, D0016 §B), where a 1-simplex has 𝔥 = ρ_{i₀i₁}² which a
-- cocycle does not make trivial — exactly the discrepancy the note
-- reports at §0.3 and declines to resolve.
------------------------------------------------------------------------

module Sharp
  {I : Type ℓ} {G : Type ℓ'}
  (_·_ : G → G → G) (e : G)
  (·IdR : (g : G) → g · e ≡ g)
  (ρ : I → I → G)
  (ρ-refl : (i : I) → ρ i i ≡ e)
  (cap : G → G)
  (cap-inv : (g : G) → cap g · g ≡ e)
  (cocycle : (i j k : I) → ρ j k · ρ i j ≡ ρ i k)
  where

  open Holonomy _·_ e ·IdR ρ ρ-refl cap

  -- Under the cocycle condition the consecutive-edge product collapses
  -- to the direct edge.
  path-collapse : (i : I) (t : List I) → pathL i t ≡ ρ i (lastL i t)
  path-collapse i []       = sym (ρ-refl i)
  path-collapse i (x ∷ xs) =
    cong (_· ρ i x) (path-collapse x xs) ∙ cocycle i x (lastL x xs)

  -- PROPOSITION 4.  𝔥_σ ≡ e for every σ.
  cocycle⇒trivial : (σ : Simplex I) → 𝔥 σ ≡ e
  cocycle⇒trivial (i ◂ t) =
    cong (cap (ρ i (lastL i t)) ·_) (path-collapse i t) ∙ cap-inv (ρ i (lastL i t))

  module _ {D : Type ℓ'} (δ𝔥 : G → D) where

    -- δ is the constant family at δ𝔥 e …
    cocycle⇒defect-const : (σ : Simplex I) → δ𝔥 (𝔥 σ) ≡ δ𝔥 e
    cocycle⇒defect-const σ = cong δ𝔥 (cocycle⇒trivial σ)

    -- … hence functorial along every operator whatsoever, faces
    -- included, in both variances: any two values are EQUAL.
    cocycle⇒faces-act : (σ τ : Simplex I) → δ𝔥 (𝔥 σ) ≡ δ𝔥 (𝔥 τ)
    cocycle⇒faces-act σ τ = cocycle⇒defect-const σ ∙ sym (cocycle⇒defect-const τ)

------------------------------------------------------------------------
-- §4.  The SHARP FORM, converse half, COVARIANT (simplicial) variance
--
-- Note §9's slogan: "δ is functorial along faces exactly when ρ is a
-- cocycle, i.e. exactly when δ is zero."
-- The converse is proved here — for ONE of the two variances, and
-- §5 shows it is FALSE for the other, which is the substantive finding
-- of this extension and amends the slogan.
--
-- Covariant (simplicial) direction: a simplicial structure would give
-- δ_σ → δ_{d_jσ}, i.e. δ_σ ⊑ δ_{d_jσ} in the poset Q_α.  Only d₀ is
-- used, so the theorem holds under a WEAKER hypothesis than full
-- simpliciality.
--
-- Mechanism, in one line: iterating d₀ walks any simplex down to a
-- 0-simplex, and 𝔥 of a 0-simplex is cap(ρ_ii)·e = cap e · e = e.  So
-- δ_σ ⊑ δ_e for every σ; in (𝒫(X),⊆) with δ_e = ∅ that is δ_σ = ∅.
--
-- ARCHIVE-AGNOSTIC.  The only hypothesis on the long-edge cap is
-- `cap-e : cap e ≡ e`, which holds for BOTH readings of §0.3 (cap =
-- inverse, corpus Def. 1.4; cap = idfun, D0016 §B).  Unlike §3, this
-- half of the sharp form does not distinguish the readings at all.
------------------------------------------------------------------------

module CovariantSharp
  {I : Type ℓ} {G : Type ℓ'} {D : Type ℓ''}
  (_·_ : G → G → G) (e : G)
  (·IdR : (g : G) → g · e ≡ g)
  (ρ : I → I → G)
  (ρ-refl : (i : I) → ρ i i ≡ e)
  (cap : G → G)
  (cap-e : cap e ≡ e)
  (δ𝔥 : G → D)
  (_⊑_ : D → D → Type ℓ'')
  (⊑-refl : (A : D) → A ⊑ A)
  (⊑-trans : {A B C : D} → A ⊑ B → B ⊑ C → A ⊑ C)
  where

  open Holonomy _·_ e ·IdR ρ ρ-refl cap

  δ' : Simplex I → D
  δ' σ = δ𝔥 (𝔥 σ)

  -- A 0-simplex has trivial holonomy under BOTH readings.
  vertex-trivial : (i : I) → 𝔥 (i ◂ []) ≡ e
  vertex-trivial i =
    cong (λ g → cap g · e) (ρ-refl i) ∙ cong (_· e) cap-e ∙ ·IdR e

  -- THE CONVERSE, covariant variance: functoriality along d₀ alone
  -- already forces every defect to be ⊑ the defect of the identity.
  covariant⇒trivial :
      ((σ : Simplex I) → δ' σ ⊑ δ' (face₀ σ))
    → (σ : Simplex I) → δ' σ ⊑ δ𝔥 e
  covariant⇒trivial fc (i ◂ t) = go i t
    where
    go : (i : I) (t : List I) → δ' (i ◂ t) ⊑ δ𝔥 e
    go i []       = subst (λ g → δ𝔥 g ⊑ δ𝔥 e) (sym (vertex-trivial i)) (⊑-refl (δ𝔥 e))
    go i (x ∷ t) = ⊑-trans (fc (i ◂ (x ∷ t))) (go x t)

  -- With tests that separate — δ_σ = ∅ only when 𝔥_σ is the identity —
  -- the conclusion is triviality of the holonomy itself.
  module _ (separating : (g : G) → δ𝔥 g ⊑ δ𝔥 e → g ≡ e) where

    covariant⇒holonomy-trivial :
        ((σ : Simplex I) → δ' σ ⊑ δ' (face₀ σ))
      → (σ : Simplex I) → 𝔥 σ ≡ e
    covariant⇒holonomy-trivial fc σ = separating (𝔥 σ) (covariant⇒trivial fc σ)

------------------------------------------------------------------------
-- §4′.  From trivial holonomy to a condition on ρ — BOTH READINGS,
--       and they give DIFFERENT conditions.
--
-- Note §0.3's two readings give a pair of theorems rather than a
-- choice between them.
-- Corpus reading (cap = inverse): 𝔥 ≡ e is exactly the cocycle
-- condition ρ_jk ρ_ij = ρ_ik.  Archive reading (cap = idfun): 𝔥 ≡ e
-- gives instead ρ_ij² = e on every 1-simplex TOGETHER WITH
-- ρ_ik ρ_jk ρ_ij = e — a strictly different demand, and the exact
-- content of the note's observation that "a 1-simplex carries ρ²".
------------------------------------------------------------------------

module CocycleExtraction
  {I : Type ℓ} {G : Type ℓ'}
  (_·_ : G → G → G) (e : G)
  (·IdL : (g : G) → e · g ≡ g)
  (·IdR : (g : G) → g · e ≡ g)
  (·Assoc : (g h k : G) → (g · h) · k ≡ g · (h · k))
  (ρ : I → I → G)
  (ρ-refl : (i : I) → ρ i i ≡ e)
  where

  -- CORPUS READING (SHRINKING_TESTS_LOWER_CURVATURE.md (absent from this repository) Def. 1.4).
  module Corpus
    (cap : G → G)
    (capL : (g : G) → cap g · g ≡ e)
    (capR : (g : G) → g · cap g ≡ e)
    where

    open Holonomy _·_ e ·IdR ρ ρ-refl cap

    𝔥-two : (i j k : I) → 𝔥 (i ◂ (j ∷ k ∷ [])) ≡ cap (ρ i k) · (ρ j k · ρ i j)
    𝔥-two i j k = cong (λ g → cap (ρ i k) · (g · ρ i j)) (·IdL (ρ j k))

    trivial⇒cocycle : ((σ : Simplex I) → 𝔥 σ ≡ e)
                    → (i j k : I) → ρ j k · ρ i j ≡ ρ i k
    trivial⇒cocycle triv i j k =
        sym (·IdL (ρ j k · ρ i j))
      ∙ cong (_· (ρ j k · ρ i j)) (sym (capR (ρ i k)))
      ∙ ·Assoc (ρ i k) (cap (ρ i k)) (ρ j k · ρ i j)
      ∙ cong (ρ i k ·_) (sym (𝔥-two i j k) ∙ triv (i ◂ (j ∷ k ∷ [])))
      ∙ ·IdR (ρ i k)

  -- ARCHIVE READING (D0016 §B as transcribed: no inverse on the long
  -- edge).  The module records what the archive's formula gives, and
  -- it is not the cocycle condition.
  module Archive where

    open Holonomy _·_ e ·IdR ρ ρ-refl (λ g → g)

    𝔥-one : (i j : I) → 𝔥 (i ◂ (j ∷ [])) ≡ ρ i j · ρ i j
    𝔥-one i j = cong (ρ i j ·_) (·IdL (ρ i j))

    𝔥-two : (i j k : I) → 𝔥 (i ◂ (j ∷ k ∷ [])) ≡ ρ i k · (ρ j k · ρ i j)
    𝔥-two i j k = cong (λ g → ρ i k · (g · ρ i j)) (·IdL (ρ j k))

    -- The 1-simplex carries ρ², exactly as note §0.3 reports.
    trivial⇒involutive : ((σ : Simplex I) → 𝔥 σ ≡ e)
                       → (i j : I) → ρ i j · ρ i j ≡ e
    trivial⇒involutive triv i j = sym (𝔥-one i j) ∙ triv (i ◂ (j ∷ []))

    trivial⇒closed : ((σ : Simplex I) → 𝔥 σ ≡ e)
                   → (i j k : I) → ρ i k · (ρ j k · ρ i j) ≡ e
    trivial⇒closed triv i j k = sym (𝔥-two i j k) ∙ triv (i ◂ (j ∷ k ∷ []))

------------------------------------------------------------------------
-- §5.  The sharp form is FALSE in the CONTRAVARIANT (cosimplicial)
--      variance — a charted Chu space, not a cocycle, whose defect
--      family IS functorial along every face.
--
-- The claim proved:
--
--   there is a charted Chu space with ρ NOT a cocycle, δ_{σ₀} ≠ ∅ for
--   an explicit σ₀, and δ_{d_jσ} ⊆ δ_σ for EVERY σ and EVERY j.
--
-- Since Q_α = (𝒫(X),⊆) is a poset — thin — an assignment of morphisms
-- satisfying all the required inequalities IS a functor (every diagram
-- in a thin category commutes), so this is not "the inequalities hold
-- but coherence might fail": the face half of note (O6) is SATISFIABLE
-- off the cocycle locus.
--
-- THE CHART.  X = ℤ, Aut(X) ⊇ ℤ acting by translation, so G = (ℤ,+).
-- I = Bool = {0,1}.  ρ_ij = 1 for i ≠ j and 0 for i = j.  Tests
-- separate points (∼_S is equality on ℤ), so
--     δ_σ = {x : 𝔥_σ + x ≠ x} = ∅ ⟺ 𝔥_σ = 0.
--
-- BOTH READINGS, and this is why the chart was chosen.  Writing t(σ)
-- for the number of consecutive-vertex changes in σ and ε(σ) ∈ {0,1}
-- for the long-edge indicator,
--     corpus  𝔥_σ = −ε(σ) + t(σ),   archive  𝔥_σ = ε(σ) + t(σ).
-- So the good locus is {t = ε} for the corpus reading (the "block"
-- simplices i…i j…j, at most one change) and {t = 0 = ε} for the
-- archive reading (the constant simplices).  BOTH are closed under
-- deleting a vertex, so BOTH readings give a cosimplicially
-- face-functorial δ, with different good loci.  The pair of theorems
-- replaces a choice between the readings.
------------------------------------------------------------------------

stepB : Bool → ℕ
stepB true  = 1
stepB false = 0

step : Bool → Bool → ℕ
step i j = stepB (i ⊕ j)

step-refl : (i : Bool) → step i i ≡ 0
step-refl false = refl
step-refl true  = refl

sucStep : (b : Bool) (n : ℕ) → suc n ≡ stepB b → n ≡ 0
sucStep true  n p = injSuc p
sucStep false n p = ⊥Mod.rec (snotz p)

ρZ : Bool → Bool → ℤ
ρZ i j = pos (step i j)

ρZ-refl : (i : Bool) → ρZ i i ≡ pos 0
ρZ-refl i = cong pos (step-refl i)

-- The corpus reading (cap = −) and the archive reading (cap = idfun),
-- on ONE chart.
open Holonomy {I = Bool} {G = ℤ} _+_ (pos 0) (λ g → refl) ρZ ρZ-refl (-_)
  using () renaming (𝔥 to 𝔥C ; pathL to pathZ)

open Holonomy {I = Bool} {G = ℤ} _+_ (pos 0) (λ g → refl) ρZ ρZ-refl (λ g → g)
  using () renaming (𝔥 to 𝔥A)

-- Number of consecutive-vertex changes, mirroring pathL.
transL : Bool → List Bool → ℕ
transL i []       = 0
transL i (x ∷ xs) = step i x +ℕ transL x xs

pathZ≡ : (i : Bool) (t : List Bool) → pathZ i t ≡ pos (transL i t)
pathZ≡ i []       = refl
pathZ≡ i (x ∷ xs) =
    cong (_+ ρZ i x) (pathZ≡ x xs)
  ∙ sym (pos+ (transL x xs) (step i x))
  ∙ cong pos (+ℕ-comm (transL x xs) (step i x))

-- The two good loci, as inductive predicates on the vertex list.
data Cst (j : Bool) : List Bool → Type₀ where
  cnil  : Cst j []
  ccons : {t : List Bool} → Cst j t → Cst j (j ∷ t)

data Blk (i : Bool) : List Bool → Type₀ where
  bnil  : Blk i []
  bsame : {t : List Bool} → Blk i t → Blk i (i ∷ t)
  bjump : {j : Bool} {t : List Bool} → Cst j t → Blk i (j ∷ t)

Cst→last : {j : Bool} {t : List Bool} → Cst j t → lastL j t ≡ j
Cst→last cnil      = refl
Cst→last (ccons c) = Cst→last c

Cst→trans : {j : Bool} {t : List Bool} → Cst j t → transL j t ≡ 0
Cst→trans {j} cnil            = refl
Cst→trans {j} (ccons {t} c) =
  cong (_+ℕ transL j t) (step-refl j) ∙ Cst→trans c

trans→Cst : (i : Bool) (t : List Bool) → transL i t ≡ 0 → Cst i t
trans→Cst i []              p = cnil
trans→Cst false (false ∷ xs) p = ccons (trans→Cst false xs p)
trans→Cst true  (true  ∷ xs) p = ccons (trans→Cst true  xs p)
trans→Cst false (true  ∷ xs) p = ⊥Mod.rec (snotz p)
trans→Cst true  (false ∷ xs) p = ⊥Mod.rec (snotz p)

Cst→Blk : {i j : Bool} {t : List Bool} → Cst j t → Blk i t
Cst→Blk cnil      = bnil
Cst→Blk (ccons c) = bjump c

Blk→trans : {i : Bool} {t : List Bool} → Blk i t → transL i t ≡ step i (lastL i t)
Blk→trans {i} bnil          = sym (step-refl i)
Blk→trans {i} (bsame {t} b) =
  cong (_+ℕ transL i t) (step-refl i) ∙ Blk→trans b
Blk→trans {i} (bjump {j} {t} c) =
    cong (step i j +ℕ_) (Cst→trans c)
  ∙ +-zero (step i j)
  ∙ cong (step i) (sym (Cst→last c))

trans→Blk : (i : Bool) (t : List Bool) → transL i t ≡ step i (lastL i t) → Blk i t
trans→Blk i []               p = bnil
trans→Blk false (false ∷ xs) p = bsame (trans→Blk false xs p)
trans→Blk true  (true  ∷ xs) p = bsame (trans→Blk true  xs p)
trans→Blk false (true  ∷ xs) p =
  bjump (trans→Cst true xs (sucStep (lastL true xs) (transL true xs) p))
trans→Blk true  (false ∷ xs) p =
  bjump (trans→Cst false xs (sucStep (not (lastL false xs)) (transL false xs) p))

-- Both good loci are closed under deleting a vertex.
Cst-del : (n : ℕ) {j : Bool} {t : List Bool} → Cst j t → Cst j (delL n t)
Cst-del n       cnil      = cnil
Cst-del zero    (ccons c) = c
Cst-del (suc n) (ccons c) = ccons (Cst-del n c)

Blk-del : (n : ℕ) {i : Bool} {t : List Bool} → Blk i t → Blk i (delL n t)
Blk-del n       bnil      = bnil
Blk-del zero    (bsame b) = b
Blk-del zero    (bjump c) = Cst→Blk c
Blk-del (suc n) (bsame b) = bsame (Blk-del n b)
Blk-del (suc n) (bjump c) = bjump (Cst-del n c)

-- Closure under d₀ is proved at the level of the counts rather than of
-- the predicates: d₀ moves the basepoint, so it is not an instance of
-- delL, and matching on a constructor with index (x ∷ t) is exactly the
-- pattern Cubical Agda declines.
trans-face₀-Cst : (i x : Bool) (t : List Bool)
                → transL i (x ∷ t) ≡ 0 → transL x t ≡ 0
trans-face₀-Cst false false t p = p
trans-face₀-Cst true  true  t p = p
trans-face₀-Cst false true  t p = ⊥Mod.rec (snotz p)
trans-face₀-Cst true  false  t p = ⊥Mod.rec (snotz p)

trans-face₀ : (i x : Bool) (t : List Bool)
            → transL i (x ∷ t) ≡ step i (lastL i (x ∷ t))
            → transL x t ≡ step x (lastL x t)
trans-face₀ false false t p = p
trans-face₀ true  true  t p = p
trans-face₀ false true  t p =
  n0 ∙ sym (cong (step true) (Cst→last (trans→Cst true t n0)) ∙ step-refl true)
  where
  n0 : transL true t ≡ 0
  n0 = sucStep (lastL true t) (transL true t) p
trans-face₀ true  false t p =
  n0 ∙ sym (cong (step false) (Cst→last (trans→Cst false t n0)) ∙ step-refl false)
  where
  n0 : transL false t ≡ 0
  n0 = sucStep (not (lastL false t)) (transL false t) p

------------------------------------------------------------------------
-- §5.1  The ℤ bookkeeping: 𝔥 ≡ 0 decoded, in each reading.
------------------------------------------------------------------------

-+≡0→≡ : (a b : ℤ) → (- a) + b ≡ pos 0 → b ≡ a
-+≡0→≡ a b p =
    pos0+ b
  ∙ cong (_+ b) (sym (-Cancel a))
  ∙ sym (+Assoc a (- a) b)
  ∙ cong (a +_) p

≡→-+≡0 : (a b : ℤ) → b ≡ a → (- a) + b ≡ pos 0
≡→-+≡0 a b p = cong ((- a) +_) p ∙ -Cancel' a

𝔥C≡ : (i : Bool) (t : List Bool)
    → 𝔥C (i ◂ t) ≡ (- pos (step i (lastL i t))) + pos (transL i t)
𝔥C≡ i t = cong ((- ρZ i (lastL i t)) +_) (pathZ≡ i t)

𝔥A≡ : (i : Bool) (t : List Bool)
    → 𝔥A (i ◂ t) ≡ pos (step i (lastL i t) +ℕ transL i t)
𝔥A≡ i t = cong (pos (step i (lastL i t)) +_) (pathZ≡ i t)
        ∙ sym (pos+ (step i (lastL i t)) (transL i t))

GoodC GoodA : Simplex Bool → Type₀
GoodC σ = 𝔥C σ ≡ pos 0
GoodA σ = 𝔥A σ ≡ pos 0

-- Corpus reading: 𝔥 ≡ 0 ⟺ t(σ) = ε(σ) ⟺ σ is a block simplex.
GoodC→eq : (i : Bool) (t : List Bool) → GoodC (i ◂ t) → transL i t ≡ step i (lastL i t)
GoodC→eq i t g =
  injPos (-+≡0→≡ (pos (step i (lastL i t))) (pos (transL i t)) (sym (𝔥C≡ i t) ∙ g))

eq→GoodC : (i : Bool) (t : List Bool) → transL i t ≡ step i (lastL i t) → GoodC (i ◂ t)
eq→GoodC i t q =
    𝔥C≡ i t
  ∙ ≡→-+≡0 (pos (step i (lastL i t))) (pos (transL i t)) (cong pos q)

GoodC→Blk : (i : Bool) (t : List Bool) → GoodC (i ◂ t) → Blk i t
GoodC→Blk i t g = trans→Blk i t (GoodC→eq i t g)

Blk→GoodC : (i : Bool) (t : List Bool) → Blk i t → GoodC (i ◂ t)
Blk→GoodC i t b = eq→GoodC i t (Blk→trans b)

-- Archive reading: 𝔥 ≡ 0 ⟺ t(σ) = 0 ⟺ σ is a constant simplex.
GoodA→eq : (i : Bool) (t : List Bool) → GoodA (i ◂ t) → transL i t ≡ 0
GoodA→eq i t g = snd-of (m+n≡0→m≡0×n≡0 (injPos (sym (𝔥A≡ i t) ∙ g)))
  where
  snd-of : {A B : Type₀} → A × B → B
  snd-of (_ , b) = b

eq→GoodA : (i : Bool) (t : List Bool) → transL i t ≡ 0 → GoodA (i ◂ t)
eq→GoodA i t q =
    𝔥A≡ i t
  ∙ cong pos (cong₂ _+ℕ_ (cong (step i) (Cst→last (trans→Cst i t q)) ∙ step-refl i) q)

GoodA→Cst : (i : Bool) (t : List Bool) → GoodA (i ◂ t) → Cst i t
GoodA→Cst i t g = trans→Cst i t (GoodA→eq i t g)

Cst→GoodA : (i : Bool) (t : List Bool) → Cst i t → GoodA (i ◂ t)
Cst→GoodA i t c = eq→GoodA i t (Cst→trans c)

------------------------------------------------------------------------
-- §5.2  The defect as a subset of X = ℤ, and the poset (𝒫(X), ⊆).
------------------------------------------------------------------------

SubZ : Type₁
SubZ = ℤ → Type₀

_⊆Z_ : SubZ → SubZ → Type₀
A ⊆Z B = (x : ℤ) → A x → B x

infix 4 _⊆Z_

δZ : (Simplex Bool → ℤ) → Simplex Bool → SubZ
δZ h σ x = ¬ (h σ + x ≡ x)

act-triv : (h : ℤ) → h ≡ pos 0 → (x : ℤ) → h + x ≡ x
act-triv h p x = cong (_+ x) p ∙ sym (pos0+ x)

act-triv⁻ : (h x : ℤ) → h + x ≡ x → h ≡ pos 0
act-triv⁻ h x p = sym (plusMinus x h) ∙ cong (_- x) p ∙ -Cancel x

-- Closure of the good loci under EVERY face operator.
goodC-face : (j : ℕ) (σ : Simplex Bool) → GoodC σ → GoodC (face j σ)
goodC-face zero    (i ◂ [])      g = g
goodC-face zero    (i ◂ (x ∷ t)) g =
  eq→GoodC x t (trans-face₀ i x t (GoodC→eq i (x ∷ t) g))
goodC-face (suc j) (i ◂ t)       g =
  Blk→GoodC i (delL j t) (Blk-del j (GoodC→Blk i t g))

goodA-face : (j : ℕ) (σ : Simplex Bool) → GoodA σ → GoodA (face j σ)
goodA-face zero    (i ◂ [])      g = g
goodA-face zero    (i ◂ (x ∷ t)) g =
  eq→GoodA x t (trans-face₀-Cst i x t (GoodA→eq i (x ∷ t) g))
goodA-face (suc j) (i ◂ t)       g =
  Cst→GoodA i (delL j t) (Cst-del j (GoodA→Cst i t g))

-- THE COSIMPLICIAL FACE ACTION, in both readings: δ_{d_jσ} ⊆ δ_σ.
faces-act-contravariantly-C :
  (j : ℕ) (σ : Simplex Bool) → δZ 𝔥C (face j σ) ⊆Z δZ 𝔥C σ
faces-act-contravariantly-C j σ x nd q =
  nd (act-triv (𝔥C (face j σ)) (goodC-face j σ (act-triv⁻ (𝔥C σ) x q)) x)

faces-act-contravariantly-A :
  (j : ℕ) (σ : Simplex Bool) → δZ 𝔥A (face j σ) ⊆Z δZ 𝔥A σ
faces-act-contravariantly-A j σ x nd q =
  nd (act-triv (𝔥A (face j σ)) (goodA-face j σ (act-triv⁻ (𝔥A σ) x q)) x)

------------------------------------------------------------------------
-- §5.3  … and the family is NOT trivial: an explicit nonempty defect,
--       and ρ is not a cocycle.
------------------------------------------------------------------------

σ₀ : Simplex Bool
σ₀ = false ◂ (true ∷ false ∷ [])

-- 𝔥_{σ₀} = 2 in both readings (the long edge is ρ₀₀ = 0).
𝔥C-σ₀ : 𝔥C σ₀ ≡ pos 2
𝔥C-σ₀ = refl

𝔥A-σ₀ : 𝔥A σ₀ ≡ pos 2
𝔥A-σ₀ = refl

pos2≢pos0 : ¬ (pos 2 ≡ pos 0)
pos2≢pos0 p = snotz (injPos p)

defect-σ₀-C : δZ 𝔥C σ₀ (pos 0)
defect-σ₀-C p = pos2≢pos0 p

defect-σ₀-A : δZ 𝔥A σ₀ (pos 0)
defect-σ₀-A p = pos2≢pos0 p

ρZ-not-cocycle : ¬ (ρZ true false + ρZ false true ≡ ρZ false false)
ρZ-not-cocycle p = snotz (injPos p)

-- THEOREM (§5, assembled).  In each reading of the holonomy: a charted
-- Chu space whose defect family is functorial along EVERY face in the
-- COSIMPLICIAL variance, whose ρ is NOT a cocycle, and whose defect is
-- nonempty at an explicit simplex.  Hence the sharp form
--   "functorial along faces ⟺ δ = 0"
-- is TRUE in the simplicial variance (§4) and FALSE in the
-- cosimplicial one.
Cosimplicial-sharp-fails-corpus :
    ((j : ℕ) (σ : Simplex Bool) → δZ 𝔥C (face j σ) ⊆Z δZ 𝔥C σ)
  × ((δZ 𝔥C σ₀ (pos 0))
  × (¬ (ρZ true false + ρZ false true ≡ ρZ false false)))
Cosimplicial-sharp-fails-corpus =
  faces-act-contravariantly-C , (defect-σ₀-C , ρZ-not-cocycle)

Cosimplicial-sharp-fails-archive :
    ((j : ℕ) (σ : Simplex Bool) → δZ 𝔥A (face j σ) ⊆Z δZ 𝔥A σ)
  × ((δZ 𝔥A σ₀ (pos 0))
  × (¬ (ρZ true false + ρZ false true ≡ ρZ false false)))
Cosimplicial-sharp-fails-archive =
  faces-act-contravariantly-A , (defect-σ₀-A , ρZ-not-cocycle)

------------------------------------------------------------------------
-- §6.  What §4 and §5 establish.
--
--  * §4 is the converse of the slogan, in the
--    SIMPLICIAL variance, from a weaker hypothesis (d₀ only), and it is
--    agnostic between the two readings of the holonomy.
--  * §4′ converts note §0.3's discrepancy into two theorems instead of
--    a choice: corpus reading ⇒ cocycle; archive reading ⇒ ρ² = e and a
--    different closure identity.
--  * §5 REFUTES the cosimplicial half of the slogan.
--  * §5 amends note (O6): the face part is refuted for the ρ of §2 but
--    is SATISFIABLE for the ρ of §5, so "faces act in neither variance"
--    is a statement about that counterexample, not about all charts.
--  * The example of §5 uses X = ℤ, hence an infinite Chu space; §2's
--    example is finite.
------------------------------------------------------------------------
