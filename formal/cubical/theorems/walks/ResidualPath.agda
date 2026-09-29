{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

-- Γ↝ IS A SEARCH, NOT AN ORACLE
--
-- `Residual` proves
--
--   Γ↝-never-worse : Γ↝ wHere ns ≤ wHere
--   Γ↝-sound       : Γ↝ wHere ns < wHere → Σ[ n ∈ Neighbour A ] (work n < wHere)
--
-- The second statement is strictly weaker than its own proof.  The proof
-- walks `ns` and hands back a cell of that list; the TYPE says only that a
-- neighbour exists somewhere in the universe of neighbours.  A reader who
-- has the type and not the proof term cannot tell the search from an oracle
-- that guesses a better presentation out of nothing -- and the difference
-- between those two is the whole content of the fifth response.
--
-- This module supplies the missing index.  With list membership made
-- explicit, four statements pin Γ↝ down completely:
--
--   Γ↝-sound-any     the witness is IN the list that was searched;
--   Γ↝-optimal       Γ↝ is a lower bound for every listed neighbour;
--   Γ↝-never-worse   (from Residual) it is a lower bound for staying home;
--   Γ↝-greatest      it is the GREATEST such lower bound;
--   Γ↝-attained      and it is attained -- by home, or by a listed route.
--
-- Together: Γ↝ wHere ns is the minimum of {wHere} ∪ {route n | n ∈ ns},
-- certified as a minimum, not merely as some small number.
--
-- RELATION TO THE DSO LANE (stated because it is a rediscovery, not a
-- discovery).  `_⊓_` of `Residual` is, symbol for symbol, `min₂` of
-- `DSOBellmanFinite`, and it is the ℕ-fibre of `minC` of
-- `DSOMinPlusFinite` restricted along `fin`.  `Γ↝` is that
-- lane's `foldMin` with `List (Neighbour A)` in place of the finite index
-- `Ix n`, and with `wHere` -- the cost of staying home -- in place of the
-- unit `∞`; `route n = detour (out n) (back n) (work n)` is a `⊗`-product
-- of edge weights, so `Γ↝` is a one-step `bellman` over the neighbour
-- relation.  The DSO lane goes further on the algebra
-- (associativity, `⊗`-distributivity, the `⋆`-monoid, `bellman-compose`);
-- what is new here is only the direction this module adds, namely that the
-- fold's value is witnessed by a member of the structure folded over --
-- which `DSOMinPlusFinite.Argmin` already records for `foldMin`, as a
-- record rather than as a theorem.

module ResidualPath where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; _≤_ ; ≤-trans ; ¬m<m)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List ; [] ; _∷_)

open import CostGeometry
open import Residual

private
  variable
    ℓ ℓ' ℓ'' : Level

--------------------------------------------------------------------------
-- 0.  Membership
--------------------------------------------------------------------------

-- Cubical v0.7's `Cubical.Data.List` (Base / Properties / Dependent /
-- FinData) has no `Any` and no `_∈_`, so the predicate is defined here.
-- The tail constructor is named `later` rather than the customary `there`
-- because `Residual` re-exports the field `there : Neighbour A →
-- Presentation` via `open Neighbour public`.

data Any {A : Type ℓ} (P : A → Type ℓ') : List A → Type (ℓ-max ℓ ℓ') where
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  later : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

_∈_ : {A : Type ℓ} → A → List A → Type ℓ
x ∈ xs = Any (_≡ x) xs

Any-map : {A : Type ℓ} {P : A → Type ℓ'} {Q : A → Type ℓ''}
        → ({x : A} → P x → Q x)
        → {xs : List A} → Any P xs → Any Q xs
Any-map f (here p) = here (f p)
Any-map f (later a) = later (Any-map f a)

-- A proof that something in the list satisfies P names the element.
-- The list is matched only through `Any`'s own indices: writing `x ∷ xs`
-- on the left would ask the unifier for injectivity of `_∷_`, which cubical
-- Agda flags as non-computing under transport.
Any→member : {A : Type ℓ} {P : A → Type ℓ'} {xs : List A}
           → Any P xs → Σ[ x ∈ A ] ((x ∈ xs) × P x)
Any→member (here {x = x} p) = x , here refl , p
Any→member (later a) with Any→member a
... | (y , m , p) = y , later m , p

--------------------------------------------------------------------------
-- 1.  The witness returned by Γ↝-sound lies in the list searched
--------------------------------------------------------------------------

-- (Γ2′)  Same hypothesis as `Γ↝-sound`, indexed conclusion.
Γ↝-sound-any :
    {A : Presentation} (wHere : Work) (ns : List (Neighbour A))
  → Γ↝ wHere ns < wHere
  → Any (λ n → work n < wHere) ns
Γ↝-sound-any wHere [] lt = ⊥.rec (¬m<m lt)
Γ↝-sound-any wHere (n ∷ ns) lt with ⊓-split (route n) (Γ↝ wHere ns)
... | inl p =
      here (speedup-forces-better-neighbour (out n) (back n) wHere (work n)
              (subst (_< wHere) p lt))
... | inr p = later (Γ↝-sound-any wHere ns (subst (_< wHere) p lt))

-- The shape asked for in `Γ↝-sound`, with the membership certificate the
-- original proof always had and never published.
Γ↝-sound-member :
    {A : Presentation} (wHere : Work) (ns : List (Neighbour A))
  → Γ↝ wHere ns < wHere
  → Σ[ n ∈ Neighbour A ] ((n ∈ ns) × (work n < wHere))
Γ↝-sound-member wHere ns lt = Any→member (Γ↝-sound-any wHere ns lt)

--------------------------------------------------------------------------
-- 2.  Γ↝ is a lower bound for every listed neighbour
--------------------------------------------------------------------------

-- (Γ3)  Not merely small: below every route on offer.
Γ↝-optimal :
    {A : Presentation} (wHere : Work) (ns : List (Neighbour A))
    (n : Neighbour A) → n ∈ ns
  → Γ↝ wHere ns ≤ route n
Γ↝-optimal wHere _ n (here {x = m} {xs = ms} p) =
  subst (λ q → (route m ⊓ Γ↝ wHere ms) ≤ route q) p
        (⊓-≤-left (route m) (Γ↝ wHere ms))
Γ↝-optimal wHere _ n (later {x = m} {xs = ms} a) =
  ≤-trans (⊓-≤-right (route m) (Γ↝ wHere ms))
          (Γ↝-optimal wHere ms n a)

-- (Γ4)  And the greatest lower bound: anything below home and below every
-- listed route is below Γ↝.  With Γ↝-never-worse and Γ↝-optimal this is the
-- universal property, so `Γ↝ wHere ns` IS min ({wHere} ∪ route ⟨ns⟩).
Γ↝-greatest :
    {A : Presentation} (wHere : Work) (ns : List (Neighbour A)) (c : Cost)
  → c ≤ wHere
  → ((n : Neighbour A) → n ∈ ns → c ≤ route n)
  → c ≤ Γ↝ wHere ns
Γ↝-greatest wHere [] c home _ = home
Γ↝-greatest wHere (m ∷ ms) c home away with ⊓-split (route m) (Γ↝ wHere ms)
... | inl p = subst (c ≤_) (sym p) (away m (here refl))
... | inr p =
      subst (c ≤_) (sym p)
        (Γ↝-greatest wHere ms c home (λ n mem → away n (later mem)))

--------------------------------------------------------------------------
-- 3.  The value is attained
--------------------------------------------------------------------------

-- A minimum over a finite set is not an infimum: it is realised.  Either
-- staying home was already best, or some neighbour on the list achieves the
-- value exactly.
Γ↝-realised :
    {A : Presentation} (wHere : Work) (ns : List (Neighbour A))
  → (Γ↝ wHere ns ≡ wHere) ⊎ Any (λ n → route n ≡ Γ↝ wHere ns) ns
Γ↝-realised wHere [] = inl refl
Γ↝-realised wHere (m ∷ ms) with ⊓-split (route m) (Γ↝ wHere ms)
... | inl p = inr (here (sym p))
... | inr p with Γ↝-realised wHere ms
...   | inl q = inl (p ∙ q)
...   | inr a = inr (later (Any-map (λ r → r ∙ sym p) a))

-- (Γ5)  The packaged form.
Γ↝-attained :
    {A : Presentation} (wHere : Work) (ns : List (Neighbour A))
  → Σ[ c ∈ Cost ] ((Γ↝ wHere ns ≡ c)
                   × ((c ≡ wHere) ⊎ Any (λ n → route n ≡ c) ns))
Γ↝-attained wHere ns = Γ↝ wHere ns , refl , Γ↝-realised wHere ns

--------------------------------------------------------------------------
-- 4.  What the strengthening costs and buys
--------------------------------------------------------------------------

-- Cost: one datatype and four short inductions, none of which needed a new
-- idea -- every case is the same `⊓-split` case split `Γ↝-sound` already
-- performed.  That is the point.  The original proof was already this
-- strong; only its type was weak.
--
-- Buys: `Γ↝-sound-member` is falsifiable by an implementation that returns
-- a neighbour it did not look at, and `Γ↝-optimal` is falsifiable by one
-- that stops early.  `Γ↝-sound` alone was falsifiable by neither.
