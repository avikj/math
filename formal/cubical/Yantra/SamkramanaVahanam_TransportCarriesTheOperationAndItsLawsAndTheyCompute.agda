{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- संक्रमण-वहनम् — the concurrence carries the WHOLE structure, and the
-- carried structure COMPUTES.
--
-- `Machine.Samorderna` identified the pair ℕ × ℕ with the triple
-- rāśi-traya by univalence — `yugma≡rāśi-traya = ua (anuloma , viloma)` —
-- and carried the successor `Φ` across it.  A point rode the return.
--
-- This module rides an ALGEBRA across the same identity:
--
--   * a commutative monoid on ℕ × ℕ (componentwise addition, unit (0,0)),
--   * `transport`ed along `yugma≡ri-traya` to an operation on
--     rāśi-traya, `_⊞ᵣ_`;
--   * whose value is the anuloma/viloma-conjugated operation `_⊛_`
--     (`carried-is-conjugate`), so it acts on the triples exactly as
--     Brahmagupta's saordera would demand — and on concrete numerals it
--     REDUCES (`_ = refl`), which is cubical transport = uaβ made to run;
--   * and its associativity, commutativity and unit laws, transported
--     along the SAME path, so the laws on ri-traya are NOT reproved by
--     induction on the triple: they are the ℕ proofs MOVED.
--
-- This is NisvabhavaNet's `liberation` (transport of a predicate) raised
-- to a structure: where two standpoints are equivalent, everything
-- transports — the points, the operations on them, AND the equations they
-- satisfy.  पुनरुक्तिर् न — the theorem is carried, not copied; that is
-- the अहिंसा move (अहिंसा-सूत्र §६: transport carrying its equivalence),
-- made total over an algebra.
------------------------------------------------------------------------

module Yantra.SamkramanaVahanam_TransportCarriesTheOperationAndItsLawsAndTheyCompute where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport using (transport⁻Transport)
open import Cubical.Data.Nat using (ℕ ; zero ; _+_ ; +-assoc ; +-comm ; +-zero)
open import Cubical.Data.Sigma using (ΣPathP)

open import Samkramana
  using ( rāśi-traya ; anuloma ; viloma ; yugma≡rāśi-traya ; _×_ )

private
  P : (ℕ × ℕ) ≡ rāśi-traya
  P = yugma≡rāśi-traya

------------------------------------------------------------------------
-- The shapes a monoid is built from, as families over a type.  Each is
-- transported along `P` below; that is the whole point — one path, and
-- the operation and every law ride it.
------------------------------------------------------------------------

Op : Type → Type
Op T = T → T → T

Assoc : (T : Type) → Op T → Type
Assoc T _·_ = (x y z : T) → ((x · y) · z) ≡ (x · (y · z))

Comm : (T : Type) → Op T → Type
Comm T _·_ = (x y : T) → (x · y) ≡ (y · x)

LUnit : (T : Type) → Op T → T → Type
LUnit T _·_ e = (x : T) → (e · x) ≡ x

------------------------------------------------------------------------
-- The monoid on the PAIR side — plain componentwise addition on ℕ × ℕ.
-- Associativity and commutativity are ℕ's, componentwise; the unit is
-- (0 , 0) and the left-unit law is +-zero-free (0 + x ≡ x is `refl` in
-- this library's ℕ, so LUnit holds by ΣPathP of two refls).
------------------------------------------------------------------------

_⊞_ : Op (ℕ × ℕ)
(s , l) ⊞ (s' , l') = (s + s') , (l + l')

⊞-assoc : Assoc (ℕ × ℕ) _⊞_
⊞-assoc (a , b) (c , d) (e , f) =
  ΣPathP (sym (+-assoc a c e) , sym (+-assoc b d f))

⊞-comm : Comm (ℕ × ℕ) _⊞_
⊞-comm (a , b) (c , d) = ΣPathP (+-comm a c , +-comm b d)

⊞-lunit : LUnit (ℕ × ℕ) _⊞_ (zero , zero)
⊞-lunit (a , b) = refl

------------------------------------------------------------------------
-- The carry.  Each object rides `P` by `transport`; the paths `⊞-path`
-- etc. are the `transport-filler`s that connect the pair-side object to
-- its ri-traya image, and are the families along which the LAWS are
-- transported.
------------------------------------------------------------------------

_⊞ᵣ_ : Op rāśi-traya
_⊞ᵣ_ = transport (λ i → Op (P i)) _⊞_

⊞-path : PathP (λ i → Op (P i)) _⊞_ _⊞ᵣ_
⊞-path = transport-filler (λ i → Op (P i)) _⊞_

εᵣ : rāśi-traya
εᵣ = transport (λ i → P i) (zero , zero)

ε-path : PathP (λ i → P i) (zero , zero) εᵣ
ε-path = transport-filler (λ i → P i) (zero , zero)

-- the laws, MOVED — no induction on rāśi-traya anywhere below.
⊞ᵣ-assoc : Assoc rāśi-traya _⊞ᵣ_
⊞ᵣ-assoc = transport (λ i → Assoc (P i) (⊞-path i)) ⊞-assoc

⊞ᵣ-comm : Comm rāśi-traya _⊞ᵣ_
⊞ᵣ-comm = transport (λ i → Comm (P i) (⊞-path i)) ⊞-comm

⊞ᵣ-lunit : LUnit rāśi-traya _⊞ᵣ_ εᵣ
⊞ᵣ-lunit = transport (λ i → LUnit (P i) (⊞-path i) (ε-path i)) ⊞-lunit

------------------------------------------------------------------------
-- The carried operation IS the conjugated one.  `_⊛_` is what one writes
-- by hand: pull both triples back to pairs with viloma, add, push forward
-- with anuloma.  The transported `_⊞ᵣ_` equals it — the transport did the
-- conjugation itself.
------------------------------------------------------------------------

_⊛_ : Op rāśi-traya
u ⊛ v = anuloma ((viloma u) ⊞ (viloma v))

carried-is-conjugate : (u v : rāśi-traya) → (u ⊞ᵣ v) ≡ (u ⊛ v)
carried-is-conjugate u v = refl

------------------------------------------------------------------------
-- And it RUNS.  The carried operation applied to concrete triples reduces
-- to the concrete answer by `refl` — the type-checker normalises the
-- transport, so this is uaβ computing, not a lemma invoked.
------------------------------------------------------------------------

_ : (anuloma (3 , 4) ⊞ᵣ anuloma (1 , 2)) ≡ anuloma (4 , 6)
_ = refl

_ : (anuloma (3 , 4) ⊛ anuloma (1 , 2)) ≡ anuloma (4 , 6)
_ = refl

-- the transported unit really is a left unit, on a concrete triple, by the
-- MOVED law — not a fresh computation:
_ : (εᵣ ⊞ᵣ anuloma (5 , 6)) ≡ anuloma (5 , 6)
_ = ⊞ᵣ-lunit (anuloma (5 , 6))

------------------------------------------------------------------------
-- सूत्र १६ — पुनरागमनं शून्य-व्ययेन एव : the return is only at zero cost.
--
-- Carry the operation FORWARD along P to ri-traya, then BACK along
-- sym P, and it returns EXACTLY — `⊞-return` is a `refl`-free identity
-- proving the whole round trip is the identity on the operation.  The
-- identification is lossless: no receipt is owed for going across and
-- back.  This is मुक्तिः शून्य-व्ययो मार्गः (सूत्र १७) at the level of the
-- structure — transport is the null path, and the null path conserves.
------------------------------------------------------------------------

⊞-return : transport (λ i → Op (P (~ i))) _⊞ᵣ_ ≡ _⊞_
⊞-return = transport⁻Transport (λ i → Op (P i)) _⊞_

------------------------------------------------------------------------
-- The identification is a STRICT monoid isomorphism — on the nose.
--
-- Because `_⊞ᵣ_` is the conjugate DEFINITIONALLY, `anuloma` and `viloma`
-- are monoid homomorphisms with `refl` proofs: they do not merely respect
-- the operation up to a path, they respect it up to nothing.  So ℕ × ℕ
-- and rāśi-traya are not two isomorphic monoids — they are the SAME
-- commutative monoid in two presentations (सूत्र २८: everything is proven
-- somewhere, and import is identity).  This is the structure identity
-- principle at zero altitude: the equivalence carried the algebra, and
-- the carry left no residue to correct.
------------------------------------------------------------------------

anuloma-hom : (x y : ℕ × ℕ) → anuloma (x ⊞ y) ≡ (anuloma x ⊞ᵣ anuloma y)
anuloma-hom x y = refl

viloma-hom : (u v : rāśi-traya) → viloma (u ⊞ᵣ v) ≡ (viloma u ⊞ viloma v)
viloma-hom u v = refl
