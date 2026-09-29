{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- InflationVersusSubgroup
--
-- Thm 3.5 of `notes/EIGHT_CLASSES_COLLAPSE_TO_FOUR_SLOTS.md` (absent from
-- this repository) WITH ITS
-- QUALIFIER MADE PART OF THE TYPE: the enlargement it is about is
-- enlargement ALONG A QUOTIENT, and the other reading of "enlargement"
-- — a subgroup inclusion Γ ≤ G — has no map for the theorem to be
-- about.
--
-- SOURCE STATEMENT (`notes/EIGHT_CLASSES_COLLAPSE_TO_FOUR_SLOTS.md`
-- (absent from this repository) §3.5, verbatim):
--
--   *Let N ⊴ G act trivially on V, and let Γ = G/N.  Then inflation
--   inf : H¹(Γ,V) → H¹(G,V) is injective.  Hence enlarging the symmetry
--   group from Γ to G never kills a nonzero class.*
--
-- The audit `notes/FULL_READ_DRAW_5.md` (absent from this repository)
-- §D7 records that §0's table
-- keeps the qualifier ("enlarging the symmetry group along a quotient")
-- and that §2.8, §3.5's own Reading, §4's rejection row and §5.5 all
-- drop it: "symmetry enlargement: Thm 3.5 proves this is **not a repair
-- at all**", "widening *symmetry* cannot [kill]", "*refuted, not a
-- repair*", "one of which (symmetry enlargement) is **proved** to be no
-- repair" — and §3.5 calls the flattened version "the note's principal
-- negative".  The dropped qualifier has no lexical signature: the
-- flattened sentences contain no wrong word, only a missing one.
--
-- WHAT IS AT STAKE.  For Γ ≤ G there is no canonical
-- H¹(Γ,V) → H¹(G,V) at all; the canonical map runs the other way
-- (restriction).  So the subgroup reading is not "also proved" and it
-- is not even "unproved by the same argument": there is nothing for the
-- argument to be applied to, and — as this file shows on the smallest
-- model — the transport a repair-claim would need is not merely
-- unproved but IMPOSSIBLE.
--
-- THIS IS A MODEL, NOT THE FULL SETTING.  The full setting is H¹ of an
-- arbitrary group with arbitrary coefficients.  Formalized here is the
-- smallest pair that realizes both readings at once:
--
--   * G = ℤ/4, N = {0,2} ≅ ℤ/2 ⊴ G, Γ = G/N ≅ ℤ/2, V = ℤ/2 trivial
--     action.  N is BOTH the kernel of the quotient (giving the
--     inflation reading) AND a subgroup of G (giving the subgroup
--     reading), so the two readings are compared on one and the same
--     group inclusion/projection pair.
--   * With trivial action, H¹(A,V) = Hom(A,V).  Hom(ℤ/4,ℤ/2) = {0,χ}
--     with χ = proj, and Hom(ℤ/2,ℤ/2) = {0,id}; these are enumerated as
--     `H4` and `H2`, each class carried by its realizing function
--     (`real4`, `real2`).
--   * `infl` is CERTIFIED to be precomposition with `proj`
--     (`infl-is-inflation`) and `res` is CERTIFIED to be precomposition
--     with `incl` (`res-is-restriction`), so neither is an ad-hoc table.
--     `proj` and `incl` are checked to be group homomorphisms by finite
--     exhaustion over all 16 resp. 4 pairs.  Everything below is a
--     closed computation; every proof is `refl` or a case split.
--
-- HEADLINE TERMS
--   infl-injective          Thm 3.5 on this model, quotient hypothesis in the type
--   res-is-zero             the subgroup map runs the other way and is zero here
--   no-section              NO function H¹(N,V) → H¹(G,V) splits restriction
--   quotient-map-is-not-the-subgroup-map  inflation does not serve the flat reading
------------------------------------------------------------------------

module InflationVersusSubgroup where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Bool.Properties using (true≢false)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)

------------------------------------------------------------------------
-- 0.  The groups.  G = ℤ/4 ⊇ N = {0,2} ≅ ℤ/2 = Γ = G/N.

data Z4 : Type where
  z0 z1 z2 z3 : Z4

data Z2 : Type where
  e0 e1 : Z2

_+4_ : Z4 → Z4 → Z4
z0 +4 y = y
z1 +4 z0 = z1 ; z1 +4 z1 = z2 ; z1 +4 z2 = z3 ; z1 +4 z3 = z0
z2 +4 z0 = z2 ; z2 +4 z1 = z3 ; z2 +4 z2 = z0 ; z2 +4 z3 = z1
z3 +4 z0 = z3 ; z3 +4 z1 = z0 ; z3 +4 z2 = z1 ; z3 +4 z3 = z2

_+2_ : Z2 → Z2 → Z2
e0 +2 y = y
e1 +2 e0 = e1
e1 +2 e1 = e0

-- The quotient map G ↠ Γ (kernel N = {z0,z2}) and the subgroup
-- inclusion N ↪ G.  These are the two directions the flattened reading
-- confuses.
proj : Z4 → Z2
proj z0 = e0 ; proj z1 = e1 ; proj z2 = e0 ; proj z3 = e1

incl : Z2 → Z4
incl e0 = z0
incl e1 = z2

-- Both are homomorphisms: 16 resp. 4 cases, exhaustively.
proj-hom : (x y : Z4) → proj (x +4 y) ≡ proj x +2 proj y
proj-hom z0 z0 = refl ; proj-hom z0 z1 = refl ; proj-hom z0 z2 = refl ; proj-hom z0 z3 = refl
proj-hom z1 z0 = refl ; proj-hom z1 z1 = refl ; proj-hom z1 z2 = refl ; proj-hom z1 z3 = refl
proj-hom z2 z0 = refl ; proj-hom z2 z1 = refl ; proj-hom z2 z2 = refl ; proj-hom z2 z3 = refl
proj-hom z3 z0 = refl ; proj-hom z3 z1 = refl ; proj-hom z3 z2 = refl ; proj-hom z3 z3 = refl

incl-hom : (x y : Z2) → incl (x +2 y) ≡ incl x +4 incl y
incl-hom e0 e0 = refl ; incl-hom e0 e1 = refl
incl-hom e1 e0 = refl ; incl-hom e1 e1 = refl

------------------------------------------------------------------------
-- 1.  The cohomology, with trivial coefficients: H¹(A,V) = Hom(A,V).

data H4 : Type where          -- H¹(G,V) = Hom(ℤ/4,ℤ/2) = {0 , χ}
  h0 hχ : H4

data H2 : Type where          -- H¹(N,V) = H¹(Γ,V) = Hom(ℤ/2,ℤ/2) = {0 , id}
  k0 kι : H2

real4 : H4 → (Z4 → Z2)
real4 h0 _ = e0
real4 hχ g = proj g

real2 : H2 → (Z2 → Z2)
real2 k0 _ = e0
real2 kι x = x

real4-hom : (c : H4) (x y : Z4) → real4 c (x +4 y) ≡ real4 c x +2 real4 c y
real4-hom h0 _ _ = refl
real4-hom hχ x y = proj-hom x y

real2-hom : (c : H2) (x y : Z2) → real2 c (x +2 y) ≡ real2 c x +2 real2 c y
real2-hom k0 _ _ = refl
real2-hom kι _ _ = refl

-- Classes are distinguishable.
b2 : H2 → Bool
b2 k0 = false
b2 kι = true

k0≢kι : k0 ≡ kι → ⊥
k0≢kι q = true≢false (cong b2 (sym q))

b4 : H4 → Bool
b4 h0 = false
b4 hχ = true

h0≢hχ : h0 ≡ hχ → ⊥
h0≢hχ q = true≢false (cong b4 (sym q))

------------------------------------------------------------------------
-- 2.  The two maps, each certified to be the map it is named after.

-- Inflation, along the quotient G ↠ Γ.
infl : H2 → H4
infl k0 = h0
infl kι = hχ

infl-is-inflation : (c : H2) (g : Z4) → real4 (infl c) g ≡ real2 c (proj g)
infl-is-inflation k0 _ = refl
infl-is-inflation kι _ = refl

-- Restriction, along the inclusion N ↪ G.  This is the ONLY canonical
-- map attached to a subgroup, and it points the other way.
res : H4 → H2
res h0 = k0
res hχ = k0

res-is-restriction : (c : H4) (x : Z2) → real2 (res c) x ≡ real4 c (incl x)
res-is-restriction h0 _  = refl
res-is-restriction hχ e0 = refl
res-is-restriction hχ e1 = refl

------------------------------------------------------------------------
-- 3.  Thm 3.5 on this model, with the quotient hypothesis in the type:
--     inflation is injective, so enlarging Γ = G/N to G kills nothing.

infl-injective : (c d : H2) → infl c ≡ infl d → c ≡ d
infl-injective k0 k0 _ = refl
infl-injective kι kι _ = refl
infl-injective k0 kι q = ⊥-rec (h0≢hχ q)
infl-injective kι k0 q = ⊥-rec (h0≢hχ (sym q))

------------------------------------------------------------------------
-- 4.  The other reading.  For N ≤ G there is no map H¹(N,V) → H¹(G,V);
--     what exists is `res`, and on this model `res` is identically zero.

res-is-zero : (c : H4) → res c ≡ k0
res-is-zero h0 = refl
res-is-zero hχ = refl

-- Hence NO function whatsoever splits restriction: the nonzero class on
-- the subgroup is not the restriction of anything on G.  A "repair by
-- subgroup enlargement" would need exactly such a transport, and there
-- is none — for reasons that have nothing to do with Thm 3.5.
no-section : (m : H2 → H4) → res (m kι) ≡ kι → ⊥
no-section m q = k0≢kι (sym (res-is-zero (m kι)) ∙ q)

-- In particular the quotient theorem's own map does not serve the
-- flattened reading: `infl` is not a section of `res`.
quotient-map-is-not-the-subgroup-map : res (infl kι) ≡ kι → ⊥
quotient-map-is-not-the-subgroup-map = no-section infl

------------------------------------------------------------------------
-- 5.  Therefore the flattened statement — "enlargement (flatly) is
--     covered by Thm 3.5" — is false on the model, not merely unproved.
--     `NaturalMachine/Control/InflationFlattened.agda` asserts exactly
--     the antecedent below and must fail to type-check.

flattened-enlargement-false :
  ((c : H2) → res (infl c) ≡ c) → ⊥
flattened-enlargement-false h = quotient-map-is-not-the-subgroup-map (h kι)
