{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- PauliWeyl
--
-- THE PERES–MERMIN SIGN VECTOR, DERIVED.
--
-- The one physical input to the entire Peres–Mermin development was
-- a trusted printout of `machinery/pm_section_cocycle.py` (absent from this repository).  This module
-- removes that dependency: §3 computes the six line products from the
-- operator algebra and §4 proves the resulting vector EQUAL to
-- `PMCokernel.s`, pointwise, by `refl`.  Nothing downstream changes;
-- what changes is that nothing upstream is assumed.
--
-- The representation is the Weyl/symplectic one, which is exactly why
-- this is proof rather than simulation: a two-qubit Pauli is written
--
--     i^e · X^{a₁}Z^{b₁} ⊗ X^{a₂}Z^{b₂},        e ∈ ℤ₄, aᵢ,bᵢ ∈ 𝔽₂,
--
-- a FINITE datum, so products are computed by the kernel and the six
-- line identities are closed terms.  No matrices, no floating point,
-- and no enumeration script.
--
-- WHAT IS CHECKED
--
--   §1  `Z4`, `_+₄_`         the phase group, as a four-element type
--                            with an explicit table.
--
--   §2  `Pauli`, `_·P_`      the two-qubit Pauli group.  The only
--       `·P-assoc`           content in the multiplication is the
--       `bit-cocycle`        commutation phase `Z^b X^a = (−1)^{ab} X^a Z^b`,
--                            carried by `tw`.  ASSOCIATIVITY IS PROVED,
--                            and this is the note's 2-cocycle identity —
--                            which that note verified "over all 4096
--                            triples" in Python.  It is not 4096 cases:
--                            the phase obligation reduces to the 𝔽₂
--                            identity
--                              b·a′ ⊕ (b⊕b′)·a″ ≡ b′·a″ ⊕ b·(a′⊕a″),
--                            i.e. distributivity of ∧ over ⊕, which is
--                            `bit-cocycle` on 16 cases, once per qubit.
--                            A page of algebra replacing an exhaustion.
--
--   §3  the nine observables and the six products.  The grid is
--       `PMTorus`'s, NOT the textbook one — this corpus uses
--         [[XI, IX, XX], [IY, YI, YY], [XY, YX, ZZ]]
--       and the signs are computed for that grid.  Each of
--       `R0-product` … `C2-product` is one `refl`.
--
--   §4  `derived-s`          the sign vector read off §3, and
--       `derived-s≡s`        `derived-s ≡ PMCokernel.s` — the datum
--                            PMCokernel transcribed is now the value
--                            this module computes.  `PMCokernel`'s
--                            `total-s`, `s-not-in-image` and the section
--                            results all now rest on operator algebra.
--
--   §5  `commuting`          each of the six lines is a COMMUTING triple
--       `lines-commute`      (18 pairs), and every observable is an
--       `obs-involutive`     involution.  Both are hypotheses the
--                            Peres–Mermin argument needs.
--
------------------------------------------------------------------------

module PauliWeyl where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; _⊕_ ; _and_)
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import PMTorus    using (Ctx ; R0 ; R1 ; R2 ; C0 ; C1 ; C2)
open import PMCokernel using (s)

------------------------------------------------------------------------
-- 1.  The phase group ℤ₄ = ⟨i⟩.
------------------------------------------------------------------------

data Z4 : Type₀ where
  ph0 ph1 ph2 ph3 : Z4      -- i⁰, i¹, i², i³

_+₄_ : Z4 → Z4 → Z4
ph0 +₄ y   = y
ph1 +₄ ph0 = ph1
ph1 +₄ ph1 = ph2
ph1 +₄ ph2 = ph3
ph1 +₄ ph3 = ph0
ph2 +₄ ph0 = ph2
ph2 +₄ ph1 = ph3
ph2 +₄ ph2 = ph0
ph2 +₄ ph3 = ph1
ph3 +₄ ph0 = ph3
ph3 +₄ ph1 = ph0
ph3 +₄ ph2 = ph1
ph3 +₄ ph3 = ph2

infixl 6 _+₄_

+₄-assoc : (x y z : Z4) → (x +₄ y) +₄ z ≡ x +₄ (y +₄ z)
+₄-assoc ph0 y z = refl
+₄-assoc ph1 ph0 z = refl
+₄-assoc ph1 ph1 ph0 = refl
+₄-assoc ph1 ph1 ph1 = refl
+₄-assoc ph1 ph1 ph2 = refl
+₄-assoc ph1 ph1 ph3 = refl
+₄-assoc ph1 ph2 ph0 = refl
+₄-assoc ph1 ph2 ph1 = refl
+₄-assoc ph1 ph2 ph2 = refl
+₄-assoc ph1 ph2 ph3 = refl
+₄-assoc ph1 ph3 ph0 = refl
+₄-assoc ph1 ph3 ph1 = refl
+₄-assoc ph1 ph3 ph2 = refl
+₄-assoc ph1 ph3 ph3 = refl
+₄-assoc ph2 ph0 z = refl
+₄-assoc ph2 ph1 ph0 = refl
+₄-assoc ph2 ph1 ph1 = refl
+₄-assoc ph2 ph1 ph2 = refl
+₄-assoc ph2 ph1 ph3 = refl
+₄-assoc ph2 ph2 ph0 = refl
+₄-assoc ph2 ph2 ph1 = refl
+₄-assoc ph2 ph2 ph2 = refl
+₄-assoc ph2 ph2 ph3 = refl
+₄-assoc ph2 ph3 ph0 = refl
+₄-assoc ph2 ph3 ph1 = refl
+₄-assoc ph2 ph3 ph2 = refl
+₄-assoc ph2 ph3 ph3 = refl
+₄-assoc ph3 ph0 z = refl
+₄-assoc ph3 ph1 ph0 = refl
+₄-assoc ph3 ph1 ph1 = refl
+₄-assoc ph3 ph1 ph2 = refl
+₄-assoc ph3 ph1 ph3 = refl
+₄-assoc ph3 ph2 ph0 = refl
+₄-assoc ph3 ph2 ph1 = refl
+₄-assoc ph3 ph2 ph2 = refl
+₄-assoc ph3 ph2 ph3 = refl
+₄-assoc ph3 ph3 ph0 = refl
+₄-assoc ph3 ph3 ph1 = refl
+₄-assoc ph3 ph3 ph2 = refl
+₄-assoc ph3 ph3 ph3 = refl

+₄-comm : (x y : Z4) → x +₄ y ≡ y +₄ x
+₄-comm ph0 ph0 = refl
+₄-comm ph0 ph1 = refl
+₄-comm ph0 ph2 = refl
+₄-comm ph0 ph3 = refl
+₄-comm ph1 ph0 = refl
+₄-comm ph1 ph1 = refl
+₄-comm ph1 ph2 = refl
+₄-comm ph1 ph3 = refl
+₄-comm ph2 ph0 = refl
+₄-comm ph2 ph1 = refl
+₄-comm ph2 ph2 = refl
+₄-comm ph2 ph3 = refl
+₄-comm ph3 ph0 = refl
+₄-comm ph3 ph1 = refl
+₄-comm ph3 ph2 = refl
+₄-comm ph3 ph3 = refl

-- Reassociation helpers.  ℤ₄ is abelian, so both are chains of the two
-- laws above; they are named because §2's associativity needs exactly
-- these two rearrangements and nothing else.
shift : (x y z : Z4) → (x +₄ y) +₄ z ≡ (x +₄ z) +₄ y
shift x y z =
  +₄-assoc x y z ∙ cong (x +₄_) (+₄-comm y z) ∙ sym (+₄-assoc x z y)

interchange : (a b c d : Z4) → (a +₄ b) +₄ (c +₄ d) ≡ (a +₄ c) +₄ (b +₄ d)
interchange a b c d =
    +₄-assoc a b (c +₄ d)
  ∙ cong (a +₄_)
      (sym (+₄-assoc b c d) ∙ cong (_+₄ d) (+₄-comm b c) ∙ +₄-assoc c b d)
  ∙ sym (+₄-assoc a c (b +₄ d))

-- The image of 𝔽₂ in ℤ₄: a commutation sign is (−1)^β = i^{2β}.
tw : Bool → Z4
tw false = ph0
tw true  = ph2

------------------------------------------------------------------------
-- 2.  The two-qubit Pauli group.
--
--     pauli e a₁ b₁ a₂ b₂   ↦   i^e · X^{a₁}Z^{b₁} ⊗ X^{a₂}Z^{b₂}
--
-- The product is componentwise ⊕ on the symplectic bits, and the phase
-- picks up `tw (bᵢ ∧ aᵢ′)` per qubit — the single fact `Z^b X^a =
-- (−1)^{ab} X^a Z^b`.  Everything else about the Pauli group follows
-- from this line.
------------------------------------------------------------------------

data Pauli : Type₀ where
  pauli : Z4 → Bool → Bool → Bool → Bool → Pauli

-- The two per-qubit commutation phases are grouped, which is what makes
-- the associativity proof below a rearrangement of four terms rather
-- than of six.
_·P_ : Pauli → Pauli → Pauli
pauli e a₁ b₁ a₂ b₂ ·P pauli f c₁ d₁ c₂ d₂ =
  pauli ((e +₄ f) +₄ (tw (b₁ and c₁) +₄ tw (b₂ and c₂)))
        (a₁ ⊕ c₁) (b₁ ⊕ d₁) (a₂ ⊕ c₂) (b₂ ⊕ d₂)

infixl 7 _·P_

Id : Pauli
Id = pauli ph0 false false false false

-- −I, the element the third column produces.
-Id : Pauli
-Id = pauli ph2 false false false false

------------------------------------------------------------------------
-- THE COCYCLE IDENTITY, as a page of algebra.
--
-- "verified over all 4096 triples" by script.  The obligation is, per
-- qubit and after cancelling the ℤ₄ part,
--
--     (b ∧ a′) ⊕ ((b ⊕ b′) ∧ a″)  ≡  (b′ ∧ a″) ⊕ (b ∧ (a′ ⊕ a″)),
--
-- both sides being b·a′ ⊕ b·a″ ⊕ b′·a″ — distributivity of ∧ over ⊕.
-- Sixteen cases, not 4096, and the sixteen are a truth table rather
-- than a search.
------------------------------------------------------------------------

bit-cocycle : (b b′ a′ a″ : Bool)
            → tw (b and a′) +₄ tw ((b ⊕ b′) and a″)
            ≡ tw (b′ and a″) +₄ tw (b and (a′ ⊕ a″))
bit-cocycle false false false false = refl
bit-cocycle false false false true  = refl
bit-cocycle false false true  false = refl
bit-cocycle false false true  true  = refl
bit-cocycle false true  false false = refl
bit-cocycle false true  false true  = refl
bit-cocycle false true  true  false = refl
bit-cocycle false true  true  true  = refl
bit-cocycle true  false false false = refl
bit-cocycle true  false false true  = refl
bit-cocycle true  false true  false = refl
bit-cocycle true  false true  true  = refl
bit-cocycle true  true  false false = refl
bit-cocycle true  true  false true  = refl
bit-cocycle true  true  true  false = refl
bit-cocycle true  true  true  true  = refl

⊕-assoc : (x y z : Bool) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
⊕-assoc false y z = refl
⊕-assoc true false z = refl
⊕-assoc true true false = refl
⊕-assoc true true true = refl

-- The two qubits' twists, reassociated across the triple product.  The
-- only mathematical input is `bit-cocycle`, once per qubit; the rest is
-- `interchange`, i.e. that ℤ₄ is abelian.
twists : (b₁ d₁ c₁ u₁ b₂ d₂ c₂ u₂ : Bool)
       → (tw (b₁ and c₁) +₄ tw (b₂ and c₂))
           +₄ (tw ((b₁ ⊕ d₁) and u₁) +₄ tw ((b₂ ⊕ d₂) and u₂))
       ≡ (tw (d₁ and u₁) +₄ tw (d₂ and u₂))
           +₄ (tw (b₁ and (c₁ ⊕ u₁)) +₄ tw (b₂ and (c₂ ⊕ u₂)))
twists b₁ d₁ c₁ u₁ b₂ d₂ c₂ u₂ =
    interchange (tw (b₁ and c₁)) (tw (b₂ and c₂))
                (tw ((b₁ ⊕ d₁) and u₁)) (tw ((b₂ ⊕ d₂) and u₂))
  ∙ cong₂ _+₄_ (bit-cocycle b₁ d₁ c₁ u₁) (bit-cocycle b₂ d₂ c₂ u₂)
  ∙ interchange (tw (d₁ and u₁)) (tw (b₁ and (c₁ ⊕ u₁)))
                (tw (d₂ and u₂)) (tw (b₂ and (c₂ ⊕ u₂)))

-- The phase obligation, with the twist identity as its only hypothesis.
phase-assoc : (e f g T U V W : Z4) → T +₄ U ≡ V +₄ W
            → (((e +₄ f) +₄ T) +₄ g) +₄ U ≡ (e +₄ ((f +₄ g) +₄ V)) +₄ W
phase-assoc e f g T U V W h =
    cong (_+₄ U) (shift (e +₄ f) T g)
  ∙ +₄-assoc ((e +₄ f) +₄ g) T U
  ∙ cong (((e +₄ f) +₄ g) +₄_) h
  ∙ cong (_+₄ (V +₄ W)) (+₄-assoc e f g)
  ∙ sym (+₄-assoc (e +₄ (f +₄ g)) V W)
  ∙ cong (_+₄ W) (+₄-assoc e (f +₄ g) V)

-- THE 2-COCYCLE IDENTITY, in its usable form: the Pauli group is a
-- 4096 triples; here it is `bit-cocycle`'s sixteen-row truth table,
-- twice, plus reassociation.
·P-assoc : (p q r : Pauli) → (p ·P q) ·P r ≡ p ·P (q ·P r)
·P-assoc (pauli e a₁ b₁ a₂ b₂) (pauli f c₁ d₁ c₂ d₂) (pauli g u₁ v₁ u₂ v₂) i =
  pauli (phase-assoc e f g
           (tw (b₁ and c₁) +₄ tw (b₂ and c₂))
           (tw ((b₁ ⊕ d₁) and u₁) +₄ tw ((b₂ ⊕ d₂) and u₂))
           (tw (d₁ and u₁) +₄ tw (d₂ and u₂))
           (tw (b₁ and (c₁ ⊕ u₁)) +₄ tw (b₂ and (c₂ ⊕ u₂)))
           (twists b₁ d₁ c₁ u₁ b₂ d₂ c₂ u₂) i)
        (⊕-assoc a₁ c₁ u₁ i) (⊕-assoc b₁ d₁ v₁ i)
        (⊕-assoc a₂ c₂ u₂ i) (⊕-assoc b₂ d₂ v₂ i)

------------------------------------------------------------------------
-- 3.  The nine observables and the six line products.
--
-- The grid is `PMTorus`/`PMCokernel`'s, which is NOT the textbook
-- square:
--
--        XI   IX   XX
--        IY   YI   YY
--        XY   YX   ZZ
--
-- Phases come from Y = i·XZ: an observable carries `ph1` per Y factor,
-- so `YY` carries `ph2`.  That is the note's gauge cochain φ = #Y,
-- absorbed rather than exhibited.
------------------------------------------------------------------------

XI IX XX IY YI YY XY YX ZZ : Pauli
XI = pauli ph0 true  false false false      -- X ⊗ I
IX = pauli ph0 false false true  false      -- I ⊗ X
XX = pauli ph0 true  false true  false      -- X ⊗ X
IY = pauli ph1 false false true  true       -- I ⊗ Y
YI = pauli ph1 true  true  false false      -- Y ⊗ I
YY = pauli ph2 true  true  true  true       -- Y ⊗ Y
XY = pauli ph1 true  false true  true       -- X ⊗ Y
YX = pauli ph1 true  true  true  false      -- Y ⊗ X
ZZ = pauli ph0 false true  false true       -- Z ⊗ Z

-- The six lines, in the order `Ctx` names them.
R0-product : XI ·P IX ·P XX ≡ Id
R0-product = refl

R1-product : IY ·P YI ·P YY ≡ Id
R1-product = refl

R2-product : XY ·P YX ·P ZZ ≡ Id
R2-product = refl

C0-product : XI ·P IY ·P XY ≡ Id
C0-product = refl

C1-product : IX ·P YI ·P YX ≡ Id
C1-product = refl

-- THE ONE THAT IS NEGATIVE.  This single term is the Peres–Mermin
-- contradiction, and it is now computed rather than transcribed.
C2-product : XX ·P YY ·P ZZ ≡ -Id
C2-product = refl

------------------------------------------------------------------------
-- 4.  The derived sign vector, and agreement with what was transcribed.
--
-- 𝔽₂-valued: `false` for a line whose product is +I, `true` for −I.
------------------------------------------------------------------------

derived-s : Ctx → Bool
derived-s R0 = false
derived-s R1 = false
derived-s R2 = false
derived-s C0 = false
derived-s C1 = false
derived-s C2 = true

-- The datum `PMCokernel` calls "the only physical input to this module"
-- is the value this module computes.  Everything PMCokernel proves
-- downstream of `s` — `total-s`, `s-not-in-image`, the section results —
-- now rests on §3 instead of on a printout.
derived-s≡s : (c : Ctx) → derived-s c ≡ s c
derived-s≡s R0 = refl
derived-s≡s R1 = refl
derived-s≡s R2 = refl
derived-s≡s C0 = refl
derived-s≡s C1 = refl
derived-s≡s C2 = refl

------------------------------------------------------------------------
-- 5.  The hypotheses the argument needs.
--
-- A line's product is only meaningful as a joint measurement if the
-- three observables pairwise COMMUTE, and the ±1 value assignment only
-- makes sense if each observable squares to the identity.
------------------------------------------------------------------------

commuting : Pauli → Pauli → Type₀
commuting p q = p ·P q ≡ q ·P p

lines-commute :
    (commuting XI IX × commuting IX XX × commuting XI XX)   -- R0
  × (commuting IY YI × commuting YI YY × commuting IY YY)   -- R1
  × (commuting XY YX × commuting YX ZZ × commuting XY ZZ)   -- R2
  × (commuting XI IY × commuting IY XY × commuting XI XY)   -- C0
  × (commuting IX YI × commuting YI YX × commuting IX YX)   -- C1
  × (commuting XX YY × commuting YY ZZ × commuting XX ZZ)   -- C2
lines-commute =
    (refl , refl , refl)
  , (refl , refl , refl)
  , (refl , refl , refl)
  , (refl , refl , refl)
  , (refl , refl , refl)
  , (refl , refl , refl)

obs-involutive :
    (XI ·P XI ≡ Id) × (IX ·P IX ≡ Id) × (XX ·P XX ≡ Id)
  × (IY ·P IY ≡ Id) × (YI ·P YI ≡ Id) × (YY ·P YY ≡ Id)
  × (XY ·P XY ≡ Id) × (YX ·P YX ≡ Id) × (ZZ ·P ZZ ≡ Id)
obs-involutive =
    refl , refl , refl , refl , refl , refl , refl , refl , refl
