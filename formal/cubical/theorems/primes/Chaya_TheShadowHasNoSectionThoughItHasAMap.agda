{-# OPTIONS --cubical --guardedness --safe #-}

------------------------------------------------------------------------
-- छाया — the shadow, and what is actually impossible about it.
--
-- A bare map
-- ∥ A ∥₁ → A, EXISTS whenever A is inhabited, and this file exhibits one.
-- What does not exist is a SECTION — a map that returns the witness it
-- was given.  That is proved below, unconditionally, for any A carrying
-- two distinct elements, and then instantiated at the Goldbach fibre of
-- 10, which carries 3+7 and 5+5.
--
-- TERM.  छाया / *chāyā*, shadow, is `Prakasha`'s own coinage in
-- this corpus for the truncated form (`G-chaya`), and is carried here for
-- continuity.  It is NOT a sourced technical term and nothing in any
-- tradition is cited for it.  The mathematics is propositional
-- truncation — Voevodsky's h-levels, the substrate this repository names
-- as its one exception — and is claimed for nobody else.
--
------------------------------------------------------------------------

module Chaya_TheShadowHasNoSectionThoughItHasAMap where

open import Prakriti using (IsPrime)
open import Vada using (primeDec)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁; rec)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

-- ═══ a section of the truncation: it must give back what it was given ═══
Section : Type₀ → Type₀
Section A = Σ[ s ∈ (∥ A ∥₁ → A) ] ((x : A) → s ∣ x ∣₁ ≡ x)

-- ═══ the theorem ═══
-- two distinct elements are enough.  no appeal to the shape of A.
noSection : {A : Type₀} (a b : A) → ¬ (a ≡ b) → ¬ Section A
noSection a b a≢b (s , sec) =
  a≢b (sym (sec a) ∙ cong s (squash₁ ∣ a ∣₁ ∣ b ∣₁) ∙ sec b)

-- ═══ and the map that does exist ═══
-- inhabited A: a map ∥ A ∥₁ → A exists, trivially;
-- what fails is the section, not the map.
mapFromInhabited : {A : Type₀} → A → (∥ A ∥₁ → A)
mapFromInhabited a _ = a

-- ═══ pulling certificates out of the decider ═══
True : {A : Type₀} → Dec A → Type₀
True (yes _) = Unit
True (no  _) = ⊥

toWitness : {A : Type₀} {d : Dec A} → True d → A
toWitness {d = yes a} _ = a

p3 : IsPrime 3
p3 = toWitness {d = primeDec 3} tt

p5 : IsPrime 5
p5 = toWitness {d = primeDec 5} tt

p7 : IsPrime 7
p7 = toWitness {d = primeDec 7} tt

-- ═══ the Goldbach fibre of a single even number ═══
Fibre : ℕ → Type₀
Fibre n = Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] IsPrime p × IsPrime q × (p + q ≡ n)

-- 10 = 3 + 7 and 10 = 5 + 5.  Ganana.gcount 10 ≡ 2 counts exactly these.
three+seven : Fibre 10
three+seven = 3 , 7 , p3 , p7 , refl

five+five : Fibre 10
five+five = 5 , 5 , p5 , p5 , refl

3≢5 : ¬ (3 ≡ 5)
3≢5 e = znots (injSuc (injSuc (injSuc e)))

fibrePlural : ¬ (three+seven ≡ five+five)
fibrePlural e = 3≢5 (cong fst e)

-- ═══ the consequence, at the fibre ═══
noSectionAt10 : ¬ Section (Fibre 10)
noSectionAt10 = noSection three+seven five+five fibrePlural

-- and the map does exist there
mapAt10 : ∥ Fibre 10 ∥₁ → Fibre 10
mapAt10 = mapFromInhabited three+seven

-- ═══ what the shadow keeps and what it drops ═══
-- the collapse, from Prakasha, restated locally
chaya : Fibre 10 → ∥ Fibre 10 ∥₁
chaya = ∣_∣₁

-- every truncated element is equal to every other: the witness is gone
shadowIsProp : (u v : ∥ Fibre 10 ∥₁) → u ≡ v
shadowIsProp = squash₁

-- so the two distinct decompositions become one object in the shadow
bothCollapse : chaya three+seven ≡ chaya five+five
bothCollapse = squash₁ _ _
