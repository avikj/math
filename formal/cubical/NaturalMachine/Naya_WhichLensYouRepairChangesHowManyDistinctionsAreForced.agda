{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- NaturalMachine.Naya_WhichLensYouRepairChangesHowManyDistinctionsAreForced
--
-- A six-point witness: for one noncommuting lens pair (π , σ) on a finite
-- uniform space, the coarsest repair of π against σ and the coarsest repair
-- of σ against π force DIFFERENT NUMBERS of new distinctions, and their
-- surviving common views are different partitions.
--
-- What is claimed of the sources, precisely.
--
--   * Per the repository's
--     own `notes/COARSEST_REPAIR_IS_COLOUR_REFINEMENT.md` (absent from this repository), the operative
--     prior art is: commuting partitions = orthogonal partitions (Tjur,
--     *Int. Stat. Rev.* 52, 1984; Bailey, *Des. Codes Cryptogr.* 8, 1996;
--     Nelder 1965); the coarsest equitable refinement is colour refinement
--     (Paige–Tarjan 1987); the profile relation used below is Benzécri's
--     distributional equivalence (*L'Analyse des Données*, Dunod 1973).
--
--   * `Naya` in the file name names the DIAGNOSIS, not the theorem.  In
--     Jaina epistemology a *naya* is a standpoint and a *durnaya* is a
--     standpoint that asserts itself by denying the others (Siddhasena
--     Divkara, *Sanmatitarka*; Akalaka).  The result below is that the
--     π-standpoint and the σ-standpoint on one lens pair yield inequivalent
--     repairs, so calling either one "the canonical surviving view" is a
--     durnaya.
--
-- The witness (elements 0..5):
--
--     π  = {0,1} | {2,3} | {4,5}          3 blocks
--     σ  = {0,2} | {1,3,4,5}              2 blocks
--
--   coarsest repair of π against σ :  ρ₁ = {0}|{1}|{2}|{3}|{4,5}   5 blocks
--   coarsest repair of σ against π :  ρ₂ = {0,2}|{1,3}|{4,5}       3 blocks
--
--   new blocks forced:  π-side 5−3 = 2,   σ-side 3−2 = 1.   2 ≠ 1.
--
-- All arithmetic is on ℕ, cross-multiplied so that no rationals appear.
-- Every theorem below is `refl` on a closed Boolean or numeral.
------------------------------------------------------------------------

module NaturalMachine.Naya_WhichLensYouRepairChangesHowManyDistinctionsAreForced where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; injSuc ; snotz)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; _or_)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1. Finite Boolean apparatus over the six points 0..5
------------------------------------------------------------------------

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

_⇒_ : Bool → Bool → Bool
b ⇒ c = not b or c

infixr 4 _⇒_

bit : Bool → ℕ
bit true  = 1
bit false = 0

-- The carrier is {0,1,2,3,4,5}; every quantifier below is this unrolling.
count : (ℕ → Bool) → ℕ
count p = bit (p 0) + (bit (p 1) + (bit (p 2) + (bit (p 3) + (bit (p 4) + bit (p 5)))))

everyPt : (ℕ → Bool) → Bool
everyPt p = p 0 and (p 1 and (p 2 and (p 3 and (p 4 and p 5))))

somePt : (ℕ → Bool) → Bool
somePt p = p 0 or (p 1 or (p 2 or (p 3 or (p 4 or p 5))))

everyPair : (ℕ → ℕ → Bool) → Bool
everyPair r = everyPt (λ x → everyPt (λ y → r x y))

------------------------------------------------------------------------
-- 2. Partitions as colourings, and the three predicates
------------------------------------------------------------------------

Colouring : Type₀
Colouring = ℕ → ℕ

-- number of colours actually used on the carrier
nblocks : Colouring → ℕ
nblocks c = count (λ k → somePt (λ x → eqℕ (c x) k))

-- |σ-block of a|
blockSize : Colouring → ℕ → ℕ
blockSize c a = count (λ w → eqℕ (c w) (c a))

-- |ρ-block of z  ∩  σ-block of x|
meetSize : Colouring → Colouring → ℕ → ℕ → ℕ
meetSize cr cs z x = count (λ w → eqℕ (cr w) (cr z) and eqℕ (cs w) (cs x))

-- ρ commutes with σ  ⟺  V_ρ is P_σ-invariant  ⟺  for every ρ-block B the
-- density x ↦ |B ∩ σ(x)| / |σ(x)| is constant on ρ-blocks.  Cross-multiplied.
commutes : Colouring → Colouring → Bool
commutes cr cs = everyPair (λ x y →
  eqℕ (cr x) (cr y) ⇒
    everyPt (λ z → eqℕ (meetSize cr cs z x · blockSize cs y)
                       (meetSize cr cs z y · blockSize cs x)))

-- ρ refines q
refines : Colouring → Colouring → Bool
refines cr cq = everyPair (λ x y → eqℕ (cr x) (cr y) ⇒ eqℕ (cq x) (cq y))

sameParts : Colouring → Colouring → Bool
sameParts c d = everyPair (λ x y →
  (eqℕ (c x) (c y) ⇒ eqℕ (d x) (d y)) and (eqℕ (d x) (d y) ⇒ eqℕ (c x) (c y)))

------------------------------------------------------------------------
-- 3. The witness
------------------------------------------------------------------------

-- π = {0,1} | {2,3} | {4,5}
cPi : Colouring
cPi 0 = 0
cPi 1 = 0
cPi 2 = 1
cPi 3 = 1
cPi 4 = 2
cPi 5 = 2
cPi _ = 9

-- σ = {0,2} | {1,3,4,5}
cSg : Colouring
cSg 0 = 0
cSg 1 = 1
cSg 2 = 0
cSg 3 = 1
cSg 4 = 1
cSg 5 = 1
cSg _ = 9

-- ρ₁ = {0}|{1}|{2}|{3}|{4,5}   -- the coarsest repair of π against σ
cR1 : Colouring
cR1 0 = 0
cR1 1 = 1
cR1 2 = 2
cR1 3 = 3
cR1 4 = 4
cR1 5 = 4
cR1 _ = 9

-- ρ₂ = {0,2}|{1,3}|{4,5}       -- the coarsest repair of σ against π
cR2 : Colouring
cR2 0 = 0
cR2 1 = 1
cR2 2 = 0
cR2 3 = 1
cR2 4 = 2
cR2 5 = 2
cR2 _ = 9

-- the two partitions strictly between π and ρ₁ that refine π
cM1 : Colouring          -- {0}|{1}|{2,3}|{4,5}
cM1 0 = 0
cM1 1 = 1
cM1 2 = 2
cM1 3 = 2
cM1 4 = 3
cM1 5 = 3
cM1 _ = 9

cM2 : Colouring          -- {0,1}|{2}|{3}|{4,5}
cM2 0 = 0
cM2 1 = 0
cM2 2 = 1
cM2 3 = 2
cM2 4 = 3
cM2 5 = 3
cM2 _ = 9

-- J = {0,1,2,3}|{4,5}: the finest common coarsening of π and ρ₂
cJ : Colouring
cJ 0 = 0
cJ 1 = 0
cJ 2 = 0
cJ 3 = 0
cJ 4 = 1
cJ 5 = 1
cJ _ = 9

------------------------------------------------------------------------
-- 4. The pair genuinely fails to commute, and the predicate is symmetric
------------------------------------------------------------------------

pi-sigma-noncommuting : commutes cPi cSg ≡ false
pi-sigma-noncommuting = refl

sigma-pi-noncommuting : commutes cSg cPi ≡ false
sigma-pi-noncommuting = refl

------------------------------------------------------------------------
-- 5. ρ₁ is the coarsest repair of π against σ
------------------------------------------------------------------------

r1-refines-pi : refines cR1 cPi ≡ true
r1-refines-pi = refl

r1-commutes : commutes cR1 cSg ≡ true
r1-commutes = refl

-- The repair set has a unique coarsest element (LENS_REPAIR.md (absent from this repository) §1, join
-- closure), so the coarsest repair lies between π and ρ₁.  A partition there
-- keeps or splits each π-block along its ρ₁-pieces, so there are exactly four
-- (π, cM1, cM2, ρ₁) and the other three are all refuted as repairs.
m1-not-a-repair : commutes cM1 cSg ≡ false
m1-not-a-repair = refl

m2-not-a-repair : commutes cM2 cSg ≡ false
m2-not-a-repair = refl
-- (π itself is handled by `pi-sigma-noncommuting`.)

------------------------------------------------------------------------
-- 6. ρ₂ is the coarsest repair of σ against π
------------------------------------------------------------------------

r2-refines-sigma : refines cR2 cSg ≡ true
r2-refines-sigma = refl

r2-commutes : commutes cR2 cPi ≡ true
r2-commutes = refl
-- Only σ lies strictly between σ and ρ₂, and `sigma-pi-noncommuting` kills it.

------------------------------------------------------------------------
-- 7. The asymmetry
------------------------------------------------------------------------

pi-blocks : nblocks cPi ≡ 3
pi-blocks = refl

r1-blocks : nblocks cR1 ≡ 5
r1-blocks = refl

sigma-blocks : nblocks cSg ≡ 2
sigma-blocks = refl

r2-blocks : nblocks cR2 ≡ 3
r2-blocks = refl

-- new distinctions forced on each side
pi-side-forces-two : nblocks cPi + 2 ≡ nblocks cR1
pi-side-forces-two = refl

sigma-side-forces-one : nblocks cSg + 1 ≡ nblocks cR2
sigma-side-forces-one = refl

two≢one : ¬ (2 ≡ 1)
two≢one p = snotz (injSuc p)

-- REFUTED: "each side of a lens pair must make the same number of new
-- distinctions" (the reciprocity a correspondence-shaped reading predicts).
no-reciprocity-in-forced-blocks : ¬ (2 ≡ 1)
no-reciprocity-in-forced-blocks = two≢one

-- The carriers themselves differ in size, not only in the increment.
r1-and-r2-differ : sameParts cR1 cR2 ≡ false
r1-and-r2-differ = refl

------------------------------------------------------------------------
-- 8. The two surviving common views are different partitions
------------------------------------------------------------------------

-- π-side: ρ₁ refines σ, so the finest common coarsening of ρ₁ and σ is σ.
r1-refines-sigma : refines cR1 cSg ≡ true
r1-refines-sigma = refl

-- σ-side: both π and ρ₂ refine J, and J is their finest common coarsening
-- (0∼1 by π, 1∼3 by ρ₂, 3∼2 by π forces {0,1,2,3}; 4∼5 by both).
pi-refines-J : refines cPi cJ ≡ true
pi-refines-J = refl

r2-refines-J : refines cR2 cJ ≡ true
r2-refines-J = refl

-- and the two surviving views are not the same partition
surviving-views-differ : sameParts cSg cJ ≡ false
surviving-views-differ = refl
