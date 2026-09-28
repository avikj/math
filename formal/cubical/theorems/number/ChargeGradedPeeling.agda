{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ChargeGradedPeeling
--
-- DELTA 14, PROGRAM 14.74 — CHARGE AS A DEPENDENT INDEX, AND
-- LEAST-PRIME PEELING AS A DIRECTED TRANSFORMATION OF INDEXED STATES.
--
-- Delta 14 §H: `G : Charge → U`, the grand-canonical object is the
-- total space `Σ_r G r`, a fixed charge is a fibre, and T14.44 says
-- exactly when a transformation of the total space restricts to a
-- sector.  `PerspectiveCore.Graded` has those lemmas in
-- the abstract.  THIS FILE IS THE INSTANCE, in the arithmetic model
-- `SieveFiber` already built and checked (X = 30).
--
-- The instance is: index by the number of prime factors, and let the
-- transformation be **least-prime peeling** `n ↦ n / p⁻(n)`.
--
--
-- WHAT IS CHECKED (every `refl` is a finite exhaustive verification
-- over the 30-element domain, performed by the typechecker; CLAUDE.md (absent from this repository)
-- §"Exact / certified symbolic computation is proof")
--
--   §2  `peel∈`            peeling stays inside the domain [1,30].
--       `peelDrops`        Ω(peel n) + 1 = Ω(n)  for n ≥ 2.
--                          THE SPECIFIED INDEX CHANGE, exactly one step.
--       `peelFlips`        its parity shadow: charge(peel n) = ¬charge n.
--
--   §3  `peelGrade`        ℕ-GRADED FORM.  `H k` = states of exactly k
--                          prime factors; peeling is a map
--                          `H (suc k) → H k`.  Directed: the index
--                          strictly decreases, so this is a
--                          transformation BETWEEN sectors, never inside
--                          one.
--       `peelFixesUnit`    the exception, and it is the whole content of
--                          §5: `peel 1 = 1`, so the unit is peeling's
--                          fixed point and the only state where the
--                          index does not move.
--
--   §4  `Total`, `T`       BOOL-GRADED FORM, in `Graded`'s own shape:
--                          `Total = Σ Bool G`, `T : Total → Total` the
--                          peeling with its base component COMPUTED
--                          (`charge ∘ peel`), not assumed.
--       `noSectorRestriction`
--                          T14.44's hypothesis FAILS: for the sector
--                          `charge = false`, the state 4 has
--                          `base (T (false , 4)) = true`.  So peeling
--                          does not restrict to a charge sector.
--       `noSquareRestriction`
--                          AND NEITHER DOES ITS SQUARE — the naive fix.
--                          Witness 2: `T(true,2) = (false,1)` and
--                          `T(false,1) = (false,1)`, because 1 is a
--                          fixed point.  Two-step closure is NOT a
--                          property of the sector.
--
--   §5  `P¹`, `P²`         C14.46, LANDED.  On the sub-object `G₂` of
--                          states with Ω ≥ 2 — precisely the states the
--                          unit exception excludes — peeling is a map
--                          `G₂ r → G (not r)` and its square is a map
--                          `G₂ r → G r`.  The third component of each is
--                          a SUPPLIED PATH in the index, `peelFlips`
--                          resp. `peelSquareCloses`, composed with the
--                          state's own index proof.
--       `indexPathIsNotNot`
--                          the transport that makes the square close is
--                          exactly `notnot : ¬¬r ≡ r`.
--
--   §6  `sectorToFibre`, `fibreToSector`, `sector-fibre-roundtrip`
--                          "a fixed charge is a fibre" (Delta 14 §H's
--                          own phrase), as maps rather than as prose.
--
--
-- THE SENTENCE C14.46 ASKS FOR, with this file's reading of it:
--
--   *Canonical closure is dependent-index preservation up to specified
--    transport.*
--
-- Here the specified transport is `notnot`, the closure holds for the
-- SQUARE and not the map, and — the part that is not in the slogan —
-- it holds only after the sub-object `Ω ≥ 2` is carved out, because the
-- unit is a fixed point of the peeling and no transport repairs a
-- fixed point.  The exception is not noise; it is why `noSquareRestriction`
-- is a theorem.
--
--
------------------------------------------------------------------------

module ChargeGradedPeeling where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; _∸_ ; injSuc ; znots)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; notnot ; _or_ ; if_then_else_
        ; true≢false ; false≢true)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Empty as ⊥ using (⊥)

open import PerspectiveCore using (module Graded)

------------------------------------------------------------------------
-- §0  What is taken from `SieveFiber`, and the three Boolean lemmas
--     that had to be re-proved because they are `private` there.
------------------------------------------------------------------------

open import SieveFiber as SF
  using ( ltᵇ ; eqᵇ ; eqᵇ→≡ ; _div_ ; _rem_ ; isOdd
        ; _∈_ ; allOf ; allOf-sound ; memberOf ; eqBool ; eqBool→≡
        ; domain ; Ω ; charge )

private
  orSplit : (x y : Bool) → x or y ≡ true → (x ≡ true) ⊎ (y ≡ true)
  orSplit true  y p = inl refl
  orSplit false y p = inr p

  notTrue : (x : Bool) → not x ≡ true → x ≡ false
  notTrue false p = refl
  notTrue true  p = ⊥.rec (false≢true p)

  memberOf→∈ : (xs : List ℕ) (n : ℕ) → memberOf xs n ≡ true → n ∈ xs
  memberOf→∈ []       n p = ⊥.rec (false≢true p)
  memberOf→∈ (x ∷ xs) n p with orSplit (eqᵇ x n) (memberOf xs n) p
  ... | inl s = inl (sym (eqᵇ→≡ x n s))
  ... | inr s = inr (memberOf→∈ xs n s)

------------------------------------------------------------------------
-- §1  Least-prime peeling
--
-- `lpf n` is the least divisor of n that is ≥ 2, found by trial
-- division; for n < 4 or n prime the search runs past √n and returns n
-- itself, which is the right answer in both cases.  `peel` divides it
-- out, and fixes 0 and 1.
------------------------------------------------------------------------

lpfF : ℕ → ℕ → ℕ → ℕ
lpfF zero    d n = n
lpfF (suc f) d n =
  if ltᵇ n (d · d) then n
  else if eqᵇ (n rem d) zero then d
  else lpfF f (suc d) n

lpf : ℕ → ℕ
lpf n = lpfF n 2 n

peel : ℕ → ℕ
peel n = if ltᵇ n 2 then n else n div lpf n

-- Spot checks, so the definition is not taken on trust.
_ : lpf 30 ≡ 2
_ = refl

_ : lpf 25 ≡ 5
_ = refl

_ : lpf 29 ≡ 29
_ = refl

_ : peel 30 ≡ 15
_ = refl

_ : peel 29 ≡ 1
_ = refl

------------------------------------------------------------------------
-- §2  THE SPECIFIED INDEX CHANGE
------------------------------------------------------------------------

-- Peeling stays in the domain.
chkPeelDom : ℕ → Bool
chkPeelDom n = memberOf domain (peel n)

peelDomᵇ : allOf domain chkPeelDom ≡ true
peelDomᵇ = refl

peel∈ : {n : ℕ} → n ∈ domain → peel n ∈ domain
peel∈ {n} m =
  memberOf→∈ domain (peel n) (allOf-sound domain chkPeelDom peelDomᵇ m)

-- A state with any prime factor at all is ≥ 2.
chkPos : ℕ → Bool
chkPos n = eqᵇ (Ω n) 0 or not (ltᵇ n 2)

posᵇ : allOf domain chkPos ≡ true
posᵇ = refl

Ω>0→≥2 : {n : ℕ} → n ∈ domain → (Ω n ≡ 0 → ⊥) → ltᵇ n 2 ≡ false
Ω>0→≥2 {n} m h with orSplit (eqᵇ (Ω n) 0) (not (ltᵇ n 2))
                            (allOf-sound domain chkPos posᵇ m)
... | inl s = ⊥.rec (h (eqᵇ→≡ (Ω n) 0 s))
... | inr s = notTrue (ltᵇ n 2) s

-- THE INDEX CHANGE: peeling removes exactly one prime factor.
chkDrop : ℕ → Bool
chkDrop n = ltᵇ n 2 or eqᵇ (suc (Ω (peel n))) (Ω n)

dropᵇ : allOf domain chkDrop ≡ true
dropᵇ = refl

peelDrops : {n : ℕ} → n ∈ domain → ltᵇ n 2 ≡ false
          → suc (Ω (peel n)) ≡ Ω n
peelDrops {n} m h with orSplit (ltᵇ n 2) (eqᵇ (suc (Ω (peel n))) (Ω n))
                               (allOf-sound domain chkDrop dropᵇ m)
... | inl s = ⊥.rec (false≢true (sym h ∙ s))
... | inr s = eqᵇ→≡ (suc (Ω (peel n))) (Ω n) s

-- Its parity shadow, which is the Bool-graded statement of §4.
chkFlip : ℕ → Bool
chkFlip n = ltᵇ n 2 or eqBool (charge (peel n)) (not (charge n))

flipᵇ : allOf domain chkFlip ≡ true
flipᵇ = refl

peelFlips : {n : ℕ} → n ∈ domain → ltᵇ n 2 ≡ false
          → charge (peel n) ≡ not (charge n)
peelFlips {n} m h
  with orSplit (ltᵇ n 2) (eqBool (charge (peel n)) (not (charge n)))
               (allOf-sound domain chkFlip flipᵇ m)
... | inl s = ⊥.rec (false≢true (sym h ∙ s))
... | inr s = eqBool→≡ (charge (peel n)) (not (charge n)) s

------------------------------------------------------------------------
-- §3  THE ℕ-GRADED FORM
--
-- `H k` is the sector of states with exactly k prime factors.  Peeling
-- is a map `H (suc k) → H k`: it is a transformation of indexed states
-- that CHANGES the index, in a way specified up to the nose.
------------------------------------------------------------------------

H : ℕ → Type
H k = Σ[ n ∈ ℕ ] ((n ∈ domain) × (Ω n ≡ k))

peelGrade : (k : ℕ) → H (suc k) → H k
peelGrade k (n , m , e) =
  peel n , peel∈ m , injSuc (peelDrops m (Ω>0→≥2 m (λ z → znots (sym z ∙ e))) ∙ e)

-- The exception.  1 is peeling's fixed point, and `H 0` is where the
-- directed transformation stops: there is no `H 0 → H k` below it.
peelFixesUnit : peel 1 ≡ 1
peelFixesUnit = refl

unitInH0 : H 0
unitInH0 = 1 , memberOf→∈ domain 1 refl , refl

------------------------------------------------------------------------
-- §4  THE BOOL-GRADED FORM, IN `Graded`'s OWN SHAPE  (T14.44)
------------------------------------------------------------------------

-- `G : Charge → U`, Delta 14 §H's dependent index.
G : Bool → Type
G r = Σ[ n ∈ ℕ ] ((n ∈ domain) × (charge n ≡ r))

-- `PerspectiveCore.Graded` instantiated at this family.  `Total` and
-- `base` below are that module's, not new definitions.
module GradedCharge = Graded {C = Bool} G

open GradedCharge using (Total ; base)

-- The transformation.  Its base component is COMPUTED from the state —
-- `charge ∘ peel` — so nothing about index preservation is smuggled in
-- by the typing.
T : Total → Total
T (r , n , m , c) = charge (peel n) , peel n , peel∈ m , refl

-- Two states, named because the two negatives turn on them.
4∈ : 4 ∈ domain
4∈ = memberOf→∈ domain 4 refl

2∈ : 2 ∈ domain
2∈ = memberOf→∈ domain 2 refl

g₄ : G false
g₄ = 4 , 4∈ , refl

g₂ : G true
g₂ = 2 , 2∈ , refl

-- T14.44's hypothesis, and it FAILS: peeling does not restrict to a
-- charge sector.  4 has charge `false` and `peel 4 = 2` has charge
-- `true`.  So `restrict-fibre` is inapplicable — as it should be, since
-- peeling is charge-CHANGING by design.
noSectorRestriction : ((g : G false) → base (T (false , g)) ≡ false) → ⊥
noSectorRestriction h = true≢false (h g₄)

-- The naive repair also fails.  One might hope the SQUARE restricts,
-- since ¬¬ = id.  It does not, and the counterexample is the unit:
-- `T (true , 2) = (false , 1)` and `T (false , 1) = (false , 1)`,
-- because `peel 1 = 1`.  A prime peels to the unit and then stops.
noSquareRestriction : ((g : G true) → base (T (T (true , g))) ≡ true) → ⊥
noSquareRestriction h = false≢true (h g₂)

------------------------------------------------------------------------
-- §5  C14.46, LANDED ON THE SUB-OBJECT THE EXCEPTION LEAVES
--
-- Carve out the states the unit exception excludes — Ω ≥ 2 — and the
-- closure statement becomes true, with its transport supplied as data.
------------------------------------------------------------------------

big : ℕ → Bool
big n = ltᵇ 1 (Ω n)

G₂ : Bool → Type
G₂ r = Σ[ n ∈ ℕ ] ((n ∈ domain) × ((big n ≡ true) × (charge n ≡ r)))

chkBig : ℕ → Bool
chkBig n = not (big n) or not (ltᵇ n 2)

bigᵇ : allOf domain chkBig ≡ true
bigᵇ = refl

big→≥2 : {n : ℕ} → n ∈ domain → big n ≡ true → ltᵇ n 2 ≡ false
big→≥2 {n} m h with orSplit (not (big n)) (not (ltᵇ n 2))
                            (allOf-sound domain chkBig bigᵇ m)
... | inl s = ⊥.rec (false≢true (sym (cong not h) ∙ s))
... | inr s = notTrue (ltᵇ n 2) s

chkSquare : ℕ → Bool
chkSquare n = not (big n) or eqBool (charge (peel (peel n))) (charge n)

squareᵇ : allOf domain chkSquare ≡ true
squareᵇ = refl

peelSquareCloses : {n : ℕ} → n ∈ domain → big n ≡ true
                 → charge (peel (peel n)) ≡ charge n
peelSquareCloses {n} m h
  with orSplit (not (big n)) (eqBool (charge (peel (peel n))) (charge n))
               (allOf-sound domain chkSquare squareᵇ m)
... | inl s = ⊥.rec (false≢true (sym (cong not h) ∙ s))
... | inr s = eqBool→≡ (charge (peel (peel n))) (charge n) s

-- ONE STEP: a map of indexed states over `not`.  The third component is
-- the specified index path, not a side condition.
P¹ : (r : Bool) → G₂ r → G (not r)
P¹ r (n , m , h , c) =
  peel n , peel∈ m , (peelFlips m (big→≥2 m h) ∙ cong not c)

-- TWO STEPS: index preservation, i.e. canonical closure — up to the
-- transport `notnot`, which is exactly what makes the square close.
P² : (r : Bool) → G₂ r → G r
P² r (n , m , h , c) =
  peel (peel n) , peel∈ (peel∈ m) , (peelSquareCloses m h ∙ c)

indexPathIsNotNot : (r : Bool) → not (not r) ≡ r
indexPathIsNotNot = notnot

------------------------------------------------------------------------
-- §6  "A FIXED CHARGE IS A FIBRE"  (Delta 14 §H)
------------------------------------------------------------------------

fibreOf : Bool → Type
fibreOf r = Σ[ t ∈ Total ] (base t ≡ r)

sectorToFibre : (r : Bool) → G r → fibreOf r
sectorToFibre r g = (r , g) , refl

fibreToSector : (r : Bool) → fibreOf r → G r
fibreToSector r ((r' , g) , p) = subst G p g

sector-fibre-roundtrip :
  (r : Bool) (g : G r) → fibreToSector r (sectorToFibre r g) ≡ g
sector-fibre-roundtrip r g = substRefl {B = G} g
