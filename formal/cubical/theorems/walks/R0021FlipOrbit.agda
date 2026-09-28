{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- R0021FlipOrbit
--
-- INDEPENDENT AUDIT OF R0021, CLAUSES (B) AND (D)
--   (collab/discovery/claims/R0021-window5-stationary-countermodel.md (absent from this repository);
--    the finite table itself is already kernel-checked in
--    `Window5Walsh.agda`, which this module imports and extends)
--
-- R0021 claims a countermodel to the flip/orbit step in the nonzero-
-- (a,b,c) case of Tao–Teräväinen, Forum Math. Sigma 7 (2019) e33,
-- Thm 1.14 §7.  Window5Walsh already checks the headline table facts
-- (ten zeros, mass one, stationarity, Walsh spectrum, one broken-flip
-- witness).  This module formalizes the packet's clauses
--
--   (B) for |c| < 1 at most TEN of the 32 atoms vanish, with equality
--       iff c = 1/3 and |a| = |b| = 1/3  (four vertices); and
--   (D) the endpoint flip (ε₁,ε₅) ↦ (−ε₁,−ε₅) changes an atom's mass
--       by a term proportional to a(ε₁+ε₅), hence by ZERO whenever
--       ε₁ = −ε₅; and at the vertex EXACTLY FOUR of the ten zero atoms
--       have their flip image also of mass zero, all with ε₁ = −ε₅.
--
-- This module contains the finite, kernel-checkable content of both,
-- re-derived independently of the packet, plus the hand proofs of the
-- two continuous steps as comments.  Every `refl` below is a finite
-- exhaustive verification the typechecker normalises — the certificate
-- class CLAUDE.md (absent from this repository) admits as proof.  Rationals are cleared to integers
-- exactly as in Window5Walsh (m96 = 96·μ at the vertex).
--
------------------------------------------------------------------------
-- RE-DERIVATION OF (D), from scratch.
--
-- For any rationals (a,b,c) and ε ∈ {±1}⁵,
--
--   32·μ_{a,b,c}(ε) = 1 + a·A(ε) + b·B(ε) + c·C(ε),      where
--   A(ε) = ε₁ε₂ε₃ε₄ + ε₂ε₃ε₄ε₅ = ε₂ε₃ε₄·(ε₁+ε₅),
--   B(ε) = ε₁ε₃ε₄ε₅ + ε₁ε₂ε₃ε₅ = ε₁ε₃ε₅·(ε₂+ε₄),
--   C(ε) = ε₁ε₂ε₄ε₅.
--
-- Under the endpoint flip F : ε ↦ (−ε₁, ε₂, ε₃, ε₄, −ε₅):
--   A(Fε) = ε₂ε₃ε₄·(−ε₁−ε₅)      = −A(ε)   (the sum flips sign),
--   B(Fε) = (−ε₁)ε₃(−ε₅)·(ε₂+ε₄) =  B(ε)   (ε₁ε₅ is F-invariant),
--   C(Fε) = (−ε₁)ε₂ε₄(−ε₅)       =  C(ε).
-- Hence, exactly,
--
--   32·(μ(Fε) − μ(ε)) = −2a·A(ε) = −2a·ε₂ε₃ε₄·(ε₁+ε₅),
--
-- which is proportional to a(ε₁+ε₅) as clause (D) states, and vanishes
-- (for every a ≠ 0) precisely when ε₁ = −ε₅.  The published step
-- asserts nonzero a makes F change every zero probability; the identity
-- shows the assertion is false on the half of the cube where
-- ε₁ = −ε₅.  All of this is finite: §2 checks the three coefficient
-- transformations, the factorization of A, and A(ε) = 0 ⇔ ε₁ = −ε₅,
-- over all 32 patterns, so the displayed identity holds for ALL
-- (a,b,c), not only at the vertex.
--
-- At the vertex the ten zero atoms are (§3, checked complete):
--   class B (ε₁ε₅ = +1, ε₂ε₄ = −1): (ε₁, ε₂, ε₁, −ε₂, ε₁), 4 atoms;
--   class C (ε₁ε₅ = −1, ε₂ε₄ = +1): (ε₁, ε₂, ε₂,  ε₂, −ε₁), 4 atoms;
--   class A (ε₁ε₅ = +1, ε₂ε₄ = +1): (ε₁, ε₁, −ε₁, ε₁, ε₁), 2 atoms.
-- Exactly the four class-C atoms have ε₁ = −ε₅, so exactly those four
-- have flip image of mass zero — in fact F permutes them in two
-- 2-orbits, (+,+,+,+,−) ↔ (−,+,+,+,+) and (+,−,−,−,−) ↔ (−,−,−,−,+).
-- The other six zero atoms have ε₁ = ε₅ and their images all have mass
-- 4/96 (§5: 0 − 2·A with A = −2 at each of the six).  This CONFIRMS
-- the packet's (D): exactly 4, all with ε₁ = −ε₅.
--
------------------------------------------------------------------------
-- RE-DERIVATION OF (B), from scratch.  (Continuous; the kernel checks
-- its finite skeleton, §4 and §6, not the quantifier over (a,b,c).)
--
-- With s = ε₁ε₅, t = ε₂ε₄ the 32 atoms fall into four classes; on each,
-- since ε₄ = tε₂ and ε₅ = sε₁,
--   class A (s,t = +,+): 32μ = 1 + c + 2a·x + 2b·y,
--                        x = ε₁ε₃, y = ε₂ε₃; each (x,y) hit by 2 ε's;
--   class B (s,t = +,−): 32μ = 1 − c + 2a·x, x = −ε₁ε₃; each x by 4;
--   class C (s,t = −,+): 32μ = 1 − c + 2b·y, y = −ε₂ε₃; each y by 4;
--   class D (s,t = −,−): 32μ = 1 + c, all 8.
-- (This is Window5Walsh §6's kernel-checked nine-form table.)
-- Nonnegativity of all 32 is therefore equivalent to
--   −1 ≤ c ≤ 1,  2|a| ≤ 1−c,  2|b| ≤ 1−c,  2(|a|+|b|) ≤ 1+c,
-- which is the packet's clause (A).  Now assume |c| < 1.
--   * D: 1 + c > 0 — no zeros, ever.
--   * B: if a = 0 the value is 1 − c > 0; if a ≠ 0 only the sign
--     x = −sgn(a) can give 0, and does iff 2|a| = 1−c: 0 or 4 zeros.
--   * C: symmetrically, 0 or 4 zeros, 4 iff 2|b| = 1−c (forces b ≠ 0).
--   * A: 1 + c > 0.  Two distinct (x,y), (x',y') both zero would give
--       x = x', y ≠ y' ⇒ 4|b| = 0;  x ≠ x', y = y' ⇒ 4|a| = 0;
--       x = −x', y = −y' ⇒ adding the two equations, 2(1+c) = 0.
--     So: a,b both ≠ 0 ⇒ at most ONE (x,y) zero ⇒ ≤ 2 atoms;
--         exactly one of a,b zero ⇒ ≤ one value of the other sign
--         ⇒ ≤ 4 atoms;  a = b = 0 ⇒ none.
-- Counting: if B and C are both at equality then a,b ≠ 0 and
-- 2|a| = 2|b| = 1−c, so class A contributes ≤ 2 and the A-facet
-- 2(|a|+|b|) ≤ 1+c reads 2(1−c) ≤ 1+c, i.e. c ≥ 1/3.  An A-zero needs
-- equality 2(|a|+|b|) = 1+c, i.e. c = 1/3 — then |a| = |b| = 1/3 and
-- the unique zero pair (x,y) = (−sgn a, −sgn b) contributes 2 atoms:
-- total 4 + 4 + 2 = 10.  For c > 1/3 the total is 8.  If exactly one
-- of B, C is at equality the total is ≤ 4 + 4 = 8 (the A-count of 4
-- requires the OTHER coefficient to vanish; e.g. a = ±1/2, b = 0,
-- c = 0 attains 8 — checked at §7's m64).  If neither, ≤ 4.  Hence at
-- most TEN, with equality iff c = 1/3, |a| = |b| = 1/3.  ∎  (Agrees
--
-- What the kernel checks of (B):  the nine-form class table is already
-- Window5Walsh §6; here §4 pins the per-class zero counts (2,4,4,0) at
-- ALL FOUR claimed equality vertices, and §7 checks three witness
-- points of the strict-inequality side: (1/4,1/4,1/2) — the B,C-facet
-- edge with c > 1/3 — has 8 zeros; (1/2,0,0) has 8; the interior point
-- (1/6,1/6,1/3) has 0.  The universally quantified "at most ten for
-- ALL |c| < 1" itself is the hand proof above.
--
------------------------------------------------------------------------

module R0021FlipOrbit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; _or_ ; not)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; _+_ ; _·_ ; -_)

open import Window5Walsh
  -- Sg, P, M, _*_, val, Pat, allPats, sgs, m96, m96±, masses,
  -- p1234 … p1245, formOf, signed, eqᵇ, eqℤ, nonNegℤ, posℤ, eqPat,
  -- allB, anyB, countB, sumℤ, atom, flipped — all kernel-checked there.

------------------------------------------------------------------------
-- §1  The flips, and small Boolean plumbing
------------------------------------------------------------------------

negS : Sg → Sg
negS P = M
negS M = P

eqSg : Sg → Sg → Bool
eqSg P P = true
eqSg M M = true
eqSg _ _ = false

eqBool : Bool → Bool → Bool
eqBool true  true  = true
eqBool false false = true
eqBool _     _     = false

impliesB : Bool → Bool → Bool
impliesB b w = not b or w

-- the audited endpoint flip, the note's "analogous middle flip", and a
-- deliberately WRONG flip (one endpoint only) used as a control
flipEnds midFlip fakeFlip : Pat → Pat
flipEnds (e1 , e2 , e3 , e4 , e5) = (negS e1 , e2 , e3 , e4 , negS e5)
midFlip  (e1 , e2 , e3 , e4 , e5) = (e1 , negS e2 , e3 , negS e4 , e5)
fakeFlip (e1 , e2 , e3 , e4 , e5) = (negS e1 , e2 , e3 , e4 , e5)

-- structural observables of a pattern
endProd midProd mid3 : Pat → Sg
endProd (e1 , e2 , e3 , e4 , e5) = e1 * e5
midProd (e1 , e2 , e3 , e4 , e5) = e2 * e4
mid3    (e1 , e2 , e3 , e4 , e5) = e2 * (e3 * e4)

endSum : Pat → ℤ
endSum (e1 , e2 , e3 , e4 , e5) = val e1 + val e5

oppEnds oppMid : Pat → Bool          -- ε₁ = −ε₅ ; ε₂ = −ε₄
oppEnds p = eqSg (endProd p) M
oppMid  p = eqSg (midProd p) M

-- the three affine coefficients  32μ = 1 + a·coefA + b·coefB + c·coefC
-- (formOf is Window5Walsh's kernel-checked coefficient map)
coefA coefB coefC : Pat → ℤ
coefA p = fst (formOf p)
coefB p = fst (snd (formOf p))
coefC p = snd (snd (formOf p))

-- flipEnds is an involution: its orbits are pairs
flipInvolution : allB allPats (λ p → eqPat (flipEnds (flipEnds p)) p) ≡ true
flipInvolution = refl

------------------------------------------------------------------------
-- §2  CLAUSE (D), THE IDENTITY — valid for ALL (a,b,c)
--
-- coefA(Fε) = −coefA(ε), coefB and coefC are F-invariant, and
-- coefA(ε) = ε₂ε₃ε₄·(ε₁+ε₅).  Since μ is affine in (a,b,c) with these
-- coefficient functions, this IS the identity
--     32(μ_{a,b,c}(Fε) − μ_{a,b,c}(ε)) = −2a·ε₂ε₃ε₄·(ε₁+ε₅)
-- for every (a,b,c), finitely verified.  Its vanishing locus in ε (for
-- a ≠ 0) is exactly ε₁ = −ε₅.
------------------------------------------------------------------------

flipNegatesA : allB allPats (λ p → eqℤ (coefA (flipEnds p)) (- coefA p)) ≡ true
flipNegatesA = refl

flipKeepsB : allB allPats (λ p → eqℤ (coefB (flipEnds p)) (coefB p)) ≡ true
flipKeepsB = refl

flipKeepsC : allB allPats (λ p → eqℤ (coefC (flipEnds p)) (coefC p)) ≡ true
flipKeepsC = refl

-- the factorization  coefA(ε) = ε₂ε₃ε₄·(ε₁+ε₅)
coefAFactored : allB allPats (λ p → eqℤ (coefA p) (signed (endSum p) (mid3 p)))
              ≡ true
coefAFactored = refl

-- coefA vanishes exactly on the opposite-endpoint half of the cube
coefAZeroIffOpp : allB allPats (λ p → eqBool (eqℤ (coefA p) (pos 0)) (oppEnds p))
                ≡ true
coefAZeroIffOpp = refl

-- and the mass at the vertex decomposes through the same coefficients:
-- m96 = 3 + coefA + coefB + coefC  (96μ = 3 + 3a·A + 3b·B + 3c·C at
-- a = b = c = 1/3), so the general identity specialises on the nose:
formDecomposes : allB allPats
                   (λ p → eqℤ (m96 p) (pos 3 + (coefA p + (coefB p + coefC p))))
               ≡ true
formDecomposes = refl

-- the specialised flip law in m96 units: m96(Fε) = m96(ε) − 2·coefA(ε)
flipDeltaVertex : allB allPats
                    (λ p → eqℤ (m96 (flipEnds p)) (m96 p + (- (pos 2 · coefA p))))
                ≡ true
flipDeltaVertex = refl

------------------------------------------------------------------------
-- §3  The ten zero atoms at (1/3,1/3,1/3), NAMED and proven complete
--
-- Window5Walsh's `zeroCount` says there are exactly ten; here they are.
-- Order: four class-B, four class-C, two class-A (comment block above).
------------------------------------------------------------------------

zeroAtoms : List Pat
zeroAtoms =
  -- class B:  (ε₁, ε₂, ε₁, −ε₂, ε₁),  ε₁ε₅ = +1, ε₂ε₄ = −1
    (P , P , P , M , P)
  ∷ (P , M , P , P , P)
  ∷ (M , P , M , M , M)
  ∷ (M , M , M , P , M)
  -- class C:  (ε₁, ε₂, ε₂, ε₂, −ε₁),  ε₁ε₅ = −1, ε₂ε₄ = +1
  ∷ (P , P , P , P , M)
  ∷ (P , M , M , M , M)
  ∷ (M , P , P , P , P)
  ∷ (M , M , M , M , P)
  -- class A:  (ε₁, ε₁, −ε₁, ε₁, ε₁),  ε₁ε₅ = +1, ε₂ε₄ = +1
  ∷ (P , P , M , P , P)
  ∷ (M , M , P , M , M)
  ∷ []

zeroAtomsAreZero : allB zeroAtoms (λ p → eqℤ (m96 p) (pos 0)) ≡ true
zeroAtomsAreZero = refl

zeroAtomsLength : countB zeroAtoms (λ _ → true) ≡ 10
zeroAtomsLength = refl

zeroAtomsDistinct : countB zeroAtoms (λ p → eqᵇ (countB zeroAtoms (eqPat p)) 1)
                  ≡ 10
zeroAtomsDistinct = refl

-- every zero of m96 is in the list: with the three facts above (and
-- Window5Walsh's zeroCount = 10) the list IS the zero set
zeroAtomsComplete : allB allPats
                      (λ p → impliesB (eqℤ (m96 p) (pos 0))
                                      (anyB zeroAtoms (eqPat p)))
                  ≡ true
zeroAtomsComplete = refl

------------------------------------------------------------------------
-- §4  Per-class zero counts (2,4,4,0) — at ALL FOUR equality vertices
--
-- This is the finite skeleton of clause (B)'s equality case: at each of
-- the four claimed maximisers (σa/3, σb/3, 1/3) the ten zeros split as
-- class A: 2, class B: 4, class C: 4, class D: 0, exactly as the hand
-- proof requires.  (m96± σa σb is Window5Walsh's vertex mass.)
------------------------------------------------------------------------

inClass : Sg → Sg → Pat → Bool       -- σs = ε₁ε₅ , σt = ε₂ε₄
inClass σs σt p = eqSg (endProd p) σs and eqSg (midProd p) σt

vertexClassZeros : allB sgs (λ σa → allB sgs (λ σb →
       eqᵇ (countB allPats (λ p → inClass P P p and eqℤ (m96± σa σb p) (pos 0))) 2
   and (eqᵇ (countB allPats (λ p → inClass P M p and eqℤ (m96± σa σb p) (pos 0))) 4
   and (eqᵇ (countB allPats (λ p → inClass M P p and eqℤ (m96± σa σb p) (pos 0))) 4
   and  eqᵇ (countB allPats (λ p → inClass M M p and eqℤ (m96± σa σb p) (pos 0))) 0))))
                 ≡ true
vertexClassZeros = refl

------------------------------------------------------------------------
-- §5  CLAUSE (D), THE ENUMERATION — exactly four flip-fixed zeros
------------------------------------------------------------------------

-- headline: of the ten zero atoms, EXACTLY FOUR have flip image of
-- mass zero …
flipFixedCount : countB zeroAtoms (λ p → eqℤ (m96 (flipEnds p)) (pos 0)) ≡ 4
flipFixedCount = refl

-- … and a zero atom's flip image is zero IFF its endpoints are
-- opposite (ε₁ = −ε₅), atom by atom — the packet's "all with ε₁ = −ε₅"
flipFixedIffOpp : allB zeroAtoms
                    (λ p → eqBool (eqℤ (m96 (flipEnds p)) (pos 0)) (oppEnds p))
                ≡ true
flipFixedIffOpp = refl

-- the four, by name: the class-C atoms
fixC1 fixC2 fixC3 fixC4 : Pat
fixC1 = (P , P , P , P , M)
fixC2 = (M , P , P , P , P)
fixC3 = (P , M , M , M , M)
fixC4 = (M , M , M , M , P)

fixedFour : List Pat
fixedFour = fixC1 ∷ fixC2 ∷ fixC3 ∷ fixC4 ∷ []

fixedFourZeroBothWays : allB fixedFour
                          (λ p → eqℤ (m96 p) (pos 0)
                                 and eqℤ (m96 (flipEnds p)) (pos 0))
                      ≡ true
fixedFourZeroBothWays = refl

fixedFourOpp : allB fixedFour oppEnds ≡ true
fixedFourOpp = refl

-- they are EXACTLY the flip-fixed zeros …
fixedFourComplete : allB zeroAtoms
                      (λ p → eqBool (eqℤ (m96 (flipEnds p)) (pos 0))
                                    (anyB fixedFour (eqPat p)))
                  ≡ true
fixedFourComplete = refl

-- … and the flip pairs them into two 2-orbits
fixedPair12 : flipEnds fixC1 ≡ fixC2
fixedPair12 = refl

fixedPair34 : flipEnds fixC3 ≡ fixC4
fixedPair34 = refl

-- tie-in: Window5Walsh's single broken-flip witness is the first pair
atomIsFixC1 : atom ≡ fixC1
atomIsFixC1 = refl

flippedIsFixC2 : flipEnds atom ≡ flipped
flippedIsFixC2 = refl

-- the six zero atoms with ε₁ = ε₅ all move to mass 4/96 — an atom's
-- flip image has mass 4 exactly when its endpoints are EQUAL
sixMovedToFour : allB zeroAtoms
                   (λ p → eqBool (not (oppEnds p))
                                 (eqℤ (m96 (flipEnds p)) (pos 4)))
               ≡ true
sixMovedToFour = refl

-- the same enumeration holds at ALL FOUR vertices: four flip-fixed
-- zeros each, always with ε₁ = −ε₅
vertexFlipFixedCount : allB sgs (λ σa → allB sgs (λ σb →
    eqᵇ (countB allPats
           (λ p → eqℤ (m96± σa σb p) (pos 0)
                  and eqℤ (m96± σa σb (flipEnds p)) (pos 0)))
        4))
                     ≡ true
vertexFlipFixedCount = refl

vertexFlipFixedOpp : allB sgs (λ σa → allB sgs (λ σb →
    allB allPats
      (λ p → impliesB (eqℤ (m96± σa σb p) (pos 0)
                       and eqℤ (m96± σa σb (flipEnds p)) (pos 0))
                      (oppEnds p))))
                   ≡ true
vertexFlipFixedOpp = refl

------------------------------------------------------------------------
-- §6  The middle flip (ε₂,ε₄) — the note's §4 addendum
--
-- Same mechanism, b-slot: G : ε ↦ (ε₁,−ε₂,ε₃,−ε₄,ε₅) negates coefB and
-- keeps coefA, coefC, so 32(μ(Gε) − μ(ε)) = −2b·ε₁ε₃ε₅·(ε₂+ε₄), zero
-- iff ε₂ = −ε₄.  At the vertex it fixes exactly the four class-B zero
-- atoms.
------------------------------------------------------------------------

midNegatesB : allB allPats (λ p → eqℤ (coefB (midFlip p)) (- coefB p)) ≡ true
midNegatesB = refl

midKeepsA : allB allPats (λ p → eqℤ (coefA (midFlip p)) (coefA p)) ≡ true
midKeepsA = refl

midKeepsC : allB allPats (λ p → eqℤ (coefC (midFlip p)) (coefC p)) ≡ true
midKeepsC = refl

midFixedCount : countB zeroAtoms (λ p → eqℤ (m96 (midFlip p)) (pos 0)) ≡ 4
midFixedCount = refl

midFixedIffOppMid : allB zeroAtoms
                      (λ p → eqBool (eqℤ (m96 (midFlip p)) (pos 0)) (oppMid p))
                  ≡ true
midFixedIffOppMid = refl

------------------------------------------------------------------------
-- §7  Witness points for clause (B)'s strict side
--
-- Three exact rational points, cleared to integers, showing the count
-- DROPS away from the four vertices — the kernel-checkable face of the
-- classification "ten only at c = 1/3, |a| = |b| = 1/3".
--
--   (1/4,1/4,1/2): both B,C facets tight but c > 1/3 → 8 zeros
--                  (the hand proof's "c > 1/3 gives eight" branch);
--   (1/2,0,0):     B facet and A facet tight, b = 0 → 8 zeros
--                  (the "one facet + degenerate A" branch);
--   (1/6,1/6,1/3): strict interior → 0 zeros.
------------------------------------------------------------------------

-- 128·μ at (1/4,1/4,1/2)
m128 : Pat → ℤ
m128 p = pos 4 + (val (p1234 p) + (val (p2345 p)
       + (val (p1345 p) + (val (p1235 p) + (pos 2 · val (p1245 p))))))

edgePointOK : (allB (map m128 allPats) nonNegℤ ≡ true)
            × ( (sumℤ (map m128 allPats) ≡ pos 128)
              × (countB (map m128 allPats) (λ z → eqℤ z (pos 0)) ≡ 8) )
edgePointOK = refl , refl , refl

-- 64·μ at (1/2,0,0)
m64 : Pat → ℤ
m64 p = pos 2 + (val (p1234 p) + val (p2345 p))

halfPointOK : (allB (map m64 allPats) nonNegℤ ≡ true)
            × ( (sumℤ (map m64 allPats) ≡ pos 64)
              × (countB (map m64 allPats) (λ z → eqℤ z (pos 0)) ≡ 8) )
halfPointOK = refl , refl , refl

-- 192·μ at (1/6,1/6,1/3): strictly positive everywhere
m192 : Pat → ℤ
m192 p = pos 6 + (val (p1234 p) + (val (p2345 p)
       + (val (p1345 p) + (val (p1235 p) + (pos 2 · val (p1245 p))))))

interiorPointOK : (allB (map m192 allPats) posℤ ≡ true)
                × (sumℤ (map m192 allPats) ≡ pos 192)
interiorPointOK = refl , refl

------------------------------------------------------------------------
-- §8  PLANTED-FALSE CONTROLS  (house style: a check that cannot fail
--     is vacuous, so each headline check gets a falsifier)
------------------------------------------------------------------------

-- flipping ONE endpoint is not the audited symmetry: it does NOT negate
-- coefA (indeed never does), and does NOT preserve coefB
controlFakeFlipA : allB allPats (λ p → eqℤ (coefA (fakeFlip p)) (- coefA p))
                 ≡ false
controlFakeFlipA = refl

controlFakeFlipB : allB allPats (λ p → eqℤ (coefB (fakeFlip p)) (coefB p))
                 ≡ false
controlFakeFlipB = refl

-- the PRINTED step needs the flip-fixed zero count to be 0 ("each flip
-- changes a zero probability") — it is 4, not 0:
controlPrintedStepFails :
  eqᵇ (countB zeroAtoms (λ p → eqℤ (m96 (flipEnds p)) (pos 0))) 0 ≡ false
controlPrintedStepFails = refl

-- and the flip does not fix ALL the zeros either (the countermodel is
-- not the degenerate claim that F preserves the whole zero set):
controlNotAllFixed :
  eqᵇ (countB zeroAtoms (λ p → eqℤ (m96 (flipEnds p)) (pos 0))) 10 ≡ false
controlNotAllFixed = refl
