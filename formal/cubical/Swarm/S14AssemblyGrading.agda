{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S14AssemblyGrading
--
-- A TRANSLATION between two vocabularies:
--
--   (a) ryabhaa's vall, typed in `KuttakaValli` as a monoid
--       morphism  replay : List ℤ → M₂(ℤ)  with  det ∘ replay = ±1;
--
--   (b) the Smith/Hermite assembly of `machinery/bijective_smith_assembly.py` (absent from this repository),
--       whose bijection  Φ(L) = (c , L/c)  splits an index-m sublattice
--       of ℤ² into its content c (first Smith invariant, c² ∣ m) and a
--       primitive lattice of index n = m/c², yielding
--       σ₁(m) = Σ_{c²∣m} ψ(m/c²).
--
-- The bridge is one free monoid.  Extend the vall alphabet from the
-- single division letter to three:
--
--     pulv q  ↦  L q       = ( q 1 / 1 0 )   det = −1
--     scal c  ↦  dia c c   = ( c 0 / 0 c )   det = c·c
--     heck n  ↦  dia 1 n   = ( 1 0 / 0 n )   det = n
--
-- and evaluate a word by the same fold.  `detRun` says the evaluator's
-- determinant is a MONOID MORPHISM to (ℤ,·), and `split` says that
-- morphism factors through three independent characters of the free
-- monoid:
--
--     det (run w)  ≡  eps w · ((cont w · cont w) · prim w),   eps w² ≡ 1.
--
-- That is the Smith assembly, as a grading of syntax: the index of
-- anything the extended pulverizer builds is (sign)·(content)²·(primitive).
--
-- THE OBSTRUCTION.  `val = map pulv` embeds the classical vall, and
-- `pulverizerContentless` shows  cont (val v) ≡ 1  and  prim (val v) ≡ 1
-- for EVERY vall v, however long.  ryabhaa's algorithm lives entirely
-- in the eps-graded part; it can produce neither the c² nor the n of the
-- assembly.  Whatever content a lattice has must be supplied by a letter
-- outside the trace calculus.  `assembleSmith` supplies it exactly:
-- scal c ∷ heck n ∷ [] evaluates to the diagonal matrix dia c (c · n),
-- i.e. the Smith normal form with invariants (c , c·n) — Φ⁻¹(c , n) at
-- the diagonal.
--
-- WHY THIS IS THE POINT WHERE THE TWO LENSES DISAGREE.
-- Riemann's lens reads the assembly as an Euler-product factorization,
--     Σ σ₁(m) m^{-s} = ζ(s)ζ(s−1) = ζ(2s) · ( ζ(s)ζ(s−1)/ζ(2s) ),
-- the ζ(2s) being the `scal` series Σ_c c^{−2s} and the quotient the
-- `heck` series Σ ψ(n) n^{−s}.  That factorization is BLIND to `pulv`:
-- the unimodular direction contributes 1 to every Dirichlet series and
-- so does not appear at all — yet it is the whole of Āryabhaṭa and the
-- whole of KuttakaValli.agda.  Narayana's lens (generate the objects by
-- a rule) sees only `pulv`, because that is the letter with a recurrence.
-- Neither lens alone sees the alphabet.  This module is the object on
-- which both are visible: three characters of one free monoid, one of
-- which the pulverizer generates and two of which it provably cannot.
------------------------------------------------------------------------

module Swarm.S14AssemblyGrading where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

open import Gamma0Partner using (R ; M ; mul ; dia)
open import M2Unimodular using (det ; idm ; detMul)
open import Gamma0Freeness using (mulAssoc)
open import KuttakaValli using (Valli ; L ; replay ; sgn ; detL ; detReplay ; mulIdL)

open CommRingStr (ℤCommRing .snd)

-- ------------------------------------------------------------------
-- the alphabet
-- ------------------------------------------------------------------

data Step : Type where
  pulv : R → Step        -- one division step of the kuṭṭaka
  scal : R → Step        -- one unit of content   (the c² of the assembly)
  heck : R → Step        -- one primitive index   (the ψ-part)

Word : Type
Word = List Step

ev : Step → M
ev (pulv q) = L q
ev (scal c) = dia c c
ev (heck n) = dia 1r n

run : Word → M
run [] = idm
run (s ∷ w) = mul (ev s) (run w)

-- concatenation is multiplication (the vall law, on the wider alphabet)

runHom : (v w : Word) → run (v ++ w) ≡ mul (run v) (run w)
runHom [] w = sym (mulIdL (run w))
runHom (s ∷ v) w =
  cong (mul (ev s)) (runHom v w)
  ∙ sym (mulAssoc (ev s) (run v) (run w))

-- ------------------------------------------------------------------
-- the index of a word
-- ------------------------------------------------------------------

private
  diaDet : (x y : R) → x · y - 0r · 0r ≡ x · y
  diaDet _ _ = solve! ℤCommRing

detDia : (x y : R) → det (dia x y) ≡ x · y
detDia x y = diaDet x y

wt : Word → R
wt [] = 1r
wt (pulv q ∷ w) = (- 1r) · wt w
wt (scal c ∷ w) = (c · c) · wt w
wt (heck n ∷ w) = n · wt w

detRun : (w : Word) → det (run w) ≡ wt w
detRun [] = refl
detRun (pulv q ∷ w) =
  detMul (L q) (run w) ∙ cong₂ _·_ (detL q) (detRun w)
detRun (scal c ∷ w) =
  detMul (dia c c) (run w) ∙ cong₂ _·_ (detDia c c) (detRun w)
detRun (heck n ∷ w) =
  detMul (dia 1r n) (run w)
  ∙ cong₂ _·_ (detDia 1r n ∙ ·IdL n) (detRun w)

-- ------------------------------------------------------------------
-- the three characters
-- ------------------------------------------------------------------

eps : Word → R              -- orientation: (−1)^{#pulv}
eps [] = 1r
eps (pulv _ ∷ w) = (- 1r) · eps w
eps (scal _ ∷ w) = eps w
eps (heck _ ∷ w) = eps w

cont : Word → R             -- content: the first Smith invariant
cont [] = 1r
cont (pulv _ ∷ w) = cont w
cont (scal c ∷ w) = c · cont w
cont (heck _ ∷ w) = cont w

prim : Word → R             -- primitive (cyclic) index
prim [] = 1r
prim (pulv _ ∷ w) = prim w
prim (scal _ ∷ w) = prim w
prim (heck n ∷ w) = n · prim w

private
  oneCube : (1r · 1r) · 1r ≡ 1r
  oneCube = ·IdR (1r · 1r) ∙ ·IdR 1r

  unit1 : (x : R) → x ≡ x · ((1r · 1r) · 1r)
  unit1 x = sym (cong (x ·_) oneCube ∙ ·IdR x)

  lemP : (e c n : R) → (- 1r) · (e · ((c · c) · n)) ≡ ((- 1r) · e) · ((c · c) · n)
  lemP _ _ _ = solve! ℤCommRing

  lemS : (c e d n : R)
       → (c · c) · (e · ((d · d) · n)) ≡ e · (((c · d) · (c · d)) · n)
  lemS _ _ _ _ = solve! ℤCommRing

  lemH : (n e c m : R) → n · (e · ((c · c) · m)) ≡ e · ((c · c) · (n · m))
  lemH _ _ _ _ = solve! ℤCommRing

split : (w : Word) → wt w ≡ eps w · ((cont w · cont w) · prim w)
split [] = unit1 1r
split (pulv q ∷ w) =
  cong ((- 1r) ·_) (split w) ∙ lemP (eps w) (cont w) (prim w)
split (scal c ∷ w) =
  cong ((c · c) ·_) (split w) ∙ lemS c (eps w) (cont w) (prim w)
split (heck n ∷ w) =
  cong (n ·_) (split w) ∙ lemH n (eps w) (cont w) (prim w)

private
  negSq : (e : R) → ((- 1r) · e) · ((- 1r) · e) ≡ e · e
  negSq _ = solve! ℤCommRing

epsSq : (w : Word) → eps w · eps w ≡ 1r
epsSq [] = ·IdR 1r
epsSq (pulv q ∷ w) = negSq (eps w) ∙ epsSq w
epsSq (scal c ∷ w) = epsSq w
epsSq (heck n ∷ w) = epsSq w

-- MAIN THEOREM.  The index of an assembled lattice is
-- (sign) · (content)² · (primitive index), with the sign a unit.

assemblyGrading : (w : Word)
  → (det (run w) ≡ eps w · ((cont w · cont w) · prim w))
  × (eps w · eps w ≡ 1r)
assemblyGrading w = (detRun w ∙ split w) , epsSq w

-- ------------------------------------------------------------------
-- the obstruction: the classical vall is contentless
-- ------------------------------------------------------------------

val : Valli → Word
val = map pulv

embed : (v : Valli) → run (val v) ≡ replay v
embed [] = refl
embed (q ∷ v) = cong (mul (L q)) (embed v)

epsVal : (v : Valli) → eps (val v) ≡ sgn v
epsVal [] = refl
epsVal (q ∷ v) = cong ((- 1r) ·_) (epsVal v)

-- No vall, of any length, contributes to either arithmetic character.

pulverizerContentless : (v : Valli)
  → (cont (val v) ≡ 1r) × (prim (val v) ≡ 1r)
pulverizerContentless [] = refl , refl
pulverizerContentless (q ∷ v) = pulverizerContentless v

-- so its index is exactly its orientation, and its grading collapses

pulverizerIndex : (v : Valli) → det (replay v) ≡ eps (val v)
pulverizerIndex v = detReplay v ∙ sym (epsVal v)

pulverizerGradingCollapse : (v : Valli)
  → det (replay v) ≡ eps (val v) · ((1r · 1r) · 1r)
pulverizerGradingCollapse v =
  pulverizerIndex v ∙ unit1 (eps (val v))

-- ------------------------------------------------------------------
-- completeness of the wider alphabet: Φ⁻¹ at the diagonal
-- ------------------------------------------------------------------

assemble : R → R → Word
assemble c n = scal c ∷ heck n ∷ []

private
  entA : (x y : R) → x · y + 0r · 0r ≡ x · y
  entA _ _ = solve! ℤCommRing
  entB : (x y : R) → x · 0r + 0r · y ≡ 0r
  entB _ _ = solve! ℤCommRing
  entC : (x y : R) → 0r · x + y · 0r ≡ 0r
  entC _ _ = solve! ℤCommRing
  entD : (x y : R) → 0r · 0r + x · y ≡ x · y
  entD _ _ = solve! ℤCommRing

  innerDia : (n : R) → mul (dia 1r n) idm ≡ dia 1r n
  innerDia n i =
    ( (entA 1r 1r ∙ ·IdR 1r) i
    , entB 1r 1r i
    , entC 1r n i
    , (entD n 1r ∙ ·IdR n) i )

  outerDia : (c n : R) → mul (dia c c) (dia 1r n) ≡ dia c (c · n)
  outerDia c n i =
    ( (entA c 1r ∙ ·IdR c) i
    , entB c n i
    , entC 1r c i
    , entD c n i )

-- The word scal c ∷ heck n ∷ [] evaluates to the Smith normal form
-- diag(c , c·n): first invariant c, second c·n, index c²n.  This is
-- Φ⁻¹(c , n) on the diagonal representative of the stratum.

assembleSmith : (c n : R) → run (assemble c n) ≡ dia c (c · n)
assembleSmith c n =
  cong (mul (dia c c)) (innerDia n) ∙ outerDia c n

assembleCharacters : (c n : R)
  → (eps (assemble c n) ≡ 1r)
  × (cont (assemble c n) ≡ c)
  × (prim (assemble c n) ≡ n)
assembleCharacters c n = refl , ·IdR c , ·IdR n

private
  idxLem : (c n : R) → (c · c) · (n · 1r) ≡ (c · c) · n
  idxLem c n = cong ((c · c) ·_) (·IdR n)

assembleIndex : (c n : R) → det (run (assemble c n)) ≡ (c · c) · n
assembleIndex c n = detRun (assemble c n) ∙ idxLem c n

-- Prefixing any vall to an assembly changes only the orientation:
-- the pulverizer can normalize a basis but cannot move it between
-- strata of the Smith assembly.

strataInvariance : (v : Valli) (c n : R)
  → (cont (val v ++ assemble c n) ≡ cont (assemble c n))
  × (prim (val v ++ assemble c n) ≡ prim (assemble c n))
strataInvariance [] c n = refl , refl
strataInvariance (q ∷ v) c n = strataInvariance v c n
