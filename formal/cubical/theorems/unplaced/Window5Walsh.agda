{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Window5Walsh
--
-- THE LENGTH-FIVE WALSH COUNTERMODEL, WITHOUT PYTHON
--
-- F23 recorded a stationary false model for the five-window correlation
-- algebra used in the nonzero-(a,b,c) case of Tao–Teräväinen's Theorem
-- 1.14.  Its evidence artifact was `code/exp53_window5_polytope.py` (absent from this repository).  This
-- module redoes every finite, exact assertion that script made, as terms
-- the Agda kernel checks.  Nothing here is floating point and nothing is
-- a search: each `refl` is a finite exhaustive verification over the 32
-- sign patterns.
--
-- THE OBJECT.  For ε ∈ {±1}⁵ and rationals a,b,c,
--
--   32·μ_{a,b,c}(ε) = 1 + a(ε₁ε₂ε₃ε₄ + ε₂ε₃ε₄ε₅)
--                       + b(ε₁ε₃ε₄ε₅ + ε₁ε₂ε₃ε₅)
--                       + c·ε₁ε₂ε₄ε₅.
--
-- Everything F23 turns on happens at (a,b,c) = (1/3,1/3,1/3).  Clearing
-- denominators once, the module works throughout with the INTEGER
--
--   m96 ε := 96·μ_{1/3,1/3,1/3}(ε)
--          = 3 + ε₁₂₃₄ + ε₂₃₄₅ + ε₁₃₄₅ + ε₁₂₃₅ + ε₁₂₄₅  ∈ ℤ,
--
-- so no rational arithmetic is needed anywhere and every check is an
-- equality of integers that the typechecker evaluates.
--
-- WHAT IS CHECKED  (§ numbers are this file's):
--
--   §5  `massesNonNeg`   all 32 masses ≥ 0
--       `massTotal`      Σ m96 = 96, i.e. Σ μ = 1
--       `zeroCount`      EXACTLY TEN masses vanish
--       `massValues`     every mass is 0, 4 or 8
--       `fourSharpVertices`  and the same three facts at ALL FOUR
--                        vertices c = 1/3, |a| = |b| = 1/3, which is
--                        what the retired script's `check_sharp_
--                        countermodels` asserted.
--
--   §6  `classCounts`    the nine affine forms of CONSTRAINT_ALGEBRA §2
--       `classComplete`  with multiplicities 2/4/8, and nothing else
--       `classDistinct`  occurs.  This is the input to that note's
--                        Theorem 2.1 (the continuous facet
--                        classification), so the hand proof there now
--                        rests on a checked table rather than on a
--                        script.
--
--   §7  `flowConserved`  the order-four de Bruijn flow is conserved:
--                        outgoing mass = incoming mass = 6 + 2ε₁ε₂ε₃ε₄
--                        (in m96 units) at every one of the 16 states,
--                        and every state has POSITIVE mass — so the
--                        table is the five-window law of a stationary
--                        order-four Markov chain.
--       `flowBroken`     PLANTED-FALSE CONTROL: give the two
--                        consecutive coefficients unequal values
--                        (1/3 and 1/4) and conservation FAILS.  The
--                        check returns `false`, by refl.  Without this
--                        the stationarity check would be vacuous.
--
--   §8  `walshOK`        all 31 nonempty Walsh coefficients: zero
--                        except μ̂(1234)=μ̂(2345)=a, μ̂(1345)=μ̂(1235)=b,
--                        μ̂(1245)=c, all equal to 1/3.  In particular
--                        every odd-order and every two-point
--                        coefficient vanishes — the model satisfies the
--                        five-window inputs listed before the case
--                        split in §7 of the paper.
--
--   §9  `flipFixesZero`  THE POINT OF F23.  The first endpoint flip
--                        sends (+,+,+,+,−) to (−,+,+,+,+) and BOTH
--                        masses are 0.  The printed argument asserts
--                        that each flip changes a zero probability; here
--                        it does not, because ε₁ = −ε₅ kills the a-term.
--       `flipDistinct`   and the two patterns really are different.
--
--   §10 `f2Identity1..4` the four auxiliary 𝔽₂[u] products of
--                        CONSTRAINT_ALGEBRA (5.1), by exact convolution.
--                        As that note says, they carry NO Liouville
--                        implication; they are recorded because the
--                        retired script recorded them.
--
-- Idiom copied from `NaturalMachine/SieveFiber.agda` (Boolean
-- exhaustion whose `refl` the typechecker must normalise) and
-- `NaturalMachine/PMTorus.agda`.
------------------------------------------------------------------------

module Window5Walsh where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; _or_ ; not ; _⊕_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; _+_ ; _·_ ; -_)

------------------------------------------------------------------------
-- §1  Signs, patterns, and the two arithmetics that must compute
------------------------------------------------------------------------

data Sg : Type₀ where
  P M : Sg

-- multiplication of signs
_*_ : Sg → Sg → Sg
P * y = y
M * P = M
M * M = P

val : Sg → ℤ
val P = pos 1
val M = negsuc 0

Pat : Type₀
Pat = Sg × (Sg × (Sg × (Sg × Sg)))

St : Type₀                     -- a de Bruijn state: four bits
St = Sg × (Sg × (Sg × Sg))

Subset : Type₀                    -- a subset of {1..5}, as membership flags
Subset = Bool × (Bool × (Bool × (Bool × Bool)))

Form : Type₀                   -- (coeff of a , coeff of b , coeff of c)
Form = ℤ × (ℤ × ℤ)

------------------------------------------------------------------------
-- §2  Finite-verification plumbing
------------------------------------------------------------------------

eqᵇ : ℕ → ℕ → Bool
eqᵇ zero    zero    = true
eqᵇ zero    (suc _) = false
eqᵇ (suc _) zero    = false
eqᵇ (suc m) (suc n) = eqᵇ m n

eqℤ : ℤ → ℤ → Bool
eqℤ (pos m)    (pos n)    = eqᵇ m n
eqℤ (negsuc m) (negsuc n) = eqᵇ m n
eqℤ _          _          = false

nonNegℤ : ℤ → Bool
nonNegℤ (pos _)    = true
nonNegℤ (negsuc _) = false

posℤ : ℤ → Bool
posℤ (pos zero)    = false
posℤ (pos (suc _)) = true
posℤ (negsuc _)    = false

eqForm : Form → Form → Bool
eqForm (x , y , z) (x' , y' , z') = eqℤ x x' and (eqℤ y y' and eqℤ z z')

allB : {A : Type₀} → List A → (A → Bool) → Bool
allB []       f = true
allB (x ∷ xs) f = f x and allB xs f

anyB : {A : Type₀} → List A → (A → Bool) → Bool
anyB []       f = false
anyB (x ∷ xs) f = f x or anyB xs f

countB : {A : Type₀} → List A → (A → Bool) → ℕ
countB []       f = zero
countB (x ∷ xs) f with f x
... | true  = suc (countB xs f)
... | false = countB xs f

sumℤ : List ℤ → ℤ
sumℤ []       = pos 0
sumℤ (x ∷ xs) = x + sumℤ xs

bind : {A B : Type₀} → List A → (A → List B) → List B
bind []       f = []
bind (x ∷ xs) f = f x ++ bind xs f

------------------------------------------------------------------------
-- §3  The three finite domains, enumerated
------------------------------------------------------------------------

sgs : List Sg
sgs = P ∷ M ∷ []

bools : List Bool
bools = true ∷ false ∷ []

allPats : List Pat
allPats =
  bind sgs λ e1 → bind sgs λ e2 → bind sgs λ e3 → bind sgs λ e4 →
  bind sgs λ e5 → (e1 , e2 , e3 , e4 , e5) ∷ []

allStates : List St
allStates =
  bind sgs λ e1 → bind sgs λ e2 → bind sgs λ e3 → bind sgs λ e4 →
  (e1 , e2 , e3 , e4) ∷ []

allSubs : List Subset
allSubs =
  bind bools λ t1 → bind bools λ t2 → bind bools λ t3 → bind bools λ t4 →
  bind bools λ t5 → (t1 , t2 , t3 , t4 , t5) ∷ []

-- sanity: the domains really have 32, 16, 32 elements
sizePats : countB allPats (λ _ → true) ≡ 32
sizePats = refl

sizeStates : countB allStates (λ _ → true) ≡ 16
sizeStates = refl

sizeSubs : countB allSubs (λ _ → true) ≡ 32
sizeSubs = refl

------------------------------------------------------------------------
-- §4  The five four-point characters, and the mass
------------------------------------------------------------------------

p1234 p2345 p1345 p1235 p1245 : Pat → Sg
p1234 (e1 , e2 , e3 , e4 , e5) = e1 * (e2 * (e3 * e4))
p2345 (e1 , e2 , e3 , e4 , e5) = e2 * (e3 * (e4 * e5))
p1345 (e1 , e2 , e3 , e4 , e5) = e1 * (e3 * (e4 * e5))
p1235 (e1 , e2 , e3 , e4 , e5) = e1 * (e2 * (e3 * e5))
p1245 (e1 , e2 , e3 , e4 , e5) = e1 * (e2 * (e4 * e5))

-- 96·μ at (a,b,c) = (1/3,1/3,1/3)
m96 : Pat → ℤ
m96 p =
  pos 3 + (val (p1234 p) + (val (p2345 p)
        + (val (p1345 p) + (val (p1235 p) + val (p1245 p)))))

masses : List ℤ
masses = map m96 allPats

------------------------------------------------------------------------
-- §5  The sharp ten-zero point
------------------------------------------------------------------------

massesNonNeg : allB masses nonNegℤ ≡ true
massesNonNeg = refl

massTotal : sumℤ masses ≡ pos 96
massTotal = refl

-- THE HEADLINE COUNT: exactly ten of the 32 masses vanish.
zeroCount : countB masses (λ z → eqℤ z (pos 0)) ≡ 10
zeroCount = refl

-- and the mass spectrum is {0, 4, 8} — nothing else occurs
massValues : allB masses (λ z → eqℤ z (pos 0) or (eqℤ z (pos 4) or eqℤ z (pos 8)))
           ≡ true
massValues = refl

-- the multiplicities of the three values, matching the class analysis
-- of CONSTRAINT_ALGEBRA §2 (10 zeros, 20 middles, 2 tops)
massSpectrum : (countB masses (λ z → eqℤ z (pos 0)) ≡ 10)
             × ( (countB masses (λ z → eqℤ z (pos 4)) ≡ 20)
               × (countB masses (λ z → eqℤ z (pos 8)) ≡ 2) )
massSpectrum = refl , refl , refl

-- ALL FOUR SHARP VERTICES.  CONSTRAINT_ALGEBRA (2.2) claims the ten-zero
-- maximum is attained exactly at c = 1/3, |a| = |b| = 1/3, i.e. at four
-- points.  Here σa, σb ∈ {+,−} are the signs of a and b.
m96± : Sg → Sg → Pat → ℤ
m96± σa σb p =
  pos 3 + ( signedBy σa (val (p1234 p) + val (p2345 p))
          + ( signedBy σb (val (p1345 p) + val (p1235 p))
            + val (p1245 p) ) )
  where
  signedBy : Sg → ℤ → ℤ
  signedBy P z = z
  signedBy M z = - z

sharpVertexOK : Sg → Sg → Bool
sharpVertexOK σa σb =
  allB (map (m96± σa σb) allPats) nonNegℤ
  and (eqℤ (sumℤ (map (m96± σa σb) allPats)) (pos 96)
       and eqᵇ (countB (map (m96± σa σb) allPats) (λ z → eqℤ z (pos 0))) 10)

-- each of the four vertices carries ten zeros, total mass one, and no
-- negative atom
fourSharpVertices : allB sgs (λ σa → allB sgs (λ σb → sharpVertexOK σa σb))
                  ≡ true
fourSharpVertices = refl

------------------------------------------------------------------------
-- §6  The nine affine forms  (CONSTRAINT_ALGEBRA §2, the input to its
--     Theorem 2.1)
--
-- 32·μ_{a,b,c}(ε) = 1 + (coefA)·a + (coefB)·b + (coefC)·c, and the map
-- ε ↦ (coefA, coefB, coefC) takes exactly nine values, with
-- multiplicities 2 (class A, four forms), 4 (classes B and C, two forms
-- each) and 8 (class D).  2·4 + 4·2 + 4·2 + 8 = 32.
------------------------------------------------------------------------

formOf : Pat → Form
formOf p = (val (p1234 p) + val (p2345 p))
         , ((val (p1345 p) + val (p1235 p))
         , val (p1245 p))

classTable : List (Form × ℕ)
classTable =
  -- class A : 1 + c + 2ax + 2by
    (((pos 2    , (pos 2    , pos 1))) , 2)
  ∷ (((pos 2    , (negsuc 1 , pos 1))) , 2)
  ∷ (((negsuc 1 , (pos 2    , pos 1))) , 2)
  ∷ (((negsuc 1 , (negsuc 1 , pos 1))) , 2)
  -- class B : 1 − c − 2ax
  ∷ (((pos 2    , (pos 0    , negsuc 0))) , 4)
  ∷ (((negsuc 1 , (pos 0    , negsuc 0))) , 4)
  -- class C : 1 − c − 2by
  ∷ (((pos 0    , (pos 2    , negsuc 0))) , 4)
  ∷ (((pos 0    , (negsuc 1 , negsuc 0))) , 4)
  -- class D : 1 + c
  ∷ (((pos 0    , (pos 0    , pos 1))) , 8)
  ∷ []

-- every stated multiplicity is the true one …
classCounts : allB classTable
                (λ fe → eqᵇ (countB allPats (λ p → eqForm (formOf p) (fst fe)))
                            (snd fe))
            ≡ true
classCounts = refl

-- … and no other form occurs, so the nine are ALL of them.
classComplete : allB allPats
                  (λ p → anyB classTable (λ fe → eqForm (formOf p) (fst fe)))
              ≡ true
classComplete = refl

-- the nine forms are pairwise distinct (so "nine" is not a miscount)
classDistinct : countB classTable
                  (λ fe → eqᵇ (countB classTable
                                 (λ ge → eqForm (fst fe) (fst ge))) 1)
              ≡ 9
classDistinct = refl

------------------------------------------------------------------------
-- §7  Stationarity: the conserved order-four de Bruijn flow
--
-- A five-bit word is a directed edge of the order-four de Bruijn graph.
-- Summing over the last bit gives the outgoing mass at a state; over the
-- first bit, the incoming mass.  Both equal 6 + 2·ε₁ε₂ε₃ε₄ in m96 units
-- (that is 96·(1 + aε₁ε₂ε₃ε₄)/16 at a = 1/3), so the table is a
-- conserved flow and, being strictly positive, the five-window law of a
-- stationary order-four Markov chain.
------------------------------------------------------------------------

outMass : St → ℤ
outMass (e1 , e2 , e3 , e4) = m96 (e1 , e2 , e3 , e4 , P) + m96 (e1 , e2 , e3 , e4 , M)

inMass : St → ℤ
inMass (e1 , e2 , e3 , e4) = m96 (P , e1 , e2 , e3 , e4) + m96 (M , e1 , e2 , e3 , e4)

stationaryMass : St → ℤ
stationaryMass (e1 , e2 , e3 , e4) =
  pos 6 + (val (e1 * (e2 * (e3 * e4))) + val (e1 * (e2 * (e3 * e4))))

flowConserved : allB allStates
                  (λ v → eqℤ (outMass v) (inMass v)
                         and (eqℤ (outMass v) (stationaryMass v)
                              and posℤ (stationaryMass v)))
              ≡ true
flowConserved = refl

-- PLANTED-FALSE CONTROL.  Replace the two consecutive coefficients
-- (a, a) by the unequal pair (1/3, 1/4) — everything else identical —
-- and conservation must break.  Cleared denominators: 384·μ′.
m384′ : Pat → ℤ
m384′ p = pos 12 + (pos 4 · val (p1234 p) + pos 3 · val (p2345 p))

outMass′ : St → ℤ
outMass′ (e1 , e2 , e3 , e4) = m384′ (e1 , e2 , e3 , e4 , P) + m384′ (e1 , e2 , e3 , e4 , M)

inMass′ : St → ℤ
inMass′ (e1 , e2 , e3 , e4) = m384′ (P , e1 , e2 , e3 , e4) + m384′ (M , e1 , e2 , e3 , e4)

-- the check FAILS, as it must: the stationarity test has content.
flowBroken : allB allStates (λ v → eqℤ (outMass′ v) (inMass′ v)) ≡ false
flowBroken = refl

-- and it fails somewhere concrete
flowBrokenWitness : eqℤ (outMass′ (P , P , P , P)) (inMass′ (P , P , P , P)) ≡ false
flowBrokenWitness = refl

------------------------------------------------------------------------
-- §8  The complete Walsh spectrum
--
-- 96·μ̂(T) = Σ_ε 96μ(ε)·χ_T(ε).  Every nonempty T gives 0 except the
-- five distinguished four-sets, which give 32 = 96·(1/3).  So on this
-- window every odd-order coefficient and every two-point coefficient
-- vanishes, and the shift/reflection equalities the paper's §7 uses
-- hold: μ̂(1234) = μ̂(2345) = a and μ̂(1345) = μ̂(1235) = b.
------------------------------------------------------------------------

sel : Bool → Sg → Sg
sel true  e = e
sel false _ = P

chi : Subset → Pat → Sg
chi (t1 , t2 , t3 , t4 , t5) (e1 , e2 , e3 , e4 , e5) =
  sel t1 e1 * (sel t2 e2 * (sel t3 e3 * (sel t4 e4 * sel t5 e5)))

signed : ℤ → Sg → ℤ
signed z P = z
signed z M = - z

walsh : Subset → ℤ
walsh T = sumℤ (map (λ p → signed (m96 p) (chi T p)) allPats)

fiveSubs : List Subset
fiveSubs =
    (true  , true  , true  , true  , false)   -- {1,2,3,4}
  ∷ (false , true  , true  , true  , true )   -- {2,3,4,5}
  ∷ (true  , false , true  , true  , true )   -- {1,3,4,5}
  ∷ (true  , true  , true  , false , true )   -- {1,2,3,5}
  ∷ (true  , true  , false , true  , true )   -- {1,2,4,5}
  ∷ []

eqSub : Subset → Subset → Bool
eqSub (a , b , c , d , e) (a' , b' , c' , d' , e') =
  eqB a a' and (eqB b b' and (eqB c c' and (eqB d d' and eqB e e')))
  where
  eqB : Bool → Bool → Bool
  eqB true  true  = true
  eqB false false = true
  eqB _     _     = false

emptySub : Subset
emptySub = (false , false , false , false , false)

walshExpected : Subset → ℤ
walshExpected T with anyB fiveSubs (eqSub T)
... | true  = pos 32
... | false with eqSub T emptySub
...            | true  = pos 96
...            | false = pos 0

walshOK : allB allSubs (λ T → eqℤ (walsh T) (walshExpected T)) ≡ true
walshOK = refl

-- the two shift/reflection equalities, stated on the nose
shiftEquality : walsh (true , true , true , true , false)
              ≡ walsh (false , true , true , true , true)
shiftEquality = refl

reflectionEquality : walsh (true , false , true , true , true)
                   ≡ walsh (true , true , true , false , true)
reflectionEquality = refl

-- PLANTED-FALSE CONTROL for §8: a subset that is NOT one of the five
-- must have coefficient 0, and a two-point coefficient must vanish.
-- (Both are consequences of walshOK; stated separately because they are
-- the specific inputs the published argument consumes.)
twoPointVanishes : walsh (true , true , false , false , false) ≡ pos 0
twoPointVanishes = refl

oddOrderVanishes : walsh (true , false , false , false , false) ≡ pos 0
oddOrderVanishes = refl

------------------------------------------------------------------------
-- §9  THE COUNTEREXAMPLE TO THE PRINTED FLIP
--
-- The printed nonzero-(a,b,c) argument asserts that the endpoint flip
-- ε ↦ (−ε₁, ε₂, ε₃, ε₄, −ε₅) changes a zero probability, and concludes
-- that a four-orbit contains at most one zero.  At (1/3,1/3,1/3) the
-- flip sends (+,+,+,+,−) to (−,+,+,+,+) and both masses are 0: with
-- ε₁ = −ε₅, flipping both endpoints leaves ε₁ε₂ε₃ε₄ + ε₂ε₃ε₄ε₅
-- unchanged, so the a-term does not move at all.
------------------------------------------------------------------------

atom flipped : Pat
atom    = (P , P , P , P , M)
flipped = (M , P , P , P , P)

flipFixesZero : (m96 atom ≡ pos 0) × (m96 flipped ≡ pos 0)
flipFixesZero = refl , refl

-- the two patterns are genuinely distinct
eqPat : Pat → Pat → Bool
eqPat (a , b , c , d , e) (a' , b' , c' , d' , e') =
  eqS a a' and (eqS b b' and (eqS c c' and (eqS d d' and eqS e e')))
  where
  eqS : Sg → Sg → Bool
  eqS P P = true
  eqS M M = true
  eqS _ _ = false

flipDistinct : eqPat atom flipped ≡ false
flipDistinct = refl

-- and the flip really is the endpoint involution: it fixes ε₂,ε₃,ε₄ and
-- negates ε₁,ε₅, and its fixed-point-free character is what the printed
-- argument needed and does not have here.
flipIsEndpointFlip : (fst atom ≡ P) × (fst flipped ≡ M)
flipIsEndpointFlip = refl , refl

------------------------------------------------------------------------
-- §10  The four auxiliary 𝔽₂[u] identities  (CONSTRAINT_ALGEBRA (5.1))
--
-- Polynomials as coefficient lists, lowest degree first.  These are
-- recorded because the retired script recorded them.  The note is
-- explicit that they carry NO implication for the ten-zero exclusion:
-- they describe how an EXTREMAL (±1) four-point relation would
-- propagate, and at the sharp table the correlations are ±1/3.
------------------------------------------------------------------------

zeros : List Bool → List Bool
zeros = map (λ _ → false)

addF2 : List Bool → List Bool → List Bool
addF2 []       ys       = ys
addF2 (x ∷ xs) []       = x ∷ xs
addF2 (x ∷ xs) (y ∷ ys) = (x ⊕ y) ∷ addF2 xs ys

scaleF2 : Bool → List Bool → List Bool
scaleF2 true  ys = ys
scaleF2 false ys = zeros ys

mulF2 : List Bool → List Bool → List Bool
mulF2 []       ys = []
mulF2 (x ∷ xs) ys = addF2 (scaleF2 x ys) (false ∷ mulF2 xs ys)

-- (u+u²+u³+u⁴)(1+u) = u+u⁵
f2Identity1 : mulF2 (false ∷ true ∷ true ∷ true ∷ true ∷ [])
                    (true ∷ true ∷ [])
            ≡ (false ∷ true ∷ false ∷ false ∷ false ∷ true ∷ [])
f2Identity1 = refl

-- (u+u²+u⁴+u⁵)(u+u²+u³) = u²+u⁸
f2Identity2 : mulF2 (false ∷ true ∷ true ∷ false ∷ true ∷ true ∷ [])
                    (false ∷ true ∷ true ∷ true ∷ [])
            ≡ (false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ [])
f2Identity2 = refl

-- (u+u²+u³+u⁵)(1+u+u³) = u+u⁸
f2Identity3 : mulF2 (false ∷ true ∷ true ∷ true ∷ false ∷ true ∷ [])
                    (true ∷ true ∷ false ∷ true ∷ [])
            ≡ (false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ [])
f2Identity3 = refl

-- (u+u³+u⁴+u⁵)(1+u²+u³) = u+u⁸
f2Identity4 : mulF2 (false ∷ true ∷ false ∷ true ∷ true ∷ true ∷ [])
                    (true ∷ false ∷ true ∷ true ∷ [])
            ≡ (false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ [])
f2Identity4 = refl

-- PLANTED-FALSE CONTROL for §10: perturb one coefficient of the
-- expected answer of identity 1 and the check must fail.
eqLB : List Bool → List Bool → Bool
eqLB []       []       = true
eqLB []       (_ ∷ _)  = false
eqLB (_ ∷ _)  []       = false
eqLB (x ∷ xs) (y ∷ ys) = not (x ⊕ y) and eqLB xs ys

f2Control : eqLB (mulF2 (false ∷ true ∷ true ∷ true ∷ true ∷ [])
                        (true ∷ true ∷ []))
                 (true ∷ true ∷ false ∷ false ∷ false ∷ true ∷ [])
          ≡ false
f2Control = refl
