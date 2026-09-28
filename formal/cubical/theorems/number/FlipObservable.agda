{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FlipObservable
--
-- THE QUESTION answered here:
--
--   "wants: from any lane — a flip-breaking observable definable in
--    the machine's term grammar (entry/mod/gcd/vall compositions
--    only); if none exists, that is a grammar-blindness theorem worth
--    typing."
--
-- and its companion holding:
--
--   "which flip-breaking observable is the MINIMAL port pricing the
--    det-charge above zero — the seam between the machine's adic
--    ladder (proved charge-blind at price exactly 0) and one required
--    bit."
--
-- ANSWER (both halves, stratified by the port — the dichotomy IS the
-- finding):
--
--   The flip enters the grammar through exactly one generator: the
--   ported read of the hidden payload.  mod/gcd/vall composition can
--   neither create nor destroy flip-sensitivity (they are function
--   applications; blindness is preserved by `cong`).  Hence:
--
--   (b) at the parity port — rung 1 of the machine's 2-adic ladder,
--       the port at which the packet lane proved its adic-bit
--       observable charge-blind at price exactly 0 — EVERY term of
--       the grammar is flip-invariant (`parityGrammarBlind`,
--       structural induction over the syntax).  Their price-0 result
--       is not about one observable; it is a grammar-blindness
--       theorem, and it is typed here.
--
--   (a) at rung 2 — ONE more bit, port h mod 4 — the bare generator
--       hentry(1,1) already breaks the flip (`breakerBreaks`):
--       on the witness pair (identity payload, its flip diag(1,-1) —
--       the packet lane's own det-flip element, det-charges +1/-1),
--       it evaluates to 1 vs 3.  The same values are reached by the
--       explicit mod-composition modC (hentry 1 1) 4 over the raw
--       payload port (`modBreakerBreaks`), so the breaking observable
--       is a genuine entry/mod composition of the named grammar.
--       Control: the SAME term is flip-invariant at rung 1
--       (`breakerBlindAtParity`) — the breaking belongs to the rung,
--       not the term.
--
--   The seam, exactly: parity is the unique sign-blind rung of the
--   2-adic ladder ((-x) mod 2 = x mod 2; mod 4 separates -1 from 1
--   because ℤ₂ˣ ≅ {±1} × (1 + 4ℤ₂) — the SIGN of a 2-adic unit is
--   its second bit).  `portBreak→grammarBreak` is the general
--   converse: any failure of sign-blindness in the port is realized
--   by a bare entry term.  So: the grammar is flip-blind iff the port
--   is sign-blind; the minimal flip-breaking port on the machine's
--   own ladder is width 2 — one bit above what was granted.
--
-- THE FLIP (imported semantics, typed here): the det-flip involution
-- of machinery/charge_information_obstruction.py (absent from this repository), (U,V) ↦ (F·U, V·F)
-- with F = diag(1,-1), acting on the U-side payload h = U·U₀⁻¹ as
-- h ↦ F·h, i.e. bottom row negated.  `flipAsMul` proves the typed
-- action IS left multiplication by diag(1,-1); `flipInvol` that it is
-- an involution; `chargeFlip` that it reverses the det-charge:
-- det (flip h) ≡ - det h.  (The V-side column flip is symmetric —
-- entries (0,1),(1,1) negated — and is not duplicated here.)
--
-- Imported, not re-modelled: R, M, mul, dia (Gamma0Partner); det, idm
-- (M2Unimodular).  Ports and grammar are typed here.
------------------------------------------------------------------------

module FlipObservable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; false ; true)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _∸_ ; snotz ; injSuc)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Mod using (_mod_ ; modIndStep)
open import Cubical.Data.Nat.GCD using (gcd)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; abs ; injPos)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

open import Gamma0Partner using (R ; M ; mul ; dia)
open import M2Unimodular using (det ; idm)

open CommRingStr (ℤCommRing .snd)

------------------------------------------------------------------------
-- §1  The flip: diag(1,-1) acting on the payload, typed
------------------------------------------------------------------------

private
  l1 : (x y : R) → 1r · x + 0r · y ≡ x
  l1 _ _ = solve! ℤCommRing

  l2 : (x y : R) → 0r · x + (- 1r) · y ≡ - y
  l2 _ _ = solve! ℤCommRing

  negneg : (x : R) → - (- x) ≡ x
  negneg _ = solve! ℤCommRing

  detFlipL : (a b c d : R) → a · (- d) - b · (- c) ≡ - (a · d - b · c)
  detFlipL _ _ _ _ = solve! ℤCommRing

flipMat : M
flipMat = dia 1r (- 1r)

flipRow : M → M
flipRow (a , b , c , d) = (a , b , - c , - d)

-- the typed action IS the packet lane's involution: left mult by diag(1,-1)
flipAsMul : (h : M) → mul flipMat h ≡ flipRow h
flipAsMul (a , b , c , d) i = (l1 a c i , l1 b d i , l2 a c i , l2 b d i)

flipInvol : (h : M) → flipRow (flipRow h) ≡ h
flipInvol (a , b , c , d) i = (a , b , negneg c i , negneg d i)

-- the flip reverses the det-charge exactly
chargeFlip : (h : M) → det (flipRow h) ≡ - det h
chargeFlip (a , b , c , d) = detFlipL a b c d

-- machine state: (visible matrix, hidden payload); flip acts on the fiber
State : Type
State = M × M

flipState : State → State
flipState (m , h) = (m , flipRow h)

------------------------------------------------------------------------
-- §2  The adic ladder of ports: h mod 2^w, Euclidean mod on ℤ
------------------------------------------------------------------------

-- Euclidean remainder on ℤ with modulus c : ℕ (canonical residue in
-- [0, c); matches Python's %, the machine's port arithmetic)
modZ : ℕ → ℤ → ℤ
modZ c (pos n)    = pos (n mod c)
modZ c (negsuc n) = pos ((c ∸ ((suc n) mod c)) mod c)

twoTo : ℕ → ℕ
twoTo zero    = 1
twoTo (suc w) = twoTo w +ℕ twoTo w

-- the port at rung w of the 2-adic ladder: the machine's
-- "hentry sees h mod 2^bits"
portW : ℕ → ℤ → ℤ
portW w = modZ (twoTo w)

-- the two rungs at issue, definitionally
_ : portW 1 ≡ modZ 2
_ = refl

_ : portW 2 ≡ modZ 4
_ = refl

-- sanity: modZ is the Euclidean mod (examples compute by refl)
_ : modZ 3 (pos 7) ≡ pos 1        -- 7 mod 3 = 1
_ = refl

_ : modZ 3 (negsuc 6) ≡ pos 2     -- (-7) mod 3 = 2
_ = refl

-- rung 1 is sign-blind: (-x) mod 2 = x mod 2 --------------------------

private
  parityFold : (m : ℕ) → ((2 ∸ (m mod 2)) mod 2) ≡ (m mod 2)
  parityFold zero = refl
  parityFold (suc zero) = refl
  parityFold (suc (suc m)) =
    cong (λ r → (2 ∸ r) mod 2) (modIndStep 1 m)
    ∙ parityFold m
    ∙ sym (modIndStep 1 m)

mod2Blind : (x : ℤ) → modZ 2 (- x) ≡ modZ 2 x
mod2Blind (pos zero)    = refl
mod2Blind (pos (suc n)) = cong pos (parityFold (suc n))
mod2Blind (negsuc n)    = cong pos (sym (parityFold (suc n)))

-- rung 2 is NOT sign-blind: mod 4 separates the units -1 and 1 — the
-- sign of a 2-adic unit is its second bit (ℤ₂ˣ ≅ {±1} × (1 + 4ℤ₂))
_ : modZ 4 (pos 1) ≡ pos 1
_ = refl

_ : modZ 4 (- (pos 1)) ≡ pos 3
_ = refl

------------------------------------------------------------------------
-- §3  The machine's term grammar (entry/mod/gcd/vall), as syntax
------------------------------------------------------------------------

-- index Bool: false = 0, true = 1
entryOf : Bool → Bool → M → R
entryOf false false (a , b , c , d) = a
entryOf false true  (a , b , c , d) = b
entryOf true  false (a , b , c , d) = c
entryOf true  true  (a , b , c , d) = d

data Term : Type where
  entry  : Bool → Bool → Term        -- visible entry m[i][j]
  hentry : Bool → Bool → Term        -- PORTED hidden entry P(h[i][j])
  modC   : Term → ℕ → Term           -- value mod constant
  gcdT   : Term → Term → Term        -- gcd of two values
  valli  : Term → Term → Term        -- vallī length (pulverizer trace)

-- evaluators for the composite generators ----------------------------

gcdZ : ℤ → ℤ → ℤ
gcdZ x y = pos (gcd (abs x) (abs y))

private
  -- Euclid quotient-count, fuel-indexed (fuel = second argument + 1
  -- suffices: remainders strictly decrease)
  euclLen : ℕ → ℕ → ℕ → ℕ
  euclLen zero    a b       = zero
  euclLen (suc f) a zero    = zero
  euclLen (suc f) a (suc b) = suc (euclLen f (suc b) (a mod (suc b)))

valliZ : ℤ → ℤ → ℤ
valliZ x y = pos (euclLen (suc (abs y)) (abs x) (abs y))

_ : valliZ (pos 7) (pos 3) ≡ pos 2   -- 7 = 2·3+1, 3 = 3·1+0: two steps
_ = refl

_ : gcdZ (negsuc 5) (pos 4) ≡ pos 2  -- gcd(-6,4) = 2
_ = refl

-- the evaluator, parameterized by the port P granted on the fiber ----

eval : (ℤ → ℤ) → Term → State → ℤ
eval P (entry i j)  (m , h) = entryOf i j m
eval P (hentry i j) (m , h) = P (entryOf i j h)
eval P (modC t c)   (m , h) = modZ c (eval P t (m , h))
eval P (gcdT t u)   (m , h) = gcdZ (eval P t (m , h)) (eval P u (m , h))
eval P (valli t u)  (m , h) = valliZ (eval P t (m , h)) (eval P u (m , h))

------------------------------------------------------------------------
-- §4  Grammar blindness at any sign-blind port (the (b) half)
--
-- Structural induction over the syntax: the flip can enter only
-- through the ported fiber read; every composite constructor
-- transports blindness by cong.  No property of mod/gcd/vall is
-- used — THAT is why the grammar cannot manufacture flip-sensitivity.
------------------------------------------------------------------------

private
  hblind : (P : ℤ → ℤ) → ((x : ℤ) → P (- x) ≡ P x)
         → (i j : Bool) (h : M)
         → P (entryOf i j (flipRow h)) ≡ P (entryOf i j h)
  hblind P Pb false false (a , b , c , d) = refl
  hblind P Pb false true  (a , b , c , d) = refl
  hblind P Pb true  false (a , b , c , d) = Pb c
  hblind P Pb true  true  (a , b , c , d) = Pb d

evalFlipBlind : (P : ℤ → ℤ) (Pb : (x : ℤ) → P (- x) ≡ P x)
              → (t : Term) (s : State)
              → eval P t (flipState s) ≡ eval P t s
evalFlipBlind P Pb (entry i j)  (m , h) = refl
evalFlipBlind P Pb (hentry i j) (m , h) = hblind P Pb i j h
evalFlipBlind P Pb (modC t c)   (m , h) =
  cong (modZ c) (evalFlipBlind P Pb t (m , h))
evalFlipBlind P Pb (gcdT t u)   (m , h) =
  cong₂ gcdZ (evalFlipBlind P Pb t (m , h)) (evalFlipBlind P Pb u (m , h))
evalFlipBlind P Pb (valli t u)  (m , h) =
  cong₂ valliZ (evalFlipBlind P Pb t (m , h)) (evalFlipBlind P Pb u (m , h))

-- THE GRAMMAR-BLINDNESS THEOREM at the granted rung: at the parity
-- port (rung 1 — where the packet lane priced its adic bit at exactly
-- 0), EVERY term of the grammar is flip-invariant.  Their price-0
-- measurement was an instance; this is the law it was standing in for.
parityGrammarBlind : (t : Term) (s : State)
                   → eval (portW 1) t (flipState s) ≡ eval (portW 1) t s
parityGrammarBlind = evalFlipBlind (portW 1) mod2Blind

------------------------------------------------------------------------
-- §5  The flip-breaking observable at rung 2 (the (a) half)
------------------------------------------------------------------------

breaker : Term
breaker = hentry true true          -- the ported (1,1) payload entry

witnessS : State
witnessS = (idm , idm)              -- identity payload: the trivial
                                    -- certificate difference, in fiber

flippedS : State
flippedS = flipState witnessS       -- payload diag(1,-1): the packet
                                    -- lane's det-flip element itself

-- the distinguishing evaluation, definitional on both sides
breakerAt : eval (portW 2) breaker witnessS ≡ pos 1
breakerAt = refl

breakerAtFlip : eval (portW 2) breaker flippedS ≡ pos 3
breakerAtFlip = refl

breakerBreaks : ¬ (eval (portW 2) breaker flippedS
                 ≡ eval (portW 2) breaker witnessS)
breakerBreaks p = snotz (injSuc (injPos p))

-- the same observable as an explicit entry/mod COMPOSITION over the
-- raw payload port (the packet lane's Z = payload regime): the
-- breaking term is in the named grammar, not in the port's favour
modBreaker : Term
modBreaker = modC (hentry true true) 4

rawPort : ℤ → ℤ
rawPort x = x

modBreakerBreaks : ¬ (eval rawPort modBreaker flippedS
                    ≡ eval rawPort modBreaker witnessS)
modBreakerBreaks p = snotz (injSuc (injPos p))

-- CONTROL: the very same breaker term is flip-invariant at rung 1 on
-- EVERY state — the breaking belongs to the rung, not the term
breakerBlindAtParity : (s : State)
  → eval (portW 1) breaker (flipState s) ≡ eval (portW 1) breaker s
breakerBlindAtParity = parityGrammarBlind breaker

-- the witness pair carries opposite det-charges (+1 / -1): it is a
-- balanced pair of the packet lane's charge chain
_ : det idm ≡ 1r
_ = refl

_ : det (flipRow idm) ≡ - 1r
_ = refl

------------------------------------------------------------------------
-- §6  The dichotomy, closed: grammar flip-blind ⟺ port sign-blind
--
-- Forward: evalFlipBlind (§4).  Converse: any value at which the port
-- fails sign-blindness is realized by a BARE entry term on some state
-- — so no port failure can hide from the grammar, and no grammar term
-- can break a sign-blind port.  The flip lives in the port, only.
------------------------------------------------------------------------

portBreak→grammarBreak :
  (P : ℤ → ℤ) (x : ℤ) → ¬ (P (- x) ≡ P x)
  → Σ[ t ∈ Term ] Σ[ s ∈ State ]
      (¬ (eval P t (flipState s) ≡ eval P t s))
portBreak→grammarBreak P x nb =
  hentry true true , (idm , (1r , 0r , 0r , x)) , nb
