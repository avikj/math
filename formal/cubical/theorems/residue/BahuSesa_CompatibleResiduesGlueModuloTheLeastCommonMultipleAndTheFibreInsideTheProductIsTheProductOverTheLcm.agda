{-# OPTIONS --cubical --safe --no-import-sorts #-}
------------------------------------------------------------------------
-- बहुशेषम् (bahu-śeṣa, "many remainders"):
--   compatible residues glue modulo the least common multiple, and the
--   fibre inside the product ℤ/P is the product over the lcm, P/L points.
--
-- ────────────────────────────────────────────────────────────────────
-- SOURCES, quoted verbatim.
--
-- (1) notes/MULTIPLE_REMAINDER_DESCENT.md (absent from this repository) (branch main).  Its setting:
--
--   Let m_1,…,m_n be positive integers, put
--       P = ∏_i m_i,   L = lcm(m_1,…,m_n),
--   and observe x ∈ ℤ/Pℤ through all residues
--       Φ(x) = (x mod m_1, …, x mod m_n).                          (1)
--
--   ## Theorem
--   A tuple (a_i) ∈ ∏_i ℤ/m_iℤ lies in the image of Φ exactly when
--       a_i ≡ a_j (mod gcd(m_i, m_j))  for every i, j.              (2)
--   Every nonempty fiber has cardinality
--       |Φ⁻¹(a_i)| = P/L.                                           (3)
--   Consequently compatible local views glue, but reconstruct the declared
--   source exactly only when the moduli are pairwise coprime.
--
--   "This is the standard generalized Chinese remainder theorem, executable
--    here as a finite descent law; no novelty is claimed."
--
--   Its controls: "The controls use `(4,6,9)`, whose 36 compatible records
--   each hide 6 source states, and the pairwise-coprime family `(3,4,5)`,
--   which reconstructs all 60 states exactly."
--
-- (2) notes/DESCENT_ALONG_ONE_MAP_IS_UNOBSTRUCTED.md (absent from this repository), §9 successor seed 2:
--
--   "PROVE — the multi-map case. `MULTIPLE_REMAINDER_DESCENT.md` (absent from this repository) is a cover
--    of `Z/P` by `{Z/mᵢ}`; its Theorem (compatible tuples glue; fibre `P/L`)
--    is a `H⁰`/`H¹` statement for the nerve of that cover. The theorem here
--    says the one-map case is empty, so the finite-cover case is where the
--    content is, and nothing in `formal/cubical/` currently states it."
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED.  Everything is over ℕ: a residue "a mod m" is a natural
-- a < m (the library's `Fin m`), `_mod_` is Cubical.Data.Nat.Mod's, gcd is
-- Cubical.Data.Nat.GCD's `gcd`/`isGCD`, lcm is LCMExists's `IsLCM₂` (binary,
-- any witness) and `lcmList`/`IsLCM` (lists, WalkCapacity's predicate).
-- No integers and no library Bézout are used: §2 proves Bézout over ℕ in
-- the two subtraction-free forms m·x ≡ n·y + g / m·x + g ≡ n·y, by
-- well-founded induction along Euclid's algorithm.  Hypotheses are
-- arguments, never comments.
--
-- (T1) TWO MODULI m, n (positive, or carrying residues a : Fin m, b : Fin n;
--      g = gcd m n, L any IsLCM₂ m n witness):
--   compat-necessary₂ : (x mod m) mod g ≡ (x mod n) mod g            (a)
--   glue₂    : a mod g ≡ b mod g →
--              Σ[ x ∈ ℕ ] (x < L) × (x mod m ≡ a) × (x mod n ≡ b)     (b)
--   unique₂  : x, y < L with the same two residues are equal          (c)
--   fibre₂   : a mod g ≡ b mod g →
--              Fin (gcd m n) ≃ Σ[ x ∈ Fin (m · n) ] Solves₂ m n a b x  (d)
--   IsLCM₂·gcd : L · gcd m n ≡ m · n   — so gcd m n IS P/L, and
--   fibre₂-enum : the k-th point of the fibre is x₀ + L · k, by refl,
--   where x₀ is the glued residue (progression: {x < L·q : x ≡ r (L)} is
--   enumerated by k ↦ r + L·k, k < q).
--
-- (T2) LISTS of moduli rs : List (Σ[ m ∈ ℕ ] Fin m), L = lcmList, P = product:
--   Compatible rs   — the note's (2), one condition per unordered pair
--                     (the diagonal and the symmetric copies are automatic)
--   SolvesAll→Compatible : SolvesAll rs x → Compatible rs             (a)
--   glue        : Compatible rs → Σ[ x ∈ ℕ ] (x < L) × SolvesAll rs x  (b)
--   glue-unique : x, y < L both solving are equal                     (c)
--   fibre       : Compatible rs → q · L ≡ P → Fin q ≃ Fibre rs         (d)
--   fibre'      : Fin (P/L) ≃ Fibre rs, P/L the witness of L ∣ P.
--   The induction glues the head (m, a) with (L_rest, y) by (T1); the
--   classical step "a ≡ y (mod gcd m L_rest)" is §9's distributive law
--       gcd a (lcm b c) ∣ lcm (gcd a b) (gcd a c)          (distrib)
--   proved WITHOUT valuations: with d = gcd a L, g₁ = gcd a b, g₂ = gcd a c,
--   h = gcd g₁ g₂, the product d·h divides a·a, a·b, a·c and L·g = b·c,
--   hence g₁·g₂ = lcm g₁ g₂ · h (gcd-factorʳ twice), and h > 0 cancels.
--
-- CONTROLS (§11).  (4, 6, 9): lcm 36, product 216, the compatible tuple
-- (3, 1, 7) glues to 7 by refl, `Fin 6 ≃ Fibre`, and the six lifts
-- 7, 43, 79, 115, 151, 187 are `x₀ + 36·k` by refl and each solves by refl.
-- The tuple (1, 3, 7) is NOT compatible (3 ≢ 7 mod 3) and so, by (a), has
-- no solution at all.  (3, 4, 5): lcm = product = 60, `Fin 1 ≃ Fibre`.
-- (4, 6) with (3, 1): `Fin 2 ≃ Fibre₂`, the two points 7 and 19 by refl.
--
-- CHECKED: Agda 2.8.0 + agda/cubical v0.9, --cubical --safe, no
-- postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module BahuSesa_CompatibleResiduesGlueModuloTheLeastCommonMultipleAndTheFibreInsideTheProductIsTheProductOverTheLcm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Fin.Properties using (_%_; n%k≡n[modk]; n%sk<sk; Fin-fst-≡)
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import Cubical.Tactics.NatSolver.Reflection using (solveℕ!)

open import Cubical.Data.List using (List; []; _∷_; map)

open import WalkCapacity using (All; CommonMultiple; IsLCM)
open import LCMExists using (IsLCM₂; lcm₂-from-gcd; lcm; lcm-isLCM₂; lcmList; lcmList-isLCM)
open import FinCardinality using (cong-shift→∣)

------------------------------------------------------------------------
-- §0  small arithmetic
------------------------------------------------------------------------

onPos : (P : ℕ → Type) → ((k : ℕ) → P (suc k)) → (m : ℕ) → 0 < m → P m
onPos P f zero    p = Empty.rec (¬-<-zero p)
onPos P f (suc k) _ = f k

∣-mult : {x y z w : ℕ} → x ∣ y → z ∣ w → (x · z) ∣ (y · w)
∣-mult {x} {y} {z} {w} p q =
  ∣-trans (∣-multʳ z p) (subst2 _∣_ (·-comm z y) (·-comm w y) (∣-multʳ y q))

∣-cancel-pos : (h : ℕ) → 0 < h → {x y : ℕ} → (x · h) ∣ (y · h) → x ∣ y
∣-cancel-pos = onPos (λ h → {x y : ℕ} → (x · h) ∣ (y · h) → x ∣ y) (λ k → ∣-cancelʳ k)

pos-∣ : {x y : ℕ} → 0 < y → x ∣ y → 0 < x
pos-∣ {x} {y} py d = onPos (λ y → x ∣ y → 0 < x) (λ k → m∣sn→z<m) y py d

∣-below : (L d : ℕ) → L ∣ d → d < L → d ≡ 0
∣-below L d L∣d d<L = go (discreteℕ d 0)
  where
  go : Dec (d ≡ 0) → d ≡ 0
  go (yes p) = p
  go (no q)  = Empty.rec (¬m<m (≤<-trans (m∣n→m≤n q L∣d) d<L))

------------------------------------------------------------------------
-- §1  lcm · gcd ≡ product; any IsLCM₂ witness is LCMExists's lcm
------------------------------------------------------------------------

private
  lcm·gcd-from : (a b g : ℕ) (h : isGCD a b g) → lcm₂-from-gcd a b g h .fst · g ≡ a · b
  lcm·gcd-from a b zero h = cong (_· b) (∣-zeroˡ (h .fst .fst))
  lcm·gcd-from a b (suc k) h =
    (q · b) · suc k   ≡⟨ sym (·-assoc q b (suc k)) ⟩
    q · (b · suc k)   ≡⟨ cong (q ·_) (·-comm b (suc k)) ⟩
    q · (suc k · b)   ≡⟨ ·-assoc q (suc k) b ⟩
    (q · suc k) · b   ≡⟨ cong (_· b) (∣-untrunc (h .fst .fst) .snd) ⟩
    a · b             ∎
    where
    q : ℕ
    q = ∣-untrunc (h .fst .fst) .fst

lcm·gcd : (a b : ℕ) → lcm a b · gcd a b ≡ a · b
lcm·gcd a b = lcm·gcd-from a b (gcd a b) (gcdIsGCD a b)

IsLCM₂-unique : {a b L L' : ℕ} → IsLCM₂ a b L → IsLCM₂ a b L' → L ≡ L'
IsLCM₂-unique {a} {b} {L} {L'} (a∣L , b∣L , lst) (a∣L' , b∣L' , lst') =
  antisym∣ (lst L' a∣L' b∣L') (lst' L a∣L b∣L)

IsLCM₂·gcd : (a b L : ℕ) → IsLCM₂ a b L → L · gcd a b ≡ a · b
IsLCM₂·gcd a b L H =
  cong (_· gcd a b) (IsLCM₂-unique H (lcm-isLCM₂ a b)) ∙ lcm·gcd a b

pos-· : {a b : ℕ} → 0 < a → 0 < b → 0 < a · b
pos-· {a} {b} pa pb =
  onPos (λ a → 0 < a · b)
        (λ k → onPos (λ b → 0 < suc k · b) (λ j → suc-≤-suc zero-≤) b pb) a pa

IsLCM₂-pos : (a b L : ℕ) → 0 < a → 0 < b → IsLCM₂ a b L → 0 < L
IsLCM₂-pos a b L pa pb H = pos-∣ (pos-· pa pb) (H .snd .snd (a · b) (∣-left b) (∣-right a))

------------------------------------------------------------------------
-- §2  Bézout over ℕ, in the two subtraction-free forms
------------------------------------------------------------------------

FormA FormB : ℕ → ℕ → ℕ → Type
FormA m n g = Σ[ x ∈ ℕ ] Σ[ y ∈ ℕ ] (m · x ≡ n · y + g)
FormB m n g = Σ[ x ∈ ℕ ] Σ[ y ∈ ℕ ] (m · x + g ≡ n · y)

Bezout : ℕ → ℕ → Type
Bezout m n = Σ[ g ∈ ℕ ] isGCD m n g × (FormA m n g ⊎ FormB m n g)

private
  ringA₁ : (q s r y g : ℕ) → (q · s + r) · y + g ≡ q · s · y + (r · y + g)
  ringA₁ q s r y g = solveℕ!

  ringA₂ : (q s y x : ℕ) → q · s · y + s · x ≡ s · (q · y + x)
  ringA₂ q s y x = solveℕ!

  ringB₁ : (q s r y : ℕ) → (q · s + r) · y ≡ q · s · y + r · y
  ringB₁ q s r y = solveℕ!

  ringB₂ : (q s y x g : ℕ) → q · s · y + (s · x + g) ≡ s · (q · y + x) + g
  ringB₂ q s y x g = solveℕ!

  stepA : (m s q r g : ℕ) → q · s + r ≡ m → FormA s r g → FormB m s g
  stepA m s q r g e (x' , y' , h) = y' , (q · y' + x') ,
    ( cong (λ z → z · y' + g) (sym e)
    ∙ ringA₁ q s r y' g
    ∙ cong (q · s · y' +_) (sym h)
    ∙ ringA₂ q s y' x' )

  stepB : (m s q r g : ℕ) → q · s + r ≡ m → FormB s r g → FormA m s g
  stepB m s q r g e (x' , y' , h) = y' , (q · y' + x') ,
    ( cong (λ z → z · y') (sym e)
    ∙ ringB₁ q s r y'
    ∙ cong (q · s · y' +_) (sym h)
    ∙ ringB₂ q s y' x' g )

  step : (n : ℕ) → ((n' : ℕ) → n' < n → (m : ℕ) → Bezout m n') → (m : ℕ) → Bezout m n
  step zero    _   m = m , zeroGCD m , inl (1 , 0 , ·-identityʳ m)
  step (suc n) rec m = g , stepGCD gG , forms
    where
    r : ℕ
    r = m % suc n
    q : ℕ
    q = n%k≡n[modk] m (suc n) .fst
    e : q · suc n + r ≡ m
    e = n%k≡n[modk] m (suc n) .snd
    ih : Bezout (suc n) r
    ih = rec r (n%sk<sk m n) (suc n)
    g : ℕ
    g = ih .fst
    gG : isGCD (suc n) r g
    gG = ih .snd .fst
    swap : FormA (suc n) r g ⊎ FormB (suc n) r g → FormA m (suc n) g ⊎ FormB m (suc n) g
    swap (inl fa) = inr (stepA m (suc n) q r g e fa)
    swap (inr fb) = inl (stepB m (suc n) q r g e fb)
    forms : FormA m (suc n) g ⊎ FormB m (suc n) g
    forms = swap (ih .snd .snd)

bezout : (m n : ℕ) → Bezout m n
bezout m n = WFI.induction <-wellfounded {P = λ n → (m : ℕ) → Bezout m n} step n m

-- it computes: gcd 4 6 = 2 with certificate 4·2 = 6·1 + 2
bezout46 : bezout 4 6 .fst ≡ 2
bezout46 = refl

------------------------------------------------------------------------
-- §3  residues: shifting by a multiple, reducing along divisibility
------------------------------------------------------------------------


-- adding a multiple of the modulus does not change the residue
mod-drop : (k r c : ℕ) → (r + suc k · c) mod suc k ≡ r mod suc k
mod-drop k r c =
  mod-rCancel (suc k) r (suc k · c)
  ∙ cong (λ z → (r + z) mod suc k)
         (cong (_mod suc k) (·-comm (suc k) c) ∙ zero-charac-gen (suc k) c)
  ∙ cong (_mod suc k) (+-zero r)

mod-shift : (k r c : ℕ) → r < suc k → (r + suc k · c) mod suc k ≡ r
mod-shift k r c r< = mod-drop k r c ∙ modIndBase k r r<

-- a residue modulo a multiple determines the residue modulo the divisor
mod-∣ : (k j x : ℕ) → suc k ∣ suc j → (x mod suc j) mod suc k ≡ x mod suc k
mod-∣ k j x h = sym
  ( x mod suc k
      ≡⟨ cong (_mod suc k) (sym (≡remainder+quotient (suc j) x)) ⟩
    ((x mod suc j) + suc j · Q) mod suc k
      ≡⟨ cong (λ z → ((x mod suc j) + z) mod suc k) p ⟩
    ((x mod suc j) + suc k · (c · Q)) mod suc k
      ≡⟨ mod-drop k (x mod suc j) (c · Q) ⟩
    (x mod suc j) mod suc k ∎ )
  where
  Q : ℕ
  Q = quotient x / suc j
  c : ℕ
  c = ∣-untrunc h .fst
  p : suc j · Q ≡ suc k · (c · Q)
  p = cong (_· Q) (sym (∣-untrunc h .snd) ∙ ·-comm c (suc k)) ∙ sym (·-assoc (suc k) c Q)

-- the converse of FinCardinality.cong-shift→∣
∣→cong-shift : (k d x : ℕ) → suc k ∣ d → x mod suc k ≡ (d + x) mod suc k
∣→cong-shift k d x h =
  sym (mod-drop k x c)
  ∙ cong (_mod suc k) (cong (x +_) (·-comm (suc k) c ∙ ∣-untrunc h .snd) ∙ +-comm x d)
  where
  c : ℕ
  c = ∣-untrunc h .fst

------------------------------------------------------------------------
-- §4  two moduli: the solution predicate, necessity, existence
------------------------------------------------------------------------

Solves₂ : (m n a b x : ℕ) → Type
Solves₂ m n a b x = (x mod m ≡ a) × (x mod n ≡ b)

isPropSolves₂ : (m n a b x : ℕ) → isProp (Solves₂ m n a b x)
isPropSolves₂ m n a b x = isProp× (isSetℕ _ _) (isSetℕ _ _)

-- (a) compatibility is necessary: both residues of x reduce to x mod g
compat-necessary : (m n : ℕ) (k : ℕ) → suc k ∣ suc m → suc k ∣ suc n
  → (x : ℕ) → (x mod suc m) mod suc k ≡ (x mod suc n) mod suc k
compat-necessary m n k k∣m k∣n x = mod-∣ k m x k∣m ∙ sym (mod-∣ k n x k∣n)

private
  ringX₁ : (a M x t : ℕ) → a + M · (x · t) ≡ a + (M · x) · t
  ringX₁ a M x t = solveℕ!

  ringX₂ : (a N y G t : ℕ) → a + (N · y + G) · t ≡ (t · G + a) + N · (y · t)
  ringX₂ a N y G t = solveℕ!

  ringX₃ : (b N M y t : ℕ) → (b + N · M) + N · (y · t) ≡ b + N · (M + y · t)
  ringX₃ b N M y t = solveℕ!


-- (b) existence from FormA: shift b by a multiple of n so that a ≤ b⁺,
-- read g ∣ (b⁺ ∸ a) off the compatibility, and put x = a + m·x·t.
solveA : (m n k : ℕ) → suc k ∣ suc m → FormA (suc m) (suc n) (suc k)
  → (a b : ℕ) → a < suc m → b < suc n → a mod suc k ≡ b mod suc k
  → Σ[ x ∈ ℕ ] Solves₂ (suc m) (suc n) a b x
solveA m n k k∣M (x , y , h) a b a< b< compat = X , Xm , Xn
  where
  M N G : ℕ
  M = suc m
  N = suc n
  G = suc k
  b⁺ : ℕ
  b⁺ = b + N · M
  a≤b⁺ : a ≤ b⁺
  a≤b⁺ = ≤-trans (<-weaken a<)
           (≤-trans (≤SumLeft {n = M} {k = n · M}) (≤SumRight {n = N · M} {k = b}))
  D : ℕ
  D = a≤b⁺ .fst
  hD : D + a ≡ b⁺
  hD = a≤b⁺ .snd
  c : ℕ
  c = ∣-untrunc k∣M .fst
  hc : c · G ≡ M
  hc = ∣-untrunc k∣M .snd
  b⁺modG : b⁺ mod G ≡ b mod G
  b⁺modG = cong (λ z → (b + z) mod G)
                (cong (N ·_) (sym hc) ∙ ·-assoc N c G ∙ ·-comm (N · c) G)
           ∙ mod-drop k b (N · c)
  G∣D : G ∣ D
  G∣D = cong-shift→∣ k D a (compat ∙ sym b⁺modG ∙ cong (_mod G) (sym hD))
  t : ℕ
  t = ∣-untrunc G∣D .fst
  ht : t · G ≡ D
  ht = ∣-untrunc G∣D .snd
  X : ℕ
  X = a + M · (x · t)
  Xm : X mod M ≡ a
  Xm = mod-shift m a (x · t) a<
  X≡ : X ≡ b + N · (M + y · t)
  X≡ = ringX₁ a M x t
     ∙ cong (λ z → a + z · t) h
     ∙ ringX₂ a N y G t
     ∙ cong (λ z → (z + a) + N · (y · t)) ht
     ∙ cong (_+ N · (y · t)) hD
     ∙ ringX₃ b N M y t
  Xn : X mod N ≡ b
  Xn = cong (_mod N) X≡ ∙ mod-shift n b (M + y · t) b<

-- FormB is FormA with the roles of the two moduli exchanged
solve-forms : (m n k : ℕ) → isGCD (suc m) (suc n) (suc k)
  → FormA (suc m) (suc n) (suc k) ⊎ FormB (suc m) (suc n) (suc k)
  → (a b : ℕ) → a < suc m → b < suc n → a mod suc k ≡ b mod suc k
  → Σ[ x ∈ ℕ ] Solves₂ (suc m) (suc n) a b x
solve-forms m n k gG (inl fa) a b a< b< compat =
  solveA m n k (gG .fst .fst) fa a b a< b< compat
solve-forms m n k gG (inr (x , y , h)) a b a< b< compat =
  s .fst , s .snd .snd , s .snd .fst
  where
  s : Σ[ x ∈ ℕ ] Solves₂ (suc n) (suc m) b a x
  s = solveA n m k (gG .fst .snd) (y , x , sym h) b a b< a< (sym compat)

-- (b) existence, with the compatibility stated at the library's gcd
solve₂ : (m n a b : ℕ) → a < suc m → b < suc n
  → a mod gcd (suc m) (suc n) ≡ b mod gcd (suc m) (suc n)
  → Σ[ x ∈ ℕ ] Solves₂ (suc m) (suc n) a b x
solve₂ m n a b a< b< compat =
  onPos P body g pg gG (B .snd .snd) (subst (λ z → a mod z ≡ b mod z) g≡ compat)
  where
  B : Bezout (suc m) (suc n)
  B = bezout (suc m) (suc n)
  g : ℕ
  g = B .fst
  gG : isGCD (suc m) (suc n) g
  gG = B .snd .fst
  g≡ : gcd (suc m) (suc n) ≡ g
  g≡ = isGCD→gcd≡ gG
  pg : 0 < g
  pg = m∣sn→z<m (gG .fst .fst)
  P : ℕ → Type
  P g' = isGCD (suc m) (suc n) g' → FormA (suc m) (suc n) g' ⊎ FormB (suc m) (suc n) g'
       → a mod g' ≡ b mod g' → Σ[ x ∈ ℕ ] Solves₂ (suc m) (suc n) a b x
  body : (k : ℕ) → P (suc k)
  body k gG' forms compat' = solve-forms m n k gG' forms a b a< b< compat'

-- reducing a solution modulo a common multiple keeps it a solution
reduce₂ : (m n j : ℕ) → suc m ∣ suc j → suc n ∣ suc j → (a b x : ℕ)
  → Solves₂ (suc m) (suc n) a b x → Solves₂ (suc m) (suc n) a b (x mod suc j)
reduce₂ m n j m∣L n∣L a b x (xm , xn) = (mod-∣ m j x m∣L ∙ xm) , (mod-∣ n j x n∣L ∙ xn)

glue₂-core : (m n j : ℕ) → IsLCM₂ (suc m) (suc n) (suc j) → (a b : ℕ)
  → a < suc m → b < suc n
  → a mod gcd (suc m) (suc n) ≡ b mod gcd (suc m) (suc n)
  → Σ[ x ∈ ℕ ] (x < suc j) × Solves₂ (suc m) (suc n) a b x
glue₂-core m n j H a b a< b< compat =
  X mod suc j , mod< j X , reduce₂ m n j (H .fst) (H .snd .fst) a b X (s .snd)
  where
  s : Σ[ x ∈ ℕ ] Solves₂ (suc m) (suc n) a b x
  s = solve₂ m n a b a< b< compat
  X : ℕ
  X = s .fst

------------------------------------------------------------------------
-- §5  uniqueness below the lcm
------------------------------------------------------------------------

unique-gen : (L x y : ℕ) → x ≤ y → y < L → ((D : ℕ) → D + x ≡ y → L ∣ D) → x ≡ y
unique-gen L x y x≤y y<L f = sym (cong (_+ x) D≡0) ∙ hD
  where
  D : ℕ
  D = x≤y .fst
  hD : D + x ≡ y
  hD = x≤y .snd
  D<L : D < L
  D<L = ≤<-trans (subst (D ≤_) hD (≤SumLeft {n = D} {k = x})) y<L
  D≡0 : D ≡ 0
  D≡0 = ∣-below L D (f D hD) D<L

unique₂-≤ : (m n L : ℕ) → ((d : ℕ) → suc m ∣ d → suc n ∣ d → L ∣ d)
  → (x y : ℕ) → x ≤ y → y < L
  → x mod suc m ≡ y mod suc m → x mod suc n ≡ y mod suc n → x ≡ y
unique₂-≤ m n L least x y x≤y y<L em en =
  unique-gen L x y x≤y y<L λ D hD →
    least D (cong-shift→∣ m D x (em ∙ cong (_mod suc m) (sym hD)))
            (cong-shift→∣ n D x (en ∙ cong (_mod suc n) (sym hD)))

unique₂-core : (m n L : ℕ) → IsLCM₂ (suc m) (suc n) L → (x y : ℕ) → x < L → y < L
  → x mod suc m ≡ y mod suc m → x mod suc n ≡ y mod suc n → x ≡ y
unique₂-core m n L H x y x< y< em en = go (splitℕ-≤ x y)
  where
  go : (x ≤ y) ⊎ (y < x) → x ≡ y
  go (inl p) = unique₂-≤ m n L (H .snd .snd) x y p y< em en
  go (inr p) = sym (unique₂-≤ m n L (H .snd .snd) y x (<-weaken p) x< (sym em) (sym en))

------------------------------------------------------------------------
-- §6  an arithmetic progression below a multiple of its step
------------------------------------------------------------------------

-- {x < suc d · q : x ≡ r mod suc d} is enumerated by k ↦ r + suc d · k, k < q
progression : (d q N r : ℕ) → N ≡ suc d · q → r < suc d
  → Fin q ≃ (Σ[ x ∈ Fin N ] (x .fst mod suc d ≡ r))
progression d q N r eN r< = isoToEquiv (iso fun inv rinv linv)
  where
  bound : (k : ℕ) → k < q → r + suc d · k < N
  bound k k<q = subst (r + suc d · k <_) (sym eN)
    (<≤-trans (<-+k {m = r} {n = suc d} {k = suc d · k} r<)
              (subst2 _≤_ (·-comm (suc k) (suc d) ∙ ·-suc (suc d) k) (·-comm q (suc d))
                      (≤-·k {m = suc k} {n = q} {k = suc d} k<q)))
  fun : Fin q → Σ[ x ∈ Fin N ] (x .fst mod suc d ≡ r)
  fun (k , k<q) = (r + suc d · k , bound k k<q) , mod-shift d r k r<
  Q : ℕ → ℕ
  Q x = quotient x / suc d
  decomp : (x : ℕ) → x mod suc d ≡ r → r + suc d · Q x ≡ x
  decomp x e = cong (_+ suc d · Q x) (sym e) ∙ ≡remainder+quotient (suc d) x
  qbound : (x : ℕ) → x < N → Q x < q
  qbound x x<N = go (splitℕ-< (Q x) q)
    where
    go : (Q x < q) ⊎ (q ≤ Q x) → Q x < q
    go (inl p) = p
    go (inr p) = Empty.rec (¬m<m
      (≤<-trans (≤-trans (subst2 _≤_ (·-comm q (suc d)) (·-comm (Q x) (suc d))
                                     (≤-·k {m = q} {n = Q x} {k = suc d} p))
                         (subst (suc d · Q x ≤_) (≡remainder+quotient (suc d) x)
                                (≤SumRight {n = suc d · Q x} {k = x mod suc d})))
                (subst (x <_) eN x<N)))
  inv : Σ[ x ∈ Fin N ] (x .fst mod suc d ≡ r) → Fin q
  inv ((x , x<N) , e) = Q x , qbound x x<N
  rinv : (z : Σ[ x ∈ Fin N ] (x .fst mod suc d ≡ r)) → fun (inv z) ≡ z
  rinv ((x , x<N) , e) = Σ≡Prop (λ _ → isSetℕ _ _) (Fin-fst-≡ (decomp x e))
  linv : (k : Fin q) → inv (fun k) ≡ k
  linv (k , k<q) = Fin-fst-≡
    (inj-sm· {m = d} (inj-m+ {m = r} (decomp (r + suc d · k) (mod-shift d r k r<))))

------------------------------------------------------------------------
-- §7  the fibre inside ℤ/(m·n) has gcd m n points
------------------------------------------------------------------------

Fibre₂ : (m n a b : ℕ) → Type
Fibre₂ m n a b = Σ[ x ∈ Fin (m · n) ] Solves₂ m n a b (x .fst)

fibre₂-L : (m n j : ℕ) → IsLCM₂ (suc m) (suc n) (suc j) → (a b : ℕ)
  → a < suc m → b < suc n
  → a mod gcd (suc m) (suc n) ≡ b mod gcd (suc m) (suc n)
  → Fin (gcd (suc m) (suc n)) ≃ Fibre₂ (suc m) (suc n) a b
fibre₂-L m n j H a b a< b< compat =
  compEquiv
    (progression j (gcd (suc m) (suc n)) (suc m · suc n) x₀
                 (sym (IsLCM₂·gcd (suc m) (suc n) (suc j) H)) x₀<)
    (Σ-cong-equiv-snd λ x →
      propBiimpl→Equiv (isSetℕ _ _) (isPropSolves₂ (suc m) (suc n) a b (x .fst)) (to x) (from x))
  where
  sol : Σ[ x ∈ ℕ ] (x < suc j) × Solves₂ (suc m) (suc n) a b x
  sol = glue₂-core m n j H a b a< b< compat
  x₀ : ℕ
  x₀ = sol .fst
  x₀< : x₀ < suc j
  x₀< = sol .snd .fst
  x₀s : Solves₂ (suc m) (suc n) a b x₀
  x₀s = sol .snd .snd
  to : (x : Fin (suc m · suc n)) → x .fst mod suc j ≡ x₀ → Solves₂ (suc m) (suc n) a b (x .fst)
  to x e = (sym (mod-∣ m j (x .fst) (H .fst)) ∙ cong (_mod suc m) e ∙ x₀s .fst)
         , (sym (mod-∣ n j (x .fst) (H .snd .fst)) ∙ cong (_mod suc n) e ∙ x₀s .snd)
  from : (x : Fin (suc m · suc n)) → Solves₂ (suc m) (suc n) a b (x .fst) → x .fst mod suc j ≡ x₀
  from x s = unique₂-core m n (suc j) H (x .fst mod suc j) x₀ (mod< j (x .fst)) x₀<
               (r .fst ∙ sym (x₀s .fst)) (r .snd ∙ sym (x₀s .snd))
    where
    r : Solves₂ (suc m) (suc n) a b (x .fst mod suc j)
    r = reduce₂ m n j (H .fst) (H .snd .fst) a b (x .fst) s

-- the k-th point of the fibre is x₀ + L · k, definitionally
fibre₂-enum : (m n j : ℕ) (H : IsLCM₂ (suc m) (suc n) (suc j)) (a b : ℕ)
  (a< : a < suc m) (b< : b < suc n)
  (compat : a mod gcd (suc m) (suc n) ≡ b mod gcd (suc m) (suc n))
  (k : Fin (gcd (suc m) (suc n)))
  → equivFun (fibre₂-L m n j H a b a< b< compat) k .fst .fst
    ≡ glue₂-core m n j H a b a< b< compat .fst + suc j · k .fst
fibre₂-enum m n j H a b a< b< compat k = refl

------------------------------------------------------------------------
-- §8  the two-moduli theorem, packaged with residues in Fin
------------------------------------------------------------------------

-- (a) necessity: a positive-moduli statement, both residues of x agree mod gcd
compat-necessary₂ : (m n : ℕ) → 0 < m → 0 < n → (x : ℕ)
  → (x mod m) mod gcd m n ≡ (x mod n) mod gcd m n
compat-necessary₂ zero    n       pm _  _ = Empty.rec (¬-<-zero pm)
compat-necessary₂ (suc m) zero    _  pn _ = Empty.rec (¬-<-zero pn)
compat-necessary₂ (suc m) (suc n) _  _  x =
  onPos (λ g → g ∣ suc m → g ∣ suc n → (x mod suc m) mod g ≡ (x mod suc n) mod g)
        (λ k k∣m k∣n → compat-necessary m n k k∣m k∣n x)
        (gcd (suc m) (suc n)) (m∣sn→z<m (G .fst .fst)) (G .fst .fst) (G .fst .snd)
  where
  G : isGCD (suc m) (suc n) (gcd (suc m) (suc n))
  G = gcdIsGCD (suc m) (suc n)

-- (b) existence below any lcm witness
glue₂ : (m n : ℕ) (a : Fin m) (b : Fin n) (L : ℕ) → IsLCM₂ m n L
  → a .fst mod gcd m n ≡ b .fst mod gcd m n
  → Σ[ x ∈ ℕ ] (x < L) × Solves₂ m n (a .fst) (b .fst) x
glue₂ zero    n       a b _ _ _ = Empty.rec (¬-<-zero (a .snd))
glue₂ (suc m) zero    a b _ _ _ = Empty.rec (¬-<-zero (b .snd))
glue₂ (suc m) (suc n) a b L H c =
  onPos (λ L → IsLCM₂ (suc m) (suc n) L
             → Σ[ x ∈ ℕ ] (x < L) × Solves₂ (suc m) (suc n) (a .fst) (b .fst) x)
        (λ j H' → glue₂-core m n j H' (a .fst) (b .fst) (a .snd) (b .snd) c)
        L (IsLCM₂-pos (suc m) (suc n) L (suc-≤-suc zero-≤) (suc-≤-suc zero-≤) H) H

-- (c) uniqueness below any lcm witness
unique₂ : (m n : ℕ) → 0 < m → 0 < n → (L : ℕ) → IsLCM₂ m n L
  → (x y : ℕ) → x < L → y < L → x mod m ≡ y mod m → x mod n ≡ y mod n → x ≡ y
unique₂ zero    n       pm _  = Empty.rec (¬-<-zero pm)
unique₂ (suc m) zero    _  pn = Empty.rec (¬-<-zero pn)
unique₂ (suc m) (suc n) _  _  = unique₂-core m n

-- (d) the fibre in ℤ/(m·n) is Fin (gcd m n), and gcd m n = m·n / L
fibre₂ : (m n : ℕ) (a : Fin m) (b : Fin n)
  → a .fst mod gcd m n ≡ b .fst mod gcd m n
  → Fin (gcd m n) ≃ Fibre₂ m n (a .fst) (b .fst)
fibre₂ zero    n       a b _ = Empty.rec (¬-<-zero (a .snd))
fibre₂ (suc m) zero    a b _ = Empty.rec (¬-<-zero (b .snd))
fibre₂ (suc m) (suc n) a b c =
  onPos (λ L → IsLCM₂ (suc m) (suc n) L
             → Fin (gcd (suc m) (suc n)) ≃ Fibre₂ (suc m) (suc n) (a .fst) (b .fst))
        (λ j H → fibre₂-L m n j H (a .fst) (b .fst) (a .snd) (b .snd) c)
        (lcm (suc m) (suc n))
        (IsLCM₂-pos (suc m) (suc n) (lcm (suc m) (suc n))
                    (suc-≤-suc zero-≤) (suc-≤-suc zero-≤) (lcm-isLCM₂ (suc m) (suc n)))
        (lcm-isLCM₂ (suc m) (suc n))

------------------------------------------------------------------------
-- §9  gcd distributes over lcm (the direction the list induction needs)
------------------------------------------------------------------------

-- gcd a (lcm b c) ∣ lcm (gcd a b) (gcd a c), for a > 0.
-- With d = gcd a L, g₁ = gcd a b, g₂ = gcd a c, h = gcd g₁ g₂, e = lcm g₁ g₂:
-- d·h divides a·a, a·b, a·c and L·g = b·c, hence g₁·g₂ = e·h; cancel h.
distrib : (a b c : ℕ) → 0 < a → (L : ℕ) → IsLCM₂ b c L
  → gcd a L ∣ lcm (gcd a b) (gcd a c)
distrib a b c pa L HL = ∣-cancel-pos h ph (subst ((d · h) ∣_) (sym eh) dh∣g₁g₂)
  where
  g g₁ g₂ d h e : ℕ
  g  = gcd b c
  g₁ = gcd a b
  g₂ = gcd a c
  d  = gcd a L
  h  = gcd g₁ g₂
  e  = lcm g₁ g₂
  Lg : L · g ≡ b · c
  Lg = IsLCM₂·gcd b c L HL
  eh : e · h ≡ g₁ · g₂
  eh = lcm·gcd g₁ g₂
  d∣a : d ∣ a
  d∣a = gcdIsGCD a L .fst .fst
  d∣L : d ∣ L
  d∣L = gcdIsGCD a L .fst .snd
  h∣a : h ∣ a
  h∣a = ∣-trans (gcdIsGCD g₁ g₂ .fst .fst) (gcdIsGCD a b .fst .fst)
  h∣b : h ∣ b
  h∣b = ∣-trans (gcdIsGCD g₁ g₂ .fst .fst) (gcdIsGCD a b .fst .snd)
  h∣c : h ∣ c
  h∣c = ∣-trans (gcdIsGCD g₁ g₂ .fst .snd) (gcdIsGCD a c .fst .snd)
  h∣g : h ∣ g
  h∣g = gcdIsGCD b c .snd h (h∣b , h∣c)
  ph : 0 < h
  ph = pos-∣ pa h∣a
  dh∣aa : (d · h) ∣ (a · a)
  dh∣aa = ∣-mult d∣a h∣a
  dh∣ca : (d · h) ∣ (c · a)
  dh∣ca = subst ((d · h) ∣_) (·-comm a c) (∣-mult d∣a h∣c)
  dh∣ab : (d · h) ∣ (a · b)
  dh∣ab = ∣-mult d∣a h∣b
  dh∣cb : (d · h) ∣ (c · b)
  dh∣cb = subst ((d · h) ∣_) (Lg ∙ ·-comm b c) (∣-mult d∣L h∣g)
  dh∣ag₂ : (d · h) ∣ (a · g₂)
  dh∣ag₂ = subst ((d · h) ∣_) (gcd-factorʳ a c a ∙ ·-comm g₂ a)
                 (gcdIsGCD (a · a) (c · a) .snd (d · h) (dh∣aa , dh∣ca))
  dh∣bg₂ : (d · h) ∣ (b · g₂)
  dh∣bg₂ = subst ((d · h) ∣_) (gcd-factorʳ a c b ∙ ·-comm g₂ b)
                 (gcdIsGCD (a · b) (c · b) .snd (d · h) (dh∣ab , dh∣cb))
  dh∣g₁g₂ : (d · h) ∣ (g₁ · g₂)
  dh∣g₁g₂ = subst ((d · h) ∣_) (gcd-factorʳ a b g₂)
                  (gcdIsGCD (a · g₂) (b · g₂) .snd (d · h) (dh∣ag₂ , dh∣bg₂))

gcd-lcm-∣ : (a b c D : ℕ) → 0 < a → (L : ℕ) → IsLCM₂ b c L
  → gcd a b ∣ D → gcd a c ∣ D → gcd a L ∣ D
gcd-lcm-∣ a b c D pa L HL h₁ h₂ =
  ∣-trans (distrib a b c pa L HL) (lcm-isLCM₂ (gcd a b) (gcd a c) .snd .snd D h₁ h₂)

------------------------------------------------------------------------
-- §10  lists of moduli
------------------------------------------------------------------------


All-map : {P Q : ℕ → Type} → ((n : ℕ) → P n → Q n) → (ns : List ℕ) → All P ns → All Q ns
All-map f []       _        = tt
All-map f (n ∷ ns) (p , ps) = f n p , All-map f ns ps

gcd-lcmList-∣ : (a : ℕ) → 0 < a → (ns : List ℕ) (D : ℕ)
  → All (λ n → gcd a n ∣ D) ns → gcd a (lcmList ns) ∣ D
gcd-lcmList-∣ a pa []       D _        = subst (_∣ D) (sym (isGCD→gcd≡ (oneGCD a))) (∣-oneˡ D)
gcd-lcmList-∣ a pa (n ∷ ns) D (h , hs) =
  gcd-lcm-∣ a n (lcmList ns) D pa (lcm n (lcmList ns)) (lcm-isLCM₂ n (lcmList ns))
            h (gcd-lcmList-∣ a pa ns D hs)

-- a modulus together with a residue below it
Modulus : Type
Modulus = Σ[ m ∈ ℕ ] Fin m

moduli : List Modulus → List ℕ
moduli = map fst

Solves : Modulus → ℕ → Type
Solves (m , a) x = x mod m ≡ a .fst

SolvesAll : List Modulus → ℕ → Type
SolvesAll []       x = Unit
SolvesAll (r ∷ rs) x = Solves r x × SolvesAll rs x

-- the note's (2), one condition per unordered pair
Compat : Modulus → Modulus → Type
Compat (m , a) (n , b) = a .fst mod gcd m n ≡ b .fst mod gcd m n

CompatWith : Modulus → List Modulus → Type
CompatWith r []       = Unit
CompatWith r (s ∷ rs) = Compat r s × CompatWith r rs

Compatible : List Modulus → Type
Compatible []       = Unit
Compatible (r ∷ rs) = CompatWith r rs × Compatible rs

product : List ℕ → ℕ
product []       = 1
product (n ∷ ns) = n · product ns

isPropSolvesAll : (rs : List Modulus) (x : ℕ) → isProp (SolvesAll rs x)
isPropSolvesAll []       x = λ _ _ → refl
isPropSolvesAll (r ∷ rs) x = isProp× (isSetℕ _ _) (isPropSolvesAll rs x)

mod-pos : (r : Modulus) → 0 < r .fst
mod-pos r = ≤-trans (suc-≤-suc zero-≤) (r .snd .snd)

lcmList-pos : (rs : List Modulus) → 0 < lcmList (moduli rs)
lcmList-pos []       = suc-≤-suc zero-≤
lcmList-pos (r ∷ rs) =
  IsLCM₂-pos (r .fst) (lcmList (moduli rs)) (lcm (r .fst) (lcmList (moduli rs)))
             (mod-pos r) (lcmList-pos rs) (lcm-isLCM₂ (r .fst) (lcmList (moduli rs)))

-- positive-moduli wrappers of §3
mod-mod : (k K : ℕ) → 0 < k → 0 < K → k ∣ K → (x : ℕ) → (x mod K) mod k ≡ x mod k
mod-mod zero    K       pk _  = Empty.rec (¬-<-zero pk)
mod-mod (suc k) zero    _  pK = Empty.rec (¬-<-zero pK)
mod-mod (suc k) (suc j) _  _  h x = mod-∣ k j x h

mod-small : (K x : ℕ) → x < K → x mod K ≡ x
mod-small zero    x x< = Empty.rec (¬-<-zero x<)
mod-small (suc k) x x< = modIndBase k x x<

shift-∣ : (m : ℕ) → 0 < m → (d x : ℕ) → x mod m ≡ (d + x) mod m → m ∣ d
shift-∣ zero    pm = Empty.rec (¬-<-zero pm)
shift-∣ (suc k) _  = cong-shift→∣ k

cong→∣ : (k : ℕ) → 0 < k → (x y : ℕ) → x ≤ y → x mod k ≡ y mod k → k ∣ (y ∸ x)
cong→∣ zero    pk = Empty.rec (¬-<-zero pk)
cong→∣ (suc j) _  x y x≤y e =
  cong-shift→∣ j (y ∸ x) x (e ∙ cong (_mod suc j) (sym (≤-∸-+-cancel x≤y)))

∣→cong : (k : ℕ) → 0 < k → (x y : ℕ) → x ≤ y → k ∣ (y ∸ x) → x mod k ≡ y mod k
∣→cong zero    pk = Empty.rec (¬-<-zero pk)
∣→cong (suc j) _  x y x≤y h =
  ∣→cong-shift j (y ∸ x) x h ∙ cong (_mod suc j) (≤-∸-+-cancel x≤y)

-- solutions transfer along a common multiple of the moduli
SolvesAll-transfer : (rs : List Modulus) (K : ℕ) → 0 < K → CommonMultiple (moduli rs) K
  → (x y : ℕ) → x mod K ≡ y mod K → SolvesAll rs y → SolvesAll rs x
SolvesAll-transfer []             K pK _          x y e _            = tt
SolvesAll-transfer ((m , a) ∷ rs) K pK (m∣K , cm) x y e (sy , srest) =
  (sym (mod-mod m K (mod-pos (m , a)) pK m∣K x) ∙ cong (_mod m) e
    ∙ mod-mod m K (mod-pos (m , a)) pK m∣K y ∙ sy)
  , SolvesAll-transfer rs K pK cm x y e srest

-- two solutions differ by a common multiple
SolvesAll→CM : (rs : List Modulus) (x y D : ℕ) → D + x ≡ y
  → SolvesAll rs x → SolvesAll rs y → CommonMultiple (moduli rs) D
SolvesAll→CM []             x y D hD _         _         = tt
SolvesAll→CM ((m , a) ∷ rs) x y D hD (sx , rx) (sy , ry) =
  shift-∣ m (mod-pos (m , a)) D x (sx ∙ sym sy ∙ cong (_mod m) (sym hD))
  , SolvesAll→CM rs x y D hD rx ry

-- (T2 c) uniqueness below the lcm of the list
glue-unique : (rs : List Modulus) (x y : ℕ)
  → x < lcmList (moduli rs) → y < lcmList (moduli rs)
  → SolvesAll rs x → SolvesAll rs y → x ≡ y
glue-unique rs x y x< y< sx sy = go (splitℕ-≤ x y)
  where
  L : ℕ
  L = lcmList (moduli rs)
  go : (x ≤ y) ⊎ (y < x) → x ≡ y
  go (inl p) = unique-gen L x y p y<
    (λ D hD → lcmList-isLCM (moduli rs) .snd D (SolvesAll→CM rs x y D hD sx sy))
  go (inr p) = sym (unique-gen L y x (<-weaken p) x<
    (λ D hD → lcmList-isLCM (moduli rs) .snd D (SolvesAll→CM rs y x D hD sy sx)))

-- (T2 a) necessity: any common solution makes every pair compatible
compat-of-solves : (r s : Modulus) (x : ℕ) → Solves r x → Solves s x → Compat r s
compat-of-solves (m , a) (n , b) x sr ss =
  cong (_mod gcd m n) (sym sr)
  ∙ compat-necessary₂ m n (mod-pos (m , a)) (mod-pos (n , b)) x
  ∙ cong (_mod gcd m n) ss

SolvesAll→CompatWith : (r : Modulus) (rs : List Modulus) (x : ℕ)
  → Solves r x → SolvesAll rs x → CompatWith r rs
SolvesAll→CompatWith r []       x sr _          = tt
SolvesAll→CompatWith r (s ∷ rs) x sr (ss , srs) =
  compat-of-solves r s x sr ss , SolvesAll→CompatWith r rs x sr srs

SolvesAll→Compatible : (rs : List Modulus) (x : ℕ) → SolvesAll rs x → Compatible rs
SolvesAll→Compatible []       x _          = tt
SolvesAll→Compatible (r ∷ rs) x (sr , srs) =
  SolvesAll→CompatWith r rs x sr srs , SolvesAll→Compatible rs x srs

-- the inductive step's compatibility: a is compatible with the glued
-- residue y modulo gcd m (lcm of the rest), because it is modulo each
-- gcd m nᵢ, and gcd distributes over the lcm (§9)
compat-with→All : (m : ℕ) (a : Fin m) (rs : List Modulus) → CompatWith (m , a) rs
  → (y : ℕ) → SolvesAll rs y
  → All (λ n → a .fst mod gcd m n ≡ y mod gcd m n) (moduli rs)
compat-with→All m a []             _        y _          = tt
compat-with→All m a ((n , b) ∷ rs) (c , cs) y (sy , sys) =
  ( c ∙ cong (_mod gcd m n) (sym sy)
      ∙ mod-mod (gcd m n) n (pos-∣ (mod-pos (m , a)) (gcdIsGCD m n .fst .fst))
                (mod-pos (n , b)) (gcdIsGCD m n .fst .snd) y )
  , compat-with→All m a rs cs y sys

compat-lcmList : (m : ℕ) → 0 < m → (a y : ℕ) (ns : List ℕ)
  → All (λ n → a mod gcd m n ≡ y mod gcd m n) ns
  → a mod gcd m (lcmList ns) ≡ y mod gcd m (lcmList ns)
compat-lcmList m pm a y ns all = go (splitℕ-≤ a y)
  where
  pg : (n : ℕ) → 0 < gcd m n
  pg n = pos-∣ pm (gcdIsGCD m n .fst .fst)
  go : (a ≤ y) ⊎ (y < a) → a mod gcd m (lcmList ns) ≡ y mod gcd m (lcmList ns)
  go (inl a≤y) = ∣→cong (gcd m (lcmList ns)) (pg (lcmList ns)) a y a≤y
    (gcd-lcmList-∣ m pm ns (y ∸ a)
      (All-map (λ n e → cong→∣ (gcd m n) (pg n) a y a≤y e) ns all))
  go (inr y<a) = sym (∣→cong (gcd m (lcmList ns)) (pg (lcmList ns)) y a (<-weaken y<a)
    (gcd-lcmList-∣ m pm ns (a ∸ y)
      (All-map (λ n e → cong→∣ (gcd m n) (pg n) y a (<-weaken y<a) (sym e)) ns all)))

-- (T2 b) THE GLUING: compatible residues glue below the lcm of the list
glue : (rs : List Modulus) → Compatible rs
  → Σ[ x ∈ ℕ ] (x < lcmList (moduli rs)) × SolvesAll rs x
glue [] _ = 0 , suc-≤-suc zero-≤ , tt
glue ((m , a) ∷ rs) (cw , crest) =
  x , g2 .snd .fst , g2 .snd .snd .fst
  , SolvesAll-transfer rs K pK cm x y (g2 .snd .snd .snd ∙ sym (mod-small K y y<)) srest
  where
  ih : Σ[ y ∈ ℕ ] (y < lcmList (moduli rs)) × SolvesAll rs y
  ih = glue rs crest
  y : ℕ
  y = ih .fst
  K : ℕ
  K = lcmList (moduli rs)
  y< : y < K
  y< = ih .snd .fst
  srest : SolvesAll rs y
  srest = ih .snd .snd
  pK : 0 < K
  pK = lcmList-pos rs
  cm : CommonMultiple (moduli rs) K
  cm = lcmList-isLCM (moduli rs) .fst
  cpt : a .fst mod gcd m K ≡ y mod gcd m K
  cpt = compat-lcmList m (mod-pos (m , a)) (a .fst) y (moduli rs)
                        (compat-with→All m a rs cw y srest)
  g2 : Σ[ x ∈ ℕ ] (x < lcm m K) × Solves₂ m K (a .fst) y x
  g2 = glue₂ m K a (y , y<) (lcm m K) (lcm-isLCM₂ m K) cpt
  x : ℕ
  x = g2 .fst

-- (T2 d) the fibre inside ℤ/P, P the product of the moduli
CM-product : (ns : List ℕ) → CommonMultiple ns (product ns)
CM-product []       = tt
CM-product (n ∷ ns) = ∣-left (product ns) , All-map (λ k h → ∣-trans h (∣-right n)) ns (CM-product ns)

lcmList∣product : (rs : List Modulus) → lcmList (moduli rs) ∣ product (moduli rs)
lcmList∣product rs = lcmList-isLCM (moduli rs) .snd (product (moduli rs)) (CM-product (moduli rs))

Fibre : List Modulus → Type
Fibre rs = Σ[ x ∈ Fin (product (moduli rs)) ] SolvesAll rs (x .fst)

fibre : (rs : List Modulus) → Compatible rs
  → (q : ℕ) → q · lcmList (moduli rs) ≡ product (moduli rs) → Fin q ≃ Fibre rs
fibre rs c q =
  onPos P body (lcmList (moduli rs)) (lcmList-pos rs)
        (lcmList-isLCM (moduli rs)) (glue rs c) (glue-unique rs)
  where
  P : ℕ → Type
  P L = IsLCM (moduli rs) L
      → Σ[ x ∈ ℕ ] (x < L) × SolvesAll rs x
      → ((x y : ℕ) → x < L → y < L → SolvesAll rs x → SolvesAll rs y → x ≡ y)
      → q · L ≡ product (moduli rs) → Fin q ≃ Fibre rs
  body : (j : ℕ) → IsLCM (moduli rs) (suc j)
       → Σ[ x ∈ ℕ ] (x < suc j) × SolvesAll rs x
       → ((x y : ℕ) → x < suc j → y < suc j → SolvesAll rs x → SolvesAll rs y → x ≡ y)
       → q · suc j ≡ product (moduli rs) → Fin q ≃ Fibre rs
  body j HL sol uniq qL =
    compEquiv
      (progression j q (product (moduli rs)) x₀ (sym qL ∙ ·-comm q (suc j)) x₀<)
      (Σ-cong-equiv-snd λ x →
        propBiimpl→Equiv (isSetℕ _ _) (isPropSolvesAll rs (x .fst)) (to x) (from x))
    where
    x₀ : ℕ
    x₀ = sol .fst
    x₀< : x₀ < suc j
    x₀< = sol .snd .fst
    x₀s : SolvesAll rs x₀
    x₀s = sol .snd .snd
    to : (x : Fin (product (moduli rs))) → x .fst mod suc j ≡ x₀ → SolvesAll rs (x .fst)
    to x e = SolvesAll-transfer rs (suc j) (suc-≤-suc zero-≤) (HL .fst) (x .fst) x₀
               (e ∙ sym (modIndBase j x₀ x₀<)) x₀s
    from : (x : Fin (product (moduli rs))) → SolvesAll rs (x .fst) → x .fst mod suc j ≡ x₀
    from x s = uniq (x .fst mod suc j) x₀ (mod< j (x .fst)) x₀<
      (SolvesAll-transfer rs (suc j) (suc-≤-suc zero-≤) (HL .fst) (x .fst mod suc j) (x .fst)
                          (mod-idempotent (x .fst)) s)
      x₀s

-- the fibre has exactly P / L points, P / L read off from L ∣ P
fibre' : (rs : List Modulus) → Compatible rs
  → Fin (∣-untrunc (lcmList∣product rs) .fst) ≃ Fibre rs
fibre' rs c = fibre rs c (∣-untrunc (lcmList∣product rs) .fst) (∣-untrunc (lcmList∣product rs) .snd)

------------------------------------------------------------------------
-- §11  controls
------------------------------------------------------------------------

r469 : List Modulus
r469 = (4 , (3 , (0 , refl))) ∷ (6 , (1 , (4 , refl))) ∷ (9 , (7 , (1 , refl))) ∷ []

compat469 : Compatible r469
compat469 = (refl , refl , tt) , (refl , tt) , (tt , tt)

lcm469 : lcmList (moduli r469) ≡ 36
lcm469 = refl

prod469 : product (moduli r469) ≡ 216
prod469 = refl

glue469 : glue r469 compat469 .fst ≡ 7
glue469 = refl

fibre469 : Fin 6 ≃ Fibre r469
fibre469 = fibre r469 compat469 6 refl

lifts469 : (k : Fin 6) → equivFun fibre469 k .fst .fst ≡ 7 + 36 · k .fst
lifts469 k = refl


-- the six lifts inside ℤ/216, listed, and each one checked as a solution

lifts469-list : map (λ k → 7 + 36 · k) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
              ≡ 7 ∷ 43 ∷ 79 ∷ 115 ∷ 151 ∷ 187 ∷ []
lifts469-list = refl

lifts469-solve : SolvesAll r469 7 × SolvesAll r469 43 × SolvesAll r469 79
               × SolvesAll r469 115 × SolvesAll r469 151 × SolvesAll r469 187
lifts469-solve =
    (refl , refl , refl , tt) , (refl , refl , refl , tt) , (refl , refl , refl , tt)
  , (refl , refl , refl , tt) , (refl , refl , refl , tt) , (refl , refl , refl , tt)

-- the note's tuple (1, 3, 7) at (4, 6, 9) is NOT compatible: 3 ≢ 7 (mod 3);
-- so by necessity (SolvesAll→Compatible) no x has these three residues
r137 : List Modulus
r137 = (4 , (1 , (2 , refl))) ∷ (6 , (3 , (2 , refl))) ∷ (9 , (7 , (1 , refl))) ∷ []

¬compat137 : ¬ Compatible r137
¬compat137 c = znots (c .snd .fst .fst)

¬solves137 : (x : ℕ) → ¬ SolvesAll r137 x
¬solves137 x s = ¬compat137 (SolvesAll→Compatible r137 x s)

-- pairwise coprime (3, 4, 5): L = P = 60, the fibre is a point
r345 : List Modulus
r345 = (3 , (2 , (0 , refl))) ∷ (4 , (3 , (0 , refl))) ∷ (5 , (4 , (0 , refl))) ∷ []

compat345 : Compatible r345
compat345 = (refl , refl , tt) , (refl , tt) , (tt , tt)

lcm345 : lcmList (moduli r345) ≡ 60
lcm345 = refl

prod345 : product (moduli r345) ≡ 60
prod345 = refl

-- (identified through uniqueness rather than by the kernel: the library's
--  well-founded `%` at 60 is slow to normalise, and the theorem is faster)
glue345 : glue r345 compat345 .fst ≡ 59
glue345 = glue-unique r345 (glue r345 compat345 .fst) 59
            (glue r345 compat345 .snd .fst) (0 , refl)
            (glue r345 compat345 .snd .snd) (refl , refl , refl , tt)

fibre345 : Fin 1 ≃ Fibre r345
fibre345 = fibre r345 compat345 1 refl

-- two moduli, directly: (4, 6) with residues (3, 1): gcd 2, lcm 12, glue 7
fibre46 : Fin 2 ≃ Fibre₂ 4 6 3 1
fibre46 = fibre₂ 4 6 (3 , (0 , refl)) (1 , (4 , refl)) refl

lifts46 : (k : Fin 2) → equivFun fibre46 k .fst .fst ≡ 7 + 12 · k .fst
lifts46 k = refl
