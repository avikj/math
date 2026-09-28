{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SensorResidueBridge
--
-- THE RESIDUE BRIDGE.  `SensorNerode` proves the
-- Nerode theorem for a family `S` of moduli in the form
--
--     Ind S a b  ⟺  lcm S ∣ dist a b
--
-- with `m ∣ dist a b` in place of equal residues `(n mod m)_{m∈S}`.
-- This module is the identification of the two.
--
-- WHAT IS CHECKED
--
--   §1  `mult-diff`      the one piece of arithmetic the bridge needs:
--                        `c + m·q ≡ m·q′` forces `c` to be a multiple of
--                        `m`.  Pure induction on the two quotients; no
--                        subtraction, no order theory, no Bezout.
--       `shift-mod`      `m ∣ c → (x + c) mod m ≡ x mod m`.
--       `mod-shift→∣`    its converse for a positive modulus, by
--                        `≡remainder+quotient` on both sides and
--                        `mult-diff` on the difference of the quotients.
--
--   §2  `dist-shift`     `dist (x + c) x ≡ c`, so the distance IS the
--                        shift, and §1 applies to it.
--       `residue-bridge` **THE BRIDGE.**  For every modulus `suc n`,
--
--                          (a mod suc n ≡ b mod suc n) ≡ (suc n ∣ dist a b)
--
--                        as a PATH OF TYPES (both sides are props).  The
--                        two directions are `mod≡→∣dist` and
--                        `∣dist→mod≡`, and they are not symmetric in
--                        their hypotheses — see §4.
--
--   §3  `SameProfile`    the note's own datum: `(a mod m)_{m∈S}` agrees
--                        with `(b mod m)_{m∈S}`, pointwise.
--       `profile≡Ind`    `SameProfile S a b ≡ Ind S a b` for a family of
--                        POSITIVE moduli — SensorNerode's `Ind`, in the
--                        note's words, as an equality of types.
--       `profile-list`   and the same for the profiles read as LISTS,
--                        `map (a mod_) S ≡ map (b mod_) S`, which is
--                        what `profile_S(n) = (n mod m)_{m∈S}` says
--                        literally.
--
--   §4  `nerode-residue`     THE NERODE THEOREM IN RESIDUE FORM.
--       `profile-collapses`  and its sharp form: the whole profile of a
--                            family collapses to ONE congruence,
--
--                              SameProfile S a b ≡ (a mod lcm S ≡ b mod lcm S).
--
--                            This is `WALK_STATE_IS_ITS_LCM.md` (absent from this repository) §1's
--                            headline — "the sensor list is a redundant
--                            presentation of one number" — in the
--                            presentation the note uses and SensorNerode
--                            avoided.  It needs `0 < lcm S`, proved here
--                            (`lcm-positive`) against the product.
--       `same-lcm→same-profile`  two families with the same lcm have the
--                            same profile relation.
--
--   §5  `zero-sensor-splits-the-readings`
--                        **THE CAVEAT, AS A COUNTEREXAMPLE.**  The
--                        positivity hypothesis in §3–§4 is not
--                        decoration and the identification is NOT
--                        unconditional: cubical's `_mod_` sets
--                        `x mod 0 = 0`, so a sensor at modulus 0 reads
--                        every number alike, while `0 ∣ dist a b` says
--                        `a ≡ b`.  For `S = [0]`, `a = 0`, `b = 1`:
--                        profiles agree, `Ind` fails.  SensorNerode's
--                        `Ind` admits such families (`lcmList` has no
--                        positivity restriction), so the "entirely
--                        standard" step is standard only for positive
--                        moduli, and this file records the boundary
--                        rather than quietly assuming past it.
--
--   §6  `Chart`          THE SENSOR PROFILE IS AN AUTOMATON STATE
--                        VECTOR.  Parameterised by the base.  With
--                        `TransportDiv.value-modw` (the Horner residue
--                        automaton computes `value w mod n`), the
--                        family's reading of a NUMERAL is the vector of
--                        final states `(modw m w)_{m∈S}`, and
--                        `chart-nerode` says that vector is determined
--                        by one division:
--
--                          ChartProfile S w v ≡ (lcm S ∣ dist (value w) (value v)).
--
--                        `decInd` and `decInd-chart` then DECIDE
--                        indistinguishability — the second by
--                        `WalkResidueBridge.decDividesℕ`, i.e. by
--                        inspecting one automaton state and never the
--                        value.  (`WalkResidueBridge.decDividesℕ-agrees`
--                        says the two decisions are equal, not merely
--                        both correct.)
--
--  * "Congruent modulo every element of S iff
--    congruent modulo lcm S" is elementary, and so is the m ∣ a−b
--    characterisation of congruence.  What is new is that the two
--    presentations are now the SAME TYPE in this development, so the
--    note's `profile_S` sentences and SensorNerode's `dist` theorems can
--    be quoted interchangeably without an unchecked step in between —
--    and that the boundary case where they are NOT the same type (§5) is
--    on the record.
------------------------------------------------------------------------

import Digits            as Dg
import TransportDiv      as TD
import WalkResidueBridge as WRB

module SensorResidueBridge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Mod
  using (_mod_ ; mod-rCancel ; ≡remainder+quotient ; remainder_/_ ; quotient_/_)
open import Cubical.Data.Nat.Divisibility
  using (_∣_ ; ∣-untrunc ; isProp∣ ; ∣-left ; ∣-right)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.List.Properties using (cons-inj₁ ; cons-inj₂)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import WalkCapacity using (All ; CommonMultiple ; IsLCM)
open import LCMExists    using (lcmList ; lcmList-isLCM)
open import SensorNerode
  using (dist ; dist-0 ; Ind ; isPropInd ; allTrans ; nerode ; nerode!
        ; nerode-unique!)
open import CoprimeSplitting using (∣-from-mod ; mod-from-∣ ; dec∣)

------------------------------------------------------------------------
-- 1.  The arithmetic the bridge needs, and no more.
--
-- SensorNerode's point is that its proof carries no arithmetic.  The
-- bridge is where the arithmetic lives, and it is one induction: a
-- number that closes the gap between two multiples of `m` is itself a
-- multiple of `m`.
------------------------------------------------------------------------

-- `c + m·q ≡ m·q′` ⟹ `c` is a multiple of `m`.  Induction on the two
-- quotients simultaneously; the successor case cancels one `m` off both
-- sides, which is `inj-m+` and nothing else.
mult-diff : (m q q′ c : ℕ) → c + m · q ≡ m · q′ → Σ[ e ∈ ℕ ] c ≡ e · m
mult-diff m zero q′ c p =
  q′ , (sym (+-zero c) ∙ cong (c +_) (0≡m·0 m) ∙ p ∙ ·-comm m q′)
mult-diff m (suc q) zero c p =
  0 , m+n≡0→m≡0×n≡0 (p ∙ sym (0≡m·0 m)) .fst
mult-diff m (suc q) (suc q′) c p = mult-diff m q q′ c step
  where
  step : c + m · q ≡ m · q′
  step = inj-m+ ( +-assoc m c (m · q)
                ∙ cong (_+ (m · q)) (+-comm m c)
                ∙ sym (+-assoc c m (m · q))
                ∙ cong (c +_) (sym (·-suc m q))
                ∙ p
                ∙ ·-suc m q′ )

-- A multiple has residue zero, at every modulus (including 0, where
-- `_mod_` is constantly 0 and the statement is vacuous).
∣→mod0 : (m c : ℕ) → m ∣ c → c mod m ≡ 0
∣→mod0 zero    c h = refl
∣→mod0 (suc n) c h = mod-from-∣ n c h

mod0→∣ : (m c : ℕ) → 0 < m → c mod m ≡ 0 → m ∣ c
mod0→∣ zero    c 0<m h = Empty.rec (¬-<-zero 0<m)
mod0→∣ (suc n) c _   h = ∣-from-mod n c h

-- Shifting the argument by a multiple of `m` does not move the residue.
shift-mod : (m x c : ℕ) → m ∣ c → (x + c) mod m ≡ x mod m
shift-mod m x c h =
    mod-rCancel m x c
  ∙ cong (λ z → (x + z) mod m) (∣→mod0 m c h)
  ∙ cong (_mod m) (+-zero x)

-- …and, at a positive modulus, only multiples of `m` fail to move it.
-- Both numbers are decomposed by `≡remainder+quotient`; the shared
-- residue cancels and `mult-diff` reads off the multiple.
mod-shift→∣ : (n x c : ℕ) → (x + c) mod (suc n) ≡ x mod (suc n) → (suc n) ∣ c
mod-shift→∣ n x c h = ∣ sol .fst , sym (sol .snd) ∣₁
  where
  m : ℕ
  m = suc n

  q₁ q₂ : ℕ
  q₁ = quotient (x + c) / m
  q₂ = quotient x / m

  eq₁ : (x mod m) + m · q₁ ≡ x + c
  eq₁ = cong (_+ m · q₁) (sym h) ∙ ≡remainder+quotient m (x + c)

  eq₂ : (x mod m) + m · q₂ ≡ x
  eq₂ = ≡remainder+quotient m x

  key : c + m · q₂ ≡ m · q₁
  key = inj-m+ {m = x mod m} ( cong ((x mod m) +_) (+-comm c (m · q₂))
               ∙ +-assoc (x mod m) (m · q₂) c
               ∙ cong (_+ c) eq₂
               ∙ sym eq₁ )

  sol : Σ[ e ∈ ℕ ] c ≡ e · m
  sol = mult-diff m q₂ q₁ c key

------------------------------------------------------------------------
-- 2.  THE BRIDGE.
--
-- `dist` is the shift: `dist (x + c) x ≡ c`.  So §1 transfers verbatim,
-- and equality of residues is divisibility of the distance.
------------------------------------------------------------------------

plus∸ : (c x : ℕ) → (c + x) ∸ x ≡ c
plus∸ c zero    = +-zero c
plus∸ c (suc x) = cong (_∸ suc x) (+-suc c x) ∙ plus∸ c x

∸-plus-zero : (x c : ℕ) → x ∸ (c + x) ≡ 0
∸-plus-zero zero    c = zero∸ (c + zero)
∸-plus-zero (suc x) c = cong (suc x ∸_) (+-suc c x) ∙ ∸-plus-zero x c

dist-shift : (x c : ℕ) → dist (x + c) x ≡ c
dist-shift x c =
  cong₂ _+_ (cong (_∸ x) (+-comm x c) ∙ plus∸ c x)
            (cong (x ∸_) (+-comm x c) ∙ ∸-plus-zero x c)
  ∙ +-zero c

dist-sym : (a b : ℕ) → dist a b ≡ dist b a
dist-sym a b = +-comm (a ∸ b) (b ∸ a)

-- Divisibility of the distance ⟹ equal residues.  TRUE AT EVERY
-- MODULUS, 0 included: this half of the bridge needs no hypothesis.
∣dist→mod≡ : (m a b : ℕ) → m ∣ dist a b → a mod m ≡ b mod m
∣dist→mod≡ m a b h with splitℕ-≤ b a
... | inl (c , cb≡a) =
      cong (_mod m) (sym b+c≡a) ∙ shift-mod m b c (subst (m ∣_) d≡c h)
      where
      b+c≡a : b + c ≡ a
      b+c≡a = +-comm b c ∙ cb≡a

      d≡c : dist a b ≡ c
      d≡c = cong (λ z → dist z b) (sym b+c≡a) ∙ dist-shift b c
... | inr a<b with <-weaken a<b
...   | (c , ca≡b) =
        sym (cong (_mod m) (sym a+c≡b) ∙ shift-mod m a c (subst (m ∣_) d≡c h))
        where
        a+c≡b : a + c ≡ b
        a+c≡b = +-comm a c ∙ ca≡b

        d≡c : dist a b ≡ c
        d≡c = dist-sym a b
            ∙ cong (λ z → dist z a) (sym a+c≡b)
            ∙ dist-shift a c

-- Equal residues ⟹ divisibility of the distance, at a POSITIVE modulus.
mod≡→∣dist : (n a b : ℕ) → a mod (suc n) ≡ b mod (suc n) → (suc n) ∣ dist a b
mod≡→∣dist n a b h with splitℕ-≤ b a
... | inl (c , cb≡a) =
      subst ((suc n) ∣_) (sym d≡c)
        (mod-shift→∣ n b c (cong (_mod (suc n)) b+c≡a ∙ h))
      where
      b+c≡a : b + c ≡ a
      b+c≡a = +-comm b c ∙ cb≡a

      d≡c : dist a b ≡ c
      d≡c = cong (λ z → dist z b) (sym b+c≡a) ∙ dist-shift b c
... | inr a<b with <-weaken a<b
...   | (c , ca≡b) =
        subst ((suc n) ∣_) (sym d≡c)
          (mod-shift→∣ n a c (cong (_mod (suc n)) a+c≡b ∙ sym h))
        where
        a+c≡b : a + c ≡ b
        a+c≡b = +-comm a c ∙ ca≡b

        d≡c : dist a b ≡ c
        d≡c = dist-sym a b
            ∙ cong (λ z → dist z a) (sym a+c≡b)
            ∙ dist-shift a c

-- THE BRIDGE, as a path of types: both sides are propositions.
residue-bridge : (n a b : ℕ)
               → (a mod (suc n) ≡ b mod (suc n)) ≡ ((suc n) ∣ dist a b)
residue-bridge n a b =
  hPropExt (isSetℕ _ _) isProp∣ (mod≡→∣dist n a b) (∣dist→mod≡ (suc n) a b)

-- the same with the positivity as a hypothesis rather than a pattern
residue-bridge⁺ : (m a b : ℕ) → 0 < m
                → (a mod m ≡ b mod m) ≡ (m ∣ dist a b)
residue-bridge⁺ zero    a b 0<m = Empty.rec (¬-<-zero 0<m)
residue-bridge⁺ (suc n) a b _   = residue-bridge n a b

mod≡→∣dist⁺ : (m a b : ℕ) → 0 < m → a mod m ≡ b mod m → m ∣ dist a b
mod≡→∣dist⁺ zero    a b 0<m h = Empty.rec (¬-<-zero 0<m)
mod≡→∣dist⁺ (suc n) a b _   h = mod≡→∣dist n a b h

------------------------------------------------------------------------
-- 3.  THE PROFILE.
--
-- The note's datum: the vector of residues.  `SameProfile` is its
-- equality, pointwise; `profile` is the vector itself and `profile-list`
-- says the two readings agree.
------------------------------------------------------------------------

SameProfile : List ℕ → ℕ → ℕ → Type
SameProfile S a b = All (λ m → a mod m ≡ b mod m) S

Positive : List ℕ → Type
Positive S = All (0 <_) S

isPropSameProfile : (S : List ℕ) (a b : ℕ) → isProp (SameProfile S a b)
isPropSameProfile []      a b = isPropUnit
isPropSameProfile (m ∷ S) a b = isProp× (isSetℕ _ _) (isPropSameProfile S a b)

sameProfile→ind : (S : List ℕ) → Positive S → (a b : ℕ)
                → SameProfile S a b → Ind S a b
sameProfile→ind []      _          a b _        = tt
sameProfile→ind (m ∷ S) (0<m , ps) a b (e , es) =
  mod≡→∣dist⁺ m a b 0<m e , sameProfile→ind S ps a b es

ind→sameProfile : (S : List ℕ) (a b : ℕ) → Ind S a b → SameProfile S a b
ind→sameProfile []      a b _        = tt
ind→sameProfile (m ∷ S) a b (d , ds) =
  ∣dist→mod≡ m a b d , ind→sameProfile S a b ds

-- THE IDENTIFICATION.
profile≡Ind : (S : List ℕ) → Positive S → (a b : ℕ)
            → SameProfile S a b ≡ Ind S a b
profile≡Ind S pos a b =
  hPropExt (isPropSameProfile S a b) (isPropInd S a b)
    (sameProfile→ind S pos a b) (ind→sameProfile S a b)

-- …and the profile read literally, as the note writes it: the LIST
-- `(n mod m)_{m∈S}`.  Equality of the two lists is the pointwise
-- statement, by `cons-inj₁`/`cons-inj₂` one way and `cong₂` the other.
profile : List ℕ → ℕ → List ℕ
profile S n = map (n mod_) S

profile-list : (S : List ℕ) (a b : ℕ)
             → (profile S a ≡ profile S b) ≡ SameProfile S a b
profile-list S a b =
  hPropExt (isOfHLevelList 0 isSetℕ _ _) (isPropSameProfile S a b)
           (to S) (from S)
  where
  open import Cubical.Data.List.Properties using (isOfHLevelList)

  to : (S : List ℕ) → profile S a ≡ profile S b → SameProfile S a b
  to []      _ = tt
  to (m ∷ S) p = cons-inj₁ p , to S (cons-inj₂ p)

  from : (S : List ℕ) → SameProfile S a b → profile S a ≡ profile S b
  from []      _        = refl
  from (m ∷ S) (e , es) = cong₂ _∷_ e (from S es)

------------------------------------------------------------------------
-- 4.  THE NERODE THEOREM IN RESIDUE FORM, and the collapse.
------------------------------------------------------------------------

-- Positivity of the lcm.  The product of a family of positive numbers
-- is a positive common multiple, and the lcm divides it, so the lcm
-- cannot be 0.  (`lcmList` has no positivity restriction, which is why
-- this has to be proved rather than assumed — see §5.)
prod : List ℕ → ℕ
prod []       = 1
prod (x ∷ xs) = x · prod xs

prod-common : (S : List ℕ) → CommonMultiple S (prod S)
prod-common []       = tt
prod-common (x ∷ xs) = ∣-left (prod xs) , allTrans xs (prod-common xs) (∣-right x)

0<· : (x y : ℕ) → 0 < x → 0 < y → 0 < (x · y)
0<· zero    y       0<x 0<y = Empty.rec (¬-<-zero 0<x)
0<· (suc x) zero    0<x 0<y = Empty.rec (¬-<-zero 0<y)
0<· (suc x) (suc y) _   _   = suc-≤-suc zero-≤

prod-positive : (S : List ℕ) → Positive S → 0 < prod S
prod-positive []       _          = suc-≤-suc zero-≤
prod-positive (x ∷ xs) (0<x , ps) = 0<· x (prod xs) 0<x (prod-positive xs ps)

0∣→≡0 : (n : ℕ) → 0 ∣ n → n ≡ 0
0∣→≡0 n h = sym (∣-untrunc h .snd) ∙ sym (0≡m·0 (∣-untrunc h .fst))

≢0→0< : (x : ℕ) → ¬ (x ≡ 0) → 0 < x
≢0→0< zero    h = Empty.rec (h refl)
≢0→0< (suc x) _ = suc-≤-suc zero-≤

lcm-positive : (S : List ℕ) → Positive S → 0 < lcmList S
lcm-positive S pos = ≢0→0< (lcmList S) ¬0
  where
  L∣prod : lcmList S ∣ prod S
  L∣prod = lcmList-isLCM S .snd (prod S) (prod-common S)

  ¬0 : ¬ (lcmList S ≡ 0)
  ¬0 p = ¬-<-zero
           (subst (0 <_) (0∣→≡0 (prod S) (subst (_∣ prod S) p L∣prod))
                  (prod-positive S pos))

-- The Nerode theorem, in the note's presentation.
nerode-residue : (S : List ℕ) → Positive S → (a b : ℕ)
               → SameProfile S a b ≡ (lcmList S ∣ dist a b)
nerode-residue S pos a b = profile≡Ind S pos a b ∙ nerode! S a b

-- THE COLLAPSE.  The whole vector of residues is one residue.  This is
-- `WALK_STATE_IS_ITS_LCM.md` (absent from this repository) §1's headline sentence, as a type equality,
-- with no divisibility anywhere in it.
profile-collapses : (S : List ℕ) → Positive S → (a b : ℕ)
                  → SameProfile S a b
                  ≡ (a mod lcmList S ≡ b mod lcmList S)
profile-collapses S pos a b =
    nerode-residue S pos a b
  ∙ sym (residue-bridge⁺ (lcmList S) a b (lcm-positive S pos))

-- …hence two families with the same lcm have the same profile relation,
-- which is SensorNerode §4 with `Ind` replaced by the note's datum.
same-lcm→same-profile : (S T : List ℕ) → Positive S → Positive T
                      → lcmList S ≡ lcmList T
                      → (a b : ℕ) → SameProfile S a b ≡ SameProfile T a b
same-lcm→same-profile S T pS pT p a b =
    profile-collapses S pS a b
  ∙ (λ i → (a mod p i) ≡ (b mod p i))
  ∙ sym (profile-collapses T pT a b)

-- …and conversely the profile relation determines the lcm, by
-- SensorNerode's `nerode-unique!` composed with §3.
profile-determines-lcm : (S T : List ℕ) → Positive S → Positive T
                       → ((a b : ℕ) → SameProfile S a b ≡ SameProfile T a b)
                       → lcmList S ≡ lcmList T
profile-determines-lcm S T pS pT h =
  nerode-unique! S T
    (λ a b → sym (profile≡Ind S pS a b) ∙ h a b ∙ profile≡Ind T pT a b)

------------------------------------------------------------------------
-- 5.  WHERE THE BRIDGE IS FALSE, exhibited.
--
-- The positivity hypothesis is load-bearing and the "entirely standard"
-- identification is conditional.  cubical's `_mod_` is total by the
-- convention `x mod 0 = 0` (Cubical.Data.Nat.Mod, first comment), so a
-- sensor at modulus 0 reads every number as 0 and distinguishes
-- nothing; `Ind` at modulus 0 says `0 ∣ dist a b`, i.e. `a ≡ b`, and
-- distinguishes everything.  `SensorNerode.Ind` admits the family [0]
-- (nothing there excludes it, and `lcmList [0] = 0`), so this is a real
-- boundary of the bridge and not a convention artefact.
------------------------------------------------------------------------

zero-sensor-splits-the-readings :
  SameProfile (0 ∷ []) 0 1 × (¬ Ind (0 ∷ []) 0 1)
zero-sensor-splits-the-readings =
  (refl , tt) , λ ind → snotz (0∣→≡0 1 (ind .fst))

------------------------------------------------------------------------
-- 6.  THE PROFILE IS AN AUTOMATON STATE VECTOR.
--
-- `TransportDiv.modw` is the Horner residue automaton on digit words
-- and `value-modw` proves `modw n w ≡ value w mod n`.  So the sensor
-- family's reading of a numeral is literally the vector of the family's
-- automata's final states — one state per modulus, one pass per digit —
-- and §4 says that vector is determined by a single division.
------------------------------------------------------------------------

module Chart (k : ℕ) where
  private
    module D = Dg k
    module T = TD k
    module W = WRB k

  open D using (Word ; value ; digits ; value-digits)
  open T using (modw ; value-modw)

  -- the family's reading of a numeral, as computed
  ChartProfile : List ℕ → Word → Word → Type
  ChartProfile S w v = All (λ m → modw m w ≡ modw m v) S

  -- …is the family's reading of the number it denotes.  Pointwise
  -- `value-modw`, transported through the list: the two `All`s are
  -- connected by a path, not by a pair of implications.
  chart≡profile : (S : List ℕ) (w v : Word)
                → ChartProfile S w v ≡ SameProfile S (value w) (value v)
  chart≡profile []      w v = refl
  chart≡profile (m ∷ S) w v i =
    (value-modw m w i ≡ value-modw m v i) × chart≡profile S w v i

  -- THE NERODE THEOREM ON THE CHART.
  chart-nerode : (S : List ℕ) → Positive S → (w v : Word)
               → ChartProfile S w v ≡ (lcmList S ∣ dist (value w) (value v))
  chart-nerode S pos w v =
    chart≡profile S w v ∙ nerode-residue S pos (value w) (value v)

  chart-nerode-ℕ : (S : List ℕ) → Positive S → (a b : ℕ)
                 → ChartProfile S (digits a) (digits b) ≡ (lcmList S ∣ dist a b)
  chart-nerode-ℕ S pos a b =
      chart-nerode S pos (digits a) (digits b)
    ∙ (λ i → lcmList S ∣ dist (value-digits a i) (value-digits b i))

  -- Indistinguishability is DECIDED on the chart: `decDividesℕ` inspects
  -- the automaton's final state on the numeral of `dist a b` and never
  -- the value.  The `IsLCM S (suc n)` argument is where the family's
  -- state is named; `WalkResidueBridge.decDividesℕ-agrees` says this is
  -- the same decision as `dec∣`, so nothing downstream is disturbed.
  decInd-chart : (S : List ℕ) (n : ℕ) → IsLCM S (suc n)
               → (a b : ℕ) → Dec (Ind S a b)
  decInd-chart S n isL a b =
    subst Dec (sym (nerode isL a b)) (W.decDividesℕ n (dist a b))

-- Off the chart, the same decision from the family's own positivity.
decInd : (S : List ℕ) → Positive S → (a b : ℕ) → Dec (Ind S a b)
decInd S pos a b =
  subst Dec (sym (nerode! S a b))
    (dec∣ (lcmList S) (dist a b) (lcm-positive S pos))

decSameProfile : (S : List ℕ) → Positive S → (a b : ℕ) → Dec (SameProfile S a b)
decSameProfile S pos a b =
  subst Dec (sym (profile≡Ind S pos a b)) (decInd S pos a b)
