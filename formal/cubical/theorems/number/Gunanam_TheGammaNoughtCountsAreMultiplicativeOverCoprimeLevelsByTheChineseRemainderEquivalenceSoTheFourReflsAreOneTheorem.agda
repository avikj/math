{-# OPTIONS --cubical --safe --no-import-sorts #-}
------------------------------------------------------------------------------
-- Gunanam (गुणनम्, "multiplication"):
--   the Γ₀ counts of Gamma0Index are multiplicative over coprime levels, by
--   the Chinese-remainder equivalence — so its four crt* refls are one theorem.
--
-- SOURCE 1 — formal/cubical/theorems/number/Gamma0Index.agda, §4b, verbatim:
--
--   -- 4b.  Multiplicativity over coprime levels — the Chinese-remainder half of
--   --      the theorem, verified rather than assumed.  12 = 4·3, 10 = 2·5.
--
--   crtGL12 : cnt2 12 1 ≡ cnt2 4 1 · cnt2 3 1
--   crtGL12 = refl
--
--   crtΓ12 : cnt2 12 12 ≡ cnt2 4 4 · cnt2 3 3
--   crtΓ12 = refl
--
--   crtGL10 : cnt2 10 1 ≡ cnt2 2 1 · cnt2 5 1
--   crtGL10 = refl
--
--   crtΓ10 : cnt2 10 10 ≡ cnt2 2 2 · cnt2 5 5
--   crtΓ10 = refl
--
-- and the definition of what is counted, verbatim from its §3:
--
--   -- `cnt2 n m₂₁`      counts A ∈ GL₂(ℤ/n) with m₂₁ ∣ A₂₁.
--   ...
--   det2 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
--   det2 n a b c d = ((a · d) + (n · n) ∸ (b · c)) % n
--
--   cnt2 : ℕ → ℕ → ℕ
--   cnt2 n m21 =
--     Σ< n λ a → Σ< n λ b → Σ< n λ c → Σ< n λ d →
--       ind (isU n (det2 n a b c d)) · ind (m21 ∣? c)
--
-- SOURCE 2 — notes/GAMMA0_INDEX_EXPONENT.md (absent from this repository) (main), verbatim:
--
--   1. **Lemma 3.2 (multiplicativity / CRT).** Needs the bijection
--      `ℤ/mn ≃ ℤ/m × ℤ/n` for coprime `m,n` *plus* transport of counts along it.
--      Cubical v0.9 has `Data.Nat.GCD` (Euclid, `isGCD`), `Divisibility` and
--      `Coprime`, and **no Chinese remainder statement of any form** —
--      `grep -ril chinese Cubical/` over the v0.9 tree is empty. I checked.
--
--   Concretely, the cheapest next step is not more of this note's kind of work: it
--   is a `Fin`-cardinality layer (a count that transports along an equivalence),
--   after which CRT multiplicativity — Lemma 3.2, the "accessible part" — becomes
--   a one-file target and `Gamma0Index`'s four `crt*` `refl`s become a theorem.
--
-- WHAT IS PROVED (hypotheses are arguments, never comments).  For every
-- m, n ≥ 1 with isGCD m n 1:
--
--   crt-GL : cnt2 (m · n) 1       ≡ cnt2 m 1 · cnt2 n 1                  (T1)
--   crt-Γ  : cnt2 (m · n) (m · n) ≡ cnt2 m m · cnt2 n n                  (T2)
--
-- both instances of one statement, `cnt2-crt`, whose lower-left mask is any
-- triple (k, kₘ, kₙ) for which "k ∣ c" is the conjunction of "kₘ ∣ c mod m"
-- and "kₙ ∣ c mod n" on 0 ≤ c < m·n.  The four refls of Gamma0Index are
-- recovered as instances at 12 = 4·3 and 10 = 2·5, and each is shown EQUAL,
-- as a path in ℕ, to the corresponding instance of the theorem (§9).
--
-- THE ROUTE TAKEN.  `cnt2 N k` is a Boolean scan (a fourfold Σ< of 0/1
-- indicators over ℕ), not a cardinality.  So:
--
--   §1  the Boolean/builtin layer: `_==_`, `and`, and the fact that the
--       builtin remainder `%` of Gamma0Index is cubical's `_mod_` (they share
--       the kernel primitive `mod-helper`, so `stepGCD` from Cubical.Data.Nat.GCD
--       is exactly the Euclid step of Gamma0Index's fuelled `gcdF`);
--   §2  Gamma0Index's `isU n x` (i.e. `gcd! x n == 1`) is `isGCD x n 1`;
--   §3  `isGCD x (m·n) 1  ⟺  isGCD x m 1 × isGCD x n 1` (no coprimality of
--       m, n is needed for this: Euclid's lemma from `isGCD-multʳ`), and gcd is
--       invariant under reduction of its first argument mod the second;
--   §4  the determinant congruence: det2 (m·n) a b c d and det2 m (a mod m) …
--       agree mod m, through the truncated subtraction and the padding term;
--   §5  hence the ENTRYWISE Boolean identity
--         isU (mn) (det2 (mn) a b c d)
--           ≡ isU m (det2 m ā b̄ c̄ d̄) and isU n (det2 n ã b̃ c̃ d̃)
--       and the mask identities for k = 1 and k = N (the latter via
--       `gauss` of FinCardinality: c ≡ 0 mod m and mod n forces c = 0 below mn);
--   §6  the Fin-cardinality layer: a Σ< of ℕ-valued summands IS the card of a
--       Σ-type over Fin N whose fibres have those cards (`cardΣ-Fin`), so
--       `cnt2 N k ≡ card (C N k)` for an explicit FinSet `C N k` of matrices;
--   §7  the counted set at level m·n is EQUIVALENT to the product of the
--       counted sets at m and n: `crtEquiv` (FinCardinality) on each of the
--       four entries, §5 on the fibre, and a shuffle of the Σ's;
--   §8  transport the count: `cardEquiv` and `card×`.
--
-- The CRT equivalence itself is FinCardinality.crtEquiv (unplaced/), whose
-- header records that cubical v0.9 has none; nothing here re-proves it.
-- §10 has controls: coprimality is load-bearing (the statement is FALSE at
-- 4 = 2·2 and the module proves the negation), and the theorem fires at a
-- level (15 = 3·5) that Gamma0Index never enumerated.
--
-- Nothing is postulated.  The only kernel enumerations are in the controls
-- and in the identification with Gamma0Index's own refls.
------------------------------------------------------------------------------
module Gunanam_TheGammaNoughtCountsAreMultiplicativeOverCoprimeLevelsByTheChineseRemainderEquivalenceSoTheFourReflsAreOneTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (pathToEquiv)

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using (_⊎_; inl; inr; Σ⊎≃; ⊎-equiv)
open import Cubical.Data.Bool using (Bool; true; false; _and_; false≢true)

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD

open import Cubical.Data.Fin
open import Cubical.Data.Fin.Properties using (n%k≡n[modk]; n%sk<sk)
import Cubical.Data.SumFin as SFin

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Cardinality

open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as Prop

open import Agda.Builtin.Nat using (_==_; mod-helper)

open import Gamma0Index
  using (ite; ind; _∣?_; gcdF; gcd!; isU; Σ<; det2; cnt2;
         crtGL12; crtΓ12; crtGL10; crtΓ10)
  renaming (_%_ to _%ᴳ_)
open import FinCardinality using (FinSetFin; gauss; mod0→∣; crtEquiv)

------------------------------------------------------------------------------
-- §1  Booleans, the builtin `_==_`, and `%` versus `mod`.
--
-- Gamma0Index's `n % suc m` is `mod-helper 0 m n m`, the kernel primitive;
-- cubical's `Cubical.Data.Nat.Base` re-exports the same builtin `_%_`, so the
-- two agree definitionally at every positive modulus.  What must be PROVED is
-- that this builtin remainder is cubical's `_mod_` (Cubical.Data.Nat.Mod),
-- which is defined by `+induction` and carries the congruence lemmas.
------------------------------------------------------------------------------

Bool-ext : {x y : Bool} → (x ≡ true → y ≡ true) → (y ≡ true → x ≡ true) → x ≡ y
Bool-ext {true}  {true}  _ _ = refl
Bool-ext {true}  {false} f _ = Empty.rec (false≢true (f refl))
Bool-ext {false} {true}  _ g = Empty.rec (false≢true (g refl))
Bool-ext {false} {false} _ _ = refl

and-true→ : (x y : Bool) → (x and y) ≡ true → (x ≡ true) × (y ≡ true)
and-true→ true  y p = refl , p
and-true→ false y p = Empty.rec (false≢true p)

→and-true : (x y : Bool) → x ≡ true → y ≡ true → (x and y) ≡ true
→and-true true  y _ q = q
→and-true false y p _ = Empty.rec (false≢true p)

==-refl : (x : ℕ) → (x == x) ≡ true
==-refl zero    = refl
==-refl (suc x) = ==-refl x

==→≡ : (x y : ℕ) → (x == y) ≡ true → x ≡ y
==→≡ zero    zero    _ = refl
==→≡ zero    (suc y) p = Empty.rec (false≢true p)
==→≡ (suc x) zero    p = Empty.rec (false≢true p)
==→≡ (suc x) (suc y) p = cong suc (==→≡ x y p)

≡→== : (x y : ℕ) → x ≡ y → (x == y) ≡ true
≡→== x y p = subst (λ z → (x == z) ≡ true) p (==-refl x)

-- Gamma0Index's `%` is the kernel primitive `mod-helper`; its invariant
-- (Agda's own comment in Agda.Builtin.Nat) is: for acc + j ≡ s,
--     mod-helper acc s x j ≡ (acc + x) mod (suc s).
mod-helper-inv : (x acc j s : ℕ) → acc + j ≡ s
  → mod-helper acc s x j ≡ (acc + x) mod suc s
mod-helper-inv zero acc j s e =
  sym (cong (_mod suc s) (+-zero acc)
       ∙ modIndBase s acc (suc-≤-suc (subst (acc ≤_) e (≤SumLeft {n = acc} {k = j}))))
mod-helper-inv (suc x) acc zero s e =
    mod-helper-inv x 0 s s refl
  ∙ mod-lUnit (suc s) x
  ∙ cong (_mod suc s) (cong (λ z → suc (z + x)) (sym (sym (+-zero acc) ∙ e)) ∙ sym (+-suc acc x))
mod-helper-inv (suc x) acc (suc j) s e =
    mod-helper-inv x (suc acc) j s (sym (+-suc acc j) ∙ e)
  ∙ cong (_mod suc s) (sym (+-suc acc x))

%ᴳ≡mod : (x k : ℕ) → x %ᴳ suc k ≡ x mod suc k
%ᴳ≡mod x k = mod-helper-inv x 0 k k refl

-- the library's `%` (Cubical.Data.Fin.Properties, by well-founded
-- induction — the one `stepGCD` is stated with) is also cubical's `mod`
lib%≡mod : (x k : ℕ) → x % suc k ≡ x mod suc k
lib%≡mod x k = sym (
    x mod suc k
      ≡⟨ cong (_mod suc k) (sym (n%k≡n[modk] x (suc k) .snd)) ⟩
    (q · suc k + x % suc k) mod suc k
      ≡⟨ cong (_mod suc k) (+-comm (q · suc k) (x % suc k)) ⟩
    (x % suc k + q · suc k) mod suc k
      ≡⟨ mod-rCancel (suc k) (x % suc k) (q · suc k) ⟩
    (x % suc k + (q · suc k) mod suc k) mod suc k
      ≡⟨ cong (λ z → (x % suc k + z) mod suc k) (zero-charac-gen (suc k) q) ⟩
    (x % suc k + 0) mod suc k
      ≡⟨ cong (_mod suc k) (+-zero (x % suc k)) ⟩
    (x % suc k) mod suc k
      ≡⟨ modIndBase k (x % suc k) (n%sk<sk x k) ⟩
    x % suc k ∎)
  where
    q : ℕ
    q = n%k≡n[modk] x (suc k) .fst

------------------------------------------------------------------------------
-- §2  Gamma0Index's fuelled Euclid computes a gcd, and `isU` is `isGCD _ _ 1`.
------------------------------------------------------------------------------

-- enough fuel (more than the second argument) and `gcdF` is a GCD; the
-- inductive step is cubical's `stepGCD`, because the remainder is the same
-- kernel primitive on both sides.
gcdF-isGCD : (fuel a b : ℕ) → b < fuel → isGCD a b (gcdF fuel a b)
gcdF-isGCD zero    a b       h = Empty.rec (¬-<-zero h)
gcdF-isGCD (suc k) a zero    _ = zeroGCD a
gcdF-isGCD (suc k) a (suc b) h =
  stepGCD (subst (λ r → isGCD (suc b) r (gcdF k (suc b) (a %ᴳ suc b)))
                 (%ᴳ≡mod a b ∙ sym (lib%≡mod a b))
                 (gcdF-isGCD k (suc b) (a %ᴳ suc b)
                   (<≤-trans (subst (_< suc b) (sym (%ᴳ≡mod a b)) (mod< b a))
                             (pred-≤-pred h))))

gcd!-isGCD : (a b : ℕ) → isGCD a b (gcd! a b)
gcd!-isGCD a b = gcdF-isGCD (suc (a + b)) a b (suc-≤-suc (≤SumRight {n = b} {k = a}))

isU→isGCD : (M X : ℕ) → isU M X ≡ true → isGCD X M 1
isU→isGCD M X p = subst (isGCD X M) (==→≡ (gcd! X M) 1 p) (gcd!-isGCD X M)

isGCD→isU : (M X : ℕ) → isGCD X M 1 → isU M X ≡ true
isGCD→isU M X h =
  ≡→== (gcd! X M) 1 (cong fst (isPropGCD (gcd! X M , gcd!-isGCD X M) (1 , h)))

------------------------------------------------------------------------------
-- §3  Coprimality to a product, and invariance of gcd under reduction.
------------------------------------------------------------------------------

-- Euclid's lemma, from the library's `isGCD-multʳ`.
euclidLemma : (d m n : ℕ) → isGCD d m 1 → d ∣ (m · n) → d ∣ n
euclidLemma d m n cop h =
  subst (d ∣_) (·-identityˡ n) (isGCD-multʳ n cop .snd d (∣-left n , h))

gcd1-split : (X m n : ℕ) → isGCD X (m · n) 1 → isGCD X m 1 × isGCD X n 1
gcd1-split X m n (_ , gr) =
    ((∣-oneˡ X , ∣-oneˡ m) , λ d dd → gr d (fst dd , ∣-trans (snd dd) (∣-left n)))
  , ((∣-oneˡ X , ∣-oneˡ n) , λ d dd → gr d (fst dd , ∣-trans (snd dd) (∣-right m)))

gcd1-join : (X m n : ℕ) → isGCD X m 1 → isGCD X n 1 → isGCD X (m · n) 1
gcd1-join X m n (_ , grm) (_ , grn) =
  (∣-oneˡ X , ∣-oneˡ (m · n)) ,
  λ d dd → grn d (fst dd , euclidLemma d m n (dm-cop d (fst dd)) (snd dd))
  where
    dm-cop : (d : ℕ) → d ∣ X → isGCD d m 1
    dm-cop d d∣X = (∣-oneˡ d , ∣-oneˡ m) , λ e ee → grm e (∣-trans (fst ee) d∣X , snd ee)

-- gcd (x mod M) M and gcd x M are the same gcd (M positive).
gcdMod→ : (k x d : ℕ) → isGCD (x mod suc k) (suc k) d → isGCD x (suc k) d
gcdMod→ k x d h =
  stepGCD (subst (λ r → isGCD (suc k) r d) (sym (lib%≡mod x k)) (symGCD h))

gcdMod← : (k x d : ℕ) → isGCD x (suc k) d → isGCD (x mod suc k) (suc k) d
gcdMod← k x d h =
  subst (isGCD (x mod suc k) (suc k)) g≡d (gcd!-isGCD (x mod suc k) (suc k))
  where
    g≡d : gcd! (x mod suc k) (suc k) ≡ d
    g≡d = cong fst
      (isPropGCD (_ , gcdMod→ k x _ (gcd!-isGCD (x mod suc k) (suc k))) (d , h))

------------------------------------------------------------------------------
-- §4  The determinant congruence.
--
-- `det2 N a b c d = ((a · d) + (N · N) ∸ (b · c)) % N`: the padding N·N keeps
-- the truncated subtraction exact.  Reducing the entries mod M and re-padding
-- with M·M changes the pre-reduction value, but not its residue mod M.
------------------------------------------------------------------------------

-- the padded determinant before reduction (definitionally det2's argument)
dpre : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
dpre N a b c d = (a · d) + (N · N) ∸ (b · c)

-- addition mod M is cancellative
mod-cancelʳ : (k x y t : ℕ)
  → (x + t) mod suc k ≡ (y + t) mod suc k → x mod suc k ≡ y mod suc k
mod-cancelʳ k x y t e =
  lem x ∙ cong (λ z → (z + k · t) mod suc k) e ∙ sym (lem y)
  where
    lem : (x : ℕ) → x mod suc k ≡ ((x + t) mod suc k + k · t) mod suc k
    lem x =
      x mod suc k
        ≡⟨ cong (_mod suc k) (sym (+-zero x)) ⟩
      (x + 0) mod suc k
        ≡⟨ cong (λ z → (x + z) mod suc k) (sym (zero-charac-gen (suc k) t)) ⟩
      (x + (t · suc k) mod suc k) mod suc k
        ≡⟨ sym (mod-rCancel (suc k) x (t · suc k)) ⟩
      (x + t · suc k) mod suc k
        ≡⟨ cong (λ z → (x + z) mod suc k) (·-comm t (suc k)) ⟩
      (x + (t + k · t)) mod suc k
        ≡⟨ cong (_mod suc k) (+-assoc x t (k · t)) ⟩
      ((x + t) + k · t) mod suc k
        ≡⟨ mod-lCancel (suc k) (x + t) (k · t) ⟩
      ((x + t) mod suc k + k · t) mod suc k ∎

-- b, c ≤ N gives b·c ≤ N·N
·-≤ : (b c N : ℕ) → b ≤ N → c ≤ N → b · c ≤ N · N
·-≤ b c N hb hc =
  ≤-trans (≤-·k {k = c} hb) (subst (_≤ N · N) (·-comm c N) (≤-·k {k = N} hc))

dpre-mod : (k : ℕ) (a b c d P a' b' c' d' P' : ℕ)
  → b · c ≤ a · d + P → b' · c' ≤ a' · d' + P'
  → a mod suc k ≡ a' mod suc k → b mod suc k ≡ b' mod suc k
  → c mod suc k ≡ c' mod suc k → d mod suc k ≡ d' mod suc k
  → P mod suc k ≡ 0 → P' mod suc k ≡ 0
  → (a · d + P ∸ b · c) mod suc k ≡ (a' · d' + P' ∸ b' · c') mod suc k
dpre-mod k a b c d P a' b' c' d' P' hb hb' ea eb ec ed eP eP' =
  mod-cancelʳ k (a · d + P ∸ b · c) (a' · d' + P' ∸ b' · c') t
    (front a b c d P hb
     ∙ (λ i → ((ea i · ed i) mod M + (eP ∙ sym eP') i) mod M)
     ∙ sym (front a' b' c' d' P' hb')
     ∙ (λ i → ((a' · d' + P' ∸ b' · c') + (eb (~ i) · ec (~ i)) mod M) mod M))
  where
    M : ℕ
    M = suc k

    t : ℕ
    t = ((b mod M) · (c mod M)) mod M

    front : (a b c d P : ℕ) → b · c ≤ a · d + P
          → ((a · d + P ∸ b · c) + ((b mod M) · (c mod M)) mod M) mod M
          ≡ (((a mod M) · (d mod M)) mod M + P mod M) mod M
    front a b c d P hb =
      ((a · d + P ∸ b · c) + ((b mod M) · (c mod M)) mod M) mod M
        ≡⟨ cong (λ z → ((a · d + P ∸ b · c) + z) mod M) (sym (mod·mod≡mod M b c)) ⟩
      ((a · d + P ∸ b · c) + (b · c) mod M) mod M
        ≡⟨ sym (mod-rCancel M (a · d + P ∸ b · c) (b · c)) ⟩
      ((a · d + P ∸ b · c) + b · c) mod M
        ≡⟨ cong (_mod M) (≤-∸-+-cancel hb) ⟩
      (a · d + P) mod M
        ≡⟨ mod+mod≡mod M (a · d) P ⟩
      ((a · d) mod M + P mod M) mod M
        ≡⟨ cong (λ z → (z + P mod M) mod M) (mod·mod≡mod M a d) ⟩
      (((a mod M) · (d mod M)) mod M + P mod M) mod M ∎

------------------------------------------------------------------------------
-- §5  The entrywise Boolean identities.
------------------------------------------------------------------------------

-- One factor M = suc k of N (N ≡ R · M): the unit condition at N, read mod M,
-- is the unit condition of the reduced determinant at M.
sideU : (k N R : ℕ) → N ≡ R · suc k → (a b c d : ℕ) → b ≤ N → c ≤ N
  → (isGCD (dpre N a b c d) (suc k) 1
       → isU (suc k) (det2 (suc k) (a mod suc k) (b mod suc k) (c mod suc k) (d mod suc k)) ≡ true)
  × (isU (suc k) (det2 (suc k) (a mod suc k) (b mod suc k) (c mod suc k) (d mod suc k)) ≡ true
       → isGCD (dpre N a b c d) (suc k) 1)
sideU k N R eN a b c d hb hc =
    (λ h → isGCD→isU M (det2 M a₁ b₁ c₁ d₁)
             (subst (λ z → isGCD z M 1) e (gcdMod← k (dpre N a b c d) 1 h)))
  , (λ p → gcdMod→ k (dpre N a b c d) 1
             (subst (λ z → isGCD z M 1) (sym e) (isU→isGCD M (det2 M a₁ b₁ c₁ d₁) p)))
  where
    M : ℕ
    M = suc k

    a₁ b₁ c₁ d₁ : ℕ
    a₁ = a mod M
    b₁ = b mod M
    c₁ = c mod M
    d₁ = d mod M

    NN : (N · N) mod M ≡ 0
    NN = cong (_mod M) (cong (N ·_) eN ∙ ·-assoc N R M) ∙ zero-charac-gen M (N · R)

    e : dpre N a b c d mod M ≡ dpre M a₁ b₁ c₁ d₁ %ᴳ M
    e = dpre-mod k a b c d (N · N) a₁ b₁ c₁ d₁ (M · M)
          (≤-trans (·-≤ b c N hb hc) (≤SumRight {n = N · N} {k = a · d}))
          (≤-trans (·-≤ b₁ c₁ M (<-weaken (mod< k b)) (<-weaken (mod< k c)))
                   (≤SumRight {n = M · M} {k = a₁ · d₁}))
          (sym (mod-idempotent a)) (sym (mod-idempotent b))
          (sym (mod-idempotent c)) (sym (mod-idempotent d))
          NN (zero-charac-gen M M)
      ∙ sym (%ᴳ≡mod (dpre M a₁ b₁ c₁ d₁) k)

-- THE ENTRYWISE UNIT IDENTITY.  For entries below N = m·n, "det is a unit
-- mod N" is the conjunction of the reduced statements mod m and mod n.
unit-split : (m' n' : ℕ) (a b c d : ℕ)
  → b < suc m' · suc n' → c < suc m' · suc n'
  → isU (suc m' · suc n') (det2 (suc m' · suc n') a b c d)
  ≡ (isU (suc m') (det2 (suc m') (a mod suc m') (b mod suc m') (c mod suc m') (d mod suc m'))
     and isU (suc n') (det2 (suc n') (a mod suc n') (b mod suc n') (c mod suc n') (d mod suc n')))
unit-split m' n' a b c d hb hc = Bool-ext to from
  where
    m n N K : ℕ
    m = suc m'
    n = suc n'
    N = m · n
    K = n' + m' · suc n'      -- N ≡ suc K definitionally

    D : ℕ
    D = dpre N a b c d

    sm = sideU m' N n (·-comm m n) a b c d (<-weaken hb) (<-weaken hc)
    sn = sideU n' N m refl        a b c d (<-weaken hb) (<-weaken hc)

    to : isU N (det2 N a b c d) ≡ true
       → (isU m (det2 m (a mod m) (b mod m) (c mod m) (d mod m))
          and isU n (det2 n (a mod n) (b mod n) (c mod n) (d mod n))) ≡ true
    to p = →and-true _ _ (sm .fst (h .fst)) (sn .fst (h .snd))
      where
        h : isGCD D m 1 × isGCD D n 1
        h = gcd1-split D m n
              (gcdMod→ K D 1
                (subst (λ z → isGCD z N 1) (%ᴳ≡mod D K) (isU→isGCD N (det2 N a b c d) p)))

    from : (isU m (det2 m (a mod m) (b mod m) (c mod m) (d mod m))
            and isU n (det2 n (a mod n) (b mod n) (c mod n) (d mod n))) ≡ true
         → isU N (det2 N a b c d) ≡ true
    from q = isGCD→isU N (det2 N a b c d)
      (subst (λ z → isGCD z N 1) (sym (%ᴳ≡mod D K))
        (gcdMod← K D 1
          (gcd1-join D m n (sm .snd (and-true→ _ _ q .fst)) (sn .snd (and-true→ _ _ q .snd)))))

-- THE MASK IDENTITIES.
-- (i) 1 divides everything:
∣?1 : (x : ℕ) → (1 ∣? x) ≡ true
∣?1 x = ≡→== (x %ᴳ 1) 0 (%ᴳ≡mod x 0 ∙ ≤0→≡0 (pred-≤-pred (mod< 0 x)))

-- (ii) below suc k, "suc k ∣ x" is "x = 0":
∣?self : (k x : ℕ) → x < suc k → (suc k ∣? x) ≡ (x == 0)
∣?self k x h = cong (_== 0) (%ᴳ≡mod x k ∙ modIndBase k x h)

-- (iii) a multiple of N below N is 0:
∣<→≡0 : (N c : ℕ) → c < N → N ∣ c → c ≡ 0
∣<→≡0 N c h d with discreteℕ c 0
... | yes p = p
... | no  q = Empty.rec (¬m<m (≤<-trans (m∣n→m≤n q d) h))

-- (iv) CRT for zero: below m·n, c = 0 iff c ≡ 0 mod m and c ≡ 0 mod n.
zero-crt : (m' n' : ℕ) → isGCD (suc m') (suc n') 1 → (c : ℕ) → c < suc m' · suc n'
  → (c == 0) ≡ ((c mod suc m' == 0) and (c mod suc n' == 0))
zero-crt m' n' cop c hc = Bool-ext to from
  where
    to : (c == 0) ≡ true → ((c mod suc m' == 0) and (c mod suc n' == 0)) ≡ true
    to p = →and-true _ _
      (≡→== _ 0 (cong (_mod suc m') c≡0 ∙ modIndBase m' 0 (suc-≤-suc zero-≤)))
      (≡→== _ 0 (cong (_mod suc n') c≡0 ∙ modIndBase n' 0 (suc-≤-suc zero-≤)))
      where
        c≡0 : c ≡ 0
        c≡0 = ==→≡ c 0 p

    from : ((c mod suc m' == 0) and (c mod suc n' == 0)) ≡ true → (c == 0) ≡ true
    from q = ≡→== c 0
      (∣<→≡0 (suc m' · suc n') c hc
        (gauss (suc m') (suc n') c cop
          (mod0→∣ m' c (==→≡ _ 0 (and-true→ _ _ q .fst)))
          (mod0→∣ n' c (==→≡ _ 0 (and-true→ _ _ q .snd)))))

------------------------------------------------------------------------------
-- §6  The Fin-cardinality layer: a Σ< scan is the card of a Σ-type.
------------------------------------------------------------------------------

-- a Boolean as a finite set: Unit or ⊥, with card = ind
BT : Bool → FinSet ℓ-zero
BT true  = Unit , isFinSetUnit
BT false = ⊥    , isFinSet⊥

cardBT : (b : Bool) → card (BT b) ≡ ind b
cardBT true  = refl
cardBT false = refl

BT-and : (x y : Bool) → BT (x and y) .fst ≃ (BT x .fst × BT y .fst)
BT-and true  y = isoToEquiv (iso (λ b → tt , b) snd (λ _ → refl) (λ _ → refl))
BT-and false y = uninhabEquiv (λ x → x) fst

-- Σ< with the FIRST index split off (Σ< itself splits off the last)
Σ<-suc : (n : ℕ) (f : ℕ → ℕ) → Σ< (suc n) f ≡ f 0 + Σ< n (f ∘ suc)
Σ<-suc zero    f = refl
Σ<-suc (suc n) f =
    cong (f (suc n) +_) (Σ<-suc n f)
  ∙ +-assoc (f (suc n)) (f 0) (Σ< n (f ∘ suc))
  ∙ cong (_+ Σ< n (f ∘ suc)) (+-comm (f (suc n)) (f 0))
  ∙ sym (+-assoc (f 0) (f (suc n)) (Σ< n (f ∘ suc)))

-- the ℕ-value of a SumFin index
ι : {N : ℕ} → SFin.Fin N → ℕ
ι x = fst (SFin.SumFin→Fin x)

cardΣ-SFin : (N : ℕ) (T : SFin.Fin N → FinSet ℓ-zero) (f : ℕ → ℕ)
  → ((x : SFin.Fin N) → card (T x) ≡ f (ι x))
  → card (_ , isFinSetΣ (SFin.Fin N , isFinSetFin) T) ≡ Σ< N f
cardΣ-SFin zero T f h =
  isEmpty→card≡0 (_ , isFinSetΣ (SFin.Fin 0 , isFinSetFin) T) (λ z → fst z)
cardΣ-SFin (suc N) T f h =
    cardEquiv (_ , isFinSetΣ (SFin.Fin (suc N) , isFinSetFin) T)
              (_ , isFinSet⊎ (T (inl tt))
                             (_ , isFinSetΣ (SFin.Fin N , isFinSetFin) (T ∘ inr)))
              ∣ compEquiv Σ⊎≃ (⊎-equiv (ΣUnit (λ u → T (inl u) .fst)) (idEquiv _)) ∣₁
  ∙ cong₂ _+_ (h (inl tt)) (cardΣ-SFin N (T ∘ inr) (f ∘ suc) (h ∘ inr))
  ∙ sym (Σ<-suc N f)

-- THE BRIDGE: card of a Σ over Fin N, given the cards of the fibres.
cardΣ-Fin : (N : ℕ) (T : Fin N → FinSet ℓ-zero) (f : ℕ → ℕ)
  → ((x : Fin N) → card (T x) ≡ f (fst x))
  → card (_ , isFinSetΣ (FinSetFin N) T) ≡ Σ< N f
cardΣ-Fin N T f h =
    cardEquiv (_ , isFinSetΣ (FinSetFin N) T)
              (_ , isFinSetΣ (SFin.Fin N , isFinSetFin) (T ∘ SFin.SumFin→Fin))
              ∣ invEquiv (Σ-cong-equiv-fst {B = λ x → T x .fst} (SFin.SumFin≃Fin N)) ∣₁
  ∙ cardΣ-SFin N (T ∘ SFin.SumFin→Fin) f (h ∘ SFin.SumFin→Fin)

-- THE COUNTED SET.  A cell is the pair of conditions on one matrix; the
-- nested Σ's over Fin N are the matrices.
Cell : (N k a b c d : ℕ) → FinSet ℓ-zero
Cell N k a b c d = _ , isFinSet× (BT (isU N (det2 N a b c d))) (BT (k ∣? c))

cardCell : (N k a b c d : ℕ)
  → card (Cell N k a b c d) ≡ ind (isU N (det2 N a b c d)) · ind (k ∣? c)
cardCell N k a b c d = cong₂ _·_ (cardBT (isU N (det2 N a b c d))) (cardBT (k ∣? c))

C3 : (N k a b c : ℕ) → FinSet ℓ-zero
C3 N k a b c = _ , isFinSetΣ (FinSetFin N) (λ d → Cell N k a b c (fst d))

C2 : (N k a b : ℕ) → FinSet ℓ-zero
C2 N k a b = _ , isFinSetΣ (FinSetFin N) (λ c → C3 N k a b (fst c))

C1 : (N k a : ℕ) → FinSet ℓ-zero
C1 N k a = _ , isFinSetΣ (FinSetFin N) (λ b → C2 N k a (fst b))

C : (N k : ℕ) → FinSet ℓ-zero
C N k = _ , isFinSetΣ (FinSetFin N) (λ a → C1 N k (fst a))

-- Gamma0Index's scan IS the cardinality of the counted set.
cnt2≡card : (N k : ℕ) → cnt2 N k ≡ card (C N k)
cnt2≡card N k = sym
  (cardΣ-Fin N (λ a → C1 N k (fst a)) _ λ a →
   cardΣ-Fin N (λ b → C2 N k (fst a) (fst b)) _ λ b →
   cardΣ-Fin N (λ c → C3 N k (fst a) (fst b) (fst c)) _ λ c →
   cardΣ-Fin N (λ d → Cell N k (fst a) (fst b) (fst c) (fst d)) _ λ d →
   cardCell N k (fst a) (fst b) (fst c) (fst d))

------------------------------------------------------------------------------
-- §7  The Chinese-remainder equivalence of counted sets, and §8 its count.
------------------------------------------------------------------------------

shuffle4 : {P₁ P₂ Q₁ Q₂ : Type} → Iso ((P₁ × P₂) × (Q₁ × Q₂)) ((P₁ × Q₁) × (P₂ × Q₂))
Iso.fun shuffle4 ((p₁ , p₂) , (q₁ , q₂)) = (p₁ , q₁) , (p₂ , q₂)
Iso.inv shuffle4 ((p₁ , q₁) , (p₂ , q₂)) = (p₁ , p₂) , (q₁ , q₂)
Iso.rightInv shuffle4 _ = refl
Iso.leftInv  shuffle4 _ = refl

module Main (m' n' : ℕ) (cop : isGCD (suc m') (suc n') 1) (k km kn : ℕ)
  (H : (c : ℕ) → c < suc m' · suc n'
     → (k ∣? c) ≡ ((km ∣? (c mod suc m')) and (kn ∣? (c mod suc n'))))
  where

  private
    m n N : ℕ
    m = suc m'
    n = suc n'
    N = m · n

    e : Fin N ≃ (Fin m × Fin n)
    e = crtEquiv m' n' cop

  -- the cell on the product side: the two conditions at m and the two at n
  PCell : Fin m × Fin n → Fin m × Fin n → Fin m × Fin n → Fin m × Fin n → Type
  PCell a b c d =
      Cell m km (fst (fst a)) (fst (fst b)) (fst (fst c)) (fst (fst d)) .fst
    × Cell n kn (fst (snd a)) (fst (snd b)) (fst (snd c)) (fst (snd d)) .fst

  -- §5 as an equivalence of fibres; equivFun e is the residue-pair map,
  -- definitionally, so the reduced entries are literally `fst a mod m`.
  cellEquiv : (a b c d : Fin N)
    → Cell N k (fst a) (fst b) (fst c) (fst d) .fst
    ≃ PCell (equivFun e a) (equivFun e b) (equivFun e c) (equivFun e d)
  cellEquiv a b c d =
    compEquiv
      (pathToEquiv (λ i → BT (unit-split m' n' (fst a) (fst b) (fst c) (fst d) (snd b) (snd c) i) .fst
                        × BT (H (fst c) (snd c) i) .fst))
      (compEquiv (≃-× (BT-and um un) (BT-and qm qn)) (isoToEquiv shuffle4))
    where
      um un qm qn : Bool
      um = isU m (det2 m (fst a mod m) (fst b mod m) (fst c mod m) (fst d mod m))
      un = isU n (det2 n (fst a mod n) (fst b mod n) (fst c mod n) (fst d mod n))
      qm = km ∣? (fst c mod m)
      qn = kn ∣? (fst c mod n)

  PC : Type
  PC = Σ[ a ∈ Fin m × Fin n ] Σ[ b ∈ Fin m × Fin n ] Σ[ c ∈ Fin m × Fin n ]
       Σ[ d ∈ Fin m × Fin n ] PCell a b c d

  -- entrywise CRT on the four entries
  step1 : C N k .fst ≃ PC
  step1 = Σ-cong-equiv e (λ a → Σ-cong-equiv e (λ b → Σ-cong-equiv e (λ c →
          Σ-cong-equiv e (λ d → cellEquiv a b c d))))

  -- regroup: the m-halves together, the n-halves together
  shuffleΣ : Iso PC (C m km .fst × C n kn .fst)
  Iso.fun shuffleΣ ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (x , y)) =
    (a₁ , b₁ , c₁ , d₁ , x) , (a₂ , b₂ , c₂ , d₂ , y)
  Iso.inv shuffleΣ ((a₁ , b₁ , c₁ , d₁ , x) , (a₂ , b₂ , c₂ , d₂ , y)) =
    (a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (x , y)
  Iso.rightInv shuffleΣ _ = refl
  Iso.leftInv  shuffleΣ _ = refl

  -- THE EQUIVALENCE OF COUNTED SETS
  countEquiv : C N k .fst ≃ (C m km .fst × C n kn .fst)
  countEquiv = compEquiv step1 (isoToEquiv shuffleΣ)

  -- §8  and the count transported along it
  theorem : cnt2 N k ≡ cnt2 m km · cnt2 n kn
  theorem =
      cnt2≡card N k
    ∙ cardEquiv (C N k) (_ , isFinSet× (C m km) (C n kn)) ∣ countEquiv ∣₁
    ∙ cong₂ _·_ (sym (cnt2≡card m km)) (sym (cnt2≡card n kn))

-- The general statement, with the mask hypothesis explicit.
cnt2-crt : (m' n' : ℕ) → isGCD (suc m') (suc n') 1 → (k km kn : ℕ)
  → ((c : ℕ) → c < suc m' · suc n'
       → (k ∣? c) ≡ ((km ∣? (c mod suc m')) and (kn ∣? (c mod suc n'))))
  → cnt2 (suc m' · suc n') k ≡ cnt2 (suc m') km · cnt2 (suc n') kn
cnt2-crt m' n' cop k km kn H = Main.theorem m' n' cop k km kn H

------------------------------------------------------------------------------
-- §9  THE TWO THEOREMS, and the four refls as their instances.
------------------------------------------------------------------------------

-- (T1)  |GL₂(ℤ/mn)| = |GL₂(ℤ/m)| · |GL₂(ℤ/n)| for coprime m, n ≥ 1.
crt-GL : (m' n' : ℕ) → isGCD (suc m') (suc n') 1
  → cnt2 (suc m' · suc n') 1 ≡ cnt2 (suc m') 1 · cnt2 (suc n') 1
crt-GL m' n' cop =
  cnt2-crt m' n' cop 1 1 1
    (λ c _ → ∣?1 c
           ∙ sym (→and-true (1 ∣? (c mod suc m')) (1 ∣? (c mod suc n'))
                            (∣?1 (c mod suc m')) (∣?1 (c mod suc n'))))

-- (T2)  the same for the image of Γ₀(N) (lower-left entry ≡ 0 mod N).
crt-Γ : (m' n' : ℕ) → isGCD (suc m') (suc n') 1
  → cnt2 (suc m' · suc n') (suc m' · suc n') ≡ cnt2 (suc m') (suc m') · cnt2 (suc n') (suc n')
crt-Γ m' n' cop = cnt2-crt m' n' cop (suc m' · suc n') (suc m') (suc n') mask
  where
    mask : (c : ℕ) → c < suc m' · suc n'
         → ((suc m' · suc n') ∣? c) ≡ ((suc m' ∣? (c mod suc m')) and (suc n' ∣? (c mod suc n')))
    mask c hc =
        ∣?self (n' + m' · suc n') c hc
      ∙ zero-crt m' n' cop c hc
      ∙ cong₂ _and_ (sym (∣?self m' (c mod suc m') (mod< m' c)))
                    (sym (∣?self n' (c mod suc n') (mod< n' c)))

-- the coprimality witnesses, computed by the library's Euclid
cop-4-3 : isGCD 4 3 1
cop-4-3 = gcd≡→isGCD refl

cop-2-5 : isGCD 2 5 1
cop-2-5 = gcd≡→isGCD refl

-- the four statements of Gamma0Index §4b, now proved without enumeration
GL12 : cnt2 12 1 ≡ cnt2 4 1 · cnt2 3 1
GL12 = crt-GL 3 2 cop-4-3

Γ12 : cnt2 12 12 ≡ cnt2 4 4 · cnt2 3 3
Γ12 = crt-Γ 3 2 cop-4-3

GL10 : cnt2 10 1 ≡ cnt2 2 1 · cnt2 5 1
GL10 = crt-GL 1 4 cop-2-5

Γ10 : cnt2 10 10 ≡ cnt2 2 2 · cnt2 5 5
Γ10 = crt-Γ 1 4 cop-2-5

-- and each refl of Gamma0Index IS the corresponding instance, as a path in ℕ
GL12≡crtGL12 : GL12 ≡ crtGL12
GL12≡crtGL12 = isSetℕ _ _ GL12 crtGL12

Γ12≡crtΓ12 : Γ12 ≡ crtΓ12
Γ12≡crtΓ12 = isSetℕ _ _ Γ12 crtΓ12

GL10≡crtGL10 : GL10 ≡ crtGL10
GL10≡crtGL10 = isSetℕ _ _ GL10 crtGL10

Γ10≡crtΓ10 : Γ10 ≡ crtΓ10
Γ10≡crtΓ10 = isSetℕ _ _ Γ10 crtΓ10

------------------------------------------------------------------------------
-- §10  Controls.
------------------------------------------------------------------------------

-- (a) COPRIMALITY IS LOAD-BEARING.  At 4 = 2·2 the conclusion of crt-GL is
--     FALSE: |GL₂(ℤ/4)| = 96 but |GL₂(ℤ/2)|² = 36.  (FinCardinality already
--     shows isGCD 2 2 1 is uninhabited, so the hypothesis fails there too.)
control-needs-coprime : ¬ (cnt2 (2 · 2) 1 ≡ cnt2 2 1 · cnt2 2 1)
control-needs-coprime p = false≢true (≡→== _ _ p)

-- (b) NON-VACUITY at a level Gamma0Index never enumerated: 15 = 3·5.
cop-3-5 : isGCD 3 5 1
cop-3-5 = gcd≡→isGCD refl

GL15 : cnt2 15 1 ≡ cnt2 3 1 · cnt2 5 1
GL15 = crt-GL 2 4 cop-3-5

Γ15 : cnt2 15 15 ≡ cnt2 3 3 · cnt2 5 5
Γ15 = crt-Γ 2 4 cop-3-5

-- (c) the general mask theorem is not restricted to k ∈ {1, N}: at 12 = 4·3
--     the mask k = 4 (Γ₀(4) ⊂ GL₂(ℤ/12)) splits as (4, 1).
mask-4 : (c : ℕ) → c < 4 · 3 → (4 ∣? c) ≡ ((4 ∣? (c mod 4)) and (1 ∣? (c mod 3)))
mask-4 c hc =
    cong (_== 0) (%ᴳ≡mod c 3 ∙ sym (mod-idempotent c) ∙ sym (%ᴳ≡mod (c mod 4) 3))
  ∙ sym (cong ((4 ∣? (c mod 4)) and_) (∣?1 (c mod 3)) ∙ and-trueʳ (4 ∣? (c mod 4)))
  where
    and-trueʳ : (x : Bool) → (x and true) ≡ x
    and-trueʳ true  = refl
    and-trueʳ false = refl

Γ₀4-in-12 : cnt2 12 4 ≡ cnt2 4 4 · cnt2 3 1
Γ₀4-in-12 = cnt2-crt 3 2 cop-4-3 4 4 1 mask-4
