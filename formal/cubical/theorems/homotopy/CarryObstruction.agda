{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CarryObstruction
--
-- **carrying cannot be removed by any choice of digit set.**
--
-- Statement being formalized (ATLAS_OF_N.md (absent from this repository) §2.4(iii)).  For b ≥ 2, n ≥ 1
-- the truncation
--
--     0 → bⁿℤ/bⁿ⁺¹ℤ → ℤ/bⁿ⁺¹ --π--> ℤ/bⁿ → 0
--
-- has a set-theoretic section sₙ (the digit section), and its coboundary
--
--     cₙ(u,v) = sₙ(u) + sₙ(v) − sₙ(u+v)
--
-- is the carry.  The note proves the class of cₙ is nonzero in
-- H²(ℤ/bⁿ; ℤ/b), and derives Corollary 2.11.1 from it: a carry-free
-- positional system would be a group-theoretic splitting, which does not
-- exist.  **This module proves Corollary 2.11.1 directly, by the exponent
-- argument the note gives, with no cohomology machinery.**
--
-- The argument, in three separated layers:
--
--  (1) EXPONENT OBSTRUCTION (pure group theory, `Splitting.kills`).  If
--      π : G → Q is a homomorphism of an *abelian* G, s : Q → G is a
--      homomorphic section of π, and a single m : ℕ annihilates both Q and
--      ker π, then m annihilates all of G.  Splitting cannot raise the
--      exponent.  Nothing about cyclic groups or about ℕ enters here.
--
--  (2) CARRY-FREE ⇒ HOMOMORPHIC (`Carry.carry-free→pres`).  For a bare
--      set-theoretic section s, the coboundary c(u,v) = s(u)·s(v)·s(u·v)⁻¹
--      vanishes identically exactly when s is a homomorphism.  This is what
--      makes "no digit set eliminates carrying" and "the extension does not
--      split" the same statement.  `carry-inKer` records that c really is
--      valued in ker π (it is a 2-cochain with values in the kernel), and
--      `carry-cocycle` that it satisfies the 2-cocycle identity, so the
--      object being shown nonvanishing is the one the note names.
--
--  (3) THE ARITHMETIC INSTANCE (`Cyclic`).  For the reduction
--      ℤ/(N·e) → ℤ/N with e ∣ N and e ≥ 2, all three hypotheses of (1)
--      hold with m = N, while N·1 ≠ 0 in ℤ/(N·e).  Hence no section is a
--      homomorphism, hence no section is carry-free.  Specialized in
--      `BasePower` to N = bⁿ, e = b, giving exactly Corollary 2.11.1:
--      **for every b ≥ 2 and n ≥ 1 and every digit set whatever, some pair
--      of residues carries.**
--
-- Theorem 2.7 of the same note (ℕ ≃ base-b digit words) is NOT reproved
-- here: it is already in this corpus as `Digits.ℕ≃CanWord`,
-- with round trips `value-digits` / `digits-value` and injectivity
-- `value-inj`.  This module is the other half of §7's formalization pair.
------------------------------------------------------------------------

module CarryObstruction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥)

open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod

open IsGroupHom

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- 0.  Iterated multiplication in a group
------------------------------------------------------------------------

-- `pow G m x` is xᵐ.  Written additively in the applications: m · x.
pow : (G : Group ℓ) → ℕ → ⟨ G ⟩ → ⟨ G ⟩
pow G zero    x = GroupStr.1g (snd G)
pow G (suc m) x = GroupStr._·_ (snd G) x (pow G m x)

module _ {G : Group ℓ} {H : Group ℓ'} (φ : GroupHom G H) where
  private
    module G = GroupStr (snd G)
    module H = GroupStr (snd H)

  -- Homomorphisms commute with powers.
  pow-hom : (m : ℕ) (x : ⟨ G ⟩) → φ .fst (pow G m x) ≡ pow H m (φ .fst x)
  pow-hom zero    x = φ .snd .pres1
  pow-hom (suc m) x =
    φ .snd .pres· x (pow G m x) ∙ cong (φ .fst x H.·_) (pow-hom m x)

module _ (G : Group ℓ)
         (comm : (x y : ⟨ G ⟩) → GroupStr._·_ (snd G) x y
                               ≡ GroupStr._·_ (snd G) y x) where
  private
    module G = GroupStr (snd G)

  private
    middle4 : (x y a c : ⟨ G ⟩)
            → (x G.· y) G.· (a G.· c) ≡ (x G.· a) G.· (y G.· c)
    middle4 x y a c =
        sym (G.·Assoc x y (a G.· c))
      ∙ cong (x G.·_) (G.·Assoc y a c)
      ∙ cong (λ z → x G.· (z G.· c)) (comm y a)
      ∙ cong (x G.·_) (sym (G.·Assoc a y c))
      ∙ G.·Assoc x a (y G.· c)

  -- In an abelian group, m-th power is a homomorphism.
  pow-· : (m : ℕ) (x y : ⟨ G ⟩)
        → pow G m (x G.· y) ≡ pow G m x G.· pow G m y
  pow-· zero    x y = sym (G.·IdL G.1g)
  pow-· (suc m) x y =
      cong ((x G.· y) G.·_) (pow-· m x y)
    ∙ middle4 x y (pow G m x) (pow G m y)

------------------------------------------------------------------------
-- 1.  The exponent obstruction: splitting cannot raise the exponent
------------------------------------------------------------------------

module Splitting
  (G : Group ℓ) (Q : Group ℓ')
  (comm : (x y : ⟨ G ⟩) → GroupStr._·_ (snd G) x y
                        ≡ GroupStr._·_ (snd G) y x)
  (π : GroupHom G Q) (s : GroupHom Q G)
  (sect : (q : ⟨ Q ⟩) → π .fst (s .fst q) ≡ q)
  (m : ℕ)
  (killQ : (q : ⟨ Q ⟩) → pow Q m q ≡ GroupStr.1g (snd Q))
  (killK : (x : ⟨ G ⟩) → π .fst x ≡ GroupStr.1g (snd Q)
                       → pow G m x ≡ GroupStr.1g (snd G))
  where

  private
    module G = GroupStr (snd G)
    module Q = GroupStr (snd Q)

    -- the section's value at π x, and the kernel element it leaves over
    a : ⟨ G ⟩ → ⟨ G ⟩
    a x = s .fst (π .fst x)

    k : ⟨ G ⟩ → ⟨ G ⟩
    k x = G.inv (a x) G.· x

    split : (x : ⟨ G ⟩) → a x G.· k x ≡ x
    split x = G.·Assoc (a x) (G.inv (a x)) x
            ∙ cong (G._· x) (G.·InvR (a x))
            ∙ G.·IdL x

    k-in-ker : (x : ⟨ G ⟩) → π .fst (k x) ≡ Q.1g
    k-in-ker x =
        π .snd .pres· (G.inv (a x)) x
      ∙ cong (Q._· π .fst x) (π .snd .presinv (a x) ∙ cong Q.inv (sect (π .fst x)))
      ∙ Q.·InvL (π .fst x)

  -- m annihilates the image of the section …
  private
    kills-a : (x : ⟨ G ⟩) → pow G m (a x) ≡ G.1g
    kills-a x =
        sym (pow-hom s m (π .fst x))
      ∙ cong (s .fst) (killQ (π .fst x))
      ∙ s .snd .pres1

  -- … and therefore all of G.
  kills : (x : ⟨ G ⟩) → pow G m x ≡ G.1g
  kills x =
      cong (pow G m) (sym (split x))
    ∙ pow-· G comm m (a x) (k x)
    ∙ cong₂ G._·_ (kills-a x) (killK (k x) (k-in-ker x))
    ∙ G.·IdL G.1g

------------------------------------------------------------------------
-- 2.  The carry cochain of a set-theoretic section
------------------------------------------------------------------------

module Carry
  (G : Group ℓ) (Q : Group ℓ')
  (π : GroupHom G Q) (s : ⟨ Q ⟩ → ⟨ G ⟩)
  (sect : (q : ⟨ Q ⟩) → π .fst (s q) ≡ q)
  where

  private
    module G = GroupStr (snd G)
    module Q = GroupStr (snd Q)

  -- c(u,v) = s(u)·s(v)·s(u·v)⁻¹.  Additively: s(u)+s(v)−s(u+v) — the carry.
  carry : ⟨ Q ⟩ → ⟨ Q ⟩ → ⟨ G ⟩
  carry u v = (s u G.· s v) G.· G.inv (s (u Q.· v))

  -- It takes values in ker π: the carry is a 2-cochain with coefficients in
  -- the kernel, as Proposition 2.11 asserts.
  carry-inKer : (u v : ⟨ Q ⟩) → π .fst (carry u v) ≡ Q.1g
  carry-inKer u v =
      π .snd .pres· (s u G.· s v) (G.inv (s (u Q.· v)))
    ∙ cong₂ Q._·_
        (π .snd .pres· (s u) (s v) ∙ cong₂ Q._·_ (sect u) (sect v))
        (π .snd .presinv (s (u Q.· v)) ∙ cong Q.inv (sect (u Q.· v)))
    ∙ Q.·InvR (u Q.· v)

  -- Vanishing of the carry is exactly homomorphy of the digit section.
  carry-free→pres : ((u v : ⟨ Q ⟩) → carry u v ≡ G.1g)
                  → (u v : ⟨ Q ⟩) → s (u Q.· v) ≡ s u G.· s v
  carry-free→pres cf u v =
      sym (G.·IdL (s (u Q.· v)))
    ∙ cong (G._· s (u Q.· v)) (sym (cf u v))
    ∙ sym (G.·Assoc (s u G.· s v) (G.inv (s (u Q.· v))) (s (u Q.· v)))
    ∙ cong ((s u G.· s v) G.·_) (G.·InvL (s (u Q.· v)))
    ∙ G.·IdR (s u G.· s v)

  -- … so a carry-free digit section is a splitting homomorphism.
  carry-free→hom : ((u v : ⟨ Q ⟩) → carry u v ≡ G.1g) → GroupHom Q G
  carry-free→hom cf = s , makeIsGroupHom (λ u v → carry-free→pres cf u v)

  -- Normalization: c(u,0) = c(0,v) = 0 whenever the section is normalized
  -- (s(0) = 0), which the digit section is.
  carry-normR : (s1 : s Q.1g ≡ G.1g) (u : ⟨ Q ⟩) → carry u Q.1g ≡ G.1g
  carry-normR s1 u =
      cong (λ z → (s u G.· s Q.1g) G.· G.inv (s z)) (Q.·IdR u)
    ∙ cong (λ z → (s u G.· z) G.· G.inv (s u)) s1
    ∙ cong (G._· G.inv (s u)) (G.·IdR (s u))
    ∙ G.·InvR (s u)

  carry-normL : (s1 : s Q.1g ≡ G.1g) (v : ⟨ Q ⟩) → carry Q.1g v ≡ G.1g
  carry-normL s1 v =
      cong (λ z → (s Q.1g G.· s v) G.· G.inv (s z)) (Q.·IdL v)
    ∙ cong (λ z → (z G.· s v) G.· G.inv (s v)) s1
    ∙ cong (G._· G.inv (s v)) (G.·IdL (s v))
    ∙ G.·InvR (s v)

  -- The 2-cocycle identity, for abelian G:
  --     c(u,v) + c(u+v,w)  =  c(v,w) + c(u,v+w).
  module _ (comm : (x y : ⟨ G ⟩) → x G.· y ≡ y G.· x) where

    private
      -- (P · D⁻¹) · (D · X) ≡ P · X — no commutativity needed here.
      slide : (P D X : ⟨ G ⟩) → (P G.· G.inv D) G.· (D G.· X) ≡ P G.· X
      slide P D X =
          sym (G.·Assoc P (G.inv D) (D G.· X))
        ∙ cong (P G.·_) (G.·Assoc (G.inv D) D X)
        ∙ cong (λ z → P G.· (z G.· X)) (G.·InvL D)
        ∙ cong (P G.·_) (G.·IdL X)

    carry-cocycle : (u v w : ⟨ Q ⟩)
      → carry u v G.· carry (u Q.· v) w
      ≡ carry v w G.· carry u (v Q.· w)
    carry-cocycle u v w = left ∙ sym right
      where
        A = s u ; B = s v ; C = s w
        D = s (u Q.· v) ; E = s (v Q.· w) ; F = s ((u Q.· v) Q.· w)

        left : carry u v G.· carry (u Q.· v) w ≡ ((A G.· B) G.· C) G.· G.inv F
        left =
            cong (((A G.· B) G.· G.inv D) G.·_) (sym (G.·Assoc D C (G.inv F)))
          ∙ slide (A G.· B) D (C G.· G.inv F)
          ∙ G.·Assoc (A G.· B) C (G.inv F)

        -- the two right-hand carries land at the same element of Q
        assocQ : u Q.· (v Q.· w) ≡ (u Q.· v) Q.· w
        assocQ = Q.·Assoc u v w

        right : carry v w G.· carry u (v Q.· w) ≡ ((A G.· B) G.· C) G.· G.inv F
        right =
            cong (λ z → ((B G.· C) G.· G.inv E) G.· ((A G.· E) G.· G.inv (s z)))
                 assocQ
          ∙ cong (λ z → ((B G.· C) G.· G.inv E) G.· ((z G.· G.inv F)))
                 (comm A E)
          ∙ cong (((B G.· C) G.· G.inv E) G.·_) (sym (G.·Assoc E A (G.inv F)))
          ∙ slide (B G.· C) E (A G.· G.inv F)
          ∙ G.·Assoc (B G.· C) A (G.inv F)
          ∙ cong (G._· G.inv F) (comm (B G.· C) A)
          ∙ cong (G._· G.inv F) (G.·Assoc A B C)

------------------------------------------------------------------------
-- 3.  The cyclic instance: ℤ/(N·e) → ℤ/N with e ∣ N and e ≥ 2
------------------------------------------------------------------------

-- The underlying natural number of a power in ℤ/(suc n′).
fst-pow : (n' k : ℕ) (x : Fin (suc n'))
        → fst (pow (ℤGroup/ (suc n')) k x) ≡ (k · fst x) mod (suc n')
fst-pow n' zero    x = sym (modIndBase n' 0 (n' , +-comm n' 1))
fst-pow n' (suc k) x =
    cong (λ z → (fst x + z) mod (suc n')) (fst-pow n' k x)
  ∙ sym (mod-rCancel (suc n') (fst x) (k · fst x))

-- N annihilates ℤ/N.  (The exponent of the quotient.)
selfkill : (n' : ℕ) (q : Fin (suc n'))
         → pow (ℤGroup/ (suc n')) (suc n') q
         ≡ GroupStr.1g (snd (ℤGroup/ (suc n')))
selfkill n' q = Σ≡Prop (λ _ → isProp≤)
  ( fst-pow n' (suc n') q
  ∙ cong (_mod (suc n')) (·-comm (suc n') (fst q))
  ∙ zero-charac-gen (suc n') (fst q) )

------------------------------------------------------------------------

-- N = suc N′, e = 2 + e′ ≥ 2, and e ∣ N (witnessed by N ≡ e·f).
-- M = N·e is then, definitionally, a successor, so `ℤGroup/ M` is the
-- Fin-based cyclic group and not ℤ.
module Cyclic (N' e' f : ℕ) (div : suc N' ≡ suc (suc e') · f) where

  N e M' M : ℕ
  N  = suc N'
  e  = suc (suc e')
  M' = suc e' + N' · e
  M  = suc M'

  -- M really is N·e, definitionally.
  M≡ : M ≡ N · e
  M≡ = refl

  G Q : Group₀
  G = ℤGroup/ M
  Q = ℤGroup/ N

  private
    module G = GroupStr (snd G)
    module Q = GroupStr (snd Q)

  ----------------------------------------------------------------
  -- the truncation ℤ/M ↠ ℤ/N
  ----------------------------------------------------------------

  -- Reducing mod M and then mod N is reducing mod N (because N ∣ M).
  mod-mod : (x : ℕ) → (x mod M) mod N ≡ x mod N
  mod-mod x = sym
    ( cong (_mod N) (sym (≡remainder+quotient M x))
    ∙ mod-rCancel N (x mod M) (M · q)
    ∙ cong (λ z → ((x mod M) + z) mod N) killMq
    ∙ cong (_mod N) (+-zero (x mod M)) )
    where
      q : ℕ
      q = quotient x / M

      killMq : (M · q) mod N ≡ 0
      killMq = cong (_mod N) (sym (·-assoc N e q) ∙ ·-comm N (e · q))
             ∙ zero-charac-gen N (e · q)

  red : Fin M → Fin N
  red x = (fst x mod N) , mod< N' (fst x)

  red-pres : (x y : Fin M) → red (x +ₘ y) ≡ red x +ₘ red y
  red-pres x y = Σ≡Prop (λ _ → isProp≤)
    ( mod-mod (fst x + fst y) ∙ mod+mod≡mod N (fst x) (fst y) )

  redHom : GroupHom G Q
  redHom = red , makeIsGroupHom red-pres

  ----------------------------------------------------------------
  -- the two exponent facts
  ----------------------------------------------------------------

  -- N annihilates the kernel of the truncation.  (Here e ∣ N is used:
  -- ker = NZ/MZ has exponent e, and e ∣ N, so N annihilates it too.
  -- This is the step that needs n ≥ 1 in the base-b instance.)
  kill-ker : (x : Fin M) → red x ≡ Q.1g → pow G N x ≡ G.1g
  kill-ker x h = Σ≡Prop (λ _ → isProp≤)
    ( fst-pow M' N x ∙ cong (_mod M) arith ∙ zero-charac-gen M (f · q₀) )
    where
      q₀ : ℕ
      q₀ = quotient (fst x) / N

      fx≡ : fst x ≡ N · q₀
      fx≡ = sym (≡remainder+quotient N (fst x)) ∙ cong (_+ N · q₀) (cong fst h)

      arith : N · fst x ≡ (f · q₀) · M
      arith = cong (N ·_) fx≡
            ∙ ·-assoc N N q₀
            ∙ cong (_· q₀) (cong (N ·_) div ∙ ·-assoc N e f)
            ∙ sym (·-assoc M f q₀)
            ∙ ·-comm M (f · q₀)

  ----------------------------------------------------------------
  -- but N does NOT annihilate ℤ/M
  ----------------------------------------------------------------

  N<M : N < M
  N<M = (N' + N · e')
      , ( +-suc (N' + N · e') N
        ∙ cong suc (+-comm (N' + N · e') N)
        ∙ sym (+-suc N (N' + N · e'))
        ∙ cong (N +_) (sym (·-suc N e'))
        ∙ sym (·-suc N (suc e')) )

  one : Fin M
  one = 1 , ≤<-trans (suc-≤-suc zero-≤) N<M

  pow-one : fst (pow G N one) ≡ N
  pow-one = fst-pow M' N one
          ∙ cong (_mod M) (·-identityʳ N)
          ∙ modIndBase M' N N<M

  ----------------------------------------------------------------
  -- Proposition 2.11 / Corollary 2.11.1 for this extension
  ----------------------------------------------------------------

  -- No homomorphic section: the extension does not split.
  no-hom-section : (s : GroupHom Q G)
                 → ((q : Fin N) → red (s .fst q) ≡ q) → ⊥
  no-hom-section s sect = snotz (sym pow-one ∙ cong fst kills-one)
    where
      kills-one : pow G N one ≡ G.1g
      kills-one =
        Splitting.kills G Q +ₘ-comm redHom s sect N (selfkill N') kill-ker one

  -- The carry of an arbitrary digit set s.
  carryOf : (s : Fin N → Fin M) → Fin N → Fin N → Fin M
  carryOf s u v = (s u +ₘ s v) +ₘ (-ₘ (s (u +ₘ v)))

  -- … and it is literally the coboundary of §2.
  carryOf≡ : (s : Fin N → Fin M) (sect : (q : Fin N) → red (s q) ≡ q)
             (u v : Fin N)
           → carryOf s u v ≡ Carry.carry G Q redHom s sect u v
  carryOf≡ s sect u v = refl

  -- COROLLARY 2.11.1.  No digit set is carry-free.
  no-carry-free : (s : Fin N → Fin M)
                → ((q : Fin N) → red (s q) ≡ q)
                → ¬ ((u v : Fin N) → carryOf s u v ≡ G.1g)
  no-carry-free s sect cf =
    no-hom-section (Carry.carry-free→hom G Q redHom s sect cf) sect

  ----------------------------------------------------------------
  -- non-vacuity: the schoolbook digit set is a section, and carries
  ----------------------------------------------------------------

  -- The least-nonnegative-representative section, i.e. the alphabet
  -- {0,…,N−1} used as digits.  Existence matters: `no-carry-free`
  -- quantifies over a nonempty class.
  stdSection : Fin N → Fin M
  stdSection q = fst q , <-trans (snd q) N<M

  stdSection-sect : (q : Fin N) → red (stdSection q) ≡ q
  stdSection-sect q = Σ≡Prop (λ _ → isProp≤) (modIndBase N' (fst q) (snd q))

  -- … and it is normalized, so its carry is a normalized 2-cocycle.
  stdSection-1 : stdSection Q.1g ≡ G.1g
  stdSection-1 = Σ≡Prop (λ _ → isProp≤) refl

  std-carries : ¬ ((u v : Fin N) → carryOf stdSection u v ≡ G.1g)
  std-carries = no-carry-free stdSection stdSection-sect

------------------------------------------------------------------------
-- 4.  Corollary 2.11.1: for b ≥ 2 and n ≥ 1, no digit set is carry-free
------------------------------------------------------------------------

-- b = 2 + k, n = 1 + n′.  The two hypotheses of ATLAS_OF_N.md (absent from this repository) §2.4(iii)
-- are exactly these two `suc` patterns.
module BasePower (k n' : ℕ) where

  b n : ℕ
  b = suc (suc k)
  n = suc n'

  -- bʲ, presented so that it is *definitionally* a successor (Agda needs
  -- that to see ℤGroup/ bʲ as the Fin-based cyclic group rather than ℤ).
  bp : ℕ → ℕ
  bp zero    = 0
  bp (suc j) = suc k + b · bp j

  bpow : ℕ → ℕ
  bpow j = suc (bp j)

  -- … and it really is bʲ.
  bpow≡ : (j : ℕ) → bpow j ≡ b ^ j
  bpow≡ zero    = refl
  bpow≡ (suc j) = sym (cong (b ·_) (sym (bpow≡ j)) ∙ ·-suc b (bp j))

  -- The instance: N = bⁿ, e = b, and b ∣ bⁿ because n ≥ 1.
  open Cyclic (bp n) k (bpow n') (sym (·-suc b (bp n'))) public

  N≡ : N ≡ b ^ n
  N≡ = bpow≡ n

  M≡b : M ≡ b ^ (suc n)
  M≡b = cong (_· b) (bpow≡ n) ∙ ·-comm (b ^ n) b

  -- COROLLARY 2.11.1 (ATLAS_OF_N.md (absent from this repository) §2.4(iii)).  For every b ≥ 2, every
  -- n ≥ 1, and EVERY function s : ℤ/bⁿ → ℤ/bⁿ⁺¹ that is a section of
  -- truncation — i.e. every choice of digit set whatever — it is false
  -- that all carries vanish.  Carrying is a property of the extension,
  -- not of the alphabet.
  carry-unremovable :
      (s : Fin N → Fin M)
    → ((q : Fin N) → red (s q) ≡ q)
    → ¬ ((u v : Fin N) → carryOf s u v ≡ GroupStr.1g (snd G))
  carry-unremovable = no-carry-free

  -- Equivalently: the extension 0 → bⁿℤ/bⁿ⁺¹ℤ → ℤ/bⁿ⁺¹ → ℤ/bⁿ → 0 does
  -- not split.  (Proposition 2.11 says its class in H² is nonzero; this
  -- is the consequence of that statement which has the content.)
  extension-does-not-split :
      (s : GroupHom Q G) → ((q : Fin N) → red (s .fst q) ≡ q) → ⊥
  extension-does-not-split = no-hom-section

------------------------------------------------------------------------
-- 5.  Definitional sanity checks on the moduli (guards against an
--     off-by-one in the successor presentation of bⁿ)
------------------------------------------------------------------------

private
  -- b = 2, n = 1:  ℤ/4 ↠ ℤ/2
  _ : BasePower.N 0 0 ≡ 2
  _ = refl

  _ : BasePower.M 0 0 ≡ 4
  _ = refl

  -- b = 3, n = 2:  ℤ/27 ↠ ℤ/9
  _ : BasePower.N 1 1 ≡ 9
  _ = refl

  _ : BasePower.M 1 1 ≡ 27
  _ = refl
