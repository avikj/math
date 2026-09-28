{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ModeAdjoint
--
-- swarm-0814-02, 2026-08-14.
--
-- The admissible-mode classification for the obligation calculus of
--
-- OBLIGATION.md (absent from this repository) Definition 4 requires every edge transfer
-- t : S -> S to be monotone with t(TOP) = TOP; Theorem O2 buys exactness
-- (sigma* = MOP) from binary-meet preservation; Proposition O2.3 asserts
-- that "every transfer arising from Definition 4 is one of: the identity,
-- a constant = TOP, or a clamp s |-> s /\ c"; and Section 9 obligation 1
-- declares the resulting check "open, and permanently so: it is a duty on
-- additions, not a one-time check."
--
-- This module proves three things about that package, over an arbitrary
-- meet-semilattice, with no postulates and no holes:
--
--   (1) CLAMP COLLAPSE.  A clamp satisfies Definition 4's own condition
--       t(TOP) = TOP if and only if it is the identity.  So the VALUE row
--       of the mode table is not a legal transfer: the note's definition
--       and its mode vocabulary contradict each other.  (clampTop,
--       clampTrivial.)
--
--   (2) THRESHOLDS ARE ADMISSIBLE.  For any filter test chi (a Bool-valued
--       map with chi(x /\ y) = chi x && chi y and chi TOP = true) and any
--       floor b, the threshold map  s |-> if chi s then TOP else b
--       preserves binary meets and TOP.  These are legal transfers.
--       (thr-Pres/\, thr-PresTOP.)
--
--   (3) THE LIST IS INCOMPLETE.  On the three-element chain there is an
--       explicit threshold mode theta with theta bot = bot, theta mid =
--       top, theta top = top which is admissible and is *not* the
--       identity, *not* the constant TOP, and *not* s |-> s /\ c for any
--       c whatsoever.  (theta-Adm, theta-not-id, theta-not-constTop,
--       theta-not-clamp.)
--
-- Consequence, stated in the note's own vocabulary: obligation 1 of
-- OBLIGATION.md (absent from this repository) Section 9 is not "permanently open".  Admissibility is a
-- closed condition -- preservation of binary meets -- and the admissible
-- modes are closed under composition and pointwise meet (comp-Adm,
-- meet-Adm), i.e. they form a monoid and a meet-semilattice, not a list to
-- be re-audited per addition.  The three named modes are a proper subset
-- of it; the missing ones are exactly the thresholds, which is where a
-- hypothesis-check edge belongs.
------------------------------------------------------------------------

module ModeAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)

private
  variable
    ℓ : Level

-- local conjunction, to avoid depending on the library's naming
_&&_ : Bool → Bool → Bool
true  && y = y
false && _ = false

------------------------------------------------------------------------
-- 1. Modes over an arbitrary meet-semilattice
------------------------------------------------------------------------

-- S is a meet-semilattice with top: (S, /\) a commutative idempotent
-- semigroup with unit TOP.  The order is a <= b := a /\ b == a; it is not
-- needed below, since every statement is equational.

module Modes
  {S : Type ℓ}
  (_∧_   : S → S → S)
  (TOP   : S)
  (∧-idem  : (a : S) → a ∧ a ≡ a)
  (∧-comm  : (a b : S) → a ∧ b ≡ b ∧ a)
  (∧-assoc : (a b c : S) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c))
  (∧-unit  : (a : S) → TOP ∧ a ≡ a)
  where

  -- The property Theorem O2's tightness argument actually consumes.
  Pres∧ : (S → S) → Type ℓ
  Pres∧ t = (a b : S) → t (a ∧ b) ≡ (t a) ∧ (t b)

  -- The property Definition 4 states.
  PresTOP : (S → S) → Type ℓ
  PresTOP t = t TOP ≡ TOP

  Adm : (S → S) → Type ℓ
  Adm t = Pres∧ t × PresTOP t

  -- right unit, from commutativity
  ∧-unitR : (a : S) → a ∧ TOP ≡ a
  ∧-unitR a = ∧-comm a TOP ∙ ∧-unit a

  -- middle-four interchange; the workhorse for the clamp and for
  -- pointwise meets of modes.
  interchange : (x y z w : S) → (x ∧ y) ∧ (z ∧ w) ≡ (x ∧ z) ∧ (y ∧ w)
  interchange x y z w =
      (x ∧ y) ∧ (z ∧ w)   ≡⟨ ∧-assoc x y (z ∧ w) ⟩
      x ∧ (y ∧ (z ∧ w))   ≡⟨ cong (x ∧_) (sym (∧-assoc y z w)) ⟩
      x ∧ ((y ∧ z) ∧ w)   ≡⟨ cong (λ u → x ∧ (u ∧ w)) (∧-comm y z) ⟩
      x ∧ ((z ∧ y) ∧ w)   ≡⟨ cong (x ∧_) (∧-assoc z y w) ⟩
      x ∧ (z ∧ (y ∧ w))   ≡⟨ sym (∧-assoc x z (y ∧ w)) ⟩
      (x ∧ z) ∧ (y ∧ w)   ∎

  ----------------------------------------------------------------
  -- 1a. The admissible modes are a monoid and a meet-semilattice.
  ----------------------------------------------------------------

  id-Adm : Adm (λ s → s)
  id-Adm = (λ _ _ → refl) , refl

  constTop : S → S
  constTop _ = TOP

  constTop-Adm : Adm constTop
  constTop-Adm = (λ _ _ → sym (∧-unit TOP)) , refl

  comp-Adm : {t u : S → S} → Adm t → Adm u → Adm (λ s → t (u s))
  comp-Adm {t} {u} (pt , qt) (pu , qu) =
      (λ a b → cong t (pu a b) ∙ pt (u a) (u b))
    , (cong t qu ∙ qt)

  meet-Adm : {t u : S → S} → Adm t → Adm u → Adm (λ s → (t s) ∧ (u s))
  meet-Adm {t} {u} (pt , qt) (pu , qu) =
      (λ a b →
          (t (a ∧ b)) ∧ (u (a ∧ b))       ≡⟨ cong (λ z → z ∧ (u (a ∧ b))) (pt a b) ⟩
          ((t a) ∧ (t b)) ∧ (u (a ∧ b))   ≡⟨ cong (λ z → ((t a) ∧ (t b)) ∧ z) (pu a b) ⟩
          ((t a) ∧ (t b)) ∧ ((u a) ∧ (u b))
                                          ≡⟨ interchange (t a) (t b) (u a) (u b) ⟩
          ((t a) ∧ (u a)) ∧ ((t b) ∧ (u b)) ∎)
    , (cong (λ z → z ∧ (u TOP)) qt ∙ cong (TOP ∧_) qu ∙ ∧-unit TOP)

  ----------------------------------------------------------------
  -- 1b. CLAMP COLLAPSE.  OBLIGATION.md (absent from this repository)'s VALUE mode is illegal or trivial.
  ----------------------------------------------------------------

  clamp : S → S → S
  clamp c s = s ∧ c

  -- The clamp does preserve binary meets: this half of Prop. O2.3 is true.
  clamp-Pres∧ : (c : S) → Pres∧ (clamp c)
  clamp-Pres∧ c a b =
      (a ∧ b) ∧ c           ≡⟨ cong (λ z → (a ∧ b) ∧ z) (sym (∧-idem c)) ⟩
      (a ∧ b) ∧ (c ∧ c)     ≡⟨ interchange a b c c ⟩
      (a ∧ c) ∧ (b ∧ c)     ∎

  -- But Definition 4 also demands t TOP = TOP, and that forces c = TOP.
  clampTop : (c : S) → PresTOP (clamp c) → c ≡ TOP
  clampTop c p = sym (∧-unit c) ∙ p

  -- ... whereupon the clamp is the identity, pointwise.
  clampTrivial : (c : S) → PresTOP (clamp c) → (s : S) → clamp c s ≡ s
  clampTrivial c p s = cong (s ∧_) (clampTop c p) ∙ ∧-unitR s

  ----------------------------------------------------------------
  -- 1c. THRESHOLDS.  A legal family the note's vocabulary omits.
  ----------------------------------------------------------------

  thr : (S → Bool) → S → S → S
  thr χ b s = if χ s then TOP else b

  -- the four-case core, on Bool values, so no `with` is needed
  thrStep : (u v : Bool) (b : S)
          → (if (u && v) then TOP else b)
              ≡ ((if u then TOP else b) ∧ (if v then TOP else b))
  thrStep true  true  b = sym (∧-unit TOP)
  thrStep true  false b = sym (∧-unit b)
  thrStep false true  b = sym (∧-unitR b)
  thrStep false false b = sym (∧-idem b)

  -- chi is a *filter test*: its true-set is closed under meet and upward
  -- closed.  Both are packaged in the single multiplicativity equation.
  thr-Pres∧ : (χ : S → Bool) (b : S)
            → ((x y : S) → χ (x ∧ y) ≡ (χ x) && (χ y))
            → Pres∧ (thr χ b)
  thr-Pres∧ χ b mult a c =
      cong (λ z → if z then TOP else b) (mult a c) ∙ thrStep (χ a) (χ c) b

  thr-PresTOP : (χ : S → Bool) (b : S) → χ TOP ≡ true → PresTOP (thr χ b)
  thr-PresTOP χ b q = cong (λ z → if z then TOP else b) q

  thr-Adm : (χ : S → Bool) (b : S)
          → ((x y : S) → χ (x ∧ y) ≡ (χ x) && (χ y))
          → χ TOP ≡ true
          → Adm (thr χ b)
  thr-Adm χ b mult q = thr-Pres∧ χ b mult , thr-PresTOP χ b q

------------------------------------------------------------------------
-- 2. The three-element chain, and the certified counterexample
------------------------------------------------------------------------

data Three : Type where
  bot mid top : Three

_∧₃_ : Three → Three → Three
bot ∧₃ _   = bot
mid ∧₃ bot = bot
mid ∧₃ mid = mid
mid ∧₃ top = mid
top ∧₃ y   = y

∧₃-idem : (a : Three) → a ∧₃ a ≡ a
∧₃-idem bot = refl
∧₃-idem mid = refl
∧₃-idem top = refl

∧₃-comm : (a b : Three) → a ∧₃ b ≡ b ∧₃ a
∧₃-comm bot bot = refl
∧₃-comm bot mid = refl
∧₃-comm bot top = refl
∧₃-comm mid bot = refl
∧₃-comm mid mid = refl
∧₃-comm mid top = refl
∧₃-comm top bot = refl
∧₃-comm top mid = refl
∧₃-comm top top = refl

∧₃-assoc : (a b c : Three) → (a ∧₃ b) ∧₃ c ≡ a ∧₃ (b ∧₃ c)
∧₃-assoc bot bot bot = refl
∧₃-assoc bot bot mid = refl
∧₃-assoc bot bot top = refl
∧₃-assoc bot mid bot = refl
∧₃-assoc bot mid mid = refl
∧₃-assoc bot mid top = refl
∧₃-assoc bot top bot = refl
∧₃-assoc bot top mid = refl
∧₃-assoc bot top top = refl
∧₃-assoc mid bot bot = refl
∧₃-assoc mid bot mid = refl
∧₃-assoc mid bot top = refl
∧₃-assoc mid mid bot = refl
∧₃-assoc mid mid mid = refl
∧₃-assoc mid mid top = refl
∧₃-assoc mid top bot = refl
∧₃-assoc mid top mid = refl
∧₃-assoc mid top top = refl
∧₃-assoc top bot bot = refl
∧₃-assoc top bot mid = refl
∧₃-assoc top bot top = refl
∧₃-assoc top mid bot = refl
∧₃-assoc top mid mid = refl
∧₃-assoc top mid top = refl
∧₃-assoc top top bot = refl
∧₃-assoc top top mid = refl
∧₃-assoc top top top = refl

∧₃-unit : (a : Three) → top ∧₃ a ≡ a
∧₃-unit a = refl

module M3 = Modes _∧₃_ top ∧₃-idem ∧₃-comm ∧₃-assoc ∧₃-unit

------------------------------------------------------------------------
-- 2a. discrimination on Three (encode/decode, no library dependency)
------------------------------------------------------------------------

Code : Three → Three → Type
Code bot bot = Unit
Code mid mid = Unit
Code top top = Unit
Code _   _   = ⊥

encode : (x : Three) → Code x x
encode bot = tt
encode mid = tt
encode top = tt

decode : {x y : Three} → x ≡ y → Code x y
decode {x} p = subst (Code x) p (encode x)

------------------------------------------------------------------------
-- 2b. theta : the missing admissible mode
--
--   theta bot = bot ,  theta mid = top ,  theta top = top
--
-- Read in the calculus: "this edge transmits the source's scope
-- unrestricted provided the source is at least mid, and transmits the
-- floor bot otherwise".  That is a hypothesis check, expressed as a
-- transfer rather than as a generated obligation.
------------------------------------------------------------------------

χ₃ : Three → Bool
χ₃ bot = false
χ₃ mid = true
χ₃ top = true

χ₃-mult : (x y : Three) → χ₃ (x ∧₃ y) ≡ (χ₃ x) && (χ₃ y)
χ₃-mult bot bot = refl
χ₃-mult bot mid = refl
χ₃-mult bot top = refl
χ₃-mult mid bot = refl
χ₃-mult mid mid = refl
χ₃-mult mid top = refl
χ₃-mult top bot = refl
χ₃-mult top mid = refl
χ₃-mult top top = refl

χ₃-top : χ₃ top ≡ true
χ₃-top = refl

θ : Three → Three
θ = M3.thr χ₃ bot

-- (i) theta is admissible: it preserves binary meets and TOP, hence keeps
--     Theorem O2 exact (sigma* = MOP) if added to the mode vocabulary.
θ-Adm : M3.Adm θ
θ-Adm = M3.thr-Adm χ₃ bot χ₃-mult χ₃-top

-- (ii) theta is none of the three named modes.

θ-not-id : ((s : Three) → θ s ≡ s) → ⊥
θ-not-id h = decode (h mid)          -- Code top mid = ⊥

θ-not-constTop : ((s : Three) → θ s ≡ M3.constTop s) → ⊥
θ-not-constTop h = decode (h bot)    -- Code bot top = ⊥

θ-not-clamp : (c : Three) → ((s : Three) → θ s ≡ M3.clamp c s) → ⊥
θ-not-clamp bot h = decode (h mid)   -- Code top (mid /\ bot = bot) = ⊥
θ-not-clamp mid h = decode (h mid)   -- Code top (mid /\ mid = mid) = ⊥
θ-not-clamp top h = decode (h mid)   -- Code top (mid /\ top = mid) = ⊥

------------------------------------------------------------------------
-- 3. The statement, packaged.
--
-- OBLIGATION.md (absent from this repository) Prop. O2.3 lists identity / constant-TOP / clamp and
-- concludes distributivity.  The conclusion is true; the list is not
-- exhaustive, and one of its three entries is illegal under the note's
-- own Definition 4 unless it degenerates to the identity.
------------------------------------------------------------------------

ModeListIncomplete : Type
ModeListIncomplete =
    M3.Adm θ
  × (((s : Three) → θ s ≡ s) → ⊥)
  × (((s : Three) → θ s ≡ M3.constTop s) → ⊥)
  × ((c : Three) → ((s : Three) → θ s ≡ M3.clamp c s) → ⊥)

modeListIncomplete : ModeListIncomplete
modeListIncomplete = θ-Adm , θ-not-id , θ-not-constTop , θ-not-clamp
