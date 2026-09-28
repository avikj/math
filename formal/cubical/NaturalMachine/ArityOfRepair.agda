{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ArityOfRepair
--
-- The DELTA on NaturalMachine.FillabilityCertificate, for
-- notes/FILLABILITY_AS_SUCCESS.md (absent from this repository) (seed 177).
--
-- That module formalises the note's §2–§4: the two fillability
-- predicates, their strict separation (A∞), the decision procedure that
-- consumes finite branching, and Theorem 4.1's truncation bound.  It
-- does NOT touch the note's §5, which the note itself calls its
-- classification finding:
--
--     Theorem 5.3.  The dividing line for quantitative defects is NOT
--     "presupposes an attainable distinguished zero" (Thm A) but the
--     ARITY of the repair certificate (Thm B).  Γ⇑ escapes Thm A —
--     its success predicate Fill_∞ presupposes no zero — and is still
--     caught by Thm B, whose proof uses only unarity.
--
-- This module makes that a typing fact.  The whole point is that the
-- impossibility is visible in the SIGNATURE of the operator: the
-- refuted objects below mention no zero, no distinguished element, no
-- FillSys and no tower.  They mention an arity and an input type.
--
-- HEADLINE STATEMENTS (all checked, no postulates, no holes, --safe):
--
--  1. Bounds / Certifies / Tight / pinned
--                       A repair certificate for a QUANTITATIVE defect
--                       is bilateral: a pair (lo , hi) with
--                       lo ≤ δ ≤ hi (the note's C₋ ⪯ δ ⪯ C₊,
--                       §5.2).  `pinned` proves the elementary fact
--                       that a tight bilateral certificate DETERMINES
--                       the magnitude — which is why unarity bites.
--
--  2. unary-lower-always
--                       One side is free: every slot admits a unary
--                       lower bound (lo := 0).  This is Theorem B's
--                       "at most one of C₊, C₋", positive half, and it
--                       is what stops the negative below from being a
--                       triviality about functions.
--
--  3. no-unary-bilateral
--                       Theorem B, formalised.  If the structural
--                       presentation is AMBIGUOUS — two data with the
--                       same presentation and different magnitudes —
--                       then no operation whose only input is that
--                       presentation is sound and tight.  The proof is
--                       four steps and uses nothing about zeros.
--
--  4. no-nary-bilateral
--                       Arity within the same input type never helps:
--                       for every n, an n-ary operation on structural
--                       presentations is refuted, because the certificate
--                       for a single datum has only that datum to be
--                       computed from (diagonal application).  `Ar` makes
--                       the arity an explicit index of the type.
--
--  5. binary-heterogeneous-works
--                       …and the dividing line really is arity, not
--                       impossibility: a BINARY operation taking the
--                       presentation together with a construction is
--                       sound and tight, exhibited.
--
--  6. second-argument-separates
--                       The note's slogan, as a theorem: "the filler
--                       would have to be the proof" (§5.2).  ANY correct
--                       binary operation's second argument must already
--                       distinguish the ambiguous pair — so the second
--                       input is not coherence data, it carries the whole
--                       content of the missing bound.
--
--  7. tower-readout-caught
--                       Obstruction 1 of §5.2, for Γ⇑ specifically and
--                       for any successor mode: whatever tower type T an
--                       operation on structural data produces, and
--                       whatever readout T → Bounds is applied to it, the
--                       composite is a unary operation on presentations
--                       and is refuted by 3.  T is universally
--                       quantified — nothing about towers is used.
--
--  8. arity-not-zero    Theorem 5.3 as one term: the A∞ system of
--                       FillabilityCertificate §5 has a total branch
--                       with NO level ever distinguished (so a Fill_∞
--                       success presupposes no attainable zero, and
--                       Thm A's criterion does not apply to it), AND the
--                       arity obstruction of 3 holds regardless.  The
--                       two components are independent terms; the bundle
--                       is the statement that the second survives the
--                       failure of the first.
--
------------------------------------------------------------------------

module NaturalMachine.ArityOfRepair where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-antisym; zero-≤)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import NaturalMachine.FillabilityCertificate
  using (FillSys; Obs; IsZero; A∞; branchA∞; Branch)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1.  A quantitative slot, and what a repair certificate for one is.
--
--      `Datum` is the defect-carrying datum; `mag` is the magnitude the
--      defect actually has (the truth); `pres` is the STRUCTURAL
--      presentation — everything an operation on defect-carrying data
--      gets to see.  The note's §5.2 Obstruction 1 is exactly the
--      observation that Γ⇑'s domain is a structural presentation: a
--      parallel pair u , v with u ≠ v, and no more.
------------------------------------------------------------------------

record QSlot (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Datum : Type ℓ
    Str   : Type ℓ
    pres  : Datum → Str
    mag   : Datum → ℕ

open QSlot public

-- A bilateral certificate: a lower and an upper bound, together.
record Bounds : Type where
  constructor bounds
  field
    lo hi : ℕ

open Bounds public

-- Soundness of a bilateral certificate for a magnitude m: C₋ ⪯ δ ⪯ C₊.
Certifies : Bounds → ℕ → Type
Certifies b m = (lo b ≤ m) × (m ≤ hi b)

-- Tightness: the two sides meet.  This is what "closing the gap"
-- means in §5.2 — the note's Lemma 3.2 "is an inequality, not a
-- constant" is precisely the failure of tightness.
Tight : Bounds → Type
Tight b = hi b ≡ lo b

-- A tight bilateral certificate DETERMINES the magnitude.  Everything
-- below is a consequence of this one line.
pinned : (b : Bounds) (m : ℕ) → Certifies b m → Tight b → lo b ≡ m
pinned b m (l≤m , m≤h) t = ≤-antisym l≤m (subst (m ≤_) t m≤h)

------------------------------------------------------------------------
-- §2.  Ambiguity: the hypothesis that makes the arity bite.
--
--      The structural presentation does not determine the magnitude.
--      This is the formal content of "a quantitative defect has no
--      presentation as a parallel pair" (§5.2): the pair can be named,
--      and naming it is `pres`; what the name omits is the magnitude.
------------------------------------------------------------------------

Ambiguous : QSlot ℓ → Type ℓ
Ambiguous S =
  Σ[ x ∈ Datum S ] Σ[ y ∈ Datum S ]
    (pres S x ≡ pres S y) × (¬ (mag S x ≡ mag S y))

-- Not vacuous: a two-element slot with one presentation and two
-- magnitudes.  (`Bool` as the datum; `Unit` as everything visible.)
toySlot : QSlot ℓ-zero
Datum toySlot   = Bool
Str   toySlot   = Unit
pres  toySlot _ = tt
mag   toySlot true  = 0
mag   toySlot false = 1

ambiguousToy : Ambiguous toySlot
ambiguousToy = true , false , refl , λ p → true≢false (magPath p)
  where
  -- 0 ≡ 1 in ℕ would give true ≡ false by reading the bit back off.
  bit : ℕ → Bool
  bit zero    = true
  bit (suc _) = false

  magPath : (0 ≡ 1) → true ≡ false
  magPath p = cong bit p

------------------------------------------------------------------------
-- §3.  Theorem B, positive half: one side is always unarily available.
--
--      Without this the negative in §4 would be a triviality about
--      functions failing to be defined.  It is not: the operation is
--      available, sound, and unary — it is only ever unilateral.
------------------------------------------------------------------------

UnarySoundLower : (S : QSlot ℓ) → (Str S → Bounds) → Type ℓ
UnarySoundLower S g = (x : Datum S) → lo (g (pres S x)) ≤ mag S x

unary-lower-always : (S : QSlot ℓ) → Σ[ g ∈ (Str S → Bounds) ] UnarySoundLower S g
unary-lower-always S = (λ _ → bounds 0 0) , λ _ → zero-≤

------------------------------------------------------------------------
-- §4.  Theorem B, the negative.  ARITY, and nothing else, is used.
--
--      Note what does NOT appear in the statement: no distinguished
--      element, no zero, no FillSys, no tower, no success predicate.
--      That is the content of Theorem 5.3 — this obstruction is
--      independent of Theorem A, so an operation that escapes Thm A by
--      having a non-singleton success predicate (Γ⇑, whose success is
--      Fill_∞) is caught here anyway.
------------------------------------------------------------------------

-- A unary bilateral repair for a slot: sees only the presentation,
-- returns a bilateral certificate, sound at every datum and tight.
record UnaryBilateral (S : QSlot ℓ) : Type ℓ where
  field
    op    : Str S → Bounds
    sound : (x : Datum S) → Certifies (op (pres S x)) (mag S x)
    tight : (s : Str S) → Tight (op s)

open UnaryBilateral public

no-unary-bilateral : (S : QSlot ℓ) → Ambiguous S → ¬ UnaryBilateral S
no-unary-bilateral S (x , y , same , diff) G = diff magEq
  where
  px = pinned (op G (pres S x)) (mag S x) (sound G x) (tight G (pres S x))
  py = pinned (op G (pres S y)) (mag S y) (sound G y) (tight G (pres S y))

  magEq : mag S x ≡ mag S y
  magEq = sym px ∙ cong (λ s → lo (op G s)) same ∙ py

------------------------------------------------------------------------
-- §5.  Arity within the same input type never helps.
--
--      `Ar n A B` is the type of n-ary functions A → ⋯ → A → B, so the
--      arity is an index of the TYPE and the theorem below is indexed by
--      it.  For a single datum's certificate the only data available is
--      that datum, so an n-ary operation is applied diagonally; the
--      refutation of §4 goes through verbatim.
--
--      This is the exact sense in which the note's "to reach a
--      quantitative defect an operation would have to be binary in its
--      certificate" must be read: binary in a SECOND KIND of input
--      (§6), not n-ary in defect-carrying data.
------------------------------------------------------------------------

Ar : {ℓ ℓ' : Level} → ℕ → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
Ar {ℓ} {ℓ'} zero    A B = Lift {j = ℓ} B
Ar          (suc n) A B = A → Ar n A B

diag : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) → Ar n A B → A → B
diag zero    b a = Lift.lower b
diag (suc n) f a = diag n (f a) a

record NaryBilateral (S : QSlot ℓ) (n : ℕ) : Type ℓ where
  field
    nop   : Ar n (Str S) Bounds
    nsound : (x : Datum S) → Certifies (diag n nop (pres S x)) (mag S x)
    ntight : (s : Str S) → Tight (diag n nop s)

open NaryBilateral public

nary→unary : (S : QSlot ℓ) (n : ℕ) → NaryBilateral S n → UnaryBilateral S
op    (nary→unary S n G) = diag n (nop G)
sound (nary→unary S n G) = nsound G
tight (nary→unary S n G) = ntight G

no-nary-bilateral : (S : QSlot ℓ) → Ambiguous S → (n : ℕ) → ¬ NaryBilateral S n
no-nary-bilateral S amb n G = no-unary-bilateral S amb (nary→unary S n G)

------------------------------------------------------------------------
-- §6.  The dividing line is arity, not impossibility.
--
--      Give the operation a SECOND input of a different kind — a
--      construction, evaluated by `ev`, attached to each datum — and a
--      sound, tight bilateral operation exists.  Exhibited, not
--      asserted.
------------------------------------------------------------------------

record WithConstruction (S : QSlot ℓ) : Type (ℓ-suc ℓ) where
  field
    Constr : Type ℓ
    attach : Datum S → Constr
    ev     : Constr → ℕ
    exact  : (x : Datum S) → ev (attach x) ≡ mag S x

open WithConstruction public

-- A binary heterogeneous operation: presentation AND construction.
record BinaryBilateral (S : QSlot ℓ) (W : WithConstruction S) : Type ℓ where
  field
    bop    : Str S → Constr W → Bounds
    bsound : (x : Datum S) → Certifies (bop (pres S x) (attach W x)) (mag S x)
    btight : (s : Str S) (c : Constr W) → Tight (bop s c)

open BinaryBilateral public

binary-heterogeneous-works :
  (S : QSlot ℓ) (W : WithConstruction S) → BinaryBilateral S W
bop    (binary-heterogeneous-works S W) _ c = bounds (ev W c) (ev W c)
bsound (binary-heterogeneous-works S W) x =
  subst (λ m → ev W (attach W x) ≤ m) (exact W x) ≤-refl ,
  subst (λ m → m ≤ ev W (attach W x)) (exact W x) ≤-refl
btight (binary-heterogeneous-works S W) _ _ = refl

------------------------------------------------------------------------
-- §7.  "The filler would have to be the proof" (§5.2), as a theorem.
--
--      ANY sound and tight binary operation — not just the one above —
--      has a second argument that already separates the ambiguous pair.
--      So the second input is not a coherence datum that the operation
--      processes; it carries the missing bound itself.  This is the
--      formal form of the note's slogan, and it is why the note says a
--      binary certificate "is not an operation on defect-carrying data;
--      it is a pair of theorems".
------------------------------------------------------------------------

second-argument-separates :
  (S : QSlot ℓ) (W : WithConstruction S)
  → BinaryBilateral S W
  → (x y : Datum S)
  → pres S x ≡ pres S y
  → ¬ (mag S x ≡ mag S y)
  → ¬ (attach W x ≡ attach W y)
second-argument-separates S W G x y same diff attEq = diff magEq
  where
  px = pinned (bop G (pres S x) (attach W x)) (mag S x)
              (bsound G x) (btight G (pres S x) (attach W x))
  py = pinned (bop G (pres S y) (attach W y)) (mag S y)
              (bsound G y) (btight G (pres S y) (attach W y))

  argEq : bop G (pres S x) (attach W x) ≡ bop G (pres S y) (attach W y)
  argEq i = bop G (same i) (attEq i)

  magEq : mag S x ≡ mag S y
  magEq = sym px ∙ cong lo argEq ∙ py

------------------------------------------------------------------------
-- §8.  Obstruction 1 of §5.2, for Γ⇑ and for any successor mode.
--
--      Γ⇑ takes a structural presentation and returns a TOWER.  Whatever
--      the tower type is, and whatever readout is applied to it to
--      extract bounds, the composite is a unary operation on
--      presentations.  T is universally quantified: nothing about towers
--      is used, so this covers Γ⇑ without a model of Γ⇑, and covers a
--      sixth mode not yet named.
------------------------------------------------------------------------

tower-readout-caught :
  (S : QSlot ℓ) → Ambiguous S
  → {T : Type ℓ}
  → (Γ : Str S → T)                                   -- the operation
  → (readout : T → Bounds)                            -- bounds from the tower
  → ((x : Datum S) → Certifies (readout (Γ (pres S x))) (mag S x))
  → ((s : Str S) → Tight (readout (Γ s)))
  → ⊥
tower-readout-caught S amb Γ readout snd' tgt =
  no-unary-bilateral S amb
    (record { op = λ s → readout (Γ s) ; sound = snd' ; tight = tgt })

------------------------------------------------------------------------
-- §9.  Theorem 5.3, as one term.
--
--      Component 1: the A∞ system of FillabilityCertificate §5 has a
--      total branch (a Fill_∞ success) while NO level is ever
--      distinguished — `IsZero A∞ n d` is ⊥ by definition, so the
--      success predicate presupposes no attainable zero and Theorem A's
--      criterion does not apply.
--
--      Component 2: the arity obstruction holds anyway, and its
--      statement mentions no zero.
--
--      The bundle is the note's Theorem 5.3: Thm A's criterion separates
--      four of five; the arity criterion separates five of five.
------------------------------------------------------------------------

escapes-zero-criterion :
  Branch A∞ 0 tt × ((n : ℕ) (d : Obs A∞ n) → ¬ IsZero A∞ n d)
escapes-zero-criterion = branchA∞ 0 tt , λ _ _ z → z

arity-not-zero :
    (Branch A∞ 0 tt × ((n : ℕ) (d : Obs A∞ n) → ¬ IsZero A∞ n d))
  × ((S : QSlot ℓ) → Ambiguous S → ¬ UnaryBilateral S)
arity-not-zero = escapes-zero-criterion , no-unary-bilateral
