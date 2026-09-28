{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- PramanaSamplava_MinDeletionExceedsMaxDisjointSupports
--
-- ONE derivation hypergraph, six rules, five facts, one seed, in which
--
--     min |D| such that v dies      =  2
--     max pairwise-disjoint supports =  1
--     the fractional optimum         =  3/2
--
-- so the deletion min-max FAILS, and it fails at the smallest place a
-- conjunctive premise can be put.
--
-- WHAT THIS IS ABOUT.  `notes/REVISION_DERIVATION_HYPERGRAPH.md` (absent from this repository) proves
-- the exact deletion law for a finite AND/OR derivation hypergraph:
--
--     v ∈ Cl_D(I)   ⟺   some minimal support S of v has S ∩ D = ∅,
--
-- i.e. v dies exactly when the deleted set D is a HITTING SET of the
-- minimal-support antichain A(v).  That note computes A(v) and says
-- nothing about the size of the cheapest killing D.  This module decides
-- that question on one instance, in the direction that costs something.
--
-- NAME.  Nyya holds *prama-samplava*: one and the same object may be
-- established by more than one pramāṇa — the stock illustration being
-- fire on a hill, reached by perception, by inference and by testimony
-- (Vtsyyana, *Nyyabhya*, c. 400 CE, on the Nyyastra's opening
-- enumeration of the pramas).  Dignga holds the opposite,
-- *prama-vyavasth*: exactly two pramas, each with its OWN object,
-- svalakaa for perception and smnyalakaa for inference, so a single
-- object is not multiply established (*Pramāṇasamuccaya* I.2, c. 480–540
-- CE).  The object formalised below — one fact carrying several
-- independent supports, and the question of what survives when supports
-- are removed — is samplava's object, and the module is named for it.
--
-- PRIOR ART, searched before writing (per CLAUDE.md (absent from this repository)), all on disk:
--   * `notes/HISTORY_DIGEST.md` (absent from this repository) attributes the deletion law itself to de
--     Kleer's ATMS label semantics (1986), "essentially verbatim".  The
--     law is used, and independently
--     re-verified on this instance (`deletion-law`).
--   * `notes/PROOF_SUPPORT_COMPLEMENTARITY.md` (absent from this repository) proves the retention-side
--     observable q_v is submodular iff every minimal support is a
--     singleton.  DIFFERENT statement, and §5 of the companion message
--     shows the two failures are independent: on the unary fragment
--     q_v is already non-submodular while the deletion min-max is still
--     integral.
--   * `notes/OBLIGATION_S7_MINCUT.md` (absent from this repository) + `formal/cubical/ObligationMinCut.agda`
--     compute an audit burden as an exact max-flow/min-cut in a
--     DIGRAPH.  That is the unary fragment, where the min-max holds.
--
-- METHOD.  Everything below is closed Boolean/ℕ computation over the 64
-- deletion sets, discharged by `refl`.  CLAUDE.md (absent from this repository): "a finite exhaustive
-- verification … produces mathematical objects, not measurements."  No
-- floating point, no fitting, no sampling.
------------------------------------------------------------------------

module PramanaSamplava_MinDeletionExceedsMaxDisjointSupports where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; _or_)
open import Cubical.Data.Bool.Properties using (false≢true)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)

------------------------------------------------------------------------
-- §0  The instance.
--
-- Facts:  s (the sole seed), a, b, p, v.
-- Rules:
--
--   r1 :  s      ⟶ a
--   r2 :  s      ⟶ b
--   r3 :  a      ⟶ p
--   r4 :  b      ⟶ p
--   r5 :  p      ⟶ v
--   r6 : {a,b}   ⟶ v          -- the ONE conjunctive rule
--
-- Read plainly: v has two alternative last steps (r5 and r6); p has two
-- alternative last steps (r3 and r4); and r6 needs both branches at
-- once.  That is the whole construction.
--
-- Its three minimal supports for v are
--
--   S1 = {r1, r3, r5}    S2 = {r2, r4, r5}    S3 = {r1, r2, r6}
--
-- which pairwise share exactly one rule (r5, r1, r2 respectively) and
-- have empty common intersection.  Everything below is that sentence,
-- checked.

data Rule : Type where
  r1 r2 r3 r4 r5 r6 : Rule

-- A deletion set is its own characteristic function: D r = true means
-- "rule r has been deleted".
Del : Type
Del = Rule → Bool

alive : Del → Rule → Bool
alive D r = not (D r)

------------------------------------------------------------------------
-- §1  The least fixed point Cl_D(I), and the closed form.
--
-- `Facts` is the marking of the four non-seed facts (s is a seed and is
-- always present).  `step` is one round of the closure operator with the
-- rules of D removed.  `factA … factV` is the claimed closed form.  §1.2
-- checks, over all 64 deletion sets, that the closed form is reached by
-- four rounds from the empty marking and is a fixed point — which is the
-- Kleene characterisation of the least fixed point for a monotone
-- operator on this four-element Boolean lattice.

record Facts : Type where
  constructor mkF
  field
    fA fB fP fV : Bool

open Facts

step : Del → Facts → Facts
step D (mkF a b p v) =
  mkF (a or alive D r1)
      (b or alive D r2)
      (p or ((alive D r3 and a) or (alive D r4 and b)))
      (v or ((alive D r5 and p) or (alive D r6 and (a and b))))

bot : Facts
bot = mkF false false false false

iter4 : Del → Facts
iter4 D = step D (step D (step D (step D bot)))

-- The closed form, written out.
factA factB factP factV : Del → Bool
factA D = alive D r1
factB D = alive D r2
factP D = (alive D r3 and factA D) or (alive D r4 and factB D)
factV D = (alive D r5 and factP D) or (alive D r6 and (factA D and factB D))

closed : Del → Facts
closed D = mkF (factA D) (factB D) (factP D) (factV D)

------------------------------------------------------------------------
-- §2  The exhaustive-check machinery: a Boolean tautology over the six
--     deletion bits is checked by `refl` and then eliminated into a
--     statement about an arbitrary D.

∀B : (Bool → Bool) → Bool
∀B f = f true and f false

andT-L : (x y : Bool) → (x and y) ≡ true → x ≡ true
andT-L true  y _ = refl
andT-L false y q = ⊥-rec (false≢true q)

andT-R : (x y : Bool) → (x and y) ≡ true → y ≡ true
andT-R true  y q = q
andT-R false y q = ⊥-rec (false≢true q)

∀B-elim : (f : Bool → Bool) → ∀B f ≡ true → (x : Bool) → f x ≡ true
∀B-elim f q true  = andT-L (f true) (f false) q
∀B-elim f q false = andT-R (f true) (f false) q

Pred6 : Type
Pred6 = Bool → Bool → Bool → Bool → Bool → Bool → Bool

∀B6 : Pred6 → Bool
∀B6 g = ∀B λ x₁ → ∀B λ x₂ → ∀B λ x₃ → ∀B λ x₄ → ∀B λ x₅ → ∀B λ x₆ →
        g x₁ x₂ x₃ x₄ x₅ x₆

∀B6-elim : (g : Pred6) → ∀B6 g ≡ true
         → (x₁ x₂ x₃ x₄ x₅ x₆ : Bool) → g x₁ x₂ x₃ x₄ x₅ x₆ ≡ true
∀B6-elim g q x₁ x₂ x₃ x₄ x₅ x₆ = e6
  where
  f1 : Bool → Bool
  f1 y₁ = ∀B λ y₂ → ∀B λ y₃ → ∀B λ y₄ → ∀B λ y₅ → ∀B λ y₆ → g y₁ y₂ y₃ y₄ y₅ y₆
  e1 : f1 x₁ ≡ true
  e1 = ∀B-elim f1 q x₁

  f2 : Bool → Bool
  f2 y₂ = ∀B λ y₃ → ∀B λ y₄ → ∀B λ y₅ → ∀B λ y₆ → g x₁ y₂ y₃ y₄ y₅ y₆
  e2 : f2 x₂ ≡ true
  e2 = ∀B-elim f2 e1 x₂

  f3 : Bool → Bool
  f3 y₃ = ∀B λ y₄ → ∀B λ y₅ → ∀B λ y₆ → g x₁ x₂ y₃ y₄ y₅ y₆
  e3 : f3 x₃ ≡ true
  e3 = ∀B-elim f3 e2 x₃

  f4 : Bool → Bool
  f4 y₄ = ∀B λ y₅ → ∀B λ y₆ → g x₁ x₂ x₃ y₄ y₅ y₆
  e4 : f4 x₄ ≡ true
  e4 = ∀B-elim f4 e3 x₄

  f5 : Bool → Bool
  f5 y₅ = ∀B λ y₆ → g x₁ x₂ x₃ x₄ y₅ y₆
  e5 : f5 x₅ ≡ true
  e5 = ∀B-elim f5 e4 x₅

  f6 : Bool → Bool
  f6 y₆ = g x₁ x₂ x₃ x₄ x₅ y₆
  e6 : f6 x₆ ≡ true
  e6 = ∀B-elim f6 e5 x₆

-- The tabulated deletion set: D6 x₁ … x₆ deletes rule rᵢ iff xᵢ.
D6 : Bool → Bool → Bool → Bool → Bool → Bool → Del
D6 x₁ x₂ x₃ x₄ x₅ x₆ r1 = x₁
D6 x₁ x₂ x₃ x₄ x₅ x₆ r2 = x₂
D6 x₁ x₂ x₃ x₄ x₅ x₆ r3 = x₃
D6 x₁ x₂ x₃ x₄ x₅ x₆ r4 = x₄
D6 x₁ x₂ x₃ x₄ x₅ x₆ r5 = x₅
D6 x₁ x₂ x₃ x₄ x₅ x₆ r6 = x₆

-- Every D is definitionally its own tabulation, because every function
-- below reads D only at the six rules.
tabulate : (D : Del) (r : Rule) → D6 (D r1) (D r2) (D r3) (D r4) (D r5) (D r6) r ≡ D r
tabulate D r1 = refl
tabulate D r2 = refl
tabulate D r3 = refl
tabulate D r4 = refl
tabulate D r5 = refl
tabulate D r6 = refl

eqB : Bool → Bool → Bool
eqB true  y = y
eqB false y = not y

eqB→≡ : (x y : Bool) → eqB x y ≡ true → x ≡ y
eqB→≡ true  true  _ = refl
eqB→≡ true  false q = ⊥-rec (false≢true q)
eqB→≡ false true  q = ⊥-rec (false≢true q)
eqB→≡ false false _ = refl

eqF : Facts → Facts → Bool
eqF (mkF a b p v) (mkF a' b' p' v') =
  eqB a a' and (eqB b b' and (eqB p p' and eqB v v'))

eqF→≡ : (f g : Facts) → eqF f g ≡ true → f ≡ g
eqF→≡ (mkF a b p v) (mkF a' b' p' v') q =
  λ i → mkF (eqB→≡ a a' qa i) (eqB→≡ b b' qb i) (eqB→≡ p p' qp i) (eqB→≡ v v' qv i)
  where
  qa = andT-L (eqB a a') _ q
  q1 = andT-R (eqB a a') _ q
  qb = andT-L (eqB b b') _ q1
  q2 = andT-R (eqB b b') _ q1
  qp = andT-L (eqB p p') _ q2
  qv = andT-R (eqB p p') _ q2

------------------------------------------------------------------------
-- §1.2  The closed form IS the least fixed point.

gKleene : Pred6
gKleene x₁ x₂ x₃ x₄ x₅ x₆ =
  eqF (iter4 (D6 x₁ x₂ x₃ x₄ x₅ x₆)) (closed (D6 x₁ x₂ x₃ x₄ x₅ x₆))

gFix : Pred6
gFix x₁ x₂ x₃ x₄ x₅ x₆ =
  eqF (step (D6 x₁ x₂ x₃ x₄ x₅ x₆) (closed (D6 x₁ x₂ x₃ x₄ x₅ x₆)))
      (closed (D6 x₁ x₂ x₃ x₄ x₅ x₆))

private
  kleene-taut : ∀B6 gKleene ≡ true
  kleene-taut = refl

  fix-taut : ∀B6 gFix ≡ true
  fix-taut = refl

-- Four rounds from the empty marking reach the closed form.
kleene : (D : Del) → iter4 D ≡ closed D
kleene D =
  eqF→≡ (iter4 D) (closed D)
        (∀B6-elim gKleene kleene-taut (D r1) (D r2) (D r3) (D r4) (D r5) (D r6))

-- And the closed form is a fixed point of the closure operator.
closed-is-fixed : (D : Del) → step D (closed D) ≡ closed D
closed-is-fixed D =
  eqF→≡ (step D (closed D)) (closed D)
        (∀B6-elim gFix fix-taut (D r1) (D r2) (D r3) (D r4) (D r5) (D r6))

------------------------------------------------------------------------
-- §3  The three supports, and the deletion law on this instance.

inS1 inS2 inS3 : Rule → Bool
inS1 r1 = true ; inS1 r2 = false ; inS1 r3 = true
inS1 r4 = false ; inS1 r5 = true ; inS1 r6 = false

inS2 r1 = false ; inS2 r2 = true ; inS2 r3 = false
inS2 r4 = true  ; inS2 r5 = true ; inS2 r6 = false

inS3 r1 = true ; inS3 r2 = true ; inS3 r3 = false
inS3 r4 = false ; inS3 r5 = false ; inS3 r6 = true

-- D hits S iff D deletes some rule of S.  (S is applied first so the
-- closed membership bit drives the reduction.)
hits : Del → (Rule → Bool) → Bool
hits D S = (S r1 and D r1)
        or ((S r2 and D r2)
        or ((S r3 and D r3)
        or ((S r4 and D r4)
        or ((S r5 and D r5)
        or  (S r6 and D r6)))))

gLaw : Pred6
gLaw x₁ x₂ x₃ x₄ x₅ x₆ =
  eqB (factV (D6 x₁ x₂ x₃ x₄ x₅ x₆))
      (not (hits (D6 x₁ x₂ x₃ x₄ x₅ x₆) inS1
        and (hits (D6 x₁ x₂ x₃ x₄ x₅ x₆) inS2
        and  hits (D6 x₁ x₂ x₃ x₄ x₅ x₆) inS3)))

private
  law-taut : ∀B6 gLaw ≡ true
  law-taut = refl

-- THEOREM 1 (the deletion law, this instance, independently verified).
-- v survives the deletion of D exactly when D fails to hit one of the
-- three supports.  This is `REVISION_DERIVATION_HYPERGRAPH` (1) — de
-- Kleer's ATMS label semantics — on an instance with a genuine AND rule.
deletion-law : (D : Del)
  → factV D ≡ not (hits D inS1 and (hits D inS2 and hits D inS3))
deletion-law D =
  eqB→≡ (factV D)
        (not (hits D inS1 and (hits D inS2 and hits D inS3)))
        (∀B6-elim gLaw law-taut (D r1) (D r2) (D r3) (D r4) (D r5) (D r6))

-- The three supports form an antichain: each has a rule the others lack.
-- With Theorem 1 this pins A(v) = {S1,S2,S3} exactly — the survival
-- function's DNF is ⋁ᵢ ⋀_{r∈Sᵢ} ¬d_r, whose minimal supports are the
-- minimal members of {S1,S2,S3}, i.e. all three.
S1∖S2 : (inS1 r3 and not (inS2 r3)) ≡ true
S1∖S2 = refl
S1∖S3 : (inS1 r5 and not (inS3 r5)) ≡ true
S1∖S3 = refl
S2∖S1 : (inS2 r4 and not (inS1 r4)) ≡ true
S2∖S1 = refl
S2∖S3 : (inS2 r5 and not (inS3 r5)) ≡ true
S2∖S3 = refl
S3∖S1 : (inS3 r6 and not (inS1 r6)) ≡ true
S3∖S1 = refl
S3∖S2 : (inS3 r6 and not (inS2 r6)) ≡ true
S3∖S2 = refl

------------------------------------------------------------------------
-- §4  ν = 1: no two supports are disjoint.

share-12 : (inS1 r5 and inS2 r5) ≡ true
share-12 = refl
share-13 : (inS1 r1 and inS3 r1) ≡ true
share-13 = refl
share-23 : (inS2 r2 and inS3 r2) ≡ true
share-23 = refl

-- …and no rule lies in all three, so the family has no common element
-- to be hit at cost one.  (Checked again, differently, by `no-singleton`
-- below, which does not go through the supports at all.)
no-common : (r : Rule) → (inS1 r and (inS2 r and inS3 r)) ≡ false
no-common r1 = refl
no-common r2 = refl
no-common r3 = refl
no-common r4 = refl
no-common r5 = refl
no-common r6 = refl

------------------------------------------------------------------------
-- §5  τ = 2: the cheapest deletion that kills v has size exactly two.

c : Bool → ℕ
c true  = 1
c false = 0

card : Del → ℕ
card D = c (D r1) + (c (D r2) + (c (D r3) + (c (D r4) + (c (D r5) + c (D r6)))))

ge2 : ℕ → Bool
ge2 zero          = false
ge2 (suc zero)    = false
ge2 (suc (suc _)) = true

data _≼_ : ℕ → ℕ → Type where
  z≼ : (n : ℕ) → zero ≼ n
  s≼ : {m n : ℕ} → m ≼ n → suc m ≼ suc n

ge2→ : (n : ℕ) → ge2 n ≡ true → 2 ≼ n
ge2→ zero          q = ⊥-rec (false≢true q)
ge2→ (suc zero)    q = ⊥-rec (false≢true q)
ge2→ (suc (suc m)) _ = s≼ (s≼ (z≼ m))

gTau : Pred6
gTau x₁ x₂ x₃ x₄ x₅ x₆ =
  factV (D6 x₁ x₂ x₃ x₄ x₅ x₆) or ge2 (card (D6 x₁ x₂ x₃ x₄ x₅ x₆))

private
  tau-taut : ∀B6 gTau ≡ true
  tau-taut = refl

-- THEOREM 2 (τ ≥ 2).  Any deletion set that kills v deletes at least two
-- rules.  Note this is proved from the closure directly; it does not use
-- the support list.
min-deletion-≥2 : (D : Del) → factV D ≡ false → 2 ≼ card D
min-deletion-≥2 D k = ge2→ (card D) lemma
  where
  taut : (factV D or ge2 (card D)) ≡ true
  taut = ∀B6-elim gTau tau-taut (D r1) (D r2) (D r3) (D r4) (D r5) (D r6)
  lemma : ge2 (card D) ≡ true
  lemma = sym (cong (λ t → t or ge2 (card D)) k) ∙ taut

-- Corollary, in the form the failure is used: deleting any ONE rule
-- leaves v derivable.  (Independent of the support list.)
single : Rule → Del
single r1 = λ { r1 → true ; _ → false }
single r2 = λ { r2 → true ; _ → false }
single r3 = λ { r3 → true ; _ → false }
single r4 = λ { r4 → true ; _ → false }
single r5 = λ { r5 → true ; _ → false }
single r6 = λ { r6 → true ; _ → false }

no-singleton-kills : (r : Rule) → factV (single r) ≡ true
no-singleton-kills r1 = refl
no-singleton-kills r2 = refl
no-singleton-kills r3 = refl
no-singleton-kills r4 = refl
no-singleton-kills r5 = refl
no-singleton-kills r6 = refl

-- THEOREM 3 (τ ≤ 2).  An explicit two-rule deletion that kills v:
-- delete r1 (so a is unreachable, killing S1 and S3) and r5 (killing S2).
Dcut : Del
Dcut r1 = true
Dcut r2 = false
Dcut r3 = false
Dcut r4 = false
Dcut r5 = true
Dcut r6 = false

cut-card : card Dcut ≡ 2
cut-card = refl

cut-kills : factV Dcut ≡ false
cut-kills = refl

------------------------------------------------------------------------
-- §6  τ* = ν* = 3/2, by two certificates scaled by 2.
--
-- All weights are doubled so that everything stays in ℕ: a "fractional
-- value 3/2" is here the integer 3 against a requirement of 2 per
-- constraint.

pickN : Bool → ℕ → ℕ
pickN true  n = n
pickN false _ = 0

sumOver : (Rule → Bool) → (Rule → ℕ) → ℕ
sumOver S w = pickN (S r1) (w r1)
            + (pickN (S r2) (w r2)
            + (pickN (S r3) (w r3)
            + (pickN (S r4) (w r4)
            + (pickN (S r5) (w r5)
            +  pickN (S r6) (w r6)))))

total : (Rule → ℕ) → ℕ
total w = w r1 + (w r2 + (w r3 + (w r4 + (w r5 + w r6))))

-- (a) A fractional hitting set of value 3/2: half on r1, r2, r5.
coverY : Rule → ℕ
coverY r1 = 1
coverY r2 = 1
coverY r3 = 0
coverY r4 = 0
coverY r5 = 1
coverY r6 = 0

cover-S1 : sumOver inS1 coverY ≡ 2
cover-S1 = refl
cover-S2 : sumOver inS2 coverY ≡ 2
cover-S2 = refl
cover-S3 : sumOver inS3 coverY ≡ 2
cover-S3 = refl
cover-value : total coverY ≡ 3
cover-value = refl

-- (b) A fractional packing of value 3/2: half on each support.  Its
-- feasibility condition is that no rule carries load above 2.
data Sup : Type where
  s1 s2 s3 : Sup

inSup : Sup → Rule → Bool
inSup s1 = inS1
inSup s2 = inS2
inSup s3 = inS3

packZ : Sup → ℕ
packZ _ = 1

load : Rule → ℕ
load r = pickN (inSup s1 r) (packZ s1)
       + (pickN (inSup s2 r) (packZ s2)
       +  pickN (inSup s3 r) (packZ s3))

le2 : ℕ → Bool
le2 zero                = true
le2 (suc zero)          = true
le2 (suc (suc zero))    = true
le2 (suc (suc (suc _))) = false

pack-feasible : (r : Rule) → le2 (load r) ≡ true
pack-feasible r1 = refl
pack-feasible r2 = refl
pack-feasible r3 = refl
pack-feasible r4 = refl
pack-feasible r5 = refl
pack-feasible r6 = refl

pack-value : (packZ s1 + (packZ s2 + packZ s3)) ≡ 3
pack-value = refl

------------------------------------------------------------------------
-- §7  What is proved, in one place.
--
--   deletion-law      v survives D  ⟺  some Sᵢ avoids D          (all 64 D)
--   S1∖S2 … S3∖S2     {S1,S2,S3} is an antichain, hence = A(v)
--   share-12/13/23    every two supports meet:  ν = 1
--   min-deletion-≥2   killing v costs ≥ 2 rules
--   cut-card/kills    and exactly 2 suffice:    τ = 2
--   cover-*/pack-*    doubled LP certificates of common value 3:  τ* = ν* = 3/2
--
-- Therefore  ν = 1 < 3/2 = ν* = τ* < 2 = τ  on this instance, so the
-- minimal-support clutter of a fact in an AND/OR derivation hypergraph
-- is not ideal, and no max-flow / matroid-intersection formulation
-- computes τ in general.
------------------------------------------------------------------------
