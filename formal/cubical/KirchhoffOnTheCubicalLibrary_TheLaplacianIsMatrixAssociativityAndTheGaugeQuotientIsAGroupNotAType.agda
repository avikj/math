{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- KirchhoffOnTheCubicalLibrary_
--   TheLaplacianIsMatrixAssociativityAndTheGaugeQuotientIsAGroupNotAType
--
-- This file has no  name because its content is not Indian.
-- Its objects are, with text and date:
--
--   * G. Kirchhoff, Ann. Phys. Chem. 64 (1845) 497–514 (the node and loop
--     laws) and 72 (1847) 497–508 (the incidence matrix, the spanning tree,
--     the count |E| − |V| + 1).  `∂`, `d`, `Δ` below are his.
--   * H. Poincaré, "Analysis Situs", J. École Polytech. (2) 1 (1895) 1–121:
--     incidence matrices as boundary operators, ∂∂ = 0.
--   * B. Eckmann, Comment. Math. Helv. 17 (1945) 240–255: Δ = δd + dδ on a
--     finite complex; on a graph the dδ term is empty.
--   * The substrate: the cubical Agda library, v0.5, commit 132a2a3 —
--     `Cubical.Algebra.Matrix`, `Cubical.Algebra.Ring.BigOps`,
--     `Cubical.Algebra.Group.Subgroup`, `Cubical.Algebra.Group.QuotientGroup`.
--
-- WHY THIS FILE EXISTS.  This module takes
-- ONE hand-rolled object in this corpus and redoes it on the library's own
-- structures, in order to measure the difference exactly.
--
-- THE OBJECT.  `KirchhoffIncidence_GraphLaplacianIsDivGradAndSummationBy
-- PartsIsExact.agda` (absent from this repository) and, at the far end,
-- `NaturalMachine/FiniteGraphCohomology.agda`.  Nothing in either is
-- modified, and nothing in either is wrong; what is reported here is what
-- the library already had.
--
--   (1) §1.  Two of the three finite-sum facts that KirchhoffIncidence §0 records as
--       "facts about finite sums that the library does not ship" ARE
--       shipped.  Fubini is `∑Exchange` in `Cubical.Algebra.Matrix`; the
--       empty sum is `∑0r` = `bigOpε` in `Cubical.Algebra.Monoid.BigOp`.
--       Both are proved here BY the library term.  The third, `∑δ`, is
--       genuinely absent and is one `∑Ext` from `∑Mulr1`.
--       `∈Exchange` needs only a `Ring`; the incidence module's `∈Swap` was stated over a
--       `CommRing`.
--
--   (2) §2.  Kirchhoff's incidence matrix is a `FinMatrix`, `grad` and
--       `div` are `mulFinMatrix`, and KirchhoffIncidence's Theorem 2 (summation by parts)
--       and Theorem 3 (Δ = B Bᵀ) are BOTH the single library lemma
--       `mulFinMatrixAssoc`, one line each instead of five.  The
--       commutativity hypothesis disappears: everything in §2 holds over
--       an arbitrary ring.
--
--   (3) §3.  What the library supplies that neither hand-rolled module
--       has at all: `grad` is an `AbGroupHom`, so `ker grad` and `im grad`
--       are SUBGROUPS (`Cubical.Algebra.Group.Subgroup`), the gauge
--       quotient is a GROUP (`Cubical.Algebra.Group.QuotientGroup`) rather
--       than a bare set-quotient type, and exactness at C¹ is a theorem in
--       both directions.  `NaturalMachine/FiniteGraphCohomology.agda` has
--       `H¹ = C¹ / GaugeStep` as a type with no group structure, and no
--       statement that the kernel of the quotient map is the image of δ⁰.
--
--   (4) §4.  The library's Fubini does not need commutativity.  It is
--       proved at `Ring`, and it is instantiated below at a ring that is
--       demonstrably NOT commutative — the 2×2 matrices over ℤ, with the
--       non-commutativity witnessed.
------------------------------------------------------------------------

module KirchhoffOnTheCubicalLibrary_TheLaplacianIsMatrixAssociativityAndTheGaugeQuotientIsAGroupNotAType where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Powerset using (_∈_ ; ∈-isProp ; subst-∈ ; ℙ)

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_ ; _×_)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.FinData using (Fin ; zero ; suc ; FinVec)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)

open import Cubical.HITs.SetQuotients using ([_] ; eq/ ; effective)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Matrix
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.CommRing.Base using (CommRing→Ring)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup

open BinaryRelation

private variable ℓ : Level

------------------------------------------------------------------------
-- 1.  Two of the three "the library does not ship it" lemmas are shipped
--
--   `KirchhoffIncidence_…agda` §0 is headed "Three facts about finite sums
--   that the library does not ship" and proves ∑0, ∑δ, ∑Swap by hand over
--   a CommRing.  Below, the first and third are the library's own terms,
--   over a bare Ring.  The middle one really is absent.
------------------------------------------------------------------------

module SumsAreShipped (R' : Ring ℓ) where
  open RingStr (snd R') public
  open Sum R' public
  open KroneckerDelta R' public
  open RingTheory R' public
  private R = ⟨ R' ⟩

  -- KirchhoffIncidence's ∈0.  Library: Cubical.Algebra.Monoid.BigOp.bigOpε, re-exported
  -- through Cubical.Algebra.Ring.BigOps.Sum as ∑0r.  `replicateFinVec n 0r`
  -- is definitionally `λ _ → 0r`, so no adaptation is needed at all.
  ∑0-is-∑0r : ∀ {n} → ∑ {n} (λ _ → 0r) ≡ 0r
  ∑0-is-∑0r {n} = ∑0r n

  -- KirchhoffIncidence's ∈Swap.  Library: Cubical.Algebra.Matrix.∈Exchange.  Note the
  -- hypothesis: R' is a Ring here, not a CommRing.
  ∑Swap-is-∑Exchange : ∀ {n m} (F : Fin n → Fin m → R)
                     → ∑ (λ i → ∑ (λ j → F i j)) ≡ ∑ (λ j → ∑ (λ i → F i j))
  ∑Swap-is-∑Exchange F = ∑Exchange R' F

  -- KirchhoffIncidence's ∈δ.  This one the library does NOT have; it is one ∈Ext away
  -- from ∈Mulr1, which the library does have.
  ∑δ : ∀ {n} (j : Fin n) → ∑ (λ i → δ i j) ≡ 1r
  ∑δ {n} j = ∑Ext (λ i → sym (·IdL (δ i j))) ∙ ∑Mulr1 n (λ _ → 1r) j

------------------------------------------------------------------------
-- 2.  Kirchhoff's incidence matrix IS a FinMatrix, and two of KirchhoffIncidence's five
--     theorems are one library lemma
--
--   Vertices `Fin n`, edges `Fin m`, each edge with a source and a target.
--   Loops, parallel edges, isolated vertices and disconnection are all
--   allowed.  Coefficients in an arbitrary RING — KirchhoffIncidence needs a
--   CommRing, and §2 shows where that hypothesis was actually being spent.
--
--   Cochains are column matrices `FinMatrix R k 1` rather than `FinVec R k`.
--   That is the price of the library's packaging and it is a real cost: it
--   is one index of noise in every statement.  It is also exactly what buys
--   §3, since `FinVec` carries no group structure and `FinMatrix` does.
------------------------------------------------------------------------

module Graph (R' : Ring ℓ) (n m : ℕ) (src tgt : Fin m → Fin n) where
  open SumsAreShipped R' public
  private R = ⟨ R' ⟩

  C⁰ C¹ : Type ℓ
  C⁰ = FinMatrix R n 1          -- 0-cochains, vertex potentials
  C¹ = FinMatrix R m 1          -- 1-cochains, edge flows

  -- The coboundary matrix, rows indexed by edges: +1 at the head, −1 at
  -- the tail.  Kirchhoff 1847 writes its transpose.
  d : FinMatrix R m n
  d e v = δ (tgt e) v + (- δ (src e) v)

  -- Kirchhoff's incidence matrix itself.
  ∂ : FinMatrix R n m
  ∂ v e = d e v

  grad : C⁰ → C¹
  grad = mulFinMatrix R' d

  div : C¹ → C⁰
  div = mulFinMatrix R' ∂

  Δ : C⁰ → C⁰
  Δ φ = div (grad φ)

  -- The Laplacian AS A MATRIX.  This is already a difference: in the
  -- hand-rolled module `L` is a function `Fin n → Fin n → R` with no
  -- structure on it; here it is an element of the ring `FinMatrixRing R' n`
  -- (Cubical.Algebra.Matrix), so "the Laplacian" is a ring element and
  -- powers, sums and the identity matrix are available without further work.
  L : FinMatrix R n n
  L = mulFinMatrix R' ∂ d

  LaplacianRing : Ring ℓ
  LaplacianRing = FinMatrixRing R' n

  L-lives-in-that-ring : ⟨ LaplacianRing ⟩
  L-lives-in-that-ring = L

  ----------------------------------------------------------------------
  -- THEOREM 1 (KirchhoffIncidence's Theorem 1, restated).  `grad` really is the potential
  -- difference along an edge.  This is the only place in §2 where anything
  -- about `δ` is used, and it uses the library's `∑Mul1r`.
  ----------------------------------------------------------------------

  grad-is-potential-difference :
      (φ : C⁰) (e : Fin m) (k : Fin 1)
    → grad φ e k ≡ φ (tgt e) k + (- φ (src e) k)
  grad-is-potential-difference φ e k =
      ∑Ext (λ v → ·DistL+ (δ (tgt e) v) (- δ (src e) v) (φ v k))
    ∙ ∑Split (λ v → δ (tgt e) v · φ v k) (λ v → (- δ (src e) v) · φ v k)
    ∙ cong₂ _+_
        (∑Mul1r n (λ v → φ v k) (tgt e))
        ( ∑Ext (λ v → -DistL· (δ (src e) v) (φ v k))
        ∙ ∑Dist- (λ v → δ (src e) v · φ v k)
        ∙ cong -_ (∑Mul1r n (λ v → φ v k) (src e)) )

  ----------------------------------------------------------------------
  -- THEOREM 2 (KirchhoffIncidence's Theorem 3).  Δ = B Bᵀ.
  --
  --   The hand-rolled proof is five ∑-steps (∑Ext, ∑Mulrdist, ∑Swap, ∑Ext,
  --   ∑Ext) over a CommRing.  Here it is `mulFinMatrixAssoc`, over a Ring.
  ----------------------------------------------------------------------

  laplacian-is-gram : (φ : C⁰) → Δ φ ≡ mulFinMatrix R' L φ
  laplacian-is-gram φ = mulFinMatrixAssoc R' ∂ d φ

  ----------------------------------------------------------------------
  -- THEOREM 3 (KirchhoffIncidence's Theorem 2).  Summation by parts.
  --
  --   Again `mulFinMatrixAssoc`, and again over a Ring.  Stated for an
  --   arbitrary row covector ψ : FinMatrix R 1 n rather than for ϵ,
  --   which is the honest generalisation: the ONLY thing commutativity
  --   was buying in the hand-rolled proof was the identification of
  --   φᵀ∂ with (dφ)ᵀ, i.e. the step from a covector to a transposed
  --   vector.  Adjointness itself needs no commutativity.
  ----------------------------------------------------------------------

  by-parts : (ψ : FinMatrix R 1 n) (ω : C¹)
           → mulFinMatrix R' ψ (div ω) ≡ mulFinMatrix R' (mulFinMatrix R' ψ ∂) ω
  by-parts ψ ω = mulFinMatrixAssoc R' ψ ∂ ω

  ----------------------------------------------------------------------
  -- THEOREM 4 (KirchhoffIncidence's Theorem 4).  Constants are harmonic.  Not in the
  -- library in any form; kept because §3 needs it to say something about
  -- the kernel.
  ----------------------------------------------------------------------

  constants-harmonic : (c : R) (v : Fin n) (k : Fin 1)
                     → Δ (λ _ _ → c) v k ≡ 0r
  constants-harmonic c v k =
      ∑Ext (λ e → cong (∂ v e ·_)
                    (grad-is-potential-difference (λ _ _ → c) e k ∙ +InvR c))
    ∙ ∑Mulr0 (λ e → ∂ v e)

------------------------------------------------------------------------
-- 3.  What the library has that neither hand-rolled module has:
--     the cochain spaces are GROUPS and the gauge quotient is a GROUP
--
--   `NaturalMachine/FiniteGraphCohomology.agda` defines
--       H¹ = C¹ / GaugeStep
--   as a set quotient — a bare Type₀ — and proves that an additive
--   functional killing coboundaries descends to it.  There is no group
--   structure on H¹, no statement that GaugeStep's classes are the cosets
--   of a subgroup, and no exactness statement.
--
--   The library supplies all three, for any group homomorphism, and they
--   are collected here once, abstractly, then applied to `grad`.
------------------------------------------------------------------------

-- 3.1  Generic: the cokernel of a homomorphism into an abelian group,
--      with exactness at the middle.  Everything here is library machinery
--      (`imSubgroup`, `isNormalIm`, `_/_`, `effective`); what is added is
--      the two exactness implications, which the library does not state.

module Cokernel {G H : Group ℓ} (ϕ : GroupHom G H)
                (comm : (x y : ⟨ H ⟩) → GroupStr._·_ (snd H) x y
                                       ≡ GroupStr._·_ (snd H) y x) where
  open GroupStr (snd H)
  open GroupTheory H

  -- the image is a subgroup, and normal because H is abelian
  ImageSubgroup : NormalSubgroup H
  ImageSubgroup = imSubgroup ϕ , isNormalIm ϕ comm

  -- ... hence the quotient is a GROUP, not a type
  Q : Group ℓ
  Q = H / ImageSubgroup

  -- ... and the class map is a HOMOMORPHISM, not a function
  quot : GroupHom H Q
  quot = [_] , makeIsGroupHom λ _ _ → refl

  private
    ImP : ℙ ⟨ H ⟩
    ImP = fst (imSubgroup ϕ)

    ~prop : isPropValued (_~_ H (fst ImageSubgroup) (snd ImageSubgroup))
    ~prop x y = ∈-isProp ImP (x · inv y)

    ~equiv : isEquivRel (_~_ H (fst ImageSubgroup) (snd ImageSubgroup))
    ~equiv =
      equivRel
        (isRefl~ H (fst ImageSubgroup) (snd ImageSubgroup))
        (λ x y h → subst-∈ ImP
             (invDistr x (inv y) ∙ cong (_· inv x) (invInv y))
             (isSubgroup.inv-closed (snd (imSubgroup ϕ)) h))
        (λ x y z hxy hyz → subst-∈ ImP
             ( sym (·Assoc x (inv y) (y · inv z))
             ∙ cong (x ·_) ( ·Assoc (inv y) y (inv z)
                           ∙ cong (_· inv z) (·InvL y)
                           ∙ ·IdL (inv z)) )
             (isSubgroup.op-closed (snd (imSubgroup ϕ)) hxy hyz))

  -- EXACTNESS AT H, both directions.  This is the statement that the
  -- quotient is exactly the cokernel; the hand-rolled H¹ has neither half.
  im⊂ker : (x : ⟨ H ⟩) → isInIm ϕ x → isInKer quot x
  im⊂ker x hx = eq/ x 1g (subst-∈ ImP (sym (cong (x ·_) inv1g ∙ ·IdR x)) hx)

  ker⊂im : (x : ⟨ H ⟩) → isInKer quot x → isInIm ϕ x
  ker⊂im x p = subst-∈ ImP (cong (x ·_) inv1g ∙ ·IdR x)
                 (effective ~prop ~equiv x 1g p)

-- 3.2  Applied to the graph.

module GraphGroups (R' : Ring ℓ) (n m : ℕ) (src tgt : Fin m → Fin n) where
  open Graph R' n m src tgt public
  private R = ⟨ R' ⟩

  RAb : AbGroup ℓ
  RAb = Ring→AbGroup R'

  open FinMatrixAbGroup RAb using (addFinMatrix ; addFinMatrixComm)

  C⁰Ab C¹Ab : AbGroup ℓ
  C⁰Ab = FinMatrixAbGroup.FinMatrixAbGroup RAb n 1
  C¹Ab = FinMatrixAbGroup.FinMatrixAbGroup RAb m 1

  -- Multiplication by a fixed matrix is additive.  The library proves this
  -- ONLY for square matrices (`mulFinMatrixrDistrAddFinMatrix`, stated at
  -- ∀ {n} (M N K : FinMatrix R n n)), even though the proof never uses
  -- squareness; rectangular is re-proved here in three lines.
  private
    mul-additive : ∀ {p q} (M : FinMatrix R p q) (X Y : FinMatrix R q 1)
                 → mulFinMatrix R' M (addFinMatrix X Y)
                 ≡ addFinMatrix (mulFinMatrix R' M X) (mulFinMatrix R' M Y)
    mul-additive M X Y = funExt λ i → funExt λ k →
        ∑Ext (λ j → ·DistR+ (M i j) (X j k) (Y j k))
      ∙ ∑Split (λ j → M i j · X j k) (λ j → M i j · Y j k)

  -- `grad` and `div` as HOMOMORPHISMS.  Neither hand-rolled module states
  -- this, and without it none of the rest of §3 exists.
  gradHom : AbGroupHom C⁰Ab C¹Ab
  gradHom = grad , makeIsGroupHom (mul-additive d)

  divHom : AbGroupHom C¹Ab C⁰Ab
  divHom = div , makeIsGroupHom (mul-additive ∂)

  ΔHom : AbGroupHom C⁰Ab C⁰Ab
  ΔHom = compGroupHom gradHom divHom

  -- H⁰ as a GROUP: the harmonic 0-cochains in the strong sense — the kernel
  -- of `grad`, i.e. the locally constant potentials.
  H⁰ : Group ℓ
  H⁰ = Subgroup→Group _ (kerSubgroup gradHom)

  -- The coboundaries B¹ = im(grad) as a SUBGROUP of C¹, and H¹ = C¹/B¹ as
  -- a GROUP.  `FiniteGraphCohomology.H¹` is the same set, as a bare type.
  module Coker = Cokernel gradHom (addFinMatrixComm {m} {1})

  B¹ : Group ℓ
  B¹ = imGroup gradHom

  H¹ : Group ℓ
  H¹ = Coker.Q

  classOf : GroupHom (AbGroup→Group C¹Ab) H¹
  classOf = Coker.quot

  -- exactness at C¹, both directions
  coboundaries-are-trivial-in-H¹ :
    (ω : ⟨ C¹Ab ⟩) → isInIm gradHom ω → isInKer classOf ω
  coboundaries-are-trivial-in-H¹ = Coker.im⊂ker

  trivial-in-H¹-means-coboundary :
    (ω : ⟨ C¹Ab ⟩) → isInKer classOf ω → isInIm gradHom ω
  trivial-in-H¹-means-coboundary = Coker.ker⊂im

  -- the gauge move of FiniteGraphCohomology, now as an equation in a group
  gauge-invariance : (ω : ⟨ C¹Ab ⟩) (φ : C⁰)
                   → classOf .fst (addFinMatrix ω (grad φ))
                   ≡ classOf .fst ω
  gauge-invariance ω φ =
      classOf .snd .IsGroupHom.pres· ω (grad φ)
    ∙ cong (GroupStr._·_ (snd H¹) (classOf .fst ω))
           (coboundaries-are-trivial-in-H¹ (grad φ) ∣ φ , refl ∣₁)
    ∙ GroupStr.·IdR (snd H¹) (classOf .fst ω)

------------------------------------------------------------------------
-- 4.  THE REFUTATION.
--
--   The claim: "one had to hand-roll ∈Swap because
--   the library's Fubini, if it exists at all, is stated for commutative
--   rings — the ∑ machinery lives under CommRing in this corpus, so the
--   library's version would not have applied."
--
--   Both halves are false.  `∑Exchange` is proved in
--   `Cubical.Algebra.Matrix` inside `module _ (R' : Ring ℓ)`, and it is
--   used there to prove associativity of matrix multiplication — which is
--   precisely the case where the ring cannot be assumed commutative,
--   because the matrix ring it constructs is not.
--
--   The check that kills the claim: instantiate `∑Exchange` at the ring of
--   2×2 matrices over ℤ, and then exhibit two elements of that ring that
--   do not commute.  If the claim were true the first line would not
--   typecheck; the second line shows the instance is not vacuous.
--
--   (Guarding the negative: this is a witnessed non-identity, not an
--   exhaustion over a domain that might be empty.  `E01` and `E10` are
--   explicit elements and the two products are compared at an explicit
--   index, so there is no empty-enumeration escape.)
------------------------------------------------------------------------

module Refutation where
  ℤRing : Ring ℓ-zero
  ℤRing = CommRing→Ring ℤCommRing

  -- the ring the claim said could not occur
  M2ℤ : Ring ℓ-zero
  M2ℤ = FinMatrixRing ℤRing 2

  open Sum M2ℤ using () renaming (∑ to ∑M)

  -- FUBINI OVER A NON-COMMUTATIVE RING.  This is `∑Exchange` and nothing
  -- else; if Fubini needed commutativity, this would not typecheck.
  fubini-over-M2ℤ :
      ∀ {p q} (F : Fin p → Fin q → ⟨ M2ℤ ⟩)
    → ∑M (λ i → ∑M (λ j → F i j)) ≡ ∑M (λ j → ∑M (λ i → F i j))
  fubini-over-M2ℤ F = ∑Exchange M2ℤ F

  -- and M2ℤ really is not commutative
  open KroneckerDelta ℤRing using (δ)

  one : Fin 2
  one = suc zero

  E01 E10 : FinMatrix ℤ 2 2
  E01 i j = RingStr._·_ (snd ℤRing) (δ i zero) (δ j one)
  E10 i j = RingStr._·_ (snd ℤRing) (δ i one)  (δ j zero)

  private
    isZero : ℤ → Bool
    isZero (pos ℕ.zero)    = true
    isZero (pos (ℕ.suc _)) = false
    isZero (negsuc _)      = false

  E01E10 : mulFinMatrix ℤRing E01 E10 zero zero ≡ pos 1
  E01E10 = refl

  E10E01 : mulFinMatrix ℤRing E10 E01 zero zero ≡ pos 0
  E10E01 = refl

  M2ℤ-is-not-commutative :
    ¬ ((X Y : FinMatrix ℤ 2 2) → mulFinMatrix ℤRing X Y ≡ mulFinMatrix ℤRing Y X)
  M2ℤ-is-not-commutative h =
    true≢false (cong isZero (sym E10E01
                            ∙ cong (λ Z → Z zero zero) (sym (h E01 E10))
                            ∙ E01E10))

------------------------------------------------------------------------
-- Summary.
--
-- PROVED HERE.  Over an arbitrary ring and an arbitrary finite directed
-- multigraph: grad is the potential difference; Δ = ∂d as matrices, by
-- `mulFinMatrixAssoc`; summation by parts, by the same lemma; constants
-- are harmonic.  Over an arbitrary ring: grad and div are AbGroupHoms,
-- ker grad and im grad are subgroups, H¹ = C¹/im(grad) is a group, the
-- class map is a homomorphism, and the sequence is exact at C¹ in both
-- directions.  Over ℤ: the 2×2 matrix ring is not commutative, and
-- `∑Exchange` applies to it.
--
-- REFUTED.  That the library's Fubini would need a commutative ring.
--
-- WHAT THE LIBRARY DOES NOT SHIP, precisely, in cubical v0.5 (commit 132a2a3):
--
--   1. There is NO `Cubical.Algebra.ChainComplex`, and no chain- or
--      cochain-complex development anywhere in the library.
--      So the long exact sequence, the snake
--      lemma, and Hⁿ of a complex are unavailable; the exactness in §3 had
--      to be proved by hand from `effective`.
--
--   2. `Cubical.Cohomology` in v0.5 is Eilenberg–MacLane cohomology OF A
--      TYPE: `coHom n G A = ∥ (A → EM G n) ∥₂`
--      (Cubical/Cohomology/EilenbergMacLane/Base.agda).  It takes a space
--      and an abelian group, not a cochain complex.  A finite graph's
--      combinatorial H¹ is therefore NOT an instance of it without first
--      building the graph's geometric realisation as a type and proving a
--      comparison theorem.  This is the sharpest single answer to "why
--      does a corpus full of cocycles import zero cohomology": the
--      library's cohomology is about spaces, and this corpus's cocycles
--      are about matrices.
--
--   3. `Cubical.Categories.Abelian.Base` DOES define `IsKernel`,
--      `IsCokernel` with their universal properties, and `PreAbCategory`.
--      But `Cubical/Categories/Abelian/Instances/` contains exactly one
--      file, `Terminal.agda` (absent from this repository), and `Cubical/Categories/Additive/Instances/`
--      likewise.  `Cubical.Categories.Instances.AbGroups` builds the
--      category of abelian groups but does NOT show it preadditive.  So
--      the universal property of the cokernel is definable and has no
--      instance to apply it to; getting it for H¹ means proving AbGroup is
--      a preadditive category first.
--
--   4. `mulFinMatrixrDistrAddFinMatrix` and its left twin are stated only
--      for square matrices (`∀ {n} (M N K : FinMatrix R n n)`) although
--      their proofs are dimension-generic; `mul-additive` above re-proves
--      the rectangular case in three lines.
--
--   5. `Cubical.Algebra.Ring.BigOps` does not re-export `∑Exchange`; it
--      sits in `Cubical.Algebra.Matrix`.
------------------------------------------------------------------------
