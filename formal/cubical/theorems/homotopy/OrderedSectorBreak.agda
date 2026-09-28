{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- OrderedSectorBreak
--
-- DELTA 14, PROGRAM 14.72: the positive-cone subtype, and the exact
-- nonrestriction statement, as an inhabitant of
-- `PerspectiveCore.SectorBreak`.
--
-- Delta 14 C14.7 is the target sentence:
--
--   "Ambient equivalence can fail after sector selection precisely
--    because the sector predicate is not invariant."
--
-- `CenterRelative` supplies the ambient equivalence
-- Φ : Pair ≃ Centre over any CommRing in which 2 is invertible, and says
-- in its own "SYĀT — THE CLAIM, EXACTLY" that the positive cone cannot even be
-- posed there because `R` carries no order.  This file poses it.  Neither
-- `CenterRelative.agda` nor `PerspectiveCore.agda` is edited; both are
-- imported.
--
--
-- THE ORDER: A PARAMETER, NOT AN INSTANCE.  WHY.
--
-- The brief allowed either adding an order as a further parameter or
-- instantiating at a concrete ordered ring.  **Parameter**, for a reason
-- that is a fact about the pinned toolchain and not a preference:
--
--   cubical v0.5 contains no ordered commutative ring in which 2 is
--   invertible.  `Cubical.Data.Int` has no order module; `Cubical.HITs.
--   Rationals.QuoQ` builds ℚ as a set quotient but gives it **no
--   `CommRing` instance and no order**; `Cubical.Algebra` has
--   `OrderedCommMonoid` and nothing ordered above it.  Instantiating
--   would therefore mean first constructing ℤ[1/2] or ℚ as a `CommRing`
--   **and** its order — a module's worth of work orthogonal to C14.7,
--   which is a statement about a *predicate*, not about any particular
--   ring.
--
-- Two consequences are taken seriously rather than hidden.
--
--  (1) The hypotheses are kept as small as the theorem needs, so that a
--      reader can check satisfiability by inspection instead of trusting
--      a bundle.  §2's break needs **exactly two**: a positivity
--      predicate `P` with `P 1r` inhabited and `P 0r` uninhabited.  Any
--      ordered field supplies them.  §4's break needs four more, and they
--      are the axioms of a strictly ordered abelian group with `0 < 1`
--      — no multiplicative compatibility, no trichotomy, no decidability.
--      In particular **`0 < half` is never assumed**, which is why the
--      witnesses below are chosen as they are.
--
-- (2) That ℚ with its usual order inhabits it is standard and is CITED, not
-- formalized. What *is* checked is that the bundle has bite:
-- `StrictOrder.nontrivial` derives `¬ (1r ≡ 0r)` from it, so it is not
-- satisfied by the trivial ring and is not vacuous dressing on the break.
--
--
-- WHAT IS CHECKED, BY DELTA-14 NUMBER
--
--   §1  `PairCone`           the positive-cone subtype `p > 0 ∧ q > 0`,
--       `PositiveCone`       and its total space, on the Pair side.
--       `CentreCone`         the SAME predicate named in the Centre
--                            chart, `w > 0 ∧ r > 0`.
--       `Sector`             the natural Centre sector `w > 0`.
--       `Transported`        the sector the cone actually becomes,
--                            `w − r > 0 ∧ w + r > 0`, i.e. `|r| < w`.
--
--   §2  `break-diagonal`     C14.7: an inhabitant of `SectorBreak` for
--                            (Φ, PairCone, CentreCone).  Witness: the
--                            DIAGONAL pair `(1,1)`, strictly inside the
--                            positive cone, whose centre image sits on
--                            the wall `r = 0`.
--       `no-fibrewise-…`     hence, by `sector-not-inv`, no fibrewise
--                            correspondence of the two predicates exists.
--
--   §3  `cone-restricts`     T14.6 sufficient direction, POSITIVELY: Φ
--                            *does* restrict, to `Transported`.  This is
--                            the Feynman half — the transported sector is
--                            derived (it is `PairCone ∘ Ψ`, on the nose),
--                            not guessed, and it is `|r| < w`.
--
--   §4  `sector-break`       C14.7 again, in the direction that matters
--                            for the "natural" sector: `w > 0` does NOT
--                            restrict to the positive cone along Ψ.
--                            Witness `(w,r) = (1,2)`: centre positive,
--                            pair `(−1,3)` not.
--
--   §5  `ambient`            the ambient equivalence, unrestricted, still
--                            there — so the failure is produced by sector
--                            selection and by nothing else.  That
--                            juxtaposition IS C14.7.
--
--
--  * **No converse.**  `SectorBreak` refutes fibrewise correspondence
--    (that is `sector-not-inv`).  It does not refute the existence of
--    SOME equivalence `Σ Pair PairCone ≃ Σ Centre Sector` — such a thing
--    may exist and permute the base.  `PerspectiveCore` says exactly this
--    about T14.6's "iff", and nothing here strengthens it.
--
--  * **No archimedean or completeness content.**  `<-+ˡ` is translation
--    invariance only.  The order is not assumed total, decidable, or
--    compatible with multiplication.
------------------------------------------------------------------------

module OrderedSectorBreak where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection using (solve!)

open import CenterRelativeExecutable
  using (Pair ; Centre ; Φ ; Ψ ; ΦEquiv ; ΨΦ)
open import PerspectiveCore
  using (SectorBreak ; sector-not-inv ; restricts-suff)

private
  variable
    ℓ ℓ' : Level

module _ (R : CommRing ℓ) where
 open CommRingStr (snd R)

 private
   -- The three ring identities the file uses.  Each is discharged by the
   -- solver on the quantified goal, per BUILD.md (absent from this repository)'s convention.
   diag0 : (h x : ⟨ R ⟩) → h · (x - x) ≡ 0r
   diag0 _ _ = solve! R

   sub2 : (x : ⟨ R ⟩) → x - (x + x) ≡ - x
   sub2 _ = solve! R

   negIdR : (x : ⟨ R ⟩) → (- x) + 0r ≡ - x
   negIdR _ = solve! R

   negInvR : (x : ⟨ R ⟩) → (- x) + x ≡ 0r
   negInvR _ = solve! R

 ----------------------------------------------------------------------
 -- 0.  The order, as a parameter.
 --
 -- Exactly the axioms used: a strict order that is irreflexive,
 -- transitive, translation invariant, and has `0 < 1`.  Nothing about
 -- multiplication, nothing about trichotomy, nothing about `half`.
 ----------------------------------------------------------------------

 record StrictOrder (ℓ' : Level) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
   field
     _<_      : ⟨ R ⟩ → ⟨ R ⟩ → Type ℓ'
     <-irrefl : (x : ⟨ R ⟩) → x < x → ⊥
     <-trans  : {x y z : ⟨ R ⟩} → x < y → y < z → x < z
     <-+ˡ     : {x y : ⟨ R ⟩} (z : ⟨ R ⟩) → x < y → (z + x) < (z + y)
     0<1      : 0r < 1r

   -- positivity, the predicate the cone is built from
   Pos : ⟨ R ⟩ → Type ℓ'
   Pos x = 0r < x

   pos1 : Pos 1r
   pos1 = 0<1

   -- the wall `r = 0` is outside the open cone
   ¬pos0 : Pos 0r → ⊥
   ¬pos0 = <-irrefl 0r

   -- THE BUNDLE HAS BITE: it excludes the trivial ring.  Without this
   -- line a reader is entitled to suspect the break of being vacuous.
   nontrivial : 1r ≡ 0r → ⊥
   nontrivial p = <-irrefl 0r (subst (0r <_) p 0<1)

   -- `−1 < 0`, from translation invariance alone
   neg1<0 : (- 1r) < 0r
   neg1<0 = subst2 _<_ (negIdR 1r) (negInvR 1r) (<-+ˡ (- 1r) 0<1)

   ¬pos-neg1 : Pos (- 1r) → ⊥
   ¬pos-neg1 h = <-irrefl 0r (<-trans h neg1<0)

 module _ (half : ⟨ R ⟩) (half+half : half + half ≡ 1r) where

  ---------------------------------------------------------------------
  -- Local names for `CenterRelative`'s objects at these parameters.
  ---------------------------------------------------------------------

  Prs Ctr : Type ℓ
  Prs = Pair   R half half+half
  Ctr = Centre R half half+half

  φ : Prs → Ctr
  φ = Φ R half half+half

  ψ : Ctr → Prs
  ψ = Ψ R half half+half

  -- the AMBIENT equivalence, before any sector is selected
  ambient : Prs ≃ Ctr
  ambient = ΦEquiv R half half+half

  ambient⁻ : Ctr ≃ Prs
  ambient⁻ = invEquiv ambient

  -- both `equivFun`s reduce to the named maps; recorded so that the
  -- SectorBreak witnesses below are visibly about Φ and Ψ
  ambient-is-Φ : (x : Prs) → equivFun ambient x ≡ φ x
  ambient-is-Φ x = refl

  ambient⁻-is-Ψ : (y : Ctr) → equivFun ambient⁻ y ≡ ψ y
  ambient⁻-is-Ψ y = refl

  -------------------------------------------------------------------
  -- 1.  THE POSITIVE-CONE SUBTYPE, and the three Centre-side sectors.
  -------------------------------------------------------------------

  module Cone (P : ⟨ R ⟩ → Type ℓ') where

    -- the positive cone as a predicate on pairs: `p > 0 ∧ q > 0`
    PairCone : Prs → Type ℓ'
    PairCone (p , q) = P p × P q

    -- … and as a subtype (Program 14.72's first ask, literally)
    PositiveCone : Type (ℓ-max ℓ ℓ')
    PositiveCone = Σ Prs PairCone

    -- the SAME predicate, named in the other chart: `w > 0 ∧ r > 0`.
    -- This is the naive transfer, and §2 is the proof that "the same
    -- words in the other chart" is not a transport.
    CentreCone : Ctr → Type ℓ'
    CentreCone (w , r) = P w × P r

    -- the natural Centre sector: `w > 0`
    Sector : Ctr → Type ℓ'
    Sector (w , r) = P w

    -- THE SECTOR THE CONE ACTUALLY BECOMES.  Definitionally `PairCone ∘ ψ`;
    -- the explicit reading below is `refl`, and is `|r| < w`.
    Transported : Ctr → Type ℓ'
    Transported y = PairCone (ψ y)

    Transported-explicit :
      (w r : ⟨ R ⟩) → Transported (w , r) ≡ (P (w - r) × P (w + r))
    Transported-explicit w r = refl

    -----------------------------------------------------------------
    -- 2.  C14.7, FIRST BREAK: the cone does not restrict to the
    --     same-named Centre predicate.
    --
    -- Witness: the DIAGONAL pair `(1,1)`.  It is strictly inside the
    -- positive cone, and its centre image is `(half·2 , half·(1−1))`,
    -- whose relative coordinate is `0` — on the wall, not in the open
    -- sector.  Only `P 1r` and `¬ P 0r` are used; in particular the
    -- sign of `half` is never needed, which is what makes this break
    -- available over ANY ring with 2 invertible.
    -----------------------------------------------------------------

    break-diagonal :
      P 1r → (P 0r → ⊥) → SectorBreak ambient PairCone CentreCone
    break-diagonal p1 p0 =
      (1r , 1r) , ((p1 , p1) , λ z → p0 (subst P (diag0 half 1r) (z .snd)))

    -- … and therefore no fibrewise correspondence of the two predicates
    -- exists.  This is `sector-not-inv`, i.e. C14.7's "precisely
    -- because the sector predicate is not invariant".
    no-fibrewise-diagonal :
      P 1r → (P 0r → ⊥)
      → ((a : Prs) → PairCone a ≃ CentreCone (equivFun ambient a)) → ⊥
    no-fibrewise-diagonal p1 p0 =
      sector-not-inv ambient PairCone CentreCone (break-diagonal p1 p0)

    -----------------------------------------------------------------
    -- 3.  T14.6, SUFFICIENT DIRECTION, POSITIVELY.
    --
    -- The ambient equivalence DOES restrict — to `Transported`.  No
    -- order axiom is used: the fibrewise correspondence is the
    -- transport of `PairCone` along `ΨΦ`, so it holds for an arbitrary
    -- predicate `P`.  The content is that `Transported` is forced: it
    -- is `PairCone ∘ ψ`, which unfolds to `w − r > 0 ∧ w + r > 0`.
    -----------------------------------------------------------------

    cone-fibrewise : (a : Prs) → PairCone a ≃ Transported (equivFun ambient a)
    cone-fibrewise a =
      pathToEquiv (cong PairCone (sym (ΨΦ R half half+half a)))

    cone-restricts : PositiveCone ≃ (Σ Ctr Transported)
    cone-restricts = restricts-suff ambient PairCone Transported cone-fibrewise

  -------------------------------------------------------------------
  -- 4.  THE ORDERED INSTANCE, and the second break.
  -------------------------------------------------------------------

  module Ordered (O : StrictOrder ℓ') where
    open StrictOrder O
    open Cone Pos public

    -- §2 at `P = (0 <_)`: the positive cone breaks against the
    -- same-named Centre predicate.
    cone-break : SectorBreak ambient PairCone CentreCone
    cone-break = break-diagonal pos1 ¬pos0

    cone-not-invariant :
      ((a : Prs) → PairCone a ≃ CentreCone (equivFun ambient a)) → ⊥
    cone-not-invariant = no-fibrewise-diagonal pos1 ¬pos0

    -----------------------------------------------------------------
    -- C14.7, SECOND BREAK — the one against the *natural* sector.
    --
    -- Along Ψ, the sector `w > 0` does not land in the positive cone.
    -- Witness `(w , r) = (1 , 1+1)`: `w > 0` holds, and
    -- `Ψ(1,2) = (1 − 2 , 1 + 2)`, whose first coordinate is `−1 < 0`.
    -- Uses `0 < 1`, translation invariance, transitivity,
    -- irreflexivity.  It does NOT use `0 < half`.
    -----------------------------------------------------------------

    sector-break : SectorBreak ambient⁻ Sector PairCone
    sector-break =
      (1r , (1r + 1r))
        , (0<1 , λ z → ¬pos-neg1 (subst Pos (sub2 1r) (z .fst)))

    sector-not-invariant :
      ((y : Ctr) → Sector y ≃ PairCone (equivFun ambient⁻ y)) → ⊥
    sector-not-invariant =
      sector-not-inv ambient⁻ Sector PairCone sector-break

  -------------------------------------------------------------------
  -- 5.  C14.7 AS A SENTENCE.
  --
  -- The ambient equivalence is `ambient`, and it is an equivalence
  -- unconditionally.  After sector selection the correspondence dies,
  -- and `sector-not-inv` says the death is *exactly* non-invariance of
  -- the predicate: a break is a point of the sector whose image leaves
  -- it, and that datum alone refutes every fibrewise correspondence.
  --
  -- The two halves side by side, at one order, so a reader sees the
  -- juxtaposition rather than reconstructing it:
  -------------------------------------------------------------------

  module C14-7 (O : StrictOrder ℓ') where
    open Ordered O

    -- before selection: an equivalence
    before : Prs ≃ Ctr
    before = ambient

    -- after selection with the same-named predicate: no fibrewise
    -- correspondence, and the reason is an exhibited non-invariant point
    after : ((a : Prs) → PairCone a ≃ CentreCone (equivFun ambient a)) → ⊥
    after = cone-not-invariant

    -- and the repair: the predicate that IS invariant, with the
    -- restricted equivalence it supports
    repaired : PositiveCone ≃ (Σ Ctr Transported)
    repaired = cone-restricts
