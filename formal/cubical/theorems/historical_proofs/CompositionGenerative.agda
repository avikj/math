{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- BhavanaGenerative — bhāvanā as an OPERATION, not an identity.
--
-- BRAHMAGUPTA, Brhmasphuasiddhnta, 628 CE, chapter 18.  The rule is
-- called *bhvan*: "production", "bringing into being".  The name is the
-- claim.  It is not called "the multiplicativity of the norm form"; it is
-- called production, because what Brahmagupta states is that from two
-- solutions you MAKE a third.
--
-- WHAT WAS HERE BEFORE AND WHY IT WAS HALF THE RULE.  `Bhavana.agda` (absent from this repository) proves
--
--     N D a₁ b₁ · N D a₂ b₂ ≡ N D (bhA …) (bhB …)
--
-- over an arbitrary commutative ring, and `BhavanaSemiring.agda` (absent from this repository) proves the
-- subtraction-free form over ℕ.  Both are true and neither produces
-- anything.  They are equations between coordinates.  A reader holding two
-- solutions of x² − D y² = k must still assemble the third by hand and
-- discharge its norm obligation by hand, and nothing in the development
-- stops them assembling it wrongly.  Six centuries of cakravla stand on
-- bhvan being a MOVE.
--
-- WHAT THIS FILE ADDS.  The move, typed:
--
--     _⊛_ : Sol D k₁ → Sol D k₂ → Sol D (k₁ · k₂)
--
-- Read the type as the theorem.  It says composition of solutions exists and
-- that the norm multiplies, and it says so in the only place that cannot rot:
-- the obligation travels WITH the pair, so a composite that does not satisfy
-- its equation is not expressible.  The identity in `Bhavana.agda` (absent from this repository) is what
-- pays for the type; having been paid, the caller turns a handle.
--
-- The unit-norm solutions are then closed under the operation, and iterating
-- from a single seed gives an ℕ-indexed family — which is the generativity
-- the 628 rule is named for and which no file here had.
--
------------------------------------------------------------------------

module CompositionGenerative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSetΣ ; isOfHLevelRetract)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Group.Base using (Group ; makeGroup)
open import Cubical.Algebra.AbGroup.Base using (AbGroup ; makeAbGroup)
open import Cubical.Algebra.Ring.Properties using (module RingTheory)
open import Cubical.Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int using (negsuc)

open import Composition using (module Form)

private
  variable
    ℓ : Level

module Generative (CR : CommRing ℓ) where

  open CommRingStr (snd CR)
  open RingTheory (CommRing→Ring CR)
  open Form CR

  ----------------------------------------------------------------------
  -- 1.  A solution carries its own equation
  --
  -- `Sol D k` is a pair (a, b) TOGETHER WITH the proof that its norm is k.
  -- This is the same discipline `Anekanta.agda` states for verdicts —
  -- नकारः खण्डनं ददाति, स्वीकारः साक्षिणम्, nowhere a bare label — applied to
  -- solutions: there is no way to hold a solution without holding why it is
  -- one, so `_⊛_` cannot be handed a pair that does not satisfy the form, and
  -- cannot hand back one either.
  ----------------------------------------------------------------------

  record Sol (D k : R) : Type ℓ where
    constructor mkSol
    field
      coefA coefB : R
      hasNorm : N D coefA coefB ≡ k

  open Sol public

  ----------------------------------------------------------------------
  -- 2.  समासभावना — composition by addition.  THE OPERATION.
  --
  -- Brahmagupta's own coordinates, `bhA` and `bhB`, unchanged from
  -- `Bhavana.agda` (absent from this repository).  What is new is that the result is a `Sol`, so the norm
  -- obligation is discharged once here rather than at every use.
  ----------------------------------------------------------------------

  _⊛_ : {D k₁ k₂ : R} → Sol D k₁ → Sol D k₂ → Sol D (k₁ · k₂)
  _⊛_ {D} {k₁} {k₂} s t =
    mkSol (bhA D (coefA s) (coefB s) (coefA t) (coefB t))
          (bhB D (coefA s) (coefB s) (coefA t) (coefB t))
          ( sym (bhavana D (coefA s) (coefB s) (coefA t) (coefB t))
          ∙ cong₂ _·_ (hasNorm s) (hasNorm t) )

  ----------------------------------------------------------------------
  -- 3.  अन्तरभावना — composition by difference.  Brahmagupta gives both,
  -- and the second is what the cakravla uses to walk a chain DOWNWARD;
  -- omitting it would leave the rule with one direction, which is the same
  -- defect this file is repairing one level up.
  ----------------------------------------------------------------------

  _⊝_ : {D k₁ k₂ : R} → Sol D k₁ → Sol D k₂ → Sol D (k₁ · k₂)
  _⊝_ {D} {k₁} {k₂} s t =
    mkSol (coefA s · coefA t - D · (coefB s · coefB t))
          (coefA t · coefB s - coefA s · coefB t)
          ( sym (bhavanaMinus D (coefA s) (coefB s) (coefA t) (coefB t))
          ∙ cong₂ _·_ (hasNorm s) (hasNorm t) )

  ----------------------------------------------------------------------
  -- 4.  तुल्यभावना — composition of a solution with ITSELF.
  --
  -- Brahmagupta names this case separately, and it is the one the chain is
  -- built from: it is the only composition available when you hold exactly
  -- one solution, which is the situation the cakravla starts in.
  ----------------------------------------------------------------------

  tulya : {D k : R} → Sol D k → Sol D (k · k)
  tulya s = s ⊛ s

  ----------------------------------------------------------------------
  -- 5.  The trivial solution (1, 0), and composition of unit-norm solutions.
  ----------------------------------------------------------------------

  unit : (D : R) → Sol D 1r
  unit D = mkSol 1r 0r norm1
    where
    norm1 : N D 1r 0r ≡ 1r
    norm1 = cong₂ _-_ (·IdR 1r)
                      (cong (λ w → D · w) (0RightAnnihilates 0r)
                        ∙ 0RightAnnihilates D)
          ∙ cong (λ w → 1r + w) 0Selfinverse
          ∙ +IdR 1r

  -- Composition of two unit-norm solutions, retyped along 1r · 1r ≡ 1r.
  -- The `subst` is bookkeeping, not content: `_⊛_` already produced a
  -- solution of norm 1r · 1r, and `·IdR` says that is 1r.
  _∙₁_ : {D : R} → Sol D 1r → Sol D 1r → Sol D 1r
  _∙₁_ {D} s t = subst (Sol D) (·IdR 1r) (s ⊛ t)

  ----------------------------------------------------------------------
  -- 5b.  THE INVERSE, AT THE LEVEL OF COORDINATES.
  --
  -- The norm-1 solutions are a group (section 7); the coordinate equations below are its inverse
  -- law's content.
  --
  -- What they say is worth having on its own.  `normNegB` (in `Bhavana`) says
  -- the form is even in b: N D a (−b) ≡ N D a b.  So negating b sends a
  -- solution to a solution of the same norm, and composing the two returns the
  -- unit's coordinates:
  --
  --     (a, b) ⊛ (a, −b) = (a² − D b², −ab + ab) = (1, 0)   at norm 1
  --
  -- which is antara-bhvan read as inversion, and it is why the cakravla may
  -- walk a chain in either direction.
  ----------------------------------------------------------------------

  inv : {D : R} → Sol D 1r → Sol D 1r
  inv {D} s = mkSol (coefA s) (- coefB s)
                    (normNegB D (coefA s) (coefB s) ∙ hasNorm s)

  invCoefA : {D : R} (s : Sol D 1r) → coefA (s ⊛ inv s) ≡ 1r
  invCoefA {D} s =
      cong (λ w → coefA s · coefA s + D · w) (-DistR· (coefB s) (coefB s))
    ∙ cong (λ w → coefA s · coefA s + w) (-DistR· D (coefB s · coefB s))
    ∙ hasNorm s

  invCoefB : {D : R} (s : Sol D 1r) → coefB (s ⊛ inv s) ≡ 0r
  invCoefB s =
      cong (λ w → w + coefA s · coefB s) (-DistR· (coefA s) (coefB s))
    ∙ +InvL (coefA s · coefB s)

  ----------------------------------------------------------------------
  -- 6.  GENERATIVITY.  One seed, an ℕ-indexed family.
  --
  -- This is what "production" names and what the corpus did not have.  The
  -- earlier files could tell you that a composite satisfies the form; they
  -- could not hand you the n-th member of a chain.
  ----------------------------------------------------------------------

  chain : {D : R} → Sol D 1r → ℕ → Sol D 1r
  chain {D} s zero    = unit D
  chain {D} s (suc n) = s ∙₁ chain s n

  -- The seed is the first member, definitionally up to the unit law, and the
  -- family satisfies the recurrence that generates it.  Both are `refl`; they
  -- are stated so that a later edit to `chain` that broke either would fail
  -- to check rather than silently change what the family means.
  chainZero : {D : R} (s : Sol D 1r) → chain s zero ≡ unit D
  chainZero s = refl

  chainStep : {D : R} (s : Sol D 1r) (n : ℕ)
            → chain s (suc n) ≡ s ∙₁ chain s n
  chainStep s n = refl

  ----------------------------------------------------------------------
  -- 7.  The composition is commutative and associative, with unit: a monoid,
  -- as paths between `Sol` values.
  -- ASSOCIATIVITY OF `_⊛_` at the coordinate level is proved (
  -- ⊛AssocA/⊛AssocB below, from bhA-assoc/bhB-assoc in Bhavana.Form — abstract
  -- R, solver-free).  Together with commutativity (⊛CommA/⊛CommB) and the unit
  -- laws (⊛UnitA/⊛UnitB), ALL THREE monoid axioms hold at the level of the
  -- two coordinates.  And the Sol-LEVEL associativity is assembled
  -- (⊛Assoc below): a PathP between the two `Sol` records over the norm index
  -- `·Assoc k₁ k₂ k₃`, built from the two coordinate paths and a `hasNorm`
  -- PathP that isProp→PathP fills because R is a set (being a CommRing).  So
  -- `_⊛_` is associative as an operation on solutions, not merely on their
  -- coordinates.  And
  -- the Sol-level UNIT paths are assembled (IdR/IdL, over `·IdR`/·
  -- `·IdL`), so EVERY monoid axiom holds as a path between `Sol` values: the
  -- solutions of a fixed norm form a monoid, and the graded family multiplies
  -- its norm indices.
  ----------------------------------------------------------------------

  ⊛CommA : {D k₁ k₂ : R} (s : Sol D k₁) (t : Sol D k₂)
         → coefA (s ⊛ t) ≡ coefA (t ⊛ s)
  ⊛CommA {D} s t =
    cong₂ _+_ (·Comm (coefA s) (coefA t))
              (cong (λ w → D · w) (·Comm (coefB s) (coefB t)))

  ⊛CommB : {D k₁ k₂ : R} (s : Sol D k₁) (t : Sol D k₂)
         → coefB (s ⊛ t) ≡ coefB (t ⊛ s)
  ⊛CommB s t = +Comm (coefA s · coefB t) (coefA t · coefB s)

  -- The unit laws at the coordinate level: (1r, 0r) is a two-sided identity.
  -- `s ⊛ unit D` and `unit D ⊛ s` restore each coordinate, from bhA/bhB's
  -- identity lemmas.  coefA (unit D) = 1r and coefB (unit D) = 0r hold by
  -- definition, so these reduce directly to bhA-idR / bhB-idR / bhA-idL /
  -- bhB-idL applied at the coordinates of `s`.
  ⊛UnitA-R : {D k : R} (s : Sol D k) → coefA (s ⊛ unit D) ≡ coefA s
  ⊛UnitA-R {D} s = bhA-idR D (coefA s) (coefB s)

  ⊛UnitB-R : {D k : R} (s : Sol D k) → coefB (s ⊛ unit D) ≡ coefB s
  ⊛UnitB-R {D} s = bhB-idR D (coefA s) (coefB s)

  ⊛UnitA-L : {D k : R} (s : Sol D k) → coefA (unit D ⊛ s) ≡ coefA s
  ⊛UnitA-L {D} s = bhA-idL D (coefA s) (coefB s)

  ⊛UnitB-L : {D k : R} (s : Sol D k) → coefB (unit D ⊛ s) ≡ coefB s
  ⊛UnitB-L {D} s = bhB-idL D (coefA s) (coefB s)

  -- Associativity of the two coordinates, straight from bhA-assoc/bhB-assoc.
  -- coefA ((s ⊛ t) ⊛ u) and coefA (s ⊛ (t ⊛ u)) reduce definitionally to the
  -- two nested bhA/bhB terms that bhA-assoc equates; likewise for coefB.
  ⊛AssocA : {D k₁ k₂ k₃ : R} (s : Sol D k₁) (t : Sol D k₂) (u : Sol D k₃)
          → coefA ((s ⊛ t) ⊛ u) ≡ coefA (s ⊛ (t ⊛ u))
  ⊛AssocA {D} s t u =
    bhA-assoc D (coefA s) (coefB s) (coefA t) (coefB t) (coefA u) (coefB u)

  ⊛AssocB : {D k₁ k₂ k₃ : R} (s : Sol D k₁) (t : Sol D k₂) (u : Sol D k₃)
          → coefB ((s ⊛ t) ⊛ u) ≡ coefB (s ⊛ (t ⊛ u))
  ⊛AssocB {D} s t u =
    bhB-assoc D (coefA s) (coefB s) (coefA t) (coefB t) (coefA u) (coefB u)

  ----------------------------------------------------------------------
  -- The Sol-LEVEL monoid: `_⊛_` is associative as a path between `Sol`
  -- values, over the norm index `·Assoc k₁ k₂ k₃`.  The two coordinate paths
  -- are the coordinate-associativity lemmas; the `hasNorm` field is a proof
  -- in a set (R is a CommRing, hence a set), so its PathP is filled by
  -- isProp→PathP.  Record η makes the endpoints the two associations
  -- definitionally.  The solutions form a monoid.
  ----------------------------------------------------------------------

  ⊛Assoc : {D k₁ k₂ k₃ : R} (s : Sol D k₁) (t : Sol D k₂) (u : Sol D k₃)
         → PathP (λ i → Sol D (·Assoc k₁ k₂ k₃ i))
                 (s ⊛ (t ⊛ u)) ((s ⊛ t) ⊛ u)
  ⊛Assoc {D} {k₁} {k₂} {k₃} s t u i =
    mkSol (sym (⊛AssocA s t u) i) (sym (⊛AssocB s t u) i)
          (isProp→PathP
             (λ j → is-set (N D (sym (⊛AssocA s t u) j) (sym (⊛AssocB s t u) j))
                           (·Assoc k₁ k₂ k₃ j))
             (hasNorm (s ⊛ (t ⊛ u))) (hasNorm ((s ⊛ t) ⊛ u)) i)

  ----------------------------------------------------------------------
  -- The Sol-level UNIT paths, assembled the same way (over `·IdR` / `·IdL`):
  -- `unit D = (1r, 0r)` is a two-sided identity for `_⊛_` on solutions.  With
  -- Assoc·, every monoid axiom holds as a path between `Sol` values  the
  -- solutions of a fixed norm form a monoid, and the whole family a graded one
  -- (the norm indices multiply, `_⊛_ : Sol D k₁ → Sol D k₂ → Sol D (k₁·k₂)`).
  ----------------------------------------------------------------------

  ⊛IdR : {D k : R} (s : Sol D k)
       → PathP (λ i → Sol D (·IdR k i)) (s ⊛ unit D) s
  ⊛IdR {D} {k} s i =
    mkSol (⊛UnitA-R s i) (⊛UnitB-R s i)
          (isProp→PathP
             (λ j → is-set (N D (⊛UnitA-R s j) (⊛UnitB-R s j)) (·IdR k j))
             (hasNorm (s ⊛ unit D)) (hasNorm s) i)

  ⊛IdL : {D k : R} (s : Sol D k)
       → PathP (λ i → Sol D (·IdL k i)) (unit D ⊛ s) s
  ⊛IdL {D} {k} s i =
    mkSol (⊛UnitA-L s i) (⊛UnitB-L s i)
          (isProp→PathP
             (λ j → is-set (N D (⊛UnitA-L s j) (⊛UnitB-L s j)) (·IdL k j))
             (hasNorm (unit D ⊛ s)) (hasNorm s) i)

  ----------------------------------------------------------------------
  -- The GROUP: on norm-1 solutions, `inv s = (a, −b)` is a two-sided inverse
  -- as a path between `Sol` values.
  -- Right inverse from invCoefA/invCoefB directly; left inverse by
  -- routing through commutativity (⊛CommA/⊛CommB).  So the norm-1 solutions of
  -- x² − D y² = 1 form a GROUP under `_⊛_` — Brahmagupta's bhāvanā group, the
  -- engine of the cakravla, over an abstract commutative ring.
  ----------------------------------------------------------------------

  ⊛InvR : {D : R} (s : Sol D 1r)
        → PathP (λ i → Sol D (·IdR 1r i)) (s ⊛ inv s) (unit D)
  ⊛InvR {D} s i =
    mkSol (invCoefA s i) (invCoefB s i)
          (isProp→PathP
             (λ j → is-set (N D (invCoefA s j) (invCoefB s j)) (·IdR 1r j))
             (hasNorm (s ⊛ inv s)) (hasNorm (unit D)) i)

  ⊛InvL : {D : R} (s : Sol D 1r)
        → PathP (λ i → Sol D (·IdR 1r i)) (inv s ⊛ s) (unit D)
  ⊛InvL {D} s i =
    mkSol ((⊛CommA (inv s) s ∙ invCoefA s) i)
          ((⊛CommB (inv s) s ∙ invCoefB s) i)
          (isProp→PathP
             (λ j → is-set (N D ((⊛CommA (inv s) s ∙ invCoefA s) j)
                                ((⊛CommB (inv s) s ∙ invCoefB s) j))
                           (·IdR 1r j))
             (hasNorm (inv s ⊛ s)) (hasNorm (unit D)) i)

  ----------------------------------------------------------------------
  -- Sol-level COMMUTATIVITY: `s ⊛ t ≡ t ⊛ s` as a path over the norm index
  -- `·Comm k₁ k₂`, from the coordinate commutativities.
  -- With it the graded family is a
  -- commutative monoid and the norm-1 solutions an ABELIAN group — the whole
  -- of Brahmagupta's bhvan structure, as paths between `Sol` values.
  ----------------------------------------------------------------------

  ⊛Comm : {D k₁ k₂ : R} (s : Sol D k₁) (t : Sol D k₂)
        → PathP (λ i → Sol D (·Comm k₁ k₂ i)) (s ⊛ t) (t ⊛ s)
  ⊛Comm {D} s t i =
    mkSol (⊛CommA s t i) (⊛CommB s t i)
          (isProp→PathP
             (λ j → is-set (N D (⊛CommA s t j) (⊛CommB s t j)) (·Comm _ _ j))
             (hasNorm (s ⊛ t)) (hasNorm (t ⊛ s)) i)

  ----------------------------------------------------------------------
  -- The group laws in the form §5b names: PLAIN paths in `Sol D 1r` for the
  -- retyped operation `_∙₁_` (= subst along ·IdR 1r of `_⊛_`).  Each is the
  -- corresponding ⊛-path read through `fromPathP`, since `subst B p` is exactly
  -- `transport (λ i → B (p i))`.
  ----------------------------------------------------------------------

  ∙₁-idR : {D : R} (s : Sol D 1r) → s ∙₁ unit D ≡ s
  ∙₁-idR s = fromPathP (⊛IdR s)

  ∙₁-idL : {D : R} (s : Sol D 1r) → unit D ∙₁ s ≡ s
  ∙₁-idL {D} s =
      cong (λ p → subst (Sol D) p (unit D ⊛ s)) (is-set (1r · 1r) 1r (·IdR 1r) (·IdL 1r))
    ∙ fromPathP (⊛IdL s)

  ∙₁-invR : {D : R} (s : Sol D 1r) → s ∙₁ inv s ≡ unit D
  ∙₁-invR s = fromPathP (⊛InvR s)

  ∙₁-invL : {D : R} (s : Sol D 1r) → inv s ∙₁ s ≡ unit D
  ∙₁-invL s = fromPathP (⊛InvL s)

  ----------------------------------------------------------------------
  -- Associativity of `_∙₁_` — the last group law in `_∙₁_` form, and the one
  -- that packages the AbGroup record.  `subst (Sol D) p` leaves the two
  -- coordinates fixed (they do not depend on the norm index), so `_∙₁_` and
  -- `_⊛_` agree coordinate-wise; the coordinate associativity then routes
  -- through ⊛AssocA/⊛AssocB, and `hasNorm` (a prop, R being a set) closes the
  -- record path.
  ----------------------------------------------------------------------

  substCoefA : {D k k' : R} (p : k ≡ k') (x : Sol D k)
             → coefA (subst (Sol D) p x) ≡ coefA x
  substCoefA {D} p x = sym (λ i → coefA (subst-filler (Sol D) p x i))

  substCoefB : {D k k' : R} (p : k ≡ k') (x : Sol D k)
             → coefB (subst (Sol D) p x) ≡ coefB x
  substCoefB {D} p x = sym (λ i → coefB (subst-filler (Sol D) p x i))

  ∙₁-assoc : {D : R} (s t u : Sol D 1r)
           → (s ∙₁ t) ∙₁ u ≡ s ∙₁ (t ∙₁ u)
  ∙₁-assoc {D} s t u i =
    mkSol (caPath i) (cbPath i)
          (isProp→PathP (λ j → is-set (N D (caPath j) (cbPath j)) 1r)
                        (hasNorm ((s ∙₁ t) ∙₁ u)) (hasNorm (s ∙₁ (t ∙₁ u))) i)
    where
      caPath : coefA ((s ∙₁ t) ∙₁ u) ≡ coefA (s ∙₁ (t ∙₁ u))
      caPath =
          substCoefA (·IdR 1r) ((s ∙₁ t) ⊛ u)
        ∙ cong₂ (λ x y → bhA D x y (coefA u) (coefB u))
                (substCoefA (·IdR 1r) (s ⊛ t)) (substCoefB (·IdR 1r) (s ⊛ t))
        ∙ ⊛AssocA s t u
        ∙ sym (cong₂ (λ x y → bhA D (coefA s) (coefB s) x y)
                     (substCoefA (·IdR 1r) (t ⊛ u)) (substCoefB (·IdR 1r) (t ⊛ u)))
        ∙ sym (substCoefA (·IdR 1r) (s ⊛ (t ∙₁ u)))

      cbPath : coefB ((s ∙₁ t) ∙₁ u) ≡ coefB (s ∙₁ (t ∙₁ u))
      cbPath =
          substCoefB (·IdR 1r) ((s ∙₁ t) ⊛ u)
        ∙ cong₂ (λ x y → bhB D x y (coefA u) (coefB u))
                (substCoefA (·IdR 1r) (s ⊛ t)) (substCoefB (·IdR 1r) (s ⊛ t))
        ∙ ⊛AssocB s t u
        ∙ sym (cong₂ (λ x y → bhB D (coefA s) (coefB s) x y)
                     (substCoefA (·IdR 1r) (t ⊛ u)) (substCoefB (·IdR 1r) (t ⊛ u)))
        ∙ sym (substCoefB (·IdR 1r) (s ⊛ (t ∙₁ u)))

  ----------------------------------------------------------------------
  -- The AbGroup packages: `Sol D 1r` is a set (a retract of a Σ of sets — R
  -- is a set, and each `hasNorm` fibre is a prop), and with every `_∙₁_` group
  -- law in hand, `makeGroup` assembles the group object.  So the norm-1
  -- bhāvanā solutions ARE a group, `SolGroup D`, not just a list of laws —
  -- Brahmagupta's structure as a first-class algebraic object over abstract R.
  ----------------------------------------------------------------------

  isSetSol : {D k : R} → isSet (Sol D k)
  isSetSol {D} {k} =
    isOfHLevelRetract 2 f g (λ _ → refl)
      (isSetΣ is-set (λ _ → isSetΣ is-set (λ _ → isProp→isSet (is-set _ _))))
    where
      f : Sol D k → Σ[ a ∈ R ] Σ[ b ∈ R ] (N D a b ≡ k)
      f s = coefA s , coefB s , hasNorm s
      g : (Σ[ a ∈ R ] Σ[ b ∈ R ] (N D a b ≡ k)) → Sol D k
      g (a , b , p) = mkSol a b p

  SolGroup : (D : R) → Group ℓ
  SolGroup D =
    makeGroup (unit D) _∙₁_ inv isSetSol
              (λ x y z → sym (∙₁-assoc x y z))
              ∙₁-idR ∙₁-idL ∙₁-invR ∙₁-invL

  -- Commutativity of `_∙₁_` (from ⊛CommA/⊛CommB through the substs), and then
  -- the ABELIAN group: `SolAbGroup D`.  Brahmagupta's bhvan group is abelian
  -- — one solution and its conjugate commute — the fact that lets the cakravāla
  -- walk its chain in either direction.
  ∙₁-comm : {D : R} (s t : Sol D 1r) → s ∙₁ t ≡ t ∙₁ s
  ∙₁-comm {D} s t i =
    mkSol (caPath i) (cbPath i)
          (isProp→PathP (λ j → is-set (N D (caPath j) (cbPath j)) 1r)
                        (hasNorm (s ∙₁ t)) (hasNorm (t ∙₁ s)) i)
    where
      caPath : coefA (s ∙₁ t) ≡ coefA (t ∙₁ s)
      caPath = substCoefA (·IdR 1r) (s ⊛ t) ∙ ⊛CommA s t
             ∙ sym (substCoefA (·IdR 1r) (t ⊛ s))
      cbPath : coefB (s ∙₁ t) ≡ coefB (t ∙₁ s)
      cbPath = substCoefB (·IdR 1r) (s ⊛ t) ∙ ⊛CommB s t
             ∙ sym (substCoefB (·IdR 1r) (t ⊛ s))

  SolAbGroup : (D : R) → AbGroup ℓ
  SolAbGroup D =
    makeAbGroup (unit D) _∙₁_ inv isSetSol
                (λ x y z → sym (∙₁-assoc x y z))
                ∙₁-idR ∙₁-invR ∙₁-comm

  ----------------------------------------------------------------------
  -- "One solution breeds all" (Brahmagupta), made a group law: the chain
  -- `chain s n = sⁿ` under `_∙₁_` is a monoid homomorphism (ℕ, +) → SolGroup.
  -- `chain s (m + n) ≡ chain s m ∙₁ chain s n` — composing the m-th and n-th
  -- generated solutions of x² − D y² = 1 gives the (m+n)-th.  So the cakravla
  -- orbit of a seed is exactly the cyclic sub-structure it generates; the
  -- Pell solutions are the powers of a fundamental one.
  ----------------------------------------------------------------------

  chain-add : {D : R} (s : Sol D 1r) (m n : ℕ)
            → chain s (m +ℕ n) ≡ chain s m ∙₁ chain s n
  chain-add s zero    n = sym (∙₁-idL (chain s n))
  chain-add s (suc m) n =
      cong (s ∙₁_) (chain-add s m n)
    ∙ sym (∙₁-assoc s (chain s m) (chain s n))

------------------------------------------------------------------------
-- 8.  THE CHAIN AT D = 2, COMPUTED.
--
-- A construction can be correct and vacuous.  Everything above holds in the
-- zero ring, where `Sol D k` is inhabited by the unique element and the
-- monoid is trivial; nothing so far distinguishes production from a
-- tautology.  So: turn the handle over ℤ at D = 2 and look at what comes
-- out.
--
--     3² − 2·2²  = 9 − 8      = 1
--    17² − 2·12² = 289 − 288  = 1
--    99² − 2·70² = 9801 − 9800 = 1
--
-- and each is the previous one composed with the seed by samsa-bhvan.
--
-- ATTRIBUTION.  These are not Brahmagupta's own worked numbers for D = 2:
-- Brahmagupta's showcase examples in Brhmasphuasiddhnta ch. 18 are
-- D = 83 and D = 92.  The 3/2, 17/12, 99/70 ladder is the classical sequence
-- of √2 convergents and is far older than 628 — Baudhāyana's Śulba-sūtra
-- value 577/408 lies on it.
--
-- Every equation below is `refl` — the kernel computes the composite and its
-- norm, which makes this an exact verification and not a check somebody ran.
------------------------------------------------------------------------

open import Cubical.Data.Int using (ℤ ; pos ; fromNatℤ)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Relation.Nullary using (¬_)
open import Agda.Builtin.Nat using () renaming (_==_ to _==ᵇ_)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)

module ChainAtTwo where

  open Generative ℤCommRing
  open CommRingStr (snd ℤCommRing) using (_·_)

  -- The seed for D = 2.  The `refl` is the norm obligation: it is
  -- discharged by computation, and a wrong pair would not typecheck.
  seed : Sol (pos 2) (pos 1)
  seed = mkSol (pos 3) (pos 2) refl

  -- तुल्यभावना applied to the seed.  Note the type: `_⊛_` reports the norm
  -- as 1 · 1, and over ℤ that IS 1, so no retyping is needed here.
  second : Sol (pos 2) (pos 1 · pos 1)
  second = tulya seed

  secondA : coefA second ≡ pos 17
  secondA = refl

  secondB : coefB second ≡ pos 12
  secondB = refl

  -- and once more, composing the second with the seed
  third : Sol (pos 2) ((pos 1 · pos 1) · pos 1)
  third = second ⊛ seed

  thirdA : coefA third ≡ pos 99
  thirdA = refl

  thirdB : coefB third ≡ pos 70
  thirdB = refl

  -- One more doubling reaches Baudhāyana's Śulba-sūtra value for √2, 577/408
  -- (ulba-stra 1.61-62, ~800 BCE; the same number Dvikarani.agda generates
  -- by bhāvanā).  So the classical śulba √2 convergent sits in this abstract
  -- group as the fourth power of the fundamental unit — `tulya (tulya seed)` —
  -- and its norm obligation (577² − 2·408² = 1) is discharged by the kernel.
  -- ulba geometry (~800 BCE) and Brahmagupta's composition (628) meet as one
  -- element of one group; both refls are exact computation, not observation.
  fourth : Sol (pos 2) ((pos 1 · pos 1) · (pos 1 · pos 1))
  fourth = tulya second

  fourthA : coefA fourth ≡ pos 577
  fourthA = refl

  fourthB : coefB fourth ≡ pos 408
  fourthB = refl

  seedA : coefA seed ≡ pos 3
  seedA = refl

  -- DISTINCTNESS, PROVED RATHER THAN OBSERVED.
  --
  -- Below are the
  -- actual terms, from ℤ's discreteness.
  -- Separating functions into Bool; `cong` then turns a supposed path between
  -- the integers into `true ≡ false`.  No decidability machinery and, more to
  -- the point, no postulate.
  private
    -- The numeral is an EXPRESSION here, not a pattern; Agda refuses to match
    -- on natural-number literals, and rightly, since it would expand 99 into
    -- ninety-nine `suc`s.
    isN : ℕ → ℤ → Bool
    isN k (pos n)    = n ==ᵇ k
    isN _ (negsuc _) = false

    is3 is17 : ℤ → Bool
    is3  = isN 3
    is17 = isN 17

  3≢17 : ¬ (pos 3 ≡ pos 17)
  3≢17 p = true≢false (cong is3 p)

  17≢99 : ¬ (pos 17 ≡ pos 99)
  17≢99 p = true≢false (cong is17 p)

  3≢99 : ¬ (pos 3 ≡ pos 99)
  3≢99 p = true≢false (cong is3 p)

  -- So the family at D = 2 is not the constant family.  This is a fact about
  -- D = 2 established by three terms.
