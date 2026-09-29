{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- विपर्यास — transposition.  The kernel carries a contravariant,
-- grade-preserving transpose, and is not a groupoid.
--
-- WHAT THIS IS.  The kernel's `reverse` is a constructor of Step, which
-- is the passage from functions to CORRESPONDENCES: a function has no
-- transpose, a correspondence does.  This file constructs the transpose
-- on whole derivations and proves the laws it does satisfy on the strict
-- category of derivations.  (A dagger in the strict sense also needs
-- d†† = d; §4 refutes that on the nose, so this is a dagger only up to
-- meaning — the name in the title is kept for continuity.) —
--
--   §2  daṇḍa : Derivation x y → Derivation y x, with daṇḍa (done) = done
--       and CONTRAVARIANT functoriality proved:
--       daa (d ⊕ e) ≡ daa e ⊕ daa d.
--   §3  daa PRESERVES THE GRADE: dairghya (daa d) ≡ dairghya d.
--       The transpose costs what the route cost; it forgets nothing.
--   §4  daṇḍa is NOT an involution on the nose — the double transpose of
--       a one-step derivation is refuted by counting its reversal marks —
--       and, the wall: NO function whatsoever is an inverse for ⊕.  Not
--       daa, not a cleverer candidate: the grade is additive and
--       detects the unit, so `d ⊕ f d ≡ done` dies at a length-one
--       derivation for every f.  This is the Laghava dichotomy (a
--       structure is graded or invertible, never both) landed on the
--       kernel's own category: what survives the prohibition of the
--       inverse is exactly the dagger.
--
-- THE MOTIVIC SENTENCE, stated as the reading it is.  Morphisms of
-- motives are correspondences closed under transpose; a category of
-- correspondences is self-dual and NOT a groupoid, and its linearisation
-- is what discards the route.  Here the same shape is a theorem: the
-- derivation category carries its transpose as structure (§2–§3) and is
-- forbidden its inverse by its own grading (§4) — dagger yes, groupoid
-- never, and the gap between the two is where every unit of cost in the
-- corpus lives (abstract 13).  The identification of `reverse` with the
-- transpose of a Chow correspondence is asserted syt: true under the named standpoint, with the checked shape as its warrant.
------------------------------------------------------------------------

module Viparyasa_TheTransposeIsAContravariantGradePreservingDaggerAndTheGradeForbidsItFromEverBeingAnInverse where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Nat as N
open import Kernel.RewriteCertificate

private
  variable
    x y z w : Tm

------------------------------------------------------------------------
-- १ · Concatenation: strict on the nose, as data.
------------------------------------------------------------------------

_⊕_ : Derivation x y → Derivation y z → Derivation x z
done _        ⊕ e = e
then-step s d ⊕ e = then-step s (d ⊕ e)

⊕-assoc : (d : Derivation w x) (e : Derivation x y) (f : Derivation y z)
        → (d ⊕ e) ⊕ f ≡ d ⊕ (e ⊕ f)
⊕-assoc (done _)        e f = refl
⊕-assoc (then-step s d) e f = cong (then-step s) (⊕-assoc d e f)

⊕-unitr : (d : Derivation x y) → d ⊕ done y ≡ d
⊕-unitr (done _)        = refl
⊕-unitr (then-step s d) = cong (then-step s) (⊕-unitr d)

------------------------------------------------------------------------
-- २ · The transpose, and its contravariance.
------------------------------------------------------------------------

daṇḍa : Derivation x y → Derivation y x
daṇḍa (done x)        = done x
daṇḍa (then-step s d) = daṇḍa d ⊕ then-step (reverse s) (done _)

daṇḍa-anti : (d : Derivation x y) (e : Derivation y z)
           → daṇḍa (d ⊕ e) ≡ daṇḍa e ⊕ daṇḍa d
daṇḍa-anti (done _)        e = sym (⊕-unitr (daṇḍa e))
daṇḍa-anti (then-step s d) e =
  cong (_⊕ then-step (reverse s) (done _)) (daṇḍa-anti d e)
  ∙ ⊕-assoc (daṇḍa e) (daṇḍa d) (then-step (reverse s) (done _))

------------------------------------------------------------------------
-- ३ · The grade, its additivity, and its preservation by the dagger.
------------------------------------------------------------------------

dairghya : Derivation x y → N.ℕ
dairghya (done _)        = N.zero
dairghya (then-step _ d) = N.suc (dairghya d)

dairghya-⊕ : (d : Derivation x y) (e : Derivation y z)
           → dairghya (d ⊕ e) ≡ dairghya d N.+ dairghya e
dairghya-⊕ (done _)        e = refl
dairghya-⊕ (then-step s d) e = cong N.suc (dairghya-⊕ d e)

daṇḍa-mātrā : (d : Derivation x y) → dairghya (daṇḍa d) ≡ dairghya d
daṇḍa-mātrā (done _)        = refl
daṇḍa-mātrā (then-step s d) =
  dairghya-⊕ (daṇḍa d) (then-step (reverse s) (done _))
  ∙ N.+-suc (dairghya (daṇḍa d)) N.zero
  ∙ cong N.suc (N.+-zero (dairghya (daṇḍa d)))
  ∙ cong N.suc (daṇḍa-mātrā d)

------------------------------------------------------------------------
-- ४ · The wall.  Not an involution on the nose; never an inverse.
------------------------------------------------------------------------

-- The one-step witness, README-draft-2 §3's own first rule.
d₀ : Derivation (add var zero) var
d₀ = then-step (add-zero var) (done var)

-- Counting the reversal marks on the head step separates d₀ from its
-- double transpose: the dagger is weak, syntactically, exactly as the
-- master abstract says — and the count is the residue.
revGaṇana : Step x y → N.ℕ
revGaṇana (reverse s) = N.suc (revGaṇana s)
revGaṇana _           = N.zero

śiroGaṇana : Derivation x y → N.ℕ
śiroGaṇana (done _)        = N.zero
śiroGaṇana (then-step s _) = revGaṇana s

dvidaṇḍa-na-svayam : daṇḍa (daṇḍa d₀) ≡ d₀ → ⊥
dvidaṇḍa-na-svayam p = N.snotz (cong śiroGaṇana p)

-- And the general prohibition: no candidate transpose-like function is
-- an inverse for concatenation.  The grade is additive (§3) and the
-- unit's grade is zero, so a length-one derivation refutes every f at
-- once.  Graded, therefore never invertible: the dagger is all the
-- symmetry the grading permits.
na-vilomaḥ : (f : ∀ {x y} → Derivation x y → Derivation y x)
           → (∀ {x y} (d : Derivation x y) → (d ⊕ f d) ≡ done x)
           → ⊥
na-vilomaḥ f h = N.snotz (cong dairghya (h d₀))

-- The dagger itself survives the prohibition it is subject to: daa is
-- total, contravariant, grade-preserving — and by na-vilomaḥ it is not,
-- and can never be completed to, an inverse.  Self-dual and irreversibly
-- graded at once: a category of correspondences, not a groupoid.

------------------------------------------------------------------------
-- ५ · The semantic collapse.  The interpretation sends the dagger to
-- path inversion — up to a filler that exists because the meaning lives
-- in a set.  Syntactically the dagger is weak (§4); semantically its
-- whole weakness is quotiented in one stroke: every route and its
-- transpose interpret to inverse paths, with no case analysis, because
-- an identity type over ℕ is a proposition.  This is the master
-- abstract's "one order-two redundancy the interpretation divides out",
-- exhibited on the dagger itself.
------------------------------------------------------------------------

open import Cubical.Data.Nat using (isSetℕ)

daṇḍa-artha : (d : Derivation x y) (ρ : Env)
            → derivation-sound (daṇḍa d) ρ ≡ sym (derivation-sound d ρ)
daṇḍa-artha d ρ =
  isSetℕ _ _ (derivation-sound (daṇḍa d) ρ) (sym (derivation-sound d ρ))
