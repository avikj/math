{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- DefectCalculus
--
-- DELTA 15 (THEOREM FACTORY II) IN THE MACHINE CORE.
--
-- Delta 14 gave the transport toolkit (`PerspectiveCore`)
-- and the w±r instance (`CenterRelative`).  Delta 15 is
-- about what happens when transport does NOT go through, and its own
-- summary is the reason this file exists:
--
--   §15.24: "This is likely the right formal container for
--            boundary/measure/charge incompatibilities."
--   §15.2 C15.7: "Many apparent failures of univalent transport are
--            actually failures to include the relevant structure in the
--            object."
--
-- Both are right and both are now terms.  `Def` (§2) subsumes
-- `PerspectiveCore.SectorBreak`: a sector predicate is one structure,
-- and a sector break is one way `Def` fails to be inhabited.
--
-- WHAT IS CHECKED, BY DELTA-15 NUMBER
--
--   §1  `StructuredEquiv`     D15.5.
--       `notEquiv-not-str`    P15.6, concretely: `not : Bool ≃ Bool` is a
--                             bare equivalence that does NOT carry the
--                             distinguished point `true` to `true`.
--       `idEquiv-is-str`      … and the positive control, without which
--                             the previous line would be evidence that
--                             the definition is unsatisfiable rather
--                             than evidence about `not`.
--
--   §2  `Def`                 D15.83, the STRUCTURED DEFECT TYPE, and
--       `upgrade`/`downgrade` T15.84 both ways — which is definitional,
--                             and this file says so instead of dressing
--                             it up.  The content is C15.85: the defect
--                             is a TYPE, so it can be inhabited,
--                             refuted, or left open, and a lane claiming
--                             an incompatibility now has something
--                             specific to refute.
--
--   §3  `noEquiv→badFibre`    T15.81 / C15.82: a failed equivalence hands
--                             back a reconstruction question located in
--                             a specific fibre.
--
--   §4  `Stab`,`stab-id`,     D15.8 stabiliser, T15.9.
--       `stab-∘`,`stab-inv`
--
--   §5  `PolarBreak`          §15.4: D15.13's defect locus as a type,
--       `polar-restricts`     T15.12 sufficient direction, T15.14 as
--       `polar-break→¬pres`   `break → ¬ preserves`.
--
--   §6  `HasShift`,`shift-∘`  §15.6: D15.21, T15.22 (shifts add under
--       `shift-restricts`     composition), T15.24 (a degree-δ map
--                             restricts `X c → X (c · δ)`).
--
--   §7  `Coequalizes`,        §15.10: D15.39 kernel pair, T15.40 both
--       `descend-coeq`,       ways — but the substantive direction only
--       `descends-split`      for a SPLIT surjection; the section is what
--                             supplies `g`.  C15.41 is the reading — the
--                             kernel pair, not the quotient label, is
--                             the carrier of what must be irrelevant.
--
--                             `EffectiveDescent` proves
--                             T15.40 for an ARBITRARY surjection, proves
--                             the factorisation unique, packages the two
--                             as `descentEquiv`, and recovers
--                             `descends-split` with the same resulting
--                             `g` as `split-descent-agrees`.  The set
--                             hypothesis on `C` is genuinely used there,
--                             but `SetQuotients` is not needed at all —
--                             `PT.rec→Set` builds `g` with no quotient
--                             constructed.
--
--   §8  `refute-∘`            §15.19: T15.68 (no-go propagates
--       `refute-transport`    contravariantly), T15.70/C15.71 (a
--                             refutation transports across equivalence
--                             exactly as a positive theorem does).
--                             Delta 15 calls this "executable pruning
--                             without special refutation edges".
--
--   §9  `invariant-separates` T15.73 — sharper than the directive
--                             suggests.  Under univalence EVERY function
--                             out of the universe is an
--                             equivalence-invariant, so no invariance
--                             hypothesis is needed at all: `cong I (ua e)`
--                             is the whole proof.  This makes the
--                             SOUNDNESS of invariant-based separation
--                             free; it does not make FINDING a separating
--                             invariant the same search as finding an
--                             equivalence (graph invariants vs. graph
--                             isomorphism are the standard contrast).
--
--  * **Not novel.**  Structure identity, stabilisers, kernel pairs and
--    contravariant refutation are standard.  The contribution is that the
--    core now has them, so a later lane cites instead of re-deriving.
------------------------------------------------------------------------

module DefectCalculus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.Empty as Empty using (⊥)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ

------------------------------------------------------------------------
-- 1.  STRUCTURED OBJECTS AND STRUCTURED EQUIVALENCE  (D15.5, P15.6)
------------------------------------------------------------------------

StructuredEquiv :
  (Str : Type ℓ → Type ℓ') (A B : Type ℓ) → Str A → Str B → Type _
StructuredEquiv Str A B sA sB =
  Σ[ e ∈ (A ≃ B) ] (subst Str (ua e) sA ≡ sB)

-- The structure family used for the witnesses below: a distinguished
-- point.  `Pointed X = X`, so `subst Pointed p` is just `transport p`.
Pointed : Type₀ → Type₀
Pointed X = X

notEquiv : Bool ≃ Bool
notEquiv = isoToEquiv (iso not not lem lem)
  where
  lem : (b : Bool) → not (not b) ≡ b
  lem true  = refl
  lem false = refl

-- P15.6.  `notEquiv` is a bare equivalence that does not preserve the
-- distinguished point.  C15.7's diagnosis applies verbatim: the failure
-- is not in the equivalence, it is that the point was never part of what
-- was being equated.
notEquiv-not-str : subst Pointed (ua notEquiv) true ≡ true → ⊥
notEquiv-not-str p = true≢false (sym (sym (uaβ notEquiv true) ∙ p))

-- Positive control.  Without this, the line above would be evidence that
-- the definition is unsatisfiable rather than evidence about `not`.
idEquiv-is-str : subst Pointed (ua (idEquiv Bool)) true ≡ true
idEquiv-is-str = uaβ (idEquiv Bool) true

------------------------------------------------------------------------
-- 2.  THE STRUCTURED DEFECT  (D15.83, T15.84, C15.85)
--
-- The centrepiece.  Given a bare equivalence and structures on each
-- side, the defect is the identity type asserting that transport carries
-- one to the other.
------------------------------------------------------------------------

Def : (Str : Type ℓ → Type ℓ') {A B : Type ℓ}
    → (e : A ≃ B) → Str A → Str B → Type ℓ'
Def Str e sA sB = subst Str (ua e) sA ≡ sB

-- T15.84, both directions.  This is DEFINITIONAL — `StructuredEquiv` is
-- a Σ whose second component is exactly `Def` — and saying so is more
-- useful than presenting it as a theorem.  What is not definitional, and
-- is the actual point, is C15.85: `Def` is a type, so "the structures
-- are incompatible" becomes a refutable statement rather than a mood.
upgrade : (Str : Type ℓ → Type ℓ') {A B : Type ℓ} (e : A ≃ B)
        → {sA : Str A} {sB : Str B}
        → Def Str e sA sB → StructuredEquiv Str A B sA sB
upgrade Str e d = e , d

downgrade : (Str : Type ℓ → Type ℓ') {A B : Type ℓ}
          → {sA : Str A} {sB : Str B}
          → (se : StructuredEquiv Str A B sA sB)
          → Def Str (se .fst) sA sB
downgrade Str se = se .snd

-- The §1 witness, restated in the vocabulary of §2: a refuted defect.
pointDefect-refuted : Def Pointed notEquiv true true → ⊥
pointDefect-refuted = notEquiv-not-str

------------------------------------------------------------------------
-- 3.  THE EQUIVALENCE–DEFECT DICHOTOMY  (T15.81, C15.82)
--
-- Delta 15: "if f is an equivalence, all equivalence-invariant
-- mathematics transports; if it is not, at least one of its homotopy
-- fibers is noncontractible or empty."  The second half is the
-- contrapositive of the fibrewise characterisation of `isEquiv`, which
-- in cubical Agda IS the definition, so it is one step.
------------------------------------------------------------------------

noEquiv→badFibre :
  {f : A → B} → (isEquiv f → ⊥) → ((b : B) → isContr (fiber f b)) → ⊥
noEquiv→badFibre notE allContr = notE (record { equiv-proof = allContr })

-- C15.82, stated with its scope: `noEquiv→badFibre` yields only
-- ¬ (∀ b → isContr (fiber f b)) — constructively ¬¬ Σ b, not a b in hand.
-- LOCATING the bad fibre is search; turning the refutation into a named
-- site costs at least Markov's Principle in general
-- (`TritiyaMarga_TheWrittenDefectCostsMarkovsPrinciple`).  `FailedAt` is
-- the predicate a site satisfies once someone has found it.
FailedAt : (f : A → B) (b : B) → Type _
FailedAt f b = isContr (fiber f b) → ⊥

failedEquivQuestion :
  {f : A → B} (b : B) → FailedAt f b → isEquiv f → ⊥
failedEquivQuestion b bad e = bad (e .equiv-proof b)

------------------------------------------------------------------------
-- 4.  STABILISERS  (D15.8, T15.9, C15.10)
------------------------------------------------------------------------

module _ (Str : Type ℓ → Type ℓ') {A : Type ℓ} (s : Str A) where

  Stab : (A ≃ A) → Type ℓ'
  Stab g = subst Str (ua g) s ≡ s

  stab-id : Stab (idEquiv A)
  stab-id = cong (λ p → subst Str p s) uaIdEquiv ∙ substRefl {B = Str} s

  stab-∘ : (g h : A ≃ A) → Stab g → Stab h → Stab (compEquiv g h)
  stab-∘ g h sg sh =
      cong (λ p → subst Str p s) (uaCompEquiv g h)
    ∙ substComposite Str (ua g) (ua h) s
    ∙ cong (subst Str (ua h)) sg
    ∙ sh

  stab-inv : (g : A ≃ A) → Stab g → Stab (invEquiv g)
  stab-inv g sg =
      cong (subst Str (ua (invEquiv g))) (sym sg)
    ∙ sym (substComposite Str (ua g) (ua (invEquiv g)) s)
    -- `invEquiv-is-rinv` is the LIBRARY's (`Cubical.Foundations.Equiv`).
    ∙ cong (λ p → subst Str p s)
        (sym (uaCompEquiv g (invEquiv g)) ∙ cong ua (invEquiv-is-rinv g) ∙ uaIdEquiv)
    ∙ substRefl {B = Str} s

------------------------------------------------------------------------
-- 5.  POLARIZATION  (§15.4: T15.12, D15.13, T15.14)
--
-- An involution `J` and a predicate `P`.  Does `J` restrict to `P`?
------------------------------------------------------------------------

module _ {A : Type ℓ} (J : A → A) (P : A → Type ℓ') where

  -- T15.12, sufficient direction.
  polar-restricts :
    ((a : A) → P a → P (J a)) → Σ A P → Σ A P
  polar-restricts h (a , pa) = (J a , h a pa)

  -- D15.13, the defect locus, as a type rather than a set difference:
  -- a point in `P` whose reflection is not.
  PolarBreak : Type _
  PolarBreak = Σ[ a ∈ A ] (P a × (P (J a) → ⊥))

  -- T15.14.  A break refutes preservation.  (Delta 15's "D = ∅ iff J
  -- preserves P" is the set-level shadow of this; in a proof-relevant
  -- setting the inhabited/uninhabited statement is the exact one.)
  polar-break→¬pres : PolarBreak → ((a : A) → P a → P (J a)) → ⊥
  polar-break→¬pres (a , pa , notPJa) h = notPJa (h a pa)

------------------------------------------------------------------------
-- 6.  CHARGE GRADING  (§15.6: D15.21, T15.22, T15.24)
--
-- `C` is the charge carrier with a composition `_·_`.  A map of the
-- total space has shift δ when it moves the base uniformly by δ.
------------------------------------------------------------------------

module Graded {C : Type ℓ} (_·_ : C → C → C)
              (assoc· : (x y z : C) → (x · y) · z ≡ x · (y · z))
              (X : C → Type ℓ') where

  Total : Type _
  Total = Σ C X

  HasShift : (Total → Total) → C → Type _
  HasShift T δ = (t : Total) → T t .fst ≡ (t .fst) · δ

  -- T15.24.  A degree-δ map restricts to `X c → X (c · δ)`.
  shift-restricts :
    (T : Total → Total) (δ : C) → HasShift T δ
    → (c : C) → X c → X (c · δ)
  shift-restricts T δ hs c x = subst X (hs (c , x)) (T (c , x) .snd)

  -- T15.22.  Shifts add under composition.  Associativity of `_·_` is
  -- exactly what is needed and is therefore a hypothesis, not an
  -- assumption smuggled in.
  shift-∘ :
    (S T : Total → Total) (δS δT : C)
    → HasShift S δS → HasShift T δT
    → HasShift (S ∘ T) (δT · δS)
  shift-∘ S T δS δT hS hT t =
    hS (T t) ∙ cong (_· δS) (hT t) ∙ assoc· (t .fst) δT δS

------------------------------------------------------------------------
-- 7.  DESCENT THROUGH A QUOTIENT  (§15.10: D15.39, T15.40, C15.41)
------------------------------------------------------------------------

module _ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (q : A → B) (f : A → C) where

  -- D15.39, the kernel pair as a relation.
  Coequalizes : Type _
  Coequalizes = (x y : A) → q x ≡ q y → f x ≡ f y

  -- T15.40, the easy direction: a factorisation coequalises.
  descend-coeq : (Σ[ g ∈ (B → C) ] ((a : A) → g (q a) ≡ f a)) → Coequalizes
  descend-coeq (g , fact) x y p =
    sym (fact x) ∙ cong g p ∙ fact y

-- T15.40, the substantive direction, for a SPLIT surjection: the section
-- supplies `g` directly.  Delta 15 states it for a surjection; the
-- general surjection is `EffectiveDescent`, where the set hypothesis on
-- `C` is needed and `SetQuotients` is not.  `PT.rec→Set` (a 2-Constant
-- map into a set factors through `∥_∥₁`) builds `g` with no quotient——
-- constructed — the same argument `FiniteInformation`'s
-- `fiberConstant→factorsThrough` runs for `Image q`.
-- That module also proves the factorisation UNIQUE, packages the pair
-- as an equivalence `(B → C) ≃ Σ[ f ] Coequalizes q f`, and proves the
-- converse: injectivity of that map at the single set `hProp` forces `q`
-- surjective.  So surjectivity there is not a convenience hypothesis, and
-- `descends-split` below is recovered — with the same resulting `g` —
-- as `EffectiveDescent.split-descent-agrees`.
descends-split :
  {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (q : A → B) (f : A → C) (s : B → A) → ((b : B) → q (s b) ≡ b)
  → Coequalizes q f
  → Σ[ g ∈ (B → C) ] ((a : A) → g (q a) ≡ f a)
descends-split q f s sect coeq = (f ∘ s) , λ a → coeq (s (q a)) a (sect (q a))

------------------------------------------------------------------------
-- 8.  REFUTATION TRANSPORT  (§15.19: T15.68, T15.70, C15.71)
--
-- "Executable pruning without special refutation edges."
------------------------------------------------------------------------

-- T15.68.  No-go knowledge propagates contravariantly along reductions.
refute-∘ : (A → ⊥) → (B → A) → (B → ⊥)
refute-∘ f g = f ∘ g

-- T15.70 / C15.71.  A refutation transports across equivalence exactly
-- as a positive theorem does — no separate machinery.
refute-transport : (A ≃ B) → (A → ⊥) → (B → ⊥)
refute-transport e f = f ∘ invEq e

------------------------------------------------------------------------
-- 9.  INVARIANTS SEPARATE  (§15.20: T15.73, C15.74)
--
-- Sharper than the directive states it.  Delta 15 asks for an
-- *equivalence-invariant* `I`; under univalence there is no such side
-- condition to check, because every function out of the universe is one.
-- `cong I (ua e)` is the entire proof.  What collapses is the SIDE
-- CONDITION on I, not the search for one: finding a separating invariant
-- remains a separate problem from finding an equivalence.
------------------------------------------------------------------------

invariant-separates :
  {X : Type ℓ''} (I : Type ℓ → X) {A B : Type ℓ}
  → (I A ≡ I B → ⊥) → (A ≃ B) → ⊥
invariant-separates I sep e = sep (cong I (ua e))
