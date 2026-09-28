{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.ApavadaVisaya_TheLineWorldCorollaryPinsItsObservableUpToScalar
--
-- अपवादविषय — *the scope of the exception*.  उत्सर्ग / अपवाद, the general
-- rule and the special rule that blocks it, is Pini's (Adhyy, c. 500
-- BCE); विषय, the domain over which a rule actually applies, is the
-- commentators' term for the question this module answers (Patajali,
-- Mahbhya, c. 150 BCE, uses it throughout for a rule's field of
-- application). The  names the SHAPE of the question — *a special
-- rule was promoted to a general one; what exactly was its scope?* — because
-- the grammarians posed that question as a technical one and this corpus has
-- been posing it informally.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS MODULE ADDS, AND TO WHAT
--
-- `notes/ENCOUNTERED_WORLDS.md` (absent from this repository) §3.5 states, and proves:
--
--   **Theorem.**  If `T_E(x)` is a linear subspace `L ⊆ (ℤ/p)^n`, then
--   transport at `x` ⟺ `grad f(x)|_L` is not identically zero.
--
--   **Corollary (line worlds).**  For `f = X+Y` and `E = {(a, sa)}`, the
--   tangent set is `span{(1,s)}` and `grad f|_L (t) = t(1+s)`.  So `E`
--   transports **iff `s ≠ -1 (mod p)`**.
--
-- `notes/FULL_READ_DRAW_5.md` (absent from this repository) §C2 records that a summary message dropped
-- the two words "For `f = X+Y`" under a Theorem quantified over all
-- integral `f`.  `NaturalMachine.LineWorldTransport` makes the corollary's
-- hypothesis part of a type, and exhibits ONE counterexample to the
-- dropped reading: for `f = X`, `grad f|_L(t) = t`, so every line world
-- transports, at `s = -1` included.
-- `NaturalMachine.Control.QuantifierDrop` is the must-fail control.
--
-- The corpus therefore records: *there exists an `f` for which the
-- corollary fails.*  It does not record HOW MANY, or WHICH.  That is the
-- अपवादविषय question, and it has an exact answer at every prime.
--
-- ────────────────────────────────────────────────────────────────────
-- THE THEOREM, FOR EVERY PRIME (written proof; §4 below checks p = 5
-- exhaustively as a closed computation)
--
-- Let `p` be prime, `f = c₁X + c₂Y` a linear observable over ℤ/p, and
-- `E = {(a, sa)}`.  By §3.5's Theorem, `E` transports iff
-- `grad f|_L ≢ 0`, i.e. iff `c₁ + c₂ s ≢ 0 (mod p)`.  Write
--
--     Z(f) = { s ∈ ℤ/p : c₁ + c₂ s ≡ 0 }.
--
-- The corollary asserts `transports ⟺ s ≢ -1`, so corollary and truth
-- agree at every slope exactly when `Z(f) = {-1}`.
--
--   * `c₂ ≠ 0`.  ℤ/p is a field, so `c₁ + c₂ s = 0` has the unique root
--     `s = -c₁c₂⁻¹` and `Z(f)` is a singleton.  It is `{-1}` iff
--     `-c₁c₂⁻¹ = -1`, i.e. iff `c₁ = c₂`.
--   * `c₂ = 0`, `c₁ ≠ 0`.  `Z(f) = ∅ ≠ {-1}`.
--   * `c₂ = c₁ = 0`.  `Z(f) = ℤ/p ≠ {-1}`, since `p ≥ 2`.
--
--     **The line-world corollary holds for `f = c₁X + c₂Y` if and only
--     if `c₁ = c₂ ≠ 0`** — that is, iff `f` is a NONZERO SCALAR MULTIPLE
--     of `X+Y`.                                                      ∎
--
-- So the hypothesis "For `f = X+Y`" is not merely sufficient.  Within the
-- linear family it is **necessary, and it pins `f` up to a scalar**: the
-- corollary is a complete characterisation of its own observable.  The
-- dropped-quantifier reading is false on exactly `p² - (p-1)` of the `p²`
-- linear observables — 21 of 25 at `p = 5`.
--
-- This strictly strengthens `LineWorldTransport.dropped-hypothesis-false`,
-- which exhibits one witness.  It does not correct it; it locates it.
--
-- ────────────────────────────────────────────────────────────────────
-- WHERE PRIMALITY ENTERS, AND TWO LITERATURES THAT SAY SO
--
-- §3.5's proof turns on one step: *"`{grad f(x)·h : h ∈ L}` is a subgroup
-- of ℤ/p, hence `{0}` or all of ℤ/p."*  That dichotomy is primality and
-- nothing else.  In ℤ/N with `N` composite, a nonzero `g` generates the
-- subgroup of index `gcd(g,N)`, so transport can fail with `grad ≢ 0`:
-- at `N = 4`, `g = 2`, target `3`, the attainable set is `{0,2}` and `3`
-- is not in it.  This is not a correction to §3.5 — the note is p-adic
-- throughout — it is a statement of where its hypothesis is load-bearing.
--
-- Two literatures had to confront exactly the
-- composite case the corpus never enters, and each records a result:
--
--   * **Music and tuning theory.**  A cyclic division into `N` steps, and
--     a fixed interval of `g` steps: the chain of that interval visits
--     `N / gcd(g,N)` pitch classes and then closes.  The tradition works
--     at composite `N` and therefore had to face this.  Bharata,
--     *Nāṭyaśāstra* ch. 28 (c. 200 BCE – 200 CE) establishes the 22
--     śrutis by the *sāraṇā* procedure — two vīṇās identically tuned, one
--     displaced one ruti at a time, coincidences observed; the fourfold
--     form *sra-catuaya* is set out in Abhinavagupta's
--     *Abhinavabhrat* (c. 1000 CE) at N 28.26.  On the resulting
--     4-3-2-4-4-3-2 division, aja and pacama are separated by 13 of
--     the 22 steps, and `gcd(13,22) = 1`, so the chain of pacamas
--     exhausts all 22; a chain of 4 steps has `gcd(4,22) = 2` and closes
--     early into two disjoint circles.  rgadeva,
--     *Saṅgītaratnākara* I (c. 1210–1247 CE), tabulates the division.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS MODULE DELIBERATELY DOES NOT DO
--
-- It does NOT widen `LineWorldTransport.Obs` from two constructors to the
-- full linear family, although that is where the mathematics wants to
-- live.  `Obs` is the quantification domain of the must-fail control
-- `Control/QuantifierDrop.agda`, whose designed failure is pinned to a
-- verbatim error message under two toolchains
-- (`notes/PIN_SWEEP_NATURALMACHINE.md` (absent from this repository) §4, Agda 2.8.0 + cubical v0.9;
-- and the container, Agda 2.6.3 + cubical v0.5).  Adding constructors to
-- `Obs` changes how `transports f s` reduces on an open `f` and can move
-- or destroy that error site.  So this module IMPORTS `Slope`, `mod5`,
-- `attains`, `crit`, `eqℕ` and works over its own `Lin`; every statement
-- below is about the corpus's own `attains` and `crit`, not about copies.
------------------------------------------------------------------------

module NaturalMachine.ApavadaVisaya_TheLineWorldCorollaryPinsItsObservableUpToScalar where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_)
open import Cubical.Data.Bool.Properties using (true≢false)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import NaturalMachine.LineWorldTransport
  using (Slope ; s0 ; s1 ; s2 ; s3 ; s4 ; val ; mod5 ; eqℕ ; attains ; crit)

private
  eqB : Bool → Bool → Bool
  eqB true  true  = true
  eqB false false = true
  eqB _     _     = false

  false≢true : ¬ (false ≡ true)
  false≢true q = true≢false (sym q)

------------------------------------------------------------------------
-- 1.  THE FULL LINEAR OBSERVABLE FAMILY over ℤ/5.
--
-- `LineWorldTransport.Obs` carries two observables, the two the audit
-- contrasted.  A linear observable `f = c₁X + c₂Y` is exactly its pair of
-- gradient coefficients, and over ℤ/5 there are 25 of them.  Coefficients
-- are reused as `Slope` because both range over ℤ/5.

Lin : Type
Lin = Slope × Slope

-- `grad f|_L(1) = c₁ + c₂·s`, the same computation as
-- `LineWorldTransport.grad`, over the full family.
gradL : Lin → Slope → ℕ
gradL (a , b) s = mod5 (val a + val b · val s)

transportsL : Lin → Slope → Bool
transportsL f s = attains (gradL f s)

------------------------------------------------------------------------
-- 2.  सारणा — WHICH CHAINS EXHAUST THE CYCLE.
--
-- `attains g` asks whether the target `-1 = 4` lies in `{t·g : t ∈ ℤ/5}`,
-- i.e. whether the chain of the interval `g` reaches a given step of the
-- cycle.  At a PRIME modulus the answer is degenerate: every nonzero
-- interval exhausts the cycle, so `attains` is just "`g` is nonzero".
--
-- This is the whole content of §3.5's step "hence `{0}` or all of ℤ/p",
-- and it is where primality does its work.  In the tuning literature the
-- modulus is composite (12, 22) and the corresponding statement is the
-- gcd law, which does not degenerate; see the header.

sarana-at-a-prime : (s : Slope) → attains (val s) ≡ not (eqℕ (val s) 0)
sarana-at-a-prime s0 = refl
sarana-at-a-prime s1 = refl
sarana-at-a-prime s2 = refl
sarana-at-a-prime s3 = refl
sarana-at-a-prime s4 = refl

------------------------------------------------------------------------
-- 3.  THE TWO PREDICATES BEING COMPARED.
--
-- `agrees f` : does the corollary's criterion `s ≢ -1` agree with actual
-- transport at every one of the five slopes?  Decided by exhaustion, so
-- every proof below is a closed computation and `refl`.
--
-- `scalarOfXY f` : is `f` a nonzero scalar multiple of `X+Y`, i.e.
-- `c₁ = c₂ ≠ 0`?

agrees : Lin → Bool
agrees f =
      eqB (transportsL f s0) (crit s0)
  and eqB (transportsL f s1) (crit s1)
  and eqB (transportsL f s2) (crit s2)
  and eqB (transportsL f s3) (crit s3)
  and eqB (transportsL f s4) (crit s4)

scalarOfXY : Lin → Bool
scalarOfXY (a , b) = eqℕ (val a) (val b) and not (eqℕ (val a) 0)

------------------------------------------------------------------------
-- 4.  THE अपवादविषय THEOREM at p = 5, exhaustively: the corollary's
--     criterion is correct for a linear observable EXACTLY WHEN that
--     observable is a nonzero scalar multiple of `X+Y`.
--
--     Twenty-five closed cases, twenty-five `refl`.  This is the p = 5
--     instance of the written proof in the header.

visaya : (f : Lin) → agrees f ≡ scalarOfXY f
visaya (s0 , s0) = refl
visaya (s0 , s1) = refl
visaya (s0 , s2) = refl
visaya (s0 , s3) = refl
visaya (s0 , s4) = refl
visaya (s1 , s0) = refl
visaya (s1 , s1) = refl
visaya (s1 , s2) = refl
visaya (s1 , s3) = refl
visaya (s1 , s4) = refl
visaya (s2 , s0) = refl
visaya (s2 , s1) = refl
visaya (s2 , s2) = refl
visaya (s2 , s3) = refl
visaya (s2 , s4) = refl
visaya (s3 , s0) = refl
visaya (s3 , s1) = refl
visaya (s3 , s2) = refl
visaya (s3 , s3) = refl
visaya (s3 , s4) = refl
visaya (s4 , s0) = refl
visaya (s4 , s1) = refl
visaya (s4 , s2) = refl
visaya (s4 , s3) = refl
visaya (s4 , s4) = refl

-- The corollary's own observable is in scope, as the corpus has it.
XY-is-in-the-visaya : agrees (s1 , s1) ≡ true
XY-is-in-the-visaya = refl

-- And so are its three nonzero scalar multiples — the corollary does NOT
-- pin `f` on the nose, only up to a scalar.
2XY-is-in-the-visaya : agrees (s2 , s2) ≡ true
2XY-is-in-the-visaya = refl

3XY-is-in-the-visaya : agrees (s3 , s3) ≡ true
3XY-is-in-the-visaya = refl

4XY-is-in-the-visaya : agrees (s4 , s4) ≡ true
4XY-is-in-the-visaya = refl

-- Anything with `c₁ ≠ c₂`, or with `c₁ = c₂ = 0`, is outside it.
outside-the-visaya : (f : Lin) → agrees f ≡ true → scalarOfXY f ≡ true
outside-the-visaya f h = sym (visaya f) ∙ h

------------------------------------------------------------------------
-- 5.  THE FAILURE HAS SHAPES, NOT A SHAPE.
--
-- `LineWorldTransport` records that the criterion "names the wrong set"
-- for `f = X`.  It names a DIFFERENT wrong set for each observable
-- outside the viaya, and the sets are not nested.  `disagreeAt f` is the
-- indicator of the disagreement, slope by slope.

disagreeAt : Lin → Bool × Bool × Bool × Bool × Bool
disagreeAt f = d s0 , d s1 , d s2 , d s3 , d s4
  where
  d : Slope → Bool
  d s = not (eqB (transportsL f s) (crit s))

-- `f = X`, gradient `(1,0)`: the criterion is wrong at `s = -1` only.
shape-X : disagreeAt (s1 , s0) ≡ (false , false , false , false , true)
shape-X = refl

-- `f = Y`, gradient `(0,1)`: wrong at `s = 0` AND at `s = -1`.
shape-Y : disagreeAt (s0 , s1) ≡ (true , false , false , false , true)
shape-Y = refl

-- `f = 0`, gradient `(0,0)`: wrong at every slope EXCEPT `s = -1`, the
-- one slope the criterion excludes.  The criterion is exactly inverted.
shape-zero : disagreeAt (s0 , s0) ≡ (true , true , true , true , false)
shape-zero = refl

-- The three are pairwise distinct, so "the criterion names the wrong set"
-- is a family of statements, not one.
X≠Y : ¬ (disagreeAt (s1 , s0) ≡ disagreeAt (s0 , s1))
X≠Y q = false≢true (cong fst q)

X≠zero : ¬ (disagreeAt (s1 , s0) ≡ disagreeAt (s0 , s0))
X≠zero q = false≢true (cong fst q)

Y≠zero : ¬ (disagreeAt (s0 , s1) ≡ disagreeAt (s0 , s0))
Y≠zero q = false≢true (cong (λ t → fst (snd t)) q)

------------------------------------------------------------------------
-- 6.  THE SENTENCE.
--
-- The dropped hypothesis was not a hypothesis that happened to be needed.
-- It was a complete description of the corollary's viaya: the criterion
-- `s ≢ -1` is correct for a linear observable if and only if that
-- observable is a nonzero scalar multiple of the one named in the
-- hypothesis.  Dropping "For `f = X+Y`" from the corollary does not
-- overreach by a margin.  It overreaches onto 21 of 25 observables at
-- `p = 5`, and onto `p² - (p-1)` of `p²` at every prime, in `p²-p+1`
-- distinct failure shapes at most — one per distinct zero-set of a
-- linear form, plus the constant.
--
-- `Control/QuantifierDrop.agda` is therefore testing a maximal claim: the
-- statement it asserts is false as widely as a statement of that form can
-- be, and remains false however `Obs` is enlarged inside the linear
-- family, since the corollary's truth set is fixed at four observables.
------------------------------------------------------------------------
