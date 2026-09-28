{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- BhavanaAssoc — associativity of bhāvanā as an EQUALITY AFTER TRANSPORT,
-- with every coordinate identity rederived by the ring solver.
--
-- THE SETTING.  In `BhavanaGenerative.agda` (absent from this repository) the two associations of the
-- composition live at DIFFERENT norm indices,
-- `Sol D (k₁ · (k₂ · k₃))` and `Sol D ((k₁ · k₂) · k₃)`, so `≡` cannot even
-- be written between them without first bringing the indices together.
--
-- WHAT IS ALREADY THERE.  Section 7 of `BhavanaGenerative` assembles
-- `Assoc`, `Comm`,
-- `⊛IdR`, `⊛IdL` as PathPs over `·Assoc`/`·Comm`/`·IdR`/`·IdL`.
-- Those are DEPENDENT paths.  What that file does NOT
-- state, for general norm indices, is the non-dependent form the §7 note
-- describes as the obstacle — an equality in ONE type, after transporting one
-- side along the ring identity — and it reaches equality of `Sol` records
-- only by rebuilding `mkSol … (isProp→PathP …)` by hand at every use, with
-- no reusable lemma saying "two solutions with the same coordinates are
-- equal".  (Its `_∙₁_` laws are such equalities, but only at index 1r.)
--
-- WHAT THIS FILE PROVES, over an arbitrary commutative ring R:
--
--   Sol≡      : coefA s ≡ coefA t → coefB s ≡ coefB t → s ≡ t     (same index)
--   SolPathP  : the same over an index path q : k ≡ k'
--   ⊛AssocSubst : subst (Sol D) (·Assoc k₁ k₂ k₃) (s ⊛ (t ⊛ u)) ≡ (s ⊛ t) ⊛ u
--   ⊛AssocSubst⁻: s ⊛ (t ⊛ u) ≡ subst⁻ (Sol D) (·Assoc k₁ k₂ k₃) ((s ⊛ t) ⊛ u)
--   ⊛CommSubst  : subst (Sol D) (·Comm k₁ k₂) (s ⊛ t) ≡ t ⊛ s
--   ⊛IdRSubst   : subst (Sol D) (·IdR k) (s ⊛ unit D) ≡ s
--   ⊛IdLSubst   : subst (Sol D) (·IdL k) (unit D ⊛ s) ≡ s
--   ⊛-substL / ⊛-substR : `_⊛_` commutes with retyping either argument
--   ⊛AssocSubst≡fromPathP : the equality above IS `fromPathP (⊛Assoc s t u)`
--
-- The coordinate content is rederived here with `solve!` over the ABSTRACT
-- ring CR (assocA, assocB, commA, commB, idRA, idRB, idLA, idLB below) — a
-- second, mechanical proof of the eight polynomial identities that
-- `Bhavana.Form` proves by hand (bhA-assoc, bhB-assoc, …).  The Sol-level
-- equalities are built ONLY from those solver identities, `Sol≡`, and the
-- coordinate-transparency of `subst` (`substCoefA`/`substCoefB`); they do not
-- route through §7's PathPs.  The final lemma then checks that the two routes
-- agree, which they must since `Sol D k` is a set.
------------------------------------------------------------------------

module CompositionAssoc_TheCompositionCompositionIsAssociativeAsAnEqualityAfterTransportAndTheSolverRederivesEveryCoordinateIdentity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport using (subst⁻ ; subst⁻Subst ; substComposite)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection using (solve!)

open import Composition using (module Form)
open import CompositionGenerative using (module Generative)

private
  variable
    ℓ : Level

module Assoc (CR : CommRing ℓ) where

  open CommRingStr (snd CR)
  open Form CR using (R ; N ; bhA ; bhB)
  open Generative CR

  ----------------------------------------------------------------------
  -- 1.  Equality of solutions is equality of coordinates.
  --
  -- `hasNorm` is a path in R, and R is a set (it is a CommRing), so the
  -- norm obligation is a proposition and contributes nothing to the identity
  -- type of `Sol D k` beyond the two coordinates.  `Sol≡` is the same-index
  -- case; `SolPathP` is the version over a path of norm indices, from which
  -- every §7-style PathP in `BhavanaGenerative` could have been read off.
  ----------------------------------------------------------------------

  SolPathP : {D k k' : R} (q : k ≡ k') {s : Sol D k} {t : Sol D k'}
           → coefA s ≡ coefA t → coefB s ≡ coefB t
           → PathP (λ i → Sol D (q i)) s t
  SolPathP {D} q {s} {t} pa pb i =
    mkSol (pa i) (pb i)
          (isProp→PathP (λ j → is-set (N D (pa j) (pb j)) (q j))
                        (hasNorm s) (hasNorm t) i)

  Sol≡ : {D k : R} {s t : Sol D k}
       → coefA s ≡ coefA t → coefB s ≡ coefB t → s ≡ t
  Sol≡ = SolPathP refl

  ----------------------------------------------------------------------
  -- 2.  The eight coordinate identities, by the ring solver over abstract R.
  --
  -- Every argument is a bound ring variable; `bhA`/`bhB` unfold to
  -- polynomials in them, and `solve! CR` normalises both sides.  These are
  -- the identities `Bhavana.Form` proves by hand as bhA-assoc, bhB-assoc,
  -- bhA-idR, bhB-idR, bhA-idL, bhB-idL, plus the two commutativities that
  -- `BhavanaGenerative` proves from ·Comm/+Comm.  Restated here so that the
  -- Sol-level laws below depend on the solver alone for their arithmetic.
  ----------------------------------------------------------------------

  assocA : (D a b c d e f : R)
         → bhA D (bhA D a b c d) (bhB D a b c d) e f
         ≡ bhA D a b (bhA D c d e f) (bhB D c d e f)
  assocA _ _ _ _ _ _ _ = solve! CR

  assocB : (D a b c d e f : R)
         → bhB D (bhA D a b c d) (bhB D a b c d) e f
         ≡ bhB D a b (bhA D c d e f) (bhB D c d e f)
  assocB _ _ _ _ _ _ _ = solve! CR

  commA : (D a b c d : R) → bhA D a b c d ≡ bhA D c d a b
  commA _ _ _ _ _ = solve! CR

  commB : (D a b c d : R) → bhB D a b c d ≡ bhB D c d a b
  commB _ _ _ _ _ = solve! CR

  idRA : (D a b : R) → bhA D a b 1r 0r ≡ a
  idRA _ _ _ = solve! CR

  idRB : (D a b : R) → bhB D a b 1r 0r ≡ b
  idRB _ _ _ = solve! CR

  idLA : (D a b : R) → bhA D 1r 0r a b ≡ a
  idLA _ _ _ = solve! CR

  idLB : (D a b : R) → bhB D 1r 0r a b ≡ b
  idLB _ _ _ = solve! CR

  ----------------------------------------------------------------------
  -- 3.  `_⊛_` commutes with retyping.  `subst (Sol D) p` leaves both
  -- coordinates fixed (substCoefA/substCoefB, from `BhavanaGenerative`), and
  -- `_⊛_` reads only coordinates, so retyping an argument before composing
  -- is the same as composing and then retyping the product along the
  -- induced path on the index.  This is the coherence that makes the graded
  -- family's index arithmetic harmless.
  ----------------------------------------------------------------------

  ⊛-substL : {D k k' l : R} (p : k ≡ k') (s : Sol D k) (t : Sol D l)
           → subst (Sol D) p s ⊛ t ≡ subst (Sol D) (cong (_· l) p) (s ⊛ t)
  ⊛-substL {D} {k} {k'} {l} p s t =
    Sol≡ (cong₂ (λ x y → bhA D x y (coefA t) (coefB t))
                (substCoefA p s) (substCoefB p s)
          ∙ sym (substCoefA (cong (_· l) p) (s ⊛ t)))
         (cong₂ (λ x y → bhB D x y (coefA t) (coefB t))
                (substCoefA p s) (substCoefB p s)
          ∙ sym (substCoefB (cong (_· l) p) (s ⊛ t)))

  ⊛-substR : {D k l l' : R} (p : l ≡ l') (s : Sol D k) (t : Sol D l)
           → s ⊛ subst (Sol D) p t ≡ subst (Sol D) (cong (k ·_) p) (s ⊛ t)
  ⊛-substR {D} {k} {l} {l'} p s t =
    Sol≡ (cong₂ (λ x y → bhA D (coefA s) (coefB s) x y)
                (substCoefA p t) (substCoefB p t)
          ∙ sym (substCoefA (cong (k ·_) p) (s ⊛ t)))
         (cong₂ (λ x y → bhB D (coefA s) (coefB s) x y)
                (substCoefA p t) (substCoefB p t)
          ∙ sym (substCoefB (cong (k ·_) p) (s ⊛ t)))

  ----------------------------------------------------------------------
  -- 4.  THE MONOID LAWS AS EQUALITIES AFTER TRANSPORT.
  --
  -- Associativity first, in the form the §7 note of `BhavanaGenerative`
  -- names as the obstacle: one side transported along `·Assoc k₁ k₂ k₃` so
  -- that both sit in `Sol D ((k₁ · k₂) · k₃)`, and then a plain `≡`.  The
  -- coordinates of the transported side are those of `s ⊛ (t ⊛ u)`
  -- (substCoefA/B), which `assocA`/`assocB` identify with those of
  -- `(s ⊛ t) ⊛ u`; `Sol≡` closes the record.
  ----------------------------------------------------------------------

  ⊛AssocSubst : {D k₁ k₂ k₃ : R} (s : Sol D k₁) (t : Sol D k₂) (u : Sol D k₃)
              → subst (Sol D) (·Assoc k₁ k₂ k₃) (s ⊛ (t ⊛ u)) ≡ (s ⊛ t) ⊛ u
  ⊛AssocSubst {D} {k₁} {k₂} {k₃} s t u =
    Sol≡ (substCoefA (·Assoc k₁ k₂ k₃) (s ⊛ (t ⊛ u))
          ∙ sym (assocA D (coefA s) (coefB s) (coefA t) (coefB t) (coefA u) (coefB u)))
         (substCoefB (·Assoc k₁ k₂ k₃) (s ⊛ (t ⊛ u))
          ∙ sym (assocB D (coefA s) (coefB s) (coefA t) (coefB t) (coefA u) (coefB u)))

  -- The same law read from the other side: the left association transported
  -- BACK along `·Assoc` is the right association.  Not a restatement by
  -- symmetry — it is `⊛AssocSubst` composed with the subst/subst⁻ round trip.
  ⊛AssocSubst⁻ : {D k₁ k₂ k₃ : R} (s : Sol D k₁) (t : Sol D k₂) (u : Sol D k₃)
               → s ⊛ (t ⊛ u) ≡ subst⁻ (Sol D) (·Assoc k₁ k₂ k₃) ((s ⊛ t) ⊛ u)
  ⊛AssocSubst⁻ {D} {k₁} {k₂} {k₃} s t u =
      sym (subst⁻Subst (Sol D) (·Assoc k₁ k₂ k₃) (s ⊛ (t ⊛ u)))
    ∙ cong (subst⁻ (Sol D) (·Assoc k₁ k₂ k₃)) (⊛AssocSubst s t u)

  ⊛CommSubst : {D k₁ k₂ : R} (s : Sol D k₁) (t : Sol D k₂)
             → subst (Sol D) (·Comm k₁ k₂) (s ⊛ t) ≡ t ⊛ s
  ⊛CommSubst {D} {k₁} {k₂} s t =
    Sol≡ (substCoefA (·Comm k₁ k₂) (s ⊛ t)
          ∙ commA D (coefA s) (coefB s) (coefA t) (coefB t))
         (substCoefB (·Comm k₁ k₂) (s ⊛ t)
          ∙ commB D (coefA s) (coefB s) (coefA t) (coefB t))

  ⊛IdRSubst : {D k : R} (s : Sol D k)
            → subst (Sol D) (·IdR k) (s ⊛ unit D) ≡ s
  ⊛IdRSubst {D} {k} s =
    Sol≡ (substCoefA (·IdR k) (s ⊛ unit D) ∙ idRA D (coefA s) (coefB s))
         (substCoefB (·IdR k) (s ⊛ unit D) ∙ idRB D (coefA s) (coefB s))

  ⊛IdLSubst : {D k : R} (s : Sol D k)
            → subst (Sol D) (·IdL k) (unit D ⊛ s) ≡ s
  ⊛IdLSubst {D} {k} s =
    Sol≡ (substCoefA (·IdL k) (unit D ⊛ s) ∙ idLA D (coefA s) (coefB s))
         (substCoefB (·IdL k) (unit D ⊛ s) ∙ idLB D (coefA s) (coefB s))

  ----------------------------------------------------------------------
  -- 5.  The two routes agree.  `BhavanaGenerative` §7's `⊛Assoc` is a PathP
  -- over `·Assoc`; `fromPathP` turns it into exactly the type of
  -- `⊛AssocSubst`.  The two equalities were built from different arithmetic
  -- (hand proofs there, solver here), and they coincide because `Sol D k` is
  -- a set (`isSetSol`, from `BhavanaGenerative`).  So the solver route is not
  -- a second theorem; it is the same path, reached mechanically.
  ----------------------------------------------------------------------

  ⊛AssocSubst≡fromPathP : {D k₁ k₂ k₃ : R} (s : Sol D k₁) (t : Sol D k₂) (u : Sol D k₃)
                        → ⊛AssocSubst s t u ≡ fromPathP (⊛Assoc s t u)
  ⊛AssocSubst≡fromPathP s t u = isSetSol _ _ (⊛AssocSubst s t u) (fromPathP (⊛Assoc s t u))

  -- And at index 1r, the general law specialises to the group law that
  -- `BhavanaGenerative` proves for `_∙₁_` by hand: both sides of `∙₁-assoc`
  -- are retypings of `_⊛_`, and `⊛-substL`/`⊛-substR` move the retypings
  -- outward until `⊛AssocSubst` applies.  This is the check that the general
  -- statement really is the one the norm-1 group uses, not a lookalike.
  ∙₁-assoc' : {D : R} (s t u : Sol D 1r) → (s ∙₁ t) ∙₁ u ≡ s ∙₁ (t ∙₁ u)
  ∙₁-assoc' {D} s t u =
      cong (subst (Sol D) (·IdR 1r)) (⊛-substL (·IdR 1r) (s ⊛ t) u)
    ∙ cong (subst (Sol D) (·IdR 1r))
           (cong (λ q → subst (Sol D) q ((s ⊛ t) ⊛ u))
                 (is-set _ _ (cong (_· 1r) (·IdR 1r)) (sym (·Assoc 1r 1r 1r) ∙ cong (1r ·_) (·IdR 1r)))
            ∙ substComposite (Sol D) (sym (·Assoc 1r 1r 1r)) (cong (1r ·_) (·IdR 1r)) ((s ⊛ t) ⊛ u))
    ∙ cong (λ x → subst (Sol D) (·IdR 1r) (subst (Sol D) (cong (1r ·_) (·IdR 1r)) x))
           (sym (⊛AssocSubst⁻ s t u))
    ∙ cong (subst (Sol D) (·IdR 1r)) (sym (⊛-substR (·IdR 1r) s (t ⊛ u)))
