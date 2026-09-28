{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- PerspectiveCore
--
-- THE GENERAL TOOLKIT OF THE ANEKĀNTA–UNIVALENCE DELTAS, as terms.
--
-- Delta 14 is a theorem factory: it lists results across sections A–O,
-- most of them standard, and asks for the exact ones to be made
-- executable in the machine core.  `CenterRelative` does
-- §A's specific object (T14.1–T14.2, C14.3, Program 14.71).  THIS file
-- does the parts of §§A, C, D, H that are about no particular object —
-- the reusable lemmas every later perspective comparison will consume.
--
-- WHAT IS CHECKED, BY DELTA-14 NUMBER
--
--   §A  `restricts-suff`     T14.6, sufficient direction: if the two
--                            sector predicates correspond fibrewise
--                            along `e`, the equivalence restricts.
--       `restricts-nec`      T14.6, necessary direction, in the form
--                            that is actually true (see below).
--       `sector-not-inv`     C14.7: an inhabitant of `A₊ a` with `B₊ (e a)`
--                            uninhabited is exactly an obstruction to
--                            restriction — so ambient equivalence can
--                            fail after sector selection, and the reason
--                            is always non-invariance of the predicate.
--
--   §C  `conj-iterate`       T14.14: `(fᵉ)ⁿ = e ∘ fⁿ ∘ e⁻¹`, by induction.
--       `conj-fixed`         C14.15 for fixed points: `e` carries
--                            `Fix f` to `Fix fᵉ` as an equivalence.
--                            Periods follow from `conj-iterate` and are
--                            stated for period n as `conj-per`.
--
--   §D  `section→inhabited`  T14.21: a section makes every fibre
--                            inhabited …
--       `inhabited↛contr`    … and NOT contractible, with the witness
--                            `Bool` — an inhabited non-contractible
--                            fibre exists, so the implication genuinely
--                            fails rather than merely being unproved.
--       `constMonodromy`     P14.24: for the constant two-point family
--                            over ANY base, transport along ANY path is
--                            the identity.  So a two-point fibre alone
--                            carries no monodromy.
--       `twoPointNoObstr`    C14.25, stated as the contrapositive that
--                            is usable: exhibiting a two-element fibre
--                            does not exhibit an obstruction, because
--                            `B × Bool → B` has two-element fibres and
--                            trivial transport throughout.
--
--   §H  `restrict-fibre`     T14.44: a total-space map restricts to the
--                            fibre over `c₀` exactly when its base
--                            component fixes `c₀`.
--       `transport-back`     T14.45: and if the base component moves
--                            `c₀` to `c₁`, a path `c₁ ≡ c₀` returns the
--                            output to `G c₀` by transport.
--
-- WHY T14.6's "IFF" IS SPLIT AND NOT PROVED AS STATED
--
-- Delta 14 states T14.6 as an iff: *"e restricts to A₊ ≃ B₊ iff
-- A₊(a) ↔ B₊(e a) for all a"*.  Read literally in a proof-relevant
-- setting that is FALSE in the ← direction, and the file says so rather
-- than quietly weakening it.  A restriction `Σ A A₊ ≃ Σ B B₊` need not
-- arise from fibrewise maps at all: it may permute the base.  What IS
-- true, and is `restricts-nec` below, is the direction that gets used:
-- if the restriction is *over* `e` (i.e. its first component is `e`),
-- then the predicates correspond.  The unrestricted converse needs
-- either "over `e`" or a fibrewise hypothesis, and adding it silently
-- would be exactly Delta 14 §N's **P14.67 false-quotient danger** in
-- miniature.
------------------------------------------------------------------------

module PerspectiveCore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty as Empty using (⊥)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ

------------------------------------------------------------------------
-- A.  BOUNDARY RESTRICTION  (T14.6, C14.7)
--
-- Delta 14's "boundary-breaking schema": given an equivalence and a
-- selected sector on each side, does the equivalence restrict?
------------------------------------------------------------------------

-- T14.6, sufficient direction.  Fibrewise correspondence of the sector
-- predicates gives the restricted equivalence.
restricts-suff :
  (e : A ≃ B) (A₊ : A → Type ℓ'') (B₊ : B → Type ℓ'')
  → ((a : A) → A₊ a ≃ B₊ (equivFun e a))
  → (Σ A A₊) ≃ (Σ B B₊)
restricts-suff e A₊ B₊ h = Σ-cong-equiv e h

-- T14.6, necessary direction, in the form that is true: a restriction
-- lying OVER `e` forces the predicates to correspond.
restricts-nec :
  (e : A ≃ B) (A₊ : A → Type ℓ'') (B₊ : B → Type ℓ'')
  → (f : Σ A A₊ → Σ B B₊)
  → ((x : Σ A A₊) → f x .fst ≡ equivFun e (x .fst))
  → (a : A) → A₊ a → B₊ (equivFun e a)
restricts-nec e A₊ B₊ f over a p = subst B₊ (over (a , p)) (f (a , p) .snd)

-- C14.7.  The obstruction to restriction, named as an object: a point of
-- the sector whose image leaves the sector.  This is what "the sector
-- predicate is not invariant" MEANS, and it is what a search for a
-- boundary break must exhibit.
SectorBreak : (e : A ≃ B) (A₊ : A → Type ℓ'') (B₊ : B → Type ℓ'') → Type _
SectorBreak {A = A} e A₊ B₊ =
  Σ[ a ∈ A ] (A₊ a × (B₊ (equivFun e a) → ⊥))

-- … and a break really does obstruct: no fibrewise correspondence can
-- exist once one is exhibited.
sector-not-inv :
  (e : A ≃ B) (A₊ : A → Type ℓ'') (B₊ : B → Type ℓ'')
  → SectorBreak e A₊ B₊
  → ((a : A) → A₊ a ≃ B₊ (equivFun e a)) → ⊥
sector-not-inv e A₊ B₊ (a , inSector , notInImage) h =
  notInImage (equivFun (h a) inSector)

------------------------------------------------------------------------
-- C.  CONJUGATION  (T14.14, C14.15)
--
-- Delta 14 §C: `fᵉ = e ∘ f ∘ e⁻¹`, and everything conjugacy-invariant
-- transports.  `CenterRelative.transport-τ-is-ρ` is the instance; this
-- is the general statement.
------------------------------------------------------------------------

conj : (e : A ≃ B) → (A → A) → (B → B)
conj e f = equivFun e ∘ f ∘ invEq e

iter : {X : Type ℓ} → (X → X) → ℕ → X → X
iter f zero    x = x
iter f (suc n) x = f (iter f n x)

-- T14.14.  Conjugation commutes with iteration.
conj-iterate :
  (e : A ≃ B) (f : A → A) (n : ℕ) (b : B)
  → iter (conj e f) n b ≡ equivFun e (iter f n (invEq e b))
conj-iterate e f zero    b = sym (secEq e b)
conj-iterate e f (suc n) b =
    cong (conj e f) (conj-iterate e f n b)
  ∙ cong (equivFun e ∘ f) (retEq e (iter f n (invEq e b)))

-- C14.15, fixed points.  A fixed point of `f` is a fixed point of `fᵉ`.
conj-fixed :
  (e : A ≃ B) (f : A → A) (a : A) → f a ≡ a
  → conj e f (equivFun e a) ≡ equivFun e a
conj-fixed e f a p =
  cong (equivFun e ∘ f) (retEq e a) ∙ cong (equivFun e) p

-- C14.15, periods.  `a` has period `n` under `f` iff `e a` does under `fᵉ`.
conj-per :
  (e : A ≃ B) (f : A → A) (n : ℕ) (a : A) → iter f n a ≡ a
  → iter (conj e f) n (equivFun e a) ≡ equivFun e a
conj-per e f n a p =
    conj-iterate e f n (equivFun e a)
  ∙ cong (equivFun e) (cong (iter f n) (retEq e a) ∙ p)

------------------------------------------------------------------------
-- D.  FIBRES, SECTIONS, AND THE MONODROMY QUESTION
--     (T14.21, P14.24, C14.25)
--
-- `SieveFiber` found that the sieve quotient DOES admit a
-- section while reconstruction fails, and that the residual is one bit.
-- T14.21 is the general form of the first half; C14.25 is the warning
-- attached to the second.
------------------------------------------------------------------------

-- T14.21.  A section makes every fibre inhabited.
section→inhabited :
  (q : A → B) (s : B → A) → ((b : B) → q (s b) ≡ b)
  → (b : B) → fiber q b
section→inhabited q s sect b = s b , sect b

-- … but NOT contractible, and here is the witness rather than the
-- assertion: the first projection `B × Bool → B` has a section, and its
-- fibre over any `b` contains two distinct points.
module TwoPointFibre {B : Type ℓ} (b : B) where

  pr : B × Bool → B
  pr = fst

  sec : B → B × Bool
  sec x = (x , true)

  sec-is-section : (x : B) → pr (sec x) ≡ x
  sec-is-section x = refl

  ptTrue ptFalse : fiber pr b
  ptTrue  = (b , true)  , refl
  ptFalse = (b , false) , refl

  -- The two fibre points are distinct, so the fibre is not a proposition
  -- and a fortiori not contractible.
  fibre-not-prop : isProp (fiber pr b) → ⊥
  fibre-not-prop hp =
    true≢false (cong (λ z → z .fst .snd) (hp ptTrue ptFalse))

-- P14.24.  For a CONSTANT family over any base, transport along any path
-- is the identity.  So "the fibre has two points" supplies no monodromy
-- whatsoever — the sheets are never exchanged.
constMonodromy :
  {B : Type ℓ} {C : Type ℓ'} {b b' : B} (p : b ≡ b') (x : C)
  → subst (λ _ → C) p x ≡ x
constMonodromy p x = transportRefl x

-- C14.25, in the form that is usable.
--
-- **A residual bit is not an obstruction.**  If someone exhibits a
-- two-element fibre and calls it a binary obstruction, the above is the
-- counterexample: `B × Bool → B` has two-element fibres over every point,
-- admits a section, and has trivial transport along every loop.  What an
-- obstruction requires is that some loop ACT nontrivially on the fibre —
-- sheet exchange — and that is a strictly further fact which must be
-- exhibited separately.
--
-- Recorded as a type so that a claim of an obstruction has
-- something to inhabit.  `MonodromyOf F b p` says the loop `p` at `b`
-- acts non-identically on the family `F`.
MonodromyOf : {B : Type ℓ} (F : B → Type ℓ') (b : B) (p : b ≡ b) → Type _
MonodromyOf F b p = Σ[ x ∈ F b ] (subst F p x ≡ x → ⊥)

-- P14.24 / C14.25.  A CONSTANT two-sheet family over any base admits no
-- monodromy at all: every loop acts as the identity.  Together with the
-- module above — two distinct points in the fibre, and a section — this
-- is the counterexample in full: two-element fibres, a section, and
-- trivial transport along every loop.  So neither "the fibre has two
-- elements" nor "a section exists" is evidence of an obstruction.
--
-- **THE GENERAL STATEMENT.**  `SetBaseNoMonodromy.setNoMonodromy` proves
-- it for EVERY family over a base that is a set — no trivialisation
-- needed, because over a 0-type `p ≡ refl` and there is no loop to act.
-- So the constant-family restriction below is not the general statement;
-- it is the special case that happens to need no hypothesis on the base.
-- Cite that module, not this one, when the base is known to be a set.
constNoMonodromy :
  {B : Type ℓ} (C : Type ℓ') (b : B) (p : b ≡ b)
  → MonodromyOf {B = B} (λ _ → C) b p → ⊥
constNoMonodromy C b p (x , nontrivial) = nontrivial (transportRefl x)

-- The two-sheet instance, named so it can be cited directly.
twoSheetNoObstr :
  {B : Type ℓ} (b : B) (p : b ≡ b)
  → MonodromyOf {B = B} (λ _ → Bool) b p → ⊥
twoSheetNoObstr = constNoMonodromy Bool

------------------------------------------------------------------------
-- H.  GRADED / DEPENDENT CHARGE  (T14.44, T14.45, C14.46)
--
-- Delta 14 §H: charge as a dependent index `G : C → U`, the
-- grand-canonical object as the total space `Σ C G`, a fixed charge as a
-- fibre.  When does a transformation of the total space restrict to a
-- sector?
------------------------------------------------------------------------

module Graded {C : Type ℓ} (G : C → Type ℓ') where

  Total : Type _
  Total = Σ C G

  base : Total → C
  base = fst

  -- T14.44.  A total-space map restricts to the fibre over `c₀` exactly
  -- when its base component fixes `c₀`.
  restrict-fibre :
    (T : Total → Total) (c₀ : C)
    → ((g : G c₀) → base (T (c₀ , g)) ≡ c₀)
    → G c₀ → G c₀
  restrict-fibre T c₀ fixes g = subst G (fixes g) (T (c₀ , g) .snd)

  -- T14.45.  If instead the base component sends `c₀` to some `c₁`, a
  -- supplied path returns the output to `G c₀` by transport.  This is
  -- C14.46: canonical closure is index preservation *up to specified
  -- transport*, and the path is data, not a side condition.
  transport-back :
    (T : Total → Total) (c₀ c₁ : C)
    → ((g : G c₀) → base (T (c₀ , g)) ≡ c₁)
    → c₁ ≡ c₀
    → G c₀ → G c₀
  transport-back T c₀ c₁ lands p g =
    subst G p (subst G (lands g) (T (c₀ , g) .snd))
