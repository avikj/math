{-# OPTIONS --cubical --safe --no-import-sorts #-}

-- MachineLibrary.agda
--
-- WHAT THIS IS.  `machine/MathMachine.hs` (absent from this repository) discovers arithmetic identities,
-- certifies each through an Agda gate (`machine/Certificate.hs` (absent from this repository)), installs it
-- as a rewrite rule, and logs a line to `machine/library.txt` (absent from this repository) /
-- `machine/library.snapshot.txt` (absent from this repository).  The certificate module it writes is a temp
-- file that is deleted after typechecking: the proof term evaporates and only
-- the log line survives.  This module is the retained form.  Every theorem
-- below carries, in the comment above it, the exact `library.snapshot.txt` (absent from this repository)
-- line it corresponds to, verbatim.
--
-- THE MATHEMATICAL POINT: TWO RECURSIONS, ONE FUNCTION.
--
-- The engine's `vocabulary` (MathMachine.hs (absent from this repository):606-617) defines its operations by
-- recursion on the SECOND argument:
--
--     x + 0     = x            x * 0     = 0
--     x + s y   = s (x + y)    x * s y   = (x * y) + x
--
-- Agda's builtin `_+_` and `_·_`, which `Cubical.Data.Nat.Base` re-exports and
-- which the engine's own gate typechecks against, recurse on the FIRST:
--
--     0 + m     = m            0 · m     = 0
--     s n + m   = s (n + m)    s n · m   = m + n · m
--
-- These are the same two functions on ℕ, but *different definitional
-- behaviour*, and the difference is exactly what `machine/library.txt` (absent from this repository)'s
-- annotations record: five of the engine's lines are marked
-- `[induction on x; kernel refl]` — the engine needed an induction, the Agda
-- gate got them by `refl`, because first-argument recursion makes them hold
-- definitionally.
--
-- So a module that discharged those five by `refl` would be proving the
-- LIBRARY's theorems, not the ENGINE's.  Section 1 below proves the engine's
-- four defining equations as lemmas, and everything after Section 1 is derived
-- from those four alone.  No proof past Section 1 appeals to first-argument
-- reduction; the module would still check verbatim if `_+_` and `_·_` were
-- replaced by second-argument definitions and Section 1's four lemmas by
-- `refl`.  That invariance is the content.
--
-- THE FALSIFIER, RUN.  The paragraph above is a checkable claim, so it was
-- checked rather than asserted.  A scratch module was assembled mechanically:
-- second-argument definitions of `_+_` and `_·_` transcribed from
-- MathMachine.hs (absent from this repository):612-617, the four Section 1 lemmas restated with proof
-- `refl`, and then Sections 2 and 4 of this file appended VERBATIM — all 17
-- `L01`…`L17` plus `+-assoc`, `zeroAdd`, `sucAdd`, `addComm`, `zeroMul`,
-- `sucMul`, `mulComm`, unedited.  It typechecks `--cubical --safe`, exit 0.
-- Had any proof below been leaning on first-argument reduction, that run would
-- have failed.  The scratch module is not retained: it is a control, and its
-- content is this file plus a header.
--
-- IMPORT DISCIPLINE.  `Cubical.Data.Nat.Base` only, never `Cubical.Data.Nat`
-- or `Cubical.Data.Nat.Properties`: those export `+-comm` and `·-comm`, and
-- re-exporting the library's commutativity under a new name would be a
-- rename, not a proof of the engine's line.  Base contributes ℕ, `zero`,
-- `suc`, `_+_`, `_·_` and nothing else used here.
--
-- Not imported: `NaturalMachine.*` (concurrently edited by other lanes).  This
-- module is self-contained and depends only on `Cubical.*`.

module MachineLibrary where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_; _·_)

-- ---------------------------------------------------------------------------
-- 1.  The engine's defining equations, as lemmas
--
-- These four are the engine's `symDefs` for `+` and `*` (MathMachine.hs (absent from this repository):612-617).
-- They are definitional for the engine and theorems for Agda; below this point
-- they are the ONLY facts about `_+_` and `_·_` that any proof uses.
-- ---------------------------------------------------------------------------

-- engine:  (bin "+" x_ zero_, x_)          i.e.  x + 0 = x
addZero : (a : ℕ) → a + zero ≡ a
addZero zero    = refl
addZero (suc a) = cong suc (addZero a)

-- engine:  (bin "+" x_ (su y_), su (bin "+" x_ y_))   i.e.  x + s y = s (x + y)
addSuc : (a b : ℕ) → a + suc b ≡ suc (a + b)
addSuc zero    b = refl
addSuc (suc a) b = cong suc (addSuc a b)

-- ---------------------------------------------------------------------------
-- 2.  Additive theory, from `addZero` and `addSuc` only
-- ---------------------------------------------------------------------------

-- Associativity of `+`.  Not itself a snapshot line: it is the bridge lemma
-- that lines 5, 6 and 7 below are each one commutation away from, and the
-- engine's rewriting uses it implicitly through its normal forms.
+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc a b zero =
  addZero (a + b) ∙ sym (cong (a +_) (addZero b))
+-assoc a b (suc c) =
  addSuc (a + b) c
    ∙ cong suc (+-assoc a b c)
    ∙ sym (cong (a +_) (addSuc b c) ∙ addSuc a (b + c))

-- library.snapshot.txt (absent from this repository):1
--   x                    = (0+x)                    [induction on x]
zeroAdd : (a : ℕ) → zero + a ≡ a
zeroAdd zero    = addZero zero
zeroAdd (suc a) = addSuc zero a ∙ cong suc (zeroAdd a)

L01 : (x : ℕ) → x ≡ zero + x
L01 x = sym (zeroAdd x)

-- library.snapshot.txt (absent from this repository):3
--   (s(x)+y)             = s((x+y))                 [induction on y]
sucAdd : (a b : ℕ) → suc a + b ≡ suc (a + b)
sucAdd a zero    = addZero (suc a) ∙ sym (cong suc (addZero a))
sucAdd a (suc b) =
  addSuc (suc a) b ∙ cong suc (sucAdd a b) ∙ sym (cong suc (addSuc a b))

L03 : (x y : ℕ) → suc x + y ≡ suc (x + y)
L03 = sucAdd

-- library.snapshot.txt (absent from this repository):2
--   s(x)                 = (s(0)+x)                 [induction on x]
L02 : (x : ℕ) → suc x ≡ suc zero + x
L02 x = sym (sucAdd zero x ∙ cong suc (zeroAdd x))

-- library.snapshot.txt (absent from this repository):4
--   (x+y)                = (y+x)                    [induction on x]
addComm : (a b : ℕ) → a + b ≡ b + a
addComm a zero    = addZero a ∙ sym (zeroAdd a)
addComm a (suc b) = addSuc a b ∙ cong suc (addComm a b) ∙ sym (sucAdd b a)

L04 : (x y : ℕ) → x + y ≡ y + x
L04 = addComm

-- library.snapshot.txt (absent from this repository):5
--   (x+(x+y))            = (y+(x+x))                [induction on y]
L05 : (x y : ℕ) → x + (x + y) ≡ y + (x + x)
L05 x y = sym (+-assoc x x y) ∙ addComm (x + x) y

-- library.snapshot.txt (absent from this repository):6
--   (x+(y+y))            = (y+(x+y))                [induction on x]
L06 : (x y : ℕ) → x + (y + y) ≡ y + (x + y)
L06 x y = sym (+-assoc x y y) ∙ addComm (x + y) y

-- library.snapshot.txt (absent from this repository):7
--   (x+(y+z))            = (y+(x+z))                [induction on x]
-- The left-exchange law; with associativity and commutativity it is the whole
-- of the engine's additive normalisation.
L07 : (x y z : ℕ) → x + (y + z) ≡ y + (x + z)
L07 x y z =
  sym (+-assoc x y z) ∙ cong (_+ z) (addComm x y) ∙ +-assoc y x z

-- ---------------------------------------------------------------------------
-- 3.  The multiplicative defining equations
-- ---------------------------------------------------------------------------

-- engine:  (bin "*" x_ zero_, zero_)       i.e.  x * 0 = 0
mulZero : (a : ℕ) → a · zero ≡ zero
mulZero zero    = refl
mulZero (suc a) = mulZero a

-- engine:  (bin "*" x_ (su y_), bin "+" (bin "*" x_ y_) x_)
--          i.e.  x * s y = (x * y) + x
-- Unlike the other three this one needs `+-assoc` in its step; that is a
-- consequence of the two recursions disagreeing, not an extra assumption.
mulSuc : (a b : ℕ) → a · suc b ≡ (a · b) + a
mulSuc zero    b = refl
mulSuc (suc a) b =
  cong (λ t → suc (b + t)) (mulSuc a b)
    ∙ cong suc (sym (+-assoc b (a · b) a))
    ∙ sym (addSuc (b + (a · b)) a)

-- ---------------------------------------------------------------------------
-- 4.  Multiplicative theory, from the four defining equations only
-- ---------------------------------------------------------------------------

-- library.snapshot.txt (absent from this repository):8
--   0                    = (0*x)                    [induction on x]
zeroMul : (a : ℕ) → zero · a ≡ zero
zeroMul zero    = mulZero zero
zeroMul (suc a) = mulSuc zero a ∙ cong (_+ zero) (zeroMul a) ∙ addZero zero

L08 : (x : ℕ) → zero ≡ zero · x
L08 x = sym (zeroMul x)

-- library.snapshot.txt (absent from this repository):10
--   (s(x)*y)             = (y+(x*y))                [induction on y]
sucMul : (a b : ℕ) → suc a · b ≡ b + (a · b)
sucMul a zero =
  mulZero (suc a) ∙ sym (zeroAdd (a · zero) ∙ mulZero a)
sucMul a (suc b) =
  mulSuc (suc a) b
    ∙ cong (_+ suc a) (sucMul a b)
    ∙ addSuc (b + (a · b)) a
    ∙ cong suc (+-assoc b (a · b) a)
    ∙ cong (λ t → suc (b + t)) (sym (mulSuc a b))
    ∙ sym (sucAdd b (a · suc b))

L10 : (x y : ℕ) → suc x · y ≡ y + (x · y)
L10 = sucMul

-- library.snapshot.txt (absent from this repository):9
--   x                    = (s(0)*x)                 [induction on x]
L09 : (x : ℕ) → x ≡ suc zero · x
L09 x = sym (sucMul zero x ∙ cong (x +_) (zeroMul x) ∙ addZero x)

-- library.snapshot.txt (absent from this repository):17  — the engine's headline line
--   (x*y)                = (y*x)                    [induction on x]
mulComm : (a b : ℕ) → a · b ≡ b · a
mulComm a zero    = mulZero a ∙ sym (zeroMul a)
mulComm a (suc b) =
  mulSuc a b
    ∙ cong (_+ a) (mulComm a b)
    ∙ addComm (b · a) a
    ∙ sym (sucMul b a)

L17 : (x y : ℕ) → x · y ≡ y · x
L17 = mulComm

-- library.snapshot.txt (absent from this repository):11
--   (s(x)*y)             = (y+(y*x))                [induction on x]
L11 : (x y : ℕ) → suc x · y ≡ y + (y · x)
L11 x y = sucMul x y ∙ cong (y +_) (mulComm x y)

-- library.snapshot.txt (absent from this repository):12
--   (x*(x*y))            = (x*(y*x))                [induction on x]
L12 : (x y : ℕ) → x · (x · y) ≡ x · (y · x)
L12 x y = cong (x ·_) (mulComm x y)

-- library.snapshot.txt (absent from this repository):13
--   (x*(y*z))            = (x*(z*y))                [induction on y]
L13 : (x y z : ℕ) → x · (y · z) ≡ x · (z · y)
L13 x y z = cong (x ·_) (mulComm y z)

-- library.snapshot.txt (absent from this repository):14
--   s((x*c0(x)))         = s((c0(x)*x))             [induction on x]
-- `c0` is the engine's Skolem constant-former: a symbol standing for a
-- previously installed unary term.  It is *not* a fixed function, so the
-- faithful reading quantifies over every unary ℕ → ℕ.  That generalisation is
-- free here and strictly stronger than any single instance.
L14 : (c0 : ℕ → ℕ) (x : ℕ) → suc (x · c0 x) ≡ suc (c0 x · x)
L14 c0 x = cong suc (mulComm x (c0 x))

-- library.snapshot.txt (absent from this repository):15
--   s((x*c0(y)))         = s((c0(y)*x))             [induction on x]
L15 : (c0 : ℕ → ℕ) (x y : ℕ) → suc (x · c0 y) ≡ suc (c0 y · x)
L15 c0 x y = cong suc (mulComm x (c0 y))

-- library.snapshot.txt (absent from this repository):16
--   s(s((x*y)))          = s(s((y*x)))              [induction on x]
-- Recorded by the engine as a separate discovery from line 17 because its
-- search is over term shapes, not over statements modulo congruence.  Here it
-- is one `cong` from L17; keeping it is honest bookkeeping of what the engine
-- actually emitted, not a claim that it is independent content.
L16 : (x y : ℕ) → suc (suc (x · y)) ≡ suc (suc (y · x))
L16 x y = cong (λ t → suc (suc t)) (mulComm x y)

-- ---------------------------------------------------------------------------
-- 5.  Prior art, and coverage
--
-- PRIOR ART.  `NaturalMachine/HaskellDiscoveryBoundary.agda` already retains
-- engine output in checked form, and does something this module does not: it
-- carries a `HaskellTerm` AST, an `evaluate`, a `Sound` predicate and a
-- `refl` bridge, so the *generated* module can prove its own AST equals
-- `expectedDiscoveries` and transport soundness onto it.  That is the better
-- architecture and this module does not replace it.  Two differences:
--
--   (a) Coverage.  It carries four equations from a five-round smoke run —
--       snapshot lines 1, 3, 8 and 2.  It does not reach `(x*y) = (y*x)`,
--       which is the engine's headline line and the one the whole `*` lane
--       exists for.  Lines 4-7 and 9-17 are new here.
--   (b) Provenance of the proofs.  Its `sound-3` is
--       `0≡m·0 (ρ 0) ∙ sym (·-comm zero (ρ 0))`, importing `·-comm` and
--       `0≡m·0` from `Cubical.Data.Nat`; its other three are `refl`, which is
--       first-argument reduction.  So all four are discharged by the LIBRARY's
--       arithmetic.  This module discharges its seventeen from the ENGINE's
--       four defining equations instead, which is why the falsifier above is
--       runnable at all.  Neither route is wrong; they are different claims,
--       and (b) is the one the engine's own annotations distinguish.
--
-- Snapshot lines 1-17 — every line over the signature {0, s, +, *} — are
-- discharged above as L01…L17.  Lines 18-28 of the snapshot are over `max`,
-- `-` (truncated subtraction) and `le`; they are out of scope for this module
-- and are not claimed.
-- ---------------------------------------------------------------------------
