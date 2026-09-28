{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- MachineCurriculum — the lemmas the engine asked for, answered.
--
-- These are not chosen by a person.  `machine/Obstruction.hs` (absent from this repository) reads the
-- kernel's REFUSALS out of machine/machine.log, recovers the residual (the
-- pair of terms at which Agda's computation stalled), triages out the
-- refutable and the degenerate, and ranks what survives by how many
-- DISTINCT parent goals each one would unblock:
--
--     distinct stalled goals   130
--     distinct lemmas demanded  78
--     top 8 unblock             54 of the 130
--
-- The top of that ranking, verbatim, with the engine's own counts:
--
--     unblocks 14   0 = y·0
--     unblocks  8   x·0 = 0
--     unblocks  5   x = x+0
--     unblocks  3   0 = 0∸y
--     unblocks  2   x = x + 0·x
--
-- WHY THE ENGINE IS ASKING FOR THESE, which is the part worth understanding.
-- It already HAS `x·0 = 0` — it is a defining equation of `*` in its own
-- vocabulary.  It is demanding a lemma it knows.  The reason is that Agda's
-- `_·_` on ℕ recurses on its SECOND argument (`m · zero = zero` holds only
-- after induction on m, while `zero · n` is immediate), so `x · 0` is not
-- definitionally `0` here, whereas the engine's rewriter discharges it at
-- once.  Every one of these lemmas is a place where the engine's notion of
-- equality is computational and Agda's is not.
--
-- So this module is not a list of things the machine did not know.  It is
-- the BRIDGE between the machine's rewriting and the kernel's definitional
-- equality, and closing it is what raises the acceptance rate — a live round
-- submitted 179 proofs and got 6 back.  (That sentence is kept in the past
-- tense it belongs in: it reports one round of one run, and per the AS-OF
-- block above it is no longer recoverable from `machine/machine.log`, whose
-- round numbers are now shared by 61 runs.  It is an anecdote about why the
-- bridge was built, not a fact the reader can check.)
--
-- Everything below is proved by induction, constructively, no postulates.
------------------------------------------------------------------------

module MachineCurriculum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_)

------------------------------------------------------------------------
-- the four that carry the ranking

-- unblocks 5.  Right unit of +.  `zero + x` is immediate; `x + zero` is not.
+zero : (x : ℕ) → x + zero ≡ x
+zero zero = refl
+zero (suc x) = cong suc (+zero x)

-- unblocks 8 (and 14, and 6, as `0 = y·0` and `0 = z·0` — the engine states
-- the same law once per variable name it happened to use).  Right
-- annihilator.  This is the single most demanded lemma in the whole stream.
·zero : (x : ℕ) → x · zero ≡ zero
·zero zero = refl
·zero (suc x) = ·zero x

-- unblocks 2.  The residual of `x ≡ 1 · x`: Agda unfolds `1 · x` to
-- `x + 0 · x` and stalls there.  This is the exact statement the kernel
-- handed back, and proving it closes the parent.
+·zero : (x : ℕ) → x + zero · x ≡ x
+·zero x = +zero x

------------------------------------------------------------------------
-- the same laws in the ORIENTATION the engine actually emitted
--
-- The stream contains both `x = x+0` and `x+0 = x`, and both `0 = y·0` and
-- `x·0 = 0`.  They are the same mathematics, and a queue that does not
-- canonicalise orientation pays for each twice — recorded here because the
-- duplication is a property of the engine worth fixing, not of ℕ.

zero+· : (y : ℕ) → zero ≡ y · zero
zero+· y = sym (·zero y)

zero+ : (x : ℕ) → x ≡ x + zero
zero+ x = sym (+zero x)

------------------------------------------------------------------------
-- consequence: the parent that was stalling
--
-- `x ≡ 1 · x` was refused by the kernel with residual `x != x + 0 · x`.
-- With the bridge in hand it closes immediately.  This is the whole
-- mechanism, demonstrated end to end on the case that motivated it.

oneMul : (x : ℕ) → x ≡ suc zero · x
oneMul x = sym (+·zero x)
