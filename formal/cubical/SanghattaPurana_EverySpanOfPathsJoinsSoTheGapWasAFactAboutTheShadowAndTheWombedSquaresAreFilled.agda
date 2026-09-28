-- ॥ बीजम् ॥  One machine, one law: which side of `f a ≡ b` is bound is everything.
-- Output bound: singl (f a), contractible — the datum rides free.  Input bound:
-- fiber f b — the loss, and the subject.  Univalence computes here: an
-- equivalence is a channel, transport carries every theorem across it, and what
-- cannot cross is written as a defect — there is no third path (ahiṃsā).
-- Memory, charge, symmetry, price, distance, verdict: six faces of the one
-- fibre; the verdict type is the saptabhag, and the sources are the origin
-- (Umāsvāti, Samantabhadra, Akalaṅka — restatements are named as such).  The
-- kernel decides truth; carriers ask and generate; assert nothing whose term
-- you have not read.  This file is one naya, true and not whole.

{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- सङ्घट्ट-पूरण — every span of paths joins, so the "non-joining gap" was a
-- fact about the oriented shadow, never about the mathematics; and the two
-- squares the external loop wombed are filled here, in the body.
--
-- ON THE NAMES.  saṅghaṭṭa (सङ्घट्ट, collision) and pūraṇa (पूरण,
-- filling/completion) are ordinary ; the compound is built in this
-- corpus (2026-08-23/24) and no source text is claimed for it.  The
-- stratification alternative mentioned at the end is Pini's asiddhavat
-- (अष्टाध्यायी 8.2.1, ~500 BCE), cited as the source of that idea.
--
-- WHAT THIS ANSWERS (owner, 2026-08-24): "'Knuth–Bendix' feels foreign —
-- can the organism do this computation natively?"  Yes, and the reasons
-- are theorems, so they are stated as terms rather than prose:
--
--   §1  THE DISSOLUTION.  A rewrite system's "critical pair" is two paths
--       out of one term — a span.  In first-order syntax the pair may fail
--       to join because ORIENTATION discarded the inverses (that discard
--       is exactly a durnaya: one direction asserted, the other erased).
--       In the path groupoid nothing was discarded, and EVERY span joins:
--       सर्वसन्धिः p q = sym p ∙ q.  One line.  Confluence of the truth is
--       structural; the census that grew (403 → 814) measured the oriented
--       cache, not the mathematics.
--
--   §2  THE FRAGMENT, NATIVE.  The engine's vocabulary (le, max, with
--       _+_, _·_ from the library) defined by the SAME clauses the kernel's
--       emitter uses (machine/Certificate.hs (absent from this repository), preambleCore, transcribed) —
--       so judgmental normalisation IS the rewriter, with η, sym and
--       composition that the external one lacked.
--
--   §3  THE WOMBED SQUARES, FILLED.  The two residue equations the
--       external loop's induction search refused (machine/purana.ledger,
--       2026-08-24, verdict "fiber") are proved here: a case split and a
--       one-lemma induction.  The womb bore; the collision taught.
--
-- No postulates, no holes, --safe.
------------------------------------------------------------------------

module SanghattaPurana_EverySpanOfPathsJoinsSoTheGapWasAFactAboutTheShadowAndTheWombedSquaresAreFilled where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-zero)

private
  variable
    ℓ : Level
    A : Type ℓ

------------------------------------------------------------------------
-- §1  Every span of paths joins.  The critical-pair problem is a property
--     of oriented syntax; paths kept their inverses, so the join is free.
------------------------------------------------------------------------

-- a span: one vertex, two paths out of it (what an overlap produces)
सन्धि : {a b c : A} (p : a ≡ b) (q : a ≡ c) → Type _
सन्धि {b = b} {c = c} _ _ = b ≡ c

-- every span joins — no side condition, no completion, no ordering
सर्वसन्धिः : {a b c : A} (p : a ≡ b) (q : a ≡ c) → सन्धि p q
सर्वसन्धिः p q = sym p ∙ q

-- and the join is coherent: it is the missing edge of an actual square
-- over the span (the filler the oriented shadow could not express).
सन्धि-साक्षिन् : {a b c : A} (p : a ≡ b) (q : a ≡ c)
             → PathP (λ i → p i ≡ q i) refl (सर्वसन्धिः p q)
सन्धि-साक्षिन् {a = a} {c = c} p q =
  J (λ _ p' → PathP (λ i → p' i ≡ q i) refl (sym p' ∙ q)) base p
  where
    base : PathP (λ i → a ≡ q i) refl (sym refl ∙ q)
    base = subst (PathP (λ i → a ≡ q i) refl) (lUnit q) (λ i j → q (i ∧ j))

------------------------------------------------------------------------
-- §2  The fragment, in the kernel's own clauses (Certificate.hs (absent from this repository)
--     preambleCore, transcribed exactly; _+_ , _·_ are the library's).
------------------------------------------------------------------------

max : ℕ → ℕ → ℕ
max a zero = a
max zero b = b
max (suc a) (suc b) = suc (max a b)

le : ℕ → ℕ → ℕ
le zero b = suc zero
le (suc a) zero = zero
le (suc a) (suc b) = le a b

------------------------------------------------------------------------
-- §3  The wombed squares, filled.
------------------------------------------------------------------------

-- le is reflexively "true": the lemma the second square needed
le-आत्मनि : (a : ℕ) → le a a ≡ suc zero
le-आत्मनि zero    = refl
le-आत्मनि (suc a) = le-आत्मनि a

-- WOMB ROW 1 (purana.ledger 2026-08-24T02:55:29Z, verdict fiber):
--   *(s(le(x,0)),x) ≡ x.  A case split: at zero both sides compute to
-- zero; at suc a the guard computes to one and 1 · n is n + zero.
गर्भ-पूरण-१ : (x : ℕ) → suc (le x zero) · x ≡ x
गर्भ-पूरण-१ zero    = refl
गर्भ-पूरण-१ (suc a) = +-zero (suc a)

-- WOMB ROW 2 (purana.ledger 2026-08-24T02:56:41Z, verdict fiber):
--   s(0) ≡ le(x, max(x,s(0))).  At zero it computes; at suc a the max
-- steps to suc (max a zero) = suc a definitionally, and le a a closes it.
गर्भ-पूरण-२ : (x : ℕ) → le x (max x (suc zero)) ≡ suc zero
गर्भ-पूरण-२ zero    = refl
गर्भ-पूरण-२ (suc a) = le-आत्मनि a

------------------------------------------------------------------------
-- The reading, once, at the bottom: the external loop refused these with
-- ten agda calls each because its shape library had no case split; the
-- body holds them in two lines each because the evaluator is the rewriter
-- and the paths kept their inverses.  What remains foreign after this
-- module is a cache and a name — and the name can come off the organ.
------------------------------------------------------------------------
