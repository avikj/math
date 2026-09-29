{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Ākāṅkṣā — the pattern's demand, and what soundness does to it.
--
-- TERM.  आकाङ्क्षा, expectancy: in the Indian accounts of how uttered words
-- yield one cognition (śābdabodha) it is the first of the conditions — a
-- word EXPECTS its complements, and an utterance leaving an expectancy
-- unsatisfied does not compose.  The triad kk / yogyat / satti is
-- common to Mms and Nyya and is developed at length in the later
-- Nyya (Gagea, *Tattvacintmai*, 14th c.).
-- The word names
-- the phenomenon: a rule whose sthnin does not bind the variable has no
-- expectancy to satisfy, and the question is what its dea may then say.
--
-- WHY THIS MODULE EXISTS.  `Vyapti_…` repairs the kernel's memorisation by
-- giving an operation a schematic control,
--
--     Control t = Σ[ u ∈ Tm ] (t ≡ subVar u lhs)      and
--     apply t (u , _) = subVar u rhs .
--
-- That is the first operation in the corpus whose EMISSION READS ITS
-- EVIDENCE — every `install`ed operation has `apply _ _ = target`, a
-- constant.  As soon as an emission reads its evidence, a question arises
-- that a constant emission cannot pose:
--
--     IF TWO DIFFERENT CONTROLS ARE ADMISSIBLE AT ONE TERM, THE OPERATION
--     EMITS TWO DIFFERENT TERMS FROM ONE CONTEXT.
--
-- Nothing in the corpus ruled that out, and `apply-sound` is proved for
-- EVERY control, so both emissions would carry proofs: a generator with two
-- distinct certified outputs at one context.  That is `Sesa_…`'s semantic
-- statement (correctness does not select) arriving operationally.
--
-- The failure shape is not hypothetical outside the kernel.  Ask the
-- corpus's Pinian interface for the class `ya` and it does not answer
-- with a class: the anubandha  occurs twice in the fourteen ivastras
-- (stras 1 and 6), so the two-letter name denotes only once an OCCURRENCE
-- INDEX is supplied, and the running sabh takes that index (`avrtti`) as a
-- parameter rather than guessing.  A name needing a disambiguating index is
-- exactly a control that fails to determine its emission.
--
-- WHAT IS PROVED.  The kernel cannot host one.  Two reasons, exhaustive:
--
--   §3  MOVING PATTERNS PIN THEIR WITNESS.  If `var` occurs in `lhs` at all
--       (`deg lhs ≡ nsuc j`) then `subVar a lhs ≡ subVar b lhs → a ≡ b`, so
--       the witness is unique and the emission is determined.  Purely
--       syntactic — no semantics is used.
--
--   §5  RIGID PATTERNS CANNOT PASS THE VARIABLE ON, AND THIS IS WHERE
--       SOUNDNESS IS NEEDED.  If `var` does not occur in `lhs`, every `a`
--       is admissible and §3 is unavailable.  But a schema also carries
--       `meaning : (ρ : Env) → eval lhs ρ ≡ eval rhs ρ`, and in this
--       calculus raising x by one raises a term's value by EXACTLY its
--       degree (§4, `eval-step`).  A rigid `lhs` is therefore constant
--       along x; a sound `rhs` must be too; hence `deg rhs ≡ nzero`, and
--       then `subVar a rhs ≡ rhs` for every `a`.
--
--   §6  EVERY SOUND SCHEMA IS DETERMINISTIC.  At any term, any two
--       admissible controls emit the same term.  Not by a well-formedness
--       side condition anyone imposed — by meaning-preservation alone.
--
-- READ AS GRAMMAR: an dea may not introduce material its sthnin did not
-- bind, and that is not a stipulation of the metalanguage — it follows from
-- the rule being meaning-preserving at every environment.
--
-- READ AS SEMANTICS OF PROGRAMS: a sequential algorithm in the sense of
-- Kahn–Plotkin and Berry–Curien is a function together with a computation
-- strategy, and its output must be determined by the cells it queried.  §6
-- says every sound schema here satisfies that without being asked to: the
-- pattern is the query, and soundness makes the query sufficient.
--
-- `deg` counts `var` alone, because
-- `subVar` replaces `var` alone.
-- `Vyapti_…` is not imported: the statement is given on raw `lhs`, `rhs`
-- and `meaning`, which is what its record holds.
------------------------------------------------------------------------

module NaturalMachine.Akanksa_TheSchemaCannotHandItsReplacementAVariableItsPatternDidNotBind where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
  renaming (zero to nzero ; suc to nsuc ; _+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties
  using (snotz ; znots ; inj-+m ; +-assoc ; +-comm ; +-suc)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

open import Kernel.RewriteCertificate

------------------------------------------------------------------------
-- §1.  DEGREE — how many times the substitutable coordinate occurs.
-- `subVar` replaces `var` and leaves the other five alone, so this counts
-- `var` and nothing else.
------------------------------------------------------------------------

deg : Tm → ℕ
deg var       = nsuc nzero
deg yvar      = nzero
deg zvar      = nzero
deg uvar      = nzero
deg vvar      = nzero
deg wvar      = nzero
deg zero      = nzero
deg (suc t)   = deg t
deg (add l r) = deg l +ℕ deg r

private
  sum≡0→left : (m n : ℕ) → m +ℕ n ≡ nzero → m ≡ nzero
  sum≡0→left nzero    n p = refl
  sum≡0→left (nsuc m) n p = ⊥rec (snotz p)

  sum≡0→right : (m n : ℕ) → m +ℕ n ≡ nzero → n ≡ nzero
  sum≡0→right nzero    n p = p
  sum≡0→right (nsuc m) n p = ⊥rec (snotz p)

  sum≡suc→ : (m n j : ℕ) → m +ℕ n ≡ nsuc j
           → (Σ[ i ∈ ℕ ] (m ≡ nsuc i)) ⊎ (Σ[ i ∈ ℕ ] (n ≡ nsuc i))
  sum≡suc→ nzero    nzero    j p = ⊥rec (znots p)
  sum≡suc→ nzero    (nsuc n) j p = inr (n , refl)
  sum≡suc→ (nsuc m) n        j p = inl (m , refl)

  caseDeg : (n : ℕ) → (n ≡ nzero) ⊎ (Σ[ j ∈ ℕ ] (n ≡ nsuc j))
  caseDeg nzero    = inl refl
  caseDeg (nsuc j) = inr (j , refl)

------------------------------------------------------------------------
-- §2.  A RIGID PATTERN IS FIXED BY EVERY SUBSTITUTION.
------------------------------------------------------------------------

rigid-subVar : (t : Tm) → deg t ≡ nzero → (a : Tm) → subVar a t ≡ t
rigid-subVar var       p a = ⊥rec (snotz p)
rigid-subVar yvar      p a = refl
rigid-subVar zvar      p a = refl
rigid-subVar uvar      p a = refl
rigid-subVar vvar      p a = refl
rigid-subVar wvar      p a = refl
rigid-subVar zero      p a = refl
rigid-subVar (suc t)   p a = cong suc (rigid-subVar t p a)
rigid-subVar (add l r) p a =
  cong₂ add (rigid-subVar l (sum≡0→left  (deg l) (deg r) p) a)
            (rigid-subVar r (sum≡0→right (deg l) (deg r) p) a)

------------------------------------------------------------------------
-- §3.  A MOVING PATTERN PINS ITS WITNESS.  Syntactic.
------------------------------------------------------------------------

private
  unSuc : Tm → Tm
  unSuc (suc t) = t
  unSuc t       = t

  sucInj : {a b : Tm} → suc a ≡ suc b → a ≡ b
  sucInj = cong unSuc

  addL addR : Tm → Tm
  addL (add l r) = l
  addL t         = t
  addR (add l r) = r
  addR t         = t

  addInjL : {l r l' r' : Tm} → add l r ≡ add l' r' → l ≡ l'
  addInjL = cong addL

  addInjR : {l r l' r' : Tm} → add l r ≡ add l' r' → r ≡ r'
  addInjR = cong addR

moving-pins-its-witness :
  (t : Tm) (j : ℕ) → deg t ≡ nsuc j
  → (a b : Tm) → subVar a t ≡ subVar b t → a ≡ b
moving-pins-its-witness var       j q a b e = e
moving-pins-its-witness yvar      j q a b e = ⊥rec (znots q)
moving-pins-its-witness zvar      j q a b e = ⊥rec (znots q)
moving-pins-its-witness uvar      j q a b e = ⊥rec (znots q)
moving-pins-its-witness vvar      j q a b e = ⊥rec (znots q)
moving-pins-its-witness wvar      j q a b e = ⊥rec (znots q)
moving-pins-its-witness zero      j q a b e = ⊥rec (znots q)
moving-pins-its-witness (suc t)   j q a b e =
  moving-pins-its-witness t j q a b (sucInj e)
moving-pins-its-witness (add l r) j q a b e with sum≡suc→ (deg l) (deg r) j q
... | inl (i , ql) = moving-pins-its-witness l i ql a b (addInjL e)
... | inr (i , qr) = moving-pins-its-witness r i qr a b (addInjR e)

------------------------------------------------------------------------
-- §4.  RAISING x BY ONE RAISES THE VALUE BY EXACTLY THE DEGREE.
--
-- The whole semantic content of the module is this one equation.  It is
-- what makes "the variable occurs" a statement about MEANING and not only
-- about syntax, and it is available because the calculus has zero,
-- successor and addition and nothing that can cancel.
------------------------------------------------------------------------

private
  swapMid : (a b c d : ℕ)
          → (a +ℕ b) +ℕ (c +ℕ d) ≡ (a +ℕ c) +ℕ (b +ℕ d)
  swapMid a b c d =
      sym (+-assoc a b (c +ℕ d))
    ∙ cong (a +ℕ_) (+-assoc b c d)
    ∙ cong (λ z → a +ℕ (z +ℕ d)) (+-comm b c)
    ∙ cong (a +ℕ_) (sym (+-assoc c b d))
    ∙ +-assoc a c (b +ℕ d)

eval-step : (t : Tm) (n : ℕ) (ρ : Env)
          → eval t (setX (nsuc n) ρ) ≡ deg t +ℕ eval t (setX n ρ)
eval-step var       n ρ = refl
eval-step yvar      n ρ = refl
eval-step zvar      n ρ = refl
eval-step uvar      n ρ = refl
eval-step vvar      n ρ = refl
eval-step wvar      n ρ = refl
eval-step zero      n ρ = refl
eval-step (suc t)   n ρ =
  cong nsuc (eval-step t n ρ) ∙ sym (+-suc (deg t) (eval t (setX n ρ)))
eval-step (add l r) n ρ =
    cong₂ _+ℕ_ (eval-step l n ρ) (eval-step r n ρ)
  ∙ swapMid (deg l) (eval l (setX n ρ)) (deg r) (eval r (setX n ρ))

------------------------------------------------------------------------
-- §5.  RIGID IS CONSTANT ALONG x ; MOVING NEVER IS ; AND SOUNDNESS
--      TRANSPORTS RIGIDITY FROM THE PATTERN TO THE REPLACEMENT.
------------------------------------------------------------------------

rigid-eval-const : (t : Tm) → deg t ≡ nzero
                 → (n : ℕ) (ρ : Env) → eval t (setX n ρ) ≡ eval t (setX nzero ρ)
rigid-eval-const t p nzero    ρ = refl
rigid-eval-const t p (nsuc n) ρ =
    eval-step t n ρ
  ∙ cong (_+ℕ eval t (setX n ρ)) p
  ∙ rigid-eval-const t p n ρ

moving-eval-moves : (t : Tm) (j : ℕ) → deg t ≡ nsuc j
                  → (n : ℕ) (ρ : Env)
                  → ¬ (eval t (setX (nsuc n) ρ) ≡ eval t (setX n ρ))
moving-eval-moves t j q n ρ e = snotz (inj-+m step)
  where
    step : nsuc j +ℕ eval t (setX n ρ) ≡ nzero +ℕ eval t (setX n ρ)
    step = cong (_+ℕ eval t (setX n ρ)) (sym q) ∙ sym (eval-step t n ρ) ∙ e

-- THE TRANSPORT.  A sound rule whose pattern is rigid has a rigid
-- replacement.  This is the step that needs the semantics, and it is why
-- the grammatical prohibition is a theorem rather than a convention.
sound-rigid-pattern-has-rigid-replacement :
  (lhs rhs : Tm)
  → ((ρ : Env) → eval lhs ρ ≡ eval rhs ρ)
  → deg lhs ≡ nzero → deg rhs ≡ nzero
sound-rigid-pattern-has-rigid-replacement lhs rhs meaning p
  with caseDeg (deg rhs)
... | inl z         = z
... | inr (j , q)   = ⊥rec (moving-eval-moves rhs j q nzero ρ₀ contradiction)
  where
    ρ₀ : Env
    ρ₀ = env nzero nzero nzero nzero nzero nzero

    contradiction : eval rhs (setX (nsuc nzero) ρ₀) ≡ eval rhs (setX nzero ρ₀)
    contradiction =
        sym (meaning (setX (nsuc nzero) ρ₀))
      ∙ rigid-eval-const lhs p (nsuc nzero) ρ₀
      ∙ meaning (setX nzero ρ₀)

------------------------------------------------------------------------
-- §6.  THE COROLLARY.  EVERY SOUND SCHEMA IS DETERMINISTIC.
--
-- Two admissible controls at one term emit one term.  The two cases are
-- the two halves above and they are the only two: either the pattern binds
-- the variable, and then the evidence is pinned; or it does not, and then
-- soundness has already forbidden the replacement from mentioning it.
------------------------------------------------------------------------

schema-emission-is-determined :
  (lhs rhs : Tm)
  → ((ρ : Env) → eval lhs ρ ≡ eval rhs ρ)
  → (t a b : Tm)
  → t ≡ subVar a lhs → t ≡ subVar b lhs
  → subVar a rhs ≡ subVar b rhs
schema-emission-is-determined lhs rhs meaning t a b pa pb
  with caseDeg (deg lhs)
... | inr (j , q) =
      cong (λ z → subVar z rhs)
           (moving-pins-its-witness lhs j q a b (sym pa ∙ pb))
... | inl p =
      rigid-subVar rhs rigidRhs a ∙ sym (rigid-subVar rhs rigidRhs b)
  where
    rigidRhs : deg rhs ≡ nzero
    rigidRhs = sound-rigid-pattern-has-rigid-replacement lhs rhs meaning p

------------------------------------------------------------------------
-- §7.  THE ONE EXHIBIT.  The kernel's own accepted theorem is a moving
-- schema, so its witness is pinned: `add var (suc zero)` has degree one.
------------------------------------------------------------------------

kernels-own-pattern-moves : deg (add var (suc zero)) ≡ nsuc nzero
kernels-own-pattern-moves = refl

kernels-own-witness-is-pinned :
  (a b : Tm) → subVar a (add var (suc zero)) ≡ subVar b (add var (suc zero)) → a ≡ b
kernels-own-witness-is-pinned =
  moving-pins-its-witness (add var (suc zero)) nzero kernels-own-pattern-moves
