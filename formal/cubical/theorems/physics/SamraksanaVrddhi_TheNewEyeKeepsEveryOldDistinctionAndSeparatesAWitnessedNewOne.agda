{-# OPTIONS --cubical --safe #-}

-- SamraksanaVrddhi_TheNewEyeKeepsEveryOldDistinctionAndSeparatesAWitnessedNewOne
--
-- संरक्षण-वृद्धिः — saṁrakṣaṇa, guarding/conservation; vṛddhi, growth
-- (both ordinary ; vddhi is also Pini's technical name for
-- the strengthened vowel grade, Aṣṭādhyāyī 1.1.1 vṛddhir ādaic — taken
-- here ONLY in its ordinary sense of increase).  Compound built here for
-- U0023 (collab/upstream/raw/U0023.txt (absent from this repository)).
--
-- THE OTHER HALF OF THE ADMISSION GATE.  ApurvaIndriyam (imported)
-- checked the NOVELTY criterion: one blind pair separated by a proposal
-- refutes every possible derivation of it from the present sensorium.
-- U0023 supplies the other half — CONSERVATION:
--
--     "Form the enlarged sensorium S'(x) = (S(x), q(x)).  The old
--      sensorium is recovered exactly: S = π₁ ∘ S'.  So S' is not
--      merely novel.  It is a conservative extension. ...
--      Every old distinction remains readable, and at least one
--      previously invisible distinction becomes visible.
--      Permanent conservative refinement is organogenesis.
--      Temporary conservative refinement is attention."
--
-- WHAT IS PROVED:
--   §1  युगपत् — the joint eye ⟨S,q⟩, and BOTH projections are refl-
--       factorings: the old sensorium and the proposal are each
--       recovered from the joint reading with h = fst, h = snd.
--       Conservation costs nothing and holds always, for every q.
--   §2  the strict-refinement relation ≺: S ≺ S' iff S flows through
--       S' and S' does not flow through S.  Data, not truncated —
--       the factoring is handed over, the refutation is a function.
--   §3  the growth theorem: a single witnessed blind pair upgrades
--       the always-true conservation to STRICT refinement:
--       S ≺ ⟨S,q⟩.  Novelty reuses ApurvaIndriyam's अपूर्वम् verbatim
--       — the two halves are one construction, exactly as U0023 says
--       ("safe attention and safe organogenesis are one construction").
--   §4  what strictness refuses: ⟨S,q⟩ ≺ ⟨S,q⟩ is uninhabitable — no
--       eye strictly refines itself, so growth cannot be faked by
--       re-reading the same organ (the identity factoring on the left
--       contradicts the required refutation on the right).
--

module SamraksanaVrddhi_TheNewEyeKeepsEveryOldDistinctionAndSeparatesAWitnessedNewOne where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

open import ApurvaIndriyam_AMapThatFactorsIsBlindOnTheFibresSoASeparatedBlindPairCertifiesANewSense
  using (प्रवहति ; अपूर्वम्)

private
  variable
    ℓ ℓ' ℓ'' : Level

-- ── §1 · the joint eye, and conservation for free ────────────────────────

युगपत् : {X : Type ℓ} {O : Type ℓ'} {Q : Type ℓ''}
       → (X → O) → (X → Q) → (X → O × Q)
युगपत् S q x = S x , q x

-- the old sensorium is recovered exactly: S = fst ∘ ⟨S,q⟩, by refl
संरक्षणम् : {X : Type ℓ} {O : Type ℓ'} {Q : Type ℓ''}
            (S : X → O) (q : X → Q) → प्रवहति (युगपत् S q) S
संरक्षणम् S q = fst , λ x → refl

-- and the proposal is readable too: q = snd ∘ ⟨S,q⟩
पठनम् : {X : Type ℓ} {O : Type ℓ'} {Q : Type ℓ''}
        (S : X → O) (q : X → Q) → प्रवहति (युगपत् S q) q
पठनम् S q = snd , λ x → refl

-- ── §2 · strict refinement: readable one way, underivable the other ──────

_≺_ : {X : Type ℓ} {O : Type ℓ'} {O' : Type ℓ''}
    → (X → O) → (X → O') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
S ≺ S' = प्रवहति S' S × (प्रवहति S S' → ⊥)

-- ── §3 · the growth theorem: one blind pair makes the joint eye strict ───

वृद्धिः : {X : Type ℓ} {O : Type ℓ'} {Q : Type ℓ''}
         (S : X → O) (q : X → Q) (x y : X)
       → S x ≡ S y                -- the present eye cannot split them
       → (q x ≡ q y → ⊥)          -- the proposal splits them
       → S ≺ युगपत् S q
वृद्धिः S q x y blind sep =
  संरक्षणम् S q ,
  λ jointFlows → अपूर्वम् S q x y blind sep
    ( (λ o → snd (fst jointFlows o))
    , (λ x' → cong snd (snd jointFlows x')) )

-- ── §4 · growth cannot be faked: no eye strictly refines itself ──────────

अ-स्वातिक्रमः : {X : Type ℓ} {O : Type ℓ'}
               (S : X → O) → S ≺ S → ⊥
अ-स्वातिक्रमः S (flows , refuses) = refuses ((λ o → o) , (λ x → refl))
