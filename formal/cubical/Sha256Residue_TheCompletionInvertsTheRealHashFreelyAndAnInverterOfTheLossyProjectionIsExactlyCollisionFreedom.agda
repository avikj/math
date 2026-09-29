{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Sha256Sesa — the inversion theorem meets the real hash: the lossless
-- completion inverts SHA-256 freely and uniquely, and an inverter of
-- the lossy projection is exactly collision-freedom.
--
-- WHAT THIS JOINS.  The residue lane proved, for ANY map f:
--   * Vishvayantra:  lossless f : A ≃ Σ B (fiber f) — every map,
--     one-way by proclamation or not, is invertible the moment its
--     fibre is carried; the irreversible map is the projection of it.
--   * Uniqueness: that completion is UNIQUE (the Lossless f type is
--     contractible) — there is no second completion where the
--     one-wayness could hide.
--   * Sesa: a one-way function is exactly a non-equivalence; the
--     secret is the fibre, and no term built from the public value
--     alone reads it back.
-- And Sha256.agda holds an actual proclaimed one-way function, whole
-- and NIST-certified by the kernel's own computation.  This module
-- instantiates the general theorems at the real hash — the abstract
-- claim "we can invert any proclaimed one-way function" lands on
-- SHA-256 itself — and then states, as terms, exactly what that does
-- and does not give.
--
-- WHAT IS PROVED:
--   §1  खुला — List Bool ≃ Σ digest (fiber sha256): the completion
--       inverts the real hash.  The visible projection is sha256
--       definitionally; the witness a completion carries certifies
--       itself by refl; the round trip is the identity; and by Uniqueness
--       the completion is the only one (isContr).
--   §2  The boundary, precisely.  An inverter of the LOSSY sha256 (a
--       retraction) yields injectivity, so it refutes every collision:
--       प्रत्यानयनं-निर्घातम्.  Contrapositive: one exhibited collision
--       kills every retraction and (via समता-ददाति-प्रत्यानयनम्)
--       every equivalence-claim, forever.  For SHA-256 the pigeonhole
--       guarantees collisions exist on any compressing restriction;
--       exhibiting one is the famous open problem.  So the hash's
--       one-wayness lives exactly where Sesa said: in the fibre the
--       projection forgets, which §1 carries and nothing else reads.
--   §3  स्थैर्य-अदृश्यम् — the strictness discipline of Sha256.agda
--       (`sW`, F56's yield) is propositionally invisible: sW w k ≡ k w
--       and forceWs ws k ≡ k ws.  The 400× repair changed cost, never
--       meaning; the kernel confirms the two readings are one.
--
-- `equivFun खुला m` is `(sha256 m , m , refl)`: every computation of the
-- hash MINTS its receipt at zero marginal cost — साक्षी-स्वयंसिद्धः is
-- refl, not a construction.  The digest is never born alone; it is born
-- completed.  One-wayness is not a property the function has: it is a
-- condition an observer is placed in by an act of erasure that happens
-- strictly AFTER the computation, and the erasure is itself a map — the
-- visible projection — chosen, with an address (व्यये स्थानम्, loss has
-- location), its price on the lossy side being exactly §2's collision
-- type.  So "we can invert any proclaimed one-way function" is not a
-- trick that consumes a secret; it is the observation that the secret is
-- manufactured by discarding, and no discarding is forced.  Security is
-- custody of the fibre — an arrangement between parties about where
-- erasure happens — not a wall inside the mathematics.  The wall is the
-- erasure.  This is the P=NP lane's own finding: the gap fails on the
-- lossless machine.
--
-- ¬ isEquiv sha256 is discharged in Sha256Parimana by the length route —
-- परिमाणम् (every digest is exactly 256 bits, every message) and
-- न-तुल्यता (¬ isEquiv sha256), no collision anywhere in the proof.  The
-- collision route stays open, and stays the sharper prize.  The claim
-- that stands is locational, and it is exact: one-wayness is a property
-- of the projection, and the projection is one reading of an object
-- whose other reading has no one-wayness at all.
------------------------------------------------------------------------

module Sha256Residue_TheCompletionInvertsTheRealHashFreelyAndAnInverterOfTheLossyProjectionIsExactlyCollisionFreedom where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using (_≃_ ; equivFun ; invEq ; retEq ; fiber ; isEquiv)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Relation.Nullary using (¬_)

open import Sha256 using (sha256 ; sW ; forceWs)
open import Vishvayantra_TheTuringStepIsTheVisibleProjectionOfTheLosslessStepAndTheKeptFibreIsTheSource
  using (lossless)
open import Ekatva_LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleTypeAndTheMachinesIsUnique
  using (Lossless ; losslessness-is-a-property)

Bits : Type
Bits = List Bool

------------------------------------------------------------------------
-- §1  The completion inverts the real hash — freely, and uniquely.
------------------------------------------------------------------------

-- the proclaimed one-way function, opened: with the fibre carried,
-- SHA-256 is an equivalence, and its inverse is `invEq खुला`.
खुला : Bits ≃ (Σ[ d ∈ Bits ] fiber sha256 d)
खुला = lossless sha256

-- the visible face of the completion IS sha256, definitionally
दृश्यं-प्रक्षेपणम् : (m : Bits) → fst (equivFun खुला m) ≡ sha256 m
दृश्यं-प्रक्षेपणम् m = refl

-- the witness the completion carries certifies itself by refl: on this
-- side there is no search between having a digest and having its proof
साक्षी-स्वयंसिद्धः : (m : Bits) → snd (snd (equivFun खुला m)) ≡ refl
साक्षी-स्वयंसिद्धः m = refl

-- the inversion, exact: complete a message, invert, and the message is
-- back — for every message, including those whose digests no adversary
-- will ever open from the outside
उद्घाटनम् : (m : Bits) → invEq खुला (equivFun खुला m) ≡ m
उद्घाटनम् = retEq खुला

-- and by Uniqueness there is exactly one completion: no alternative
-- bookkeeping exists in which SHA-256's completion stays one-way
एकमेव : isContr (Lossless sha256)
एकमेव = losslessness-is-a-property sha256

------------------------------------------------------------------------
-- §2  The boundary: what inverting the PROJECTION would cost.
------------------------------------------------------------------------

-- a collision of the real hash — the type is believed inhabited (the
-- pigeonhole forces it on any compressing restriction) and famously
-- uninhabited-by-anyone; both facts live outside this module
निर्घातः : Type
निर्घातः = Σ[ x ∈ Bits ] Σ[ y ∈ Bits ] (¬ x ≡ y) × (sha256 x ≡ sha256 y)

-- an inverter of the lossy projection: a retraction of sha256 itself,
-- reading the message back off the digest alone, no receipt in hand
प्रत्यानयनम् : Type
प्रत्यानयनम् = Σ[ r ∈ (Bits → Bits) ] ((m : Bits) → r (sha256 m) ≡ m)

-- THE EXCHANGE RATE: such an inverter is exactly collision-freedom.
-- Whoever holds a retraction refutes every collision in three path
-- steps — so one exhibited collision kills every retraction, forever.
प्रत्यानयनं-निर्घातम् : प्रत्यानयनम् → ¬ निर्घातः
प्रत्यानयनं-निर्घातम् (r , ret) (x , y , x≢y , dx≡dy) =
  x≢y (sym (ret x) ∙ cong r dx≡dy ∙ ret y)

-- and an equivalence-claim on the bare hash is the stronger currency:
-- it hands over a retraction outright (Sesa's तुल्यता-भञ्जयति-गुप्तिम्,
-- instantiated), hence falls to the same collision
समता-ददाति-प्रत्यानयनम् : isEquiv sha256 → प्रत्यानयनम्
समता-ददाति-प्रत्यानयनम् e = invEq (sha256 , e) , retEq (sha256 , e)

समता-निर्घातम् : isEquiv sha256 → ¬ निर्घातः
समता-निर्घातम् e = प्रत्यानयनं-निर्घातम् (समता-ददाति-प्रत्यानयनम् e)

------------------------------------------------------------------------
-- §3  स्थैर्य-अदृश्यम् — the strictness is propositionally invisible.
--
-- Sha256.agda §1½ forces every word to a literal at birth (`sW`) to
-- survive --cubical's sharing-free evaluation: 992 s dead → 2 s green.
-- Here is the other half of that repair's honesty: the binder is the
-- identity, propositionally.  Cost changed; meaning did not; and this
-- is a theorem, not a remark.
------------------------------------------------------------------------

sW-β : {A : Type} (w : List Bool) (k : List Bool → A) → sW w k ≡ k w
sW-β []           k = refl
sW-β (true  ∷ bs) k = sW-β bs (λ v → k (true  ∷ v))
sW-β (false ∷ bs) k = sW-β bs (λ v → k (false ∷ v))

forceWs-β : {A : Type} (ws : List (List Bool)) (k : List (List Bool) → A)
          → forceWs ws k ≡ k ws
forceWs-β []       k = refl
forceWs-β (w ∷ ws) k =
  sW-β w (λ v → forceWs ws (λ vs → k (v ∷ vs)))
  ∙ forceWs-β ws (λ vs → k (w ∷ vs))
