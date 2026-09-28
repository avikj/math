{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- DescentObstructionUnified
--
-- "THE SAME DESCENT LEMMA, CHECKED THREE TIMES, NEVER UNIFIED" —
-- CHECKED, AND THE COUNT IS WRONG.
--
--
--     ProjectionChargeAudit.noChargeDescent
--   = SieveFiber "no section is charge-preserving"
--   = 0593 "novel-outcome→no-square"
--       — same descent lemma, checked three times, never unified
--
-- The corpus's own standing guard is that an identity between objects of
-- different types is its recurring failure mode, so the claim needs the
-- map EXHIBITED.  This module exhibits what exists and refuses what does
-- not.  The finding, stated before the terms:
--
--   * TWO of the named results are one lemma.  `descentObstruction`
--     below is that lemma; `recover-ProjectionChargeAudit` and
--     `recover-SieveFiber` are its instances at the two loci, and each
--     is checked here to be the type of the original.
--
--   * THE THIRD NAMED RESULT INSIDE `SieveFiber` IS NOT AN INDEPENDENT
--     PROOF.  `noChargePreservingSection` is a one-line corollary of
--     that file's own §7 `noChargeDescent` — take the descended map to
--     be `charge ∘ s`.  `section-from-descent` below is that derivation,
--     stated abstractly.  Two of the synthesis's three entries therefore
--     live in one file and one of them is downstream of the other.
--
--   * 0593's `novel-outcome→no-square` IS NOT THIS LEMMA, and the
--     synthesis's "=" is wrong there.  See §3: its certificate is a
--     MISSED POINT of a codomain, not a SEPARATED PAIR in a domain; it
--     needs no quotient, no identification, and no set-truncation
--     argument.  The two are the kernel side and the image side of a
--     factorisation, which is why they look alike in prose.  §3 states
--     the general image lemma and then shows the two certificate forms
--     are not interconvertible without extra data.
--
-- So the honest count is: ONE lemma, checked TWICE (in two files), with a
-- corollary and a different (dual) lemma also in the frame.  "Checked
-- three times" overstates by one and misidentifies one.
--
-- CHECKED ON THE PIN.  `formal/cubical/check.sh` (absent from this repository) with NM_MODULES set to
-- this module printed "RUNNING AGAINST THE PIN" (agda 2.8.0 at
-- /root/Agda-2.8.0/…, cubical /root/agda-libs/cubical-v0.9), EXIT=0
-- (errors: 0, warning lines: 0), CHECKSH_EXIT=0 read unpiped.  Scope,
-- verdict on THIS module and its import closure — which here includes
-- `ProjectionChargeAudit` and `SieveFiber`, since §2.3
-- instantiates against them.  `--safe`, no postulates, no holes.
------------------------------------------------------------------------

module DescentObstructionUnified where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; eq/ ; [_])

private
  variable
    ℓ ℓR ℓB : Level

------------------------------------------------------------------------
-- §1  THE LEMMA, once.
--
-- A datum `c : A → B` descends along the quotient A → A/R only if it is
-- R-invariant.  A single related pair on which c differs refutes every
-- candidate — not "we found none": the Σ-type quantifies over all of
-- them.  This is `NEGATIVE_KNOWLEDGE_IS_TYPED` §1's T1 certificate form.
--
-- The proof is the composite path
--     c a₀ ≡ c̄ [a₀] ≡ c̄ [a₁] ≡ c a₁
-- whose middle step is `cong c̄` applied to `eq/`.  Both files below have
-- exactly this term; nothing else about their settings is used, which is
-- the content of the claim that they are one lemma.
------------------------------------------------------------------------

module _ {A : Type ℓ} {R : A → A → Type ℓR} {B : Type ℓB} where

  Descends : (A → B) → Type (ℓ-max (ℓ-max ℓ ℓR) ℓB)
  Descends c = Σ[ c̄ ∈ (A / R → B) ] ((a : A) → c̄ [ a ] ≡ c a)

  descentObstruction :
    (c : A → B) (a₀ a₁ : A) → R a₀ a₁ → ¬ (c a₀ ≡ c a₁) → ¬ (Descends c)
  descentObstruction c a₀ a₁ r sep (c̄ , agrees) =
    sep (sym (agrees a₀) ∙ cong c̄ (eq/ a₀ a₁ r) ∙ agrees a₁)

-- The non-quotient form the two files also use: no factorisation of c
-- through any map that identifies a₀ with a₁.  Stated outside the
-- relation-indexed module above, because no relation appears in it —
-- which is itself the observation that the quotient in
-- `ProjectionChargeAudit` and `SieveFiber` §7 is presentation, not
-- content.
module _ {A : Type ℓ} {V : Type ℓR} {B : Type ℓB} where

  FactorsThrough : (A → V) → (A → B) → Type (ℓ-max (ℓ-max ℓ ℓR) ℓB)
  FactorsThrough q c = Σ[ c̄ ∈ (V → B) ] ((a : A) → c̄ (q a) ≡ c a)

  factorObstruction : (q : A → V) (c : A → B) (a₀ a₁ : A)
                    → q a₀ ≡ q a₁ → ¬ (c a₀ ≡ c a₁) → ¬ (FactorsThrough q c)
  factorObstruction q c a₀ a₁ e sep (c̄ , agrees) =
    sep (sym (agrees a₀) ∙ cong c̄ e ∙ agrees a₁)

------------------------------------------------------------------------
-- §1.1  The corollary the synthesis counted as a third proof.
--
-- "No section is charge-preserving" — `SieveFiber.noChargePreservingSection`
-- — asks for `s : V → A` with `c (s (q a)) ≡ c a`.  Compose: `c ∘ s` is
-- a factorisation of c through q.  So the section statement is the
-- factorisation statement pre-composed, and carries no extra content.
------------------------------------------------------------------------

module _ {A : Type ℓ} {V : Type ℓ} {B : Type ℓB} where

  PreservingSection : (A → V) → (A → B) → Type (ℓ-max ℓ ℓB)
  PreservingSection q c = Σ[ s ∈ (V → A) ] ((a : A) → c (s (q a)) ≡ c a)

  section-from-descent : (q : A → V) (c : A → B)
                       → ¬ (FactorsThrough q c) → ¬ (PreservingSection q c)
  section-from-descent q c nofactor (s , agrees) =
    nofactor ((λ v → c (s v)) , agrees)

------------------------------------------------------------------------
-- §2  THE TWO INSTANCES, with the map exhibited.
--
-- Each `recover-…` below is stated at the ORIGINAL type of the theorem
-- it recovers, so that the typechecker — not this comment — certifies
-- that the general lemma covers it.  §2.1/§2.2 give the shapes; §2.3
-- then IMPORTS the two original modules and applies the general lemma to
-- their actual objects, so the identification is checked against
-- `ProjectionChargeAudit.Local`/`R` and `SieveFiber.Vis`/`q`/`charge`
-- themselves and not against a paraphrase of them.
------------------------------------------------------------------------

-- §2.1  `ProjectionChargeAudit.noChargeDescent`.
--   A := Bool, R := the indiscrete relation, B := Bool, c := the
--   identity, and the separated pair is (false , true).
Indiscrete : Bool → Bool → Type
Indiscrete _ _ = Unit

recover-ProjectionChargeAudit :
  ¬ (Σ[ cbar ∈ (Bool / Indiscrete → Bool) ] ((b : Bool) → cbar [ b ] ≡ b))
recover-ProjectionChargeAudit =
  descentObstruction (λ b → b) false true tt false≢true

-- §2.2  `SieveFiber.noChargeDescentQuot`.
--   A := the domain [1,30] with its membership proof, R := "same
--   visible sieve state", B := Bool, c := the Liouville charge, and the
--   separated pair is (1 , 7).  Abstracted over the arithmetic, since
--   nothing in the descent argument uses it: what SieveFiber supplies is
--   exactly the two hypotheses below, `q 1 ≡ q 7` (`refl`, there) and
--   `¬ (charge 1 ≡ charge 7)` (`false≢true`, there).
module SieveFiberShape
  {Dom : Type} {Vis : Type}
  (q : Dom → Vis) (charge : Dom → Bool)
  (d₀ d₁ : Dom) (sameVis : q d₀ ≡ q d₁)
  (oppositeCharge : ¬ (charge d₀ ≡ charge d₁))
  where

  _∼_ : Dom → Dom → Type
  x ∼ y = q x ≡ q y

  recover-SieveFiber-quot :
    ¬ (Σ[ cbar ∈ (Dom / _∼_ → Bool) ] ((x : Dom) → cbar [ x ] ≡ charge x))
  recover-SieveFiber-quot =
    descentObstruction charge d₀ d₁ sameVis oppositeCharge

  recover-SieveFiber-bare :
    ¬ (Σ[ cbar ∈ (Vis → Bool) ] ((x : Dom) → cbar (q x) ≡ charge x))
  recover-SieveFiber-bare =
    factorObstruction q charge d₀ d₁ sameVis oppositeCharge

  -- …and the "third proof" is this, one line downstream.
  recover-SieveFiber-noSection :
    ¬ (Σ[ s ∈ (Vis → Dom) ] ((x : Dom) → charge (s (q x)) ≡ charge x))
  recover-SieveFiber-noSection =
    section-from-descent q charge recover-SieveFiber-bare

------------------------------------------------------------------------
-- §2.3  THE INSTANTIATION AGAINST THE REAL MODULES.
--
-- §2.1 and §2.2 state the shapes; this section applies the general lemma
-- to the actual objects and gives the results the ORIGINAL types, so the
-- typechecker certifies the identification rather than this file
-- asserting it.  Each of the four below is the type of the named
-- theorem in the named module, proved from `descentObstruction` /
-- `factorObstruction` alone.
------------------------------------------------------------------------

open import ProjectionChargeAudit using () renaming (R to PCA-R ; Local to PCA-Local)
open import SieveFiber as SF
  using () renaming (Vis to SF-Vis ; Dom to SF-Dom ; Sieve to SF-Sieve
                    ; q to SF-q ; charge to SF-charge ; domain to SF-domain)

-- `ProjectionChargeAudit.NoChargeDescent`, verbatim.
instance-ProjectionChargeAudit :
  ¬ (Σ[ cbar ∈ (PCA-Local → Bool) ] ((b : Bool) → cbar [ b ] ≡ b))
instance-ProjectionChargeAudit =
  descentObstruction {R = PCA-R} (λ b → b) false true tt false≢true

-- The two SieveFiber facts, from the same lemma.  The hypotheses are
-- SieveFiber's own: `q 1 ≡ q 7` is `refl` there and here, and the
-- opposite-charge fact is `false≢true` there and here.
private
  SF-1 SF-7 : SF-Dom
  SF-1 = 1 , SF.1∈
  SF-7 = 7 , SF.7∈

  SF-q∘fst : SF-Dom → SF-Vis
  SF-q∘fst x = SF-q (fst x)

  SF-charge∘fst : SF-Dom → Bool
  SF-charge∘fst x = SF-charge (fst x)

  SF-sameVis : SF-q∘fst SF-1 ≡ SF-q∘fst SF-7
  SF-sameVis = refl

  SF-opposite : ¬ (SF-charge∘fst SF-1 ≡ SF-charge∘fst SF-7)
  SF-opposite = false≢true

module SF-instance =
  SieveFiberShape SF-q∘fst SF-charge∘fst SF-1 SF-7 SF-sameVis SF-opposite

-- `SieveFiber.noChargeDescent` (the bare form, §7).
instance-SieveFiber-bare :
  ¬ (Σ[ cbar ∈ (SF-Vis → Bool) ]
       ((x : SF-Dom) → cbar (SF-q (fst x)) ≡ SF-charge (fst x)))
instance-SieveFiber-bare = SF-instance.recover-SieveFiber-bare

-- `SieveFiber.noChargeDescentQuot` (the quotient form, §7).
instance-SieveFiber-quot :
  ¬ (Σ[ cbar ∈ (SF-Dom / SF-instance._∼_ → Bool) ]
       ((x : SF-Dom) → cbar [ x ] ≡ SF-charge (fst x)))
instance-SieveFiber-quot = SF-instance.recover-SieveFiber-quot

-- `SieveFiber.noChargePreservingSection` (§8) — the entry the synthesis
-- counted as a third proof — AT ITS EXACT ORIGINAL TYPE, `s : Vis → ℕ`
-- with agreement only on the domain.  It costs one composition: the
-- candidate section is turned into a candidate factorisation by
-- post-composing with `charge`, and `instance-SieveFiber-bare` kills it.
-- No second argument is used, which is the claim.
instance-SieveFiber-noSection :
  ¬ (Σ[ s ∈ (SF-Vis → ℕ) ]
       ({n : ℕ} → n SF.∈ SF-domain → SF-charge (s (SF-q n)) ≡ SF-charge n))
instance-SieveFiber-noSection (s , agree) =
  instance-SieveFiber-bare
    ((λ v → SF-charge (s v)) , λ x → agree (snd x))

------------------------------------------------------------------------
-- §3  0593 IS A DIFFERENT LEMMA.
--
-- `ProstheticImageAdapter.novel-outcome→no-square` reads
--
--     (q : Q) (y : Y q) → isInImage (r′ q) y → ¬ isInImage (r q) y
--                       → ¬ ResponseSquare
--
-- with `Square = (q : Q) (x′ : X′) → r q (stateMap x′) ≡ r′ q x′`.
-- Stripped of the propositional truncation (which is bookkeeping — the
-- proof is `PT.map`), it is the lemma below: a commuting square pushes
-- the image of the revised response into the image of the old one, so a
-- point present after and absent before refutes the square.
--
-- WHY IT IS NOT §1.  Compare the two certificates:
--
--   §1  needs  a PAIR a₀ a₁ IN THE DOMAIN, identified by the quotient and
--              separated by the datum.  Obstruction to a map OUT of a
--              coequaliser; the content is that c is not R-invariant.
--   §3  needs  a POINT y IN THE CODOMAIN, hit after and missed before.
--              Obstruction to a map INTO an image; the content is that
--              one image is not contained in the other.
--
-- One is a kernel statement, the other an image statement.  They are the
-- two halves of a first-isomorphism-theorem shape, which is exactly why
-- both read in prose as "the new thing does not descend".  Neither is an
-- instance of the other: §1 requires an identification (and gives none
-- of a codomain point), §3 requires a codomain point (and identifies
-- nothing).  `imageObstruction` below uses no quotient, no relation, and
-- no separated pair — the absence is the argument.
------------------------------------------------------------------------

module _ {X X′ Y : Type ℓ} (r : X → Y) (r′ : X′ → Y) (stateMap : X′ → X) where

  ResponseSquare : Type ℓ
  ResponseSquare = (x′ : X′) → r (stateMap x′) ≡ r′ x′

  InImage : (Z : Type ℓ) → (Z → Y) → Y → Type ℓ
  InImage Z f y = Σ[ z ∈ Z ] (f z ≡ y)

  -- The positive half: a square carries revised-image membership back.
  preserves-image : ResponseSquare → (y : Y) → InImage X′ r′ y → InImage X r y
  preserves-image square y (x′ , hit) = stateMap x′ , (square x′ ∙ hit)

  -- The negative half: 0593's statement, in this vocabulary.
  imageObstruction : (y : Y) → InImage X′ r′ y → ¬ (InImage X r y) → ¬ ResponseSquare
  imageObstruction y revised absent square = absent (preserves-image square y revised)

-- The certificate forms, side by side, so the difference is typed and
-- not merely asserted.  A reader who wants to claim §1 = §3 must supply
-- a term of one of these from the other; neither is inhabited by
-- anything in this module, and the two records have no common field.
record KernelCertificate {A : Type ℓ} {B : Type ℓB}
                         (R : A → A → Type ℓ) (c : A → B) : Type (ℓ-max ℓ ℓB) where
  field
    left     : A
    right    : A
    related  : R left right
    separate : ¬ (c left ≡ c right)

record ImageCertificate {X X′ Y : Type ℓ} (r : X → Y) (r′ : X′ → Y) : Type ℓ where
  field
    point   : Y
    present : Σ[ x′ ∈ X′ ] (r′ x′ ≡ point)
    absent  : ¬ (Σ[ x ∈ X ] (r x ≡ point))
