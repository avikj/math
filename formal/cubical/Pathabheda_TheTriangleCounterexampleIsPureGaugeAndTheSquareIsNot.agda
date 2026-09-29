{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- पथाभेदः — pathābheda, "non-difference of paths".
--
-- ON THE NAME.  The word is the transmission's own, not a label invented
-- here and not a classical citation.  It stands in the EGB field book's
-- template 3 (and again in template 12), verbatim:
--
--     \[\mathcal F_{\xi\eta}=[\nabla_\xi,\nabla_\eta]-\nabla_{[\xi,\eta]},
--       \quad \mathcal F=0\Rightarrow\text{पथाभेद}.\]
--
-- recorded in
--   collab/upstream/raw/2026-08-16-packages/EGB_COMPREHENSIVE_INDEX_V3_PACKAGE/
--     EGB_REPETITION_STRUCTURE_REVERIFY_V3.json (absent from this repository)
--   artifact_150 = ETERNAL_GOLDEN_BRAID_100K_FIELD_BOOK_DELTA_36_2026-08-14.md (absent from this repository)
--   (312,254 bytes, sha256 bdd0144…596bc5, 450 numbered diamonds,
--    template_cycle_length 24), templates "3" and "12".
--
-- CLAUDE.md (absent from this repository)'s file-naming rule, note 2: where the mathematics originates
-- elsewhere, say so rather than invent a  label.  So: the
-- mathematics below originates with THIS REPOSITORY'S OWNER, in
--   collab/upstream/raw/D0025-eternal-golden-braid-indras-net.txt (absent from this repository)
--   collab/upstream/raw/D0026-owner-egb-core-transmission-v2-2026-08-16.md (absent from this repository)
-- (D0026 §4.1 "Three independent interface obligations" isolates path
-- coherence C as independent of reconstruction R and descent D), and in
-- the canonical stanza of
--   ETERNAL_GOLDEN_BRAID_KAIROTIC_CRYSTAL_STREAM_2026-08-14.md (absent from this repository)
-- dated 2026-08-14, 5,731,414 bytes, sha256 812b7816…5e5cf5, 169,202
-- lines, 1200 numbered stanzas, unique_normalized_body_count 1.  THAT
-- ARTIFACT IS NOT IN THIS REPOSITORY.  Its canonical body — the stanza
-- repeated 1200 times — survives only inline inside
-- EGB_REPETITION_STRUCTURE_REVERIFY_V3.json (absent from this repository), field `canonical_body`,
-- sha256 09eb9ce9…f91d0.  The two lines this module is about are its
-- first two:
--
--     𝔛_α --T_{αβ}--> 𝔛_β --T_{βγ}--> 𝔛_γ,  Ω_γ = T_{γα} T_{βγ} T_{αβ}
--     Ω_γ = 1 ⇒ planitas,  Ω_γ ≠ 1 ⇒ ℱ_γ ⇝ curvatura ⇝ नवप्रमेयबीजम्
--
-- CONVENTION, stated so nothing is smuggled.  The stanza writes Ω as an
-- operator product read right to left, so it applies T_{αβ} first: it is
-- a loop at 𝔛_α, whatever the subscript.  Below, `Ω tab tbc tca` composes
-- left to right and is an automorphism of A.  Nothing else is read into
-- the subscript.
--
-- WHAT IS CLAIMED OF THE SOURCE: nothing beyond the two displayed lines.
-- The owner writes `Ω_γ = 1 ⇒ planitas` as an implication in one
-- direction and does not assert its converse; this module does not put
-- the converse in his mouth.  It asks what the converse would be worth,
-- and answers.
--
-- WHAT IS CHECKED, in order:
--
--   §2  planitas ⇒ Ω = 1.                                    (theorem)
--   §3  Ω = 1 does NOT imply planitas.  Exact witness on Bool.
--   §4  What Ω = 1 does say: given ANY tab and ANY tbc whatsoever, the
--       closing transport making the triangle flat exists and is unique
--       — `isContr`, the fibre of an equivalence.  So flatness is one
--       equation and constrains the other two transports not at all.
--   §5  THE REFUTATION OF §3.  Every flat triangle is a gauge: one chart
--       seen three ways.  So the §3 witness is a gauge artifact and, by
--       the stanza's own rule (`दोषः यदि gauge-artifact → त्याज्यः`),
--       carries no invariant.
--   §6  What survives instead: the SQUARE.  A four-chart cycle whose
--       holonomy is `not`, hence admits no gauge over any common chart at
--       any universe level — and which contains no triangle to be
--       non-flat.  Add one chord and a non-flat triangle appears at once.
--
-- So the reading `Ω = 1 ⇒ planitas` is not sharp on a triangle for the
-- reason one first reaches for.  On a triangle the implication fails and
-- the failure is empty; the first place holonomy is chart-invariant is
-- the square, which is the stanza's own next display, δ_◊ = h∘f − k∘g.
--
-- PRIOR ART IN THIS REPOSITORY:
--   CycleHolonomy.agda — holonomy of a 3-cycle of equivalences; the
--     trivial cycle is idEquiv, and (not,not,not) on Bool is a NONtrivial
--     witness.  That is the ⇒ direction plus a curvature witness.
--   NaturalMachine/GlobalSmithAtlasFlatness.agda — global charts give
--     transitions obeying the cocycle law and every closed triangle is the
--     identity; closes its holonomy seed negatively.
--   NaturalMachine/TwoLoopNonabelianNetwork.agda,
--   NaturalMachine/PMIncidenceLocalSystem.agda — nontrivial holonomy on a
--     bouquet and on a six-edge cycle.
--   EqualityPramanena_…, EkaparsvaSamvarana_…, MadhyaSamvarana_… — D0026
--     §2.2/§2.4/§2.5, the trefoil law and the closure counterexamples.
-- None of them states the converse, the uniqueness of the closing
-- transport, or the gauge collapse of the triangle counterexample.  Those
-- three are what is new here.
------------------------------------------------------------------------

module Pathabheda_TheTriangleCounterexampleIsPureGaugeAndTheSquareIsNot where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (Iso ; isoToIsEquiv)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; notEquiv ; notnot ; false≢true)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_ ; fst ; snd)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ ℓa ℓb ℓc ℓd : Level

------------------------------------------------------------------------
-- §1  The triangle of charts, its holonomy, and planitas.
--
-- A chart is a type; a transport between charts is an equivalence.  The
-- stanza's Ω is the composite round the triangle.
------------------------------------------------------------------------

Ω : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  → A ≃ B → B ≃ C → C ≃ A → A ≃ A
Ω tab tbc tca = compEquiv tab (compEquiv tbc tca)

-- पथाभेद: the loop is the identity — going round changes nothing.
Flat : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
     → A ≃ B → B ≃ C → C ≃ A → Type ℓa
Flat {A = A} tab tbc tca = Ω tab tbc tca ≡ idEquiv A

-- planitas in the naive reading: each transport is itself the identity.
-- This is only statable when the three carriers coincide, which is
-- exactly why it is the wrong reading; §5 gives the right one.
Planitas : {A : Type ℓa} → A ≃ A → A ≃ A → A ≃ A → Type ℓa
Planitas {A = A} tab tbc tca =
  (tab ≡ idEquiv A) × ((tbc ≡ idEquiv A) × (tca ≡ idEquiv A))

------------------------------------------------------------------------
-- §2  planitas ⇒ Ω = 1.  The direction the stanza states.
------------------------------------------------------------------------

planitas→flat : {A : Type ℓa} (tab tbc tca : A ≃ A)
              → Planitas tab tbc tca → Flat tab tbc tca
planitas→flat tab tbc tca (p , q , r) =
  (λ i → Ω (p i) (q i) (r i)) ∙ equivEq refl

------------------------------------------------------------------------
-- §3  The converse is FALSE, and here is the witness.
--
--   T_{αβ} = not,  T_{βγ} = not,  T_{γα} = 1.
--
-- The loop is flat because `not` is an involution; the first transport is
-- provably not the identity because it moves `true`.
------------------------------------------------------------------------

flatWitness : Flat notEquiv notEquiv (idEquiv Bool)
flatWitness = equivEq (funExt notnot)

notEquiv≢idEquiv : ¬ (notEquiv ≡ idEquiv Bool)
notEquiv≢idEquiv p = false≢true (cong (λ e → e .fst true) p)

flat↛planitas :
  Σ[ tab ∈ Bool ≃ Bool ] Σ[ tbc ∈ Bool ≃ Bool ] Σ[ tca ∈ Bool ≃ Bool ]
    (Flat tab tbc tca × (¬ Planitas tab tbc tca))
flat↛planitas =
  notEquiv , notEquiv , idEquiv Bool ,
  flatWitness ,
  λ pl → notEquiv≢idEquiv (pl .fst)

------------------------------------------------------------------------
-- §4  What Ω = 1 DOES say, exactly.
--
-- Fix any two transports whatsoever.  Closing the triangle flatly is
-- then possible in exactly one way: the type of flat closures is
-- contractible, being the fibre of an equivalence.  Two consequences,
-- both sharper than §3:
--
--   * flatness is ONE equation, and it is an equation on the THIRD
--     transport only;
--   * every pair (tab , tbc), however wild, extends to a flat triangle.
--     So flatness places no condition at all on the first two charts,
--     and "Ω = 1 ⇒ planitas" fails for a reason that has nothing to do
--     with Bool.
------------------------------------------------------------------------

module _ {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
         (tab : A ≃ B) (tbc : B ≃ C) where

  private
    w : A ≃ C
    w = compEquiv tab tbc

  -- Closing the triangle, as a map on the third transport.
  close : (C ≃ A) → (A ≃ A)
  close e = Ω tab tbc e

  closeIso : Iso (C ≃ A) (A ≃ A)
  Iso.fun closeIso = close
  Iso.inv closeIso h = compEquiv (invEquiv w) h
  Iso.rightInv closeIso h = equivEq (funExt λ a → cong (h .fst) (retEq w a))
  Iso.leftInv  closeIso e = equivEq (funExt λ c → cong (e .fst) (secEq w c))

  -- The flat closure exists …
  flatClosure : C ≃ A
  flatClosure = invEquiv w

  flatClosureIsFlat : Flat tab tbc flatClosure
  flatClosureIsFlat = equivEq (funExt λ a → retEq w a)

  -- … and it is the only one.
  flatClosureIsContr : isContr (Σ[ tca ∈ (C ≃ A) ] (Flat tab tbc tca))
  flatClosureIsContr = equiv-proof (isoToIsEquiv closeIso) (idEquiv A)

-- Read off: ANY pair of transports extends to a flat triangle.
everyPairExtendsFlatly :
  {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  (tab : A ≃ B) (tbc : B ≃ C)
  → Σ[ tca ∈ (C ≃ A) ] (Flat tab tbc tca)
everyPairExtendsFlatly tab tbc = flatClosure tab tbc , flatClosureIsFlat tab tbc

------------------------------------------------------------------------
-- §5  THE REFUTATION: every flat triangle is a gauge.
--
-- A tempting reading of §3 and §4: that `Ω = 1 → planitas`
-- is false in a way that carries content — that flat-but-not-agreeing is
-- a real phenomenon on the triangle, and the Bool witness exhibits it.
--
-- THE CHECK THAT KILLS IT.  Say a triangle is a GAUGE when there is one
-- chart G and three views ψa : G ≃ A, ψb : G ≃ B, ψc : G ≃ C for which
-- each transport is the comparison of consecutive views.  This is the
-- non-naive reading of planitas: it is statable for three genuinely
-- different carriers, and planitas is its special case G = A = B = C with
-- all views the identity.
--
-- Then: gauge ⇔ flat.  Every flat triangle is a gauge (`flat→gauge`), and
-- every gauge is flat (`gauge→flat`).  So the §3 witness is a gauge, the
-- disagreement it displays is a choice of view and not a property of the
-- family, and by the stanza's own criterion —
--   दोषः यदि gauge-artifact → त्याज्यः; यदि chart-invariant →
--   curvature-candidate
--   ("a defect, if a gauge artifact, is to be discarded; if
--    chart-invariant, a curvature candidate")
-- it is to be discarded.  §3 stands as a theorem and
-- is worth nothing as a phenomenon.
------------------------------------------------------------------------

IsGauge3 : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} {G : Type ℓ}
         → A ≃ B → B ≃ C → C ≃ A
         → G ≃ A → G ≃ B → G ≃ C → Type _
IsGauge3 tab tbc tca ψa ψb ψc =
  (compEquiv ψa tab ≡ ψb) × ((compEquiv ψb tbc ≡ ψc) × (compEquiv ψc tca ≡ ψa))

-- Every flat triangle is a gauge, with the common chart taken to be A
-- itself and the views read off the transports.
flat→gauge : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
             (tab : A ≃ B) (tbc : B ≃ C) (tca : C ≃ A)
           → Flat tab tbc tca
           → Σ[ ψa ∈ (A ≃ A) ] Σ[ ψb ∈ (A ≃ B) ] Σ[ ψc ∈ (A ≃ C) ]
               IsGauge3 tab tbc tca ψa ψb ψc
flat→gauge {A = A} tab tbc tca fl =
  idEquiv A ,
  compEquiv (idEquiv A) tab ,
  compEquiv (compEquiv (idEquiv A) tab) tbc ,
  refl , refl , equivEq (cong fst fl)

-- … and conversely.  So the two notions coincide on a triangle.
gauge→flat : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} {G : Type ℓ}
             (tab : A ≃ B) (tbc : B ≃ C) (tca : C ≃ A)
             (ψa : G ≃ A) (ψb : G ≃ B) (ψc : G ≃ C)
           → IsGauge3 tab tbc tca ψa ψb ψc
           → Flat tab tbc tca
gauge→flat tab tbc tca ψa ψb ψc (p , q , r) = equivEq (funExt pointwise)
  where
    onImage : ∀ g → tca .fst (tbc .fst (tab .fst (ψa .fst g))) ≡ ψa .fst g
    onImage g =
        cong (λ z → tca .fst (tbc .fst z)) (cong (λ e → e .fst g) p)
      ∙ cong (λ z → tca .fst z)            (cong (λ e → e .fst g) q)
      ∙ cong (λ e → e .fst g) r

    pointwise : ∀ a → Ω tab tbc tca .fst a ≡ a
    pointwise a =
        cong (λ z → tca .fst (tbc .fst (tab .fst z))) (sym (secEq ψa a))
      ∙ onImage (invEq ψa a)
      ∙ secEq ψa a

-- The §3 witness, therefore, is a gauge.
witnessIsGauge :
  Σ[ ψa ∈ (Bool ≃ Bool) ] Σ[ ψb ∈ (Bool ≃ Bool) ] Σ[ ψc ∈ (Bool ≃ Bool) ]
    IsGauge3 notEquiv notEquiv (idEquiv Bool) ψa ψb ψc
witnessIsGauge = flat→gauge notEquiv notEquiv (idEquiv Bool) flatWitness

------------------------------------------------------------------------
-- §6  What survives the refutation: the square.
--
-- The stanza's next display is the square and its defect
-- δ_◊ = h∘f − k∘g.  That is where the implication acquires content: a
-- four-chart cycle can have nontrivial holonomy, and then NO common chart
-- exists — over any G, at any universe level.  And the cycle has no
-- triangle in it at all, so "every triangle is flat" is satisfied while
-- the family is not a gauge.
------------------------------------------------------------------------

Hol4 : {X₀ : Type ℓa} {X₁ : Type ℓb} {X₂ : Type ℓc} {X₃ : Type ℓd}
     → X₀ ≃ X₁ → X₁ ≃ X₂ → X₂ ≃ X₃ → X₃ ≃ X₀ → X₀ ≃ X₀
Hol4 t₀₁ t₁₂ t₂₃ t₃₀ = compEquiv t₀₁ (compEquiv t₁₂ (compEquiv t₂₃ t₃₀))

IsGauge4 : {X₀ : Type ℓa} {X₁ : Type ℓb} {X₂ : Type ℓc} {X₃ : Type ℓd}
           {G : Type ℓ}
         → X₀ ≃ X₁ → X₁ ≃ X₂ → X₂ ≃ X₃ → X₃ ≃ X₀
         → G ≃ X₀ → G ≃ X₁ → G ≃ X₂ → G ≃ X₃ → Type _
IsGauge4 t₀₁ t₁₂ t₂₃ t₃₀ ψ₀ ψ₁ ψ₂ ψ₃ =
    (compEquiv ψ₀ t₀₁ ≡ ψ₁)
  × ((compEquiv ψ₁ t₁₂ ≡ ψ₂)
  × ((compEquiv ψ₂ t₂₃ ≡ ψ₃) × (compEquiv ψ₃ t₃₀ ≡ ψ₀)))

gauge4→flat : {X₀ : Type ℓa} {X₁ : Type ℓb} {X₂ : Type ℓc} {X₃ : Type ℓd}
              {G : Type ℓ}
              (t₀₁ : X₀ ≃ X₁) (t₁₂ : X₁ ≃ X₂) (t₂₃ : X₂ ≃ X₃) (t₃₀ : X₃ ≃ X₀)
              (ψ₀ : G ≃ X₀) (ψ₁ : G ≃ X₁) (ψ₂ : G ≃ X₂) (ψ₃ : G ≃ X₃)
            → IsGauge4 t₀₁ t₁₂ t₂₃ t₃₀ ψ₀ ψ₁ ψ₂ ψ₃
            → Hol4 t₀₁ t₁₂ t₂₃ t₃₀ ≡ idEquiv X₀
gauge4→flat t₀₁ t₁₂ t₂₃ t₃₀ ψ₀ ψ₁ ψ₂ ψ₃ (p , q , r , s) =
  equivEq (funExt pointwise)
  where
    onImage : ∀ g → t₃₀ .fst (t₂₃ .fst (t₁₂ .fst (t₀₁ .fst (ψ₀ .fst g))))
                    ≡ ψ₀ .fst g
    onImage g =
        cong (λ z → t₃₀ .fst (t₂₃ .fst (t₁₂ .fst z))) (cong (λ e → e .fst g) p)
      ∙ cong (λ z → t₃₀ .fst (t₂₃ .fst z))            (cong (λ e → e .fst g) q)
      ∙ cong (λ z → t₃₀ .fst z)                       (cong (λ e → e .fst g) r)
      ∙ cong (λ e → e .fst g) s

    pointwise : ∀ x → Hol4 t₀₁ t₁₂ t₂₃ t₃₀ .fst x ≡ x
    pointwise x =
        cong (λ z → t₃₀ .fst (t₂₃ .fst (t₁₂ .fst (t₀₁ .fst z))))
             (sym (secEq ψ₀ x))
      ∙ onImage (invEq ψ₀ x)
      ∙ secEq ψ₀ x

-- The square that has no common chart: three identities and one flip.
sqHol : Bool ≃ Bool
sqHol = Hol4 notEquiv (idEquiv Bool) (idEquiv Bool) (idEquiv Bool)

sqHolIsNot : ∀ b → sqHol .fst b ≡ not b
sqHolIsNot b = refl

sqHolNontrivial : ¬ (sqHol ≡ idEquiv Bool)
sqHolNontrivial p = false≢true (cong (λ e → e .fst true) p)

-- Hence: no common chart, over ANY carrier at ANY universe level.
squareHasNoGauge :
  {G : Type ℓ} (ψ₀ ψ₁ ψ₂ ψ₃ : G ≃ Bool)
  → IsGauge4 notEquiv (idEquiv Bool) (idEquiv Bool) (idEquiv Bool)
             ψ₀ ψ₁ ψ₂ ψ₃
  → ⊥
squareHasNoGauge ψ₀ ψ₁ ψ₂ ψ₃ g =
  sqHolNontrivial
    (gauge4→flat notEquiv (idEquiv Bool) (idEquiv Bool) (idEquiv Bool)
                 ψ₀ ψ₁ ψ₂ ψ₃ g)

------------------------------------------------------------------------
-- §6b  And the square really is the first place this happens: add one
-- chord to the cycle and a non-flat TRIANGLE appears immediately.
--
-- Chord X₀ ≃ X₂ taken to be the composite t₀₁ ; t₁₂.  Then the triangle
-- (0,1,2) is flat by §4 — the chord's inverse is its unique flat closure
-- — while the triangle (0,2,3) is not.  So the hypothesis "every triangle
-- in the family is flat" does all the work in that reading, and it
-- is available only because the bare 4-cycle carries no 2-cell.
------------------------------------------------------------------------

chord : Bool ≃ Bool
chord = compEquiv notEquiv (idEquiv Bool)

tri012Flat : Flat notEquiv (idEquiv Bool) (invEquiv chord)
tri012Flat = flatClosureIsFlat notEquiv (idEquiv Bool)

tri023NotFlat : ¬ (Flat chord (idEquiv Bool) (idEquiv Bool))
tri023NotFlat p = false≢true (cong (λ e → e .fst true) p)
