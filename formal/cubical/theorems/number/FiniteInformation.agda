{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FiniteInformation
--
-- The finite-information kernel for observer / side-information
-- arguments, checked in Cubical Agda.
--
-- Rank-3 port of the Lean development `formal/lean/Pairfield/
-- FiniteInformation.lean` (130 lines), per the spec in
-- deliberately distribution-free: no probability law is chosen, the
-- content is factorization through an observable and exact
-- reconstruction after adding side data.
--
-- WHAT THE PORT BUYS: the Lean file opens `classical` in two theorems
-- (`factorsThrough_iff_fiberConstant` ←, and `targetFiber_injects_side`),
-- with three `Classical.choose` call sites between them.
-- Here `Set.range q` is the univalent image `Cubical.Functions.Image`
-- (`Image q = Σ[ y ∈ Y ] ∥ fiber q y ∥₁`) and the descent direction is
-- `PT.rec→Set` — elimination of `∥_∥₁` into a SET along a 2-Constant
-- family.  The first choice therefore disappears outright: the decoder
-- is CONSTRUCTED, and its computation rule `decode (restrictToImage q x)
-- ≡ t x` is `refl`, not a lemma.  The hypothesis paid for it is `isSet T`,
-- which is strictly weaker than choice.
--
------------------------------------------------------------------------
-- ⚠ REQUIRED DISCLOSURE — THE ONE RESTATED LEAN STATEMENT
------------------------------------------------------------------------
--
-- Lean `targetFiber_injects_side` is NOT ported in its literal form,
-- and no theorem below carries that name silently weakened.  The Lean
-- statement is
--
--     (decode : Y → C → T) (hdecode : ∀ x, decode (q x) (c x) = t x)
--     (y : Y) → ∃ encode : TargetFiber q t y → C, Injective encode
--
-- where `TargetFiber q t y = {v : T // ∃ x, q x = y ∧ t x = v}`.
--
-- Why the literal form is unavailable constructively.  To BUILD
-- `encode` one must turn the merely-existing witness `∃ x, q x = y ∧
-- t x = v` carried by an element of `TargetFiber` into an actual `x`,
-- and then return `c x`.  That is an escape from `∥_∥₁` into `C`, and
-- the only choice-free escape into a non-proposition is `rec→Set`,
-- which demands the eliminated family be 2-Constant.  Here it is NOT:
-- two witnesses `x , x'` for the SAME target value `v` in the same
-- fiber satisfy `decode y (c x) ≡ v ≡ decode y (c x')`, but nothing
-- forces `c x ≡ c x'` — `decode y` need not be injective, and `C`
-- carries no structure at all.  So the map `v ↦ c (witness v)` is
-- genuinely un-definable without choice; Lean's `Classical.choose` is
-- doing real work, not bookkeeping.  (`isSet C` would not help: the
-- obstruction is 2-constancy, not h-level.)
--
-- What is proved instead, per the port map, is the SURJECTION out of C
-- that carries the same cardinality content `|C| ≥ |t(q⁻¹ y)|`:
--
--     SideUsed y = Σ[ k ∈ C ] ∥ Σ[ x ∈ X ] (q x ≡ y) × (c x ≡ k) ∥₁
--     sideUsed↪C           : SideUsed y ↪ C
--     sideUsed↠targetFiber : SideUsed y ↠ TargetFiber q t y
--
-- Both directions of the sandwich are choice-free.  Their quantitative
-- consequence is proved outright (delta, strengthening the map's spec,
-- which left it as a remark): `targetFiber-card≤` gives
-- `card (TargetFiber q t y) ≤ card C` for finite side alphabets — i.e.
-- exactly the numerical statement Lean's injection was a proxy for.
--
-- And the literal Lean statement is recorded honestly as
-- `targetFiber-injects-side-given-choice`, whose extra hypothesis
--
--     pick : (u : TargetFiber q t y) → Σ[ x ∈ X ] (q x ≡ y) × (t x ≡ fst u)
--
-- IS `Classical.choose` for this family, made visible.  Its proof is
-- the Lean calc block transcribed.  So: `Classical.choice` is fully
-- eliminated from every *theorem* of this module; where Lean used it,
-- it appears as a named hypothesis of one clearly-marked statement, and
-- the choice-free replacement is proved beside it.
--
------------------------------------------------------------------------
-- Signature ledger (Lean name → this module)
--
--   FactorsThrough  (Set.range)         → FactorsThrough (Image)
--   —  (Lean: it is a Prop by fiat)     → isPropFactorsThrough (a THEOREM
--                                         here, given isSet T)
--   factorsThrough_iff_fiberConstant    → factorsThrough→fiberConstant,
--                                         fiberConstant→factorsThrough,
--                                         factorsThroughIsoFiberConstant
--   —  (unstated in Lean)               → decode-restrict (= refl)
--   Completes (Function.Injective)      → Completes
--   completes_iff_separatesFibers       → completes→separates,
--                                         separates→completes,
--                                         completesIsoSeparates
--   completes_of_injective              → completes-of-injective
--   completes_mono                      → completes-mono, separates-mono
--   factorsThrough_postprocess          → fiberConstant-postprocess,
--                                         factorsThrough-postprocess
--   TargetFiber                         → TargetFiber
--   targetFiber_injects_side            → RESTATED, see above:
--                                         sideUsed↠targetFiber
--                                         (+ decode-covers-fiber,
--                                          targetFiber-card≤,
--                                          targetFiber-injects-side-given-choice)
--
-- Deltas against the port-map spec (§3.3):
--   * The map offered "an Iso, or the two maps".  Both are delivered:
--     the two maps are the content, and the Iso is available because
--     BOTH sides are propositions when T is a set — isPropFactorsThrough
--     is proved (Lean gets it free by putting FactorsThrough in Prop,
--     which is exactly what makes the Lean decoder unusable as data).
--   * `Completes` is kept in Lean's own form (injectivity of the pair
--     map) with the fiber-separation form as a separate definition and
--     an Iso between them, rather than defining Completes to BE the
--     separation form; that keeps `completes_iff_separatesFibers` a
--     theorem instead of silently deleting it.
--   * `factorsThrough-postprocess` is stated on FactorsThrough itself
--     (Lean's form, needing isSet T for the round trip) as well as on
--     FiberConstant (the map's form, hypothesis-free).
--   * The cardinality corollary the map left as a parenthetical is
--     proved (`targetFiber-card≤`).
--   * v0.5 skew: `isEmbeddingFstΣProp` (Cubical.Data.Sigma.Properties)
--     is stated POINTWISE — `{u v : Σ A B} → isEquiv (cong fst)` — not
--     as `isEmbedding fst`, so `sideUsed↪C` wraps it in `λ _ _ →`.
--     Reapply the inverse if cubical is upgraded (cf. BUILD.md (absent from this repository)).
--
-- LINE-COUNT LEDGER.
-- The map's §1(b) criterion is "the Cubical port is shorter".  For this
-- file that prediction is FALSE:
--   Lean   130 lines total,  95 non-comment.
--   Agda   446 lines total, 206 non-comment (≈120 of the total is this
--                                            header/disclosure block).
-- Attribution of the 206, by declaration:
--   ≈107  the eight Lean statements, one for one — PAR with Lean's 95,
--         the +13% being explicit universe and type binders on every
--         signature where Lean auto-bounds `u v w z`.
--   ≈ 75  statements with NO Lean counterpart: decode-restrict,
--         isPropFiberConstant, isPropFactorsThrough (+ agree),
--         factorsThroughIsoFiberConstant, fiberConstant-postprocess,
--         SeparatesFibers + completesIsoSeparates + separates-mono,
--         decode-covers-fiber, targetFiber-card≤.
--   ≈ 24  targetFiber-injects-side-given-choice: the Lean theorem kept
--         verbatim beside its choice-free replacement, which is a cost
--         the map did not budget for and which honesty requires.
-- So the profit here is exactly the qualitative one the map's §2 ranking
-- already predicted ("the port deletes Classical.choice"), plus the
-- isProp/Iso/cardinality layer — not brevity.
--
-- No holes, no postulates, --safe.  The only ∥_∥₁-escapes in the file
-- are `PT.rec→Set` (once), `PT.rec` into propositions, and `PT.map` —
-- i.e. the port-map success test holds.
------------------------------------------------------------------------

module FiniteInformation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; 2-Constant)
open import Cubical.Foundations.HLevels using (isPropΠ ; isPropΠ3)
open import Cubical.Foundations.Isomorphism using (Iso ; iso)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-trans)
open import Cubical.Data.FinSet using (FinSet ; isFinSet ; card)
open import Cubical.Data.FinSet.Cardinality using (card↪Inequality' ; card↠Inequality')
open import Cubical.Functions.Image
  using (Image ; isInImage ; isPropIsInImage ; restrictToImage)
open import Cubical.Functions.Embedding using (_↪_)
open import Cubical.Functions.Surjection using (isSurjection ; _↠_)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc ; rec→Set)

private
  variable
    ℓx ℓy ℓz ℓt ℓc ℓd : Level

------------------------------------------------------------------------
-- 1.  Descent through an observable
--
-- A target `t` descends through an observable `q` when it is a function
-- of the observed value alone.  Lean uses `Set.range q` "to avoid an
-- arbitrary default on unobservable values"; the univalent `Image` does
-- the same job and, being a Σ over a PROPOSITION, has the additional
-- property that its paths are paths in Y (Σ≡Prop below).
------------------------------------------------------------------------

FactorsThrough : {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
               → (q : X → Y) (t : X → T) → Type (ℓ-max (ℓ-max ℓx ℓy) ℓt)
FactorsThrough {X = X} {T = T} q t =
  Σ[ decode ∈ (Image q → T) ] ((x : X) → decode (restrictToImage q x) ≡ t x)

FiberConstant : {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
              → (q : X → Y) (t : X → T) → Type (ℓ-max (ℓ-max ℓx ℓy) ℓt)
FiberConstant {X = X} q t = (x x' : X) → q x ≡ q x' → t x ≡ t x'

-- Two states with the same observation name the same point of the image.
sameObservation→samePoint :
  {X : Type ℓx} {Y : Type ℓy} (q : X → Y) {x x' : X}
  → q x ≡ q x' → restrictToImage q x ≡ restrictToImage q x'
sameObservation→samePoint q p = Σ≡Prop (isPropIsInImage q) p

-- Lean: factorsThrough_iff_fiberConstant, forward direction.
factorsThrough→fiberConstant :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (q : X → Y) (t : X → T) → FactorsThrough q t → FiberConstant q t
factorsThrough→fiberConstant q t (decode , replay) x x' p =
  sym (replay x) ∙∙ cong decode (sameObservation→samePoint q p) ∙∙ replay x'

-- Lean: factorsThrough_iff_fiberConstant, backward direction.  This is
-- the one that used `Classical.choose`; here it is `PT.rec→Set` on the
-- mere fiber witness, with the 2-Constant proof supplied by fiber
-- constancy itself.  Hypothesis traded: choice ↦ isSet T.
fiberConstant→factorsThrough :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (isSetT : isSet T) (q : X → Y) (t : X → T)
  → FiberConstant q t → FactorsThrough q t
fiberConstant→factorsThrough {X = X} {T = T} isSetT q t fc = decode , λ _ → refl
  where
    kf : (y : _) → 2-Constant {A = Σ[ x ∈ X ] (q x ≡ y)} (λ u → t (fst u))
    kf y u v = fc (fst u) (fst v) (snd u ∙ sym (snd v))

    decode : Image q → T
    decode (y , w) = rec→Set isSetT (λ u → t (fst u)) (kf y) w

-- The computation rule is DEFINITIONAL — in Lean it is the second
-- component of the existential, discharged by `apply hfiber`.
decode-restrict :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (isSetT : isSet T) (q : X → Y) (t : X → T)
  (fc : FiberConstant q t) (x : X)
  → fst (fiberConstant→factorsThrough isSetT q t fc) (restrictToImage q x) ≡ t x
decode-restrict isSetT q t fc x = refl

-- Both sides are propositions once T is a set.  For FiberConstant that
-- is immediate; for FactorsThrough it is a theorem: `restrictToImage q`
-- is surjective, so a decoder is pinned down by its values on states.
isPropFiberConstant :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (isSetT : isSet T) (q : X → Y) (t : X → T) → isProp (FiberConstant q t)
isPropFiberConstant isSetT q t = isPropΠ3 (λ _ _ _ → isSetT _ _)

isPropFactorsThrough :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (isSetT : isSet T) (q : X → Y) (t : X → T) → isProp (FactorsThrough q t)
isPropFactorsThrough isSetT q t (d₁ , h₁) (d₂ , h₂) =
  Σ≡Prop (λ _ → isPropΠ (λ _ → isSetT _ _)) (funExt agree)
  where
    agree : (im : Image q) → d₁ im ≡ d₂ im
    agree (y , w) =
      PT.rec (isSetT _ _)
        (λ u →
          let p : (y , w) ≡ restrictToImage q (fst u)
              p = Σ≡Prop (isPropIsInImage q) (sym (snd u))
          in cong d₁ p ∙∙ (h₁ (fst u) ∙ sym (h₂ (fst u))) ∙∙ cong d₂ (sym p))
        w

-- Lean: factorsThrough_iff_fiberConstant, as one object.
factorsThroughIsoFiberConstant :
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
  (isSetT : isSet T) (q : X → Y) (t : X → T)
  → Iso (FactorsThrough q t) (FiberConstant q t)
factorsThroughIsoFiberConstant isSetT q t = iso
  (factorsThrough→fiberConstant q t)
  (fiberConstant→factorsThrough isSetT q t)
  (λ fc → isPropFiberConstant isSetT q t _ fc)
  (λ ft → isPropFactorsThrough isSetT q t _ ft)

------------------------------------------------------------------------
-- 2.  Data processing: a coarser observable descends less
------------------------------------------------------------------------

-- Lean: factorsThrough_postprocess, stated on the fiber-constancy side
-- (hypothesis-free, one `cong`).
fiberConstant-postprocess :
  {X : Type ℓx} {Y : Type ℓy} {Z : Type ℓz} {T : Type ℓt}
  (q : X → Y) (r : Y → Z) (t : X → T)
  → FiberConstant (r ∘ q) t → FiberConstant q t
fiberConstant-postprocess q r t h x x' p = h x x' (cong r p)

-- Lean's own form, on FactorsThrough, via the round trip.
factorsThrough-postprocess :
  {X : Type ℓx} {Y : Type ℓy} {Z : Type ℓz} {T : Type ℓt}
  (isSetT : isSet T) (q : X → Y) (r : Y → Z) (t : X → T)
  → FactorsThrough (r ∘ q) t → FactorsThrough q t
factorsThrough-postprocess isSetT q r t h =
  fiberConstant→factorsThrough isSetT q t
    (fiberConstant-postprocess q r t
      (factorsThrough→fiberConstant (r ∘ q) t h))

------------------------------------------------------------------------
-- 3.  Side information and exact reconstruction
--
-- Lean defines `Completes q c := Function.Injective fun x => (q x, c x)`
-- and proves it equivalent to fiberwise separation.  Both forms are kept
-- here so that `completes_iff_separatesFibers` remains a theorem.
------------------------------------------------------------------------

Completes : {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc}
          → (q : X → Y) (c : X → C) → Type (ℓ-max (ℓ-max ℓx ℓy) ℓc)
Completes {X = X} q c = (x x' : X) → ((q x , c x) ≡ (q x' , c x')) → x ≡ x'

SeparatesFibers : {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc}
                → (q : X → Y) (c : X → C) → Type (ℓ-max (ℓ-max ℓx ℓy) ℓc)
SeparatesFibers {X = X} q c = (x x' : X) → q x ≡ q x' → c x ≡ c x' → x ≡ x'

completes→separates :
  {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc}
  (q : X → Y) (c : X → C) → Completes q c → SeparatesFibers q c
completes→separates q c h x x' p r = h x x' (ΣPathP (p , r))

separates→completes :
  {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc}
  (q : X → Y) (c : X → C) → SeparatesFibers q c → Completes q c
separates→completes q c h x x' p = h x x' (cong fst p) (cong snd p)

-- Both are propositions as soon as X is a set, so the equivalence of
-- the two formulations is an Iso.
completesIsoSeparates :
  {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc}
  (isSetX : isSet X) (q : X → Y) (c : X → C)
  → Iso (Completes q c) (SeparatesFibers q c)
completesIsoSeparates isSetX q c = iso
  (completes→separates q c)
  (separates→completes q c)
  (λ h → isPropΠ3 (λ _ _ _ → isPropΠ (λ _ → isSetX _ _)) _ h)
  (λ h → isPropΠ3 (λ _ _ _ → isSetX _ _) _ h)

-- Lean: completes_of_injective.  If q is already injective, no side
-- information is needed.
completes-of-injective :
  {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc}
  {q : X → Y} → ((x x' : X) → q x ≡ q x' → x ≡ x')
  → (c : X → C) → Completes q c
completes-of-injective inj c x x' p = inj x x' (cong fst p)

-- Lean: completes_mono.  Exact reconstruction is stable under adding
-- more side information.
completes-mono :
  {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc} {D : Type ℓd}
  (q : X → Y) (c : X → C) (d : X → D)
  → Completes q c → Completes q (λ x → (c x , d x))
completes-mono q c d h x x' p =
  h x x' (ΣPathP (cong fst p , cong (λ u → fst (snd u)) p))

separates-mono :
  {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc} {D : Type ℓd}
  (q : X → Y) (c : X → C) (d : X → D)
  → SeparatesFibers q c → SeparatesFibers q (λ x → (c x , d x))
separates-mono q c d h x x' p r = h x x' p (cong fst r)

------------------------------------------------------------------------
-- 4.  The target values alive inside one observer fiber
--
-- Lean: `TargetFiber q t y = {v : T // ∃ x, q x = y ∧ t x = v}`.  Note
-- this is literally `Image` of `t` restricted to the fiber of q over y,
-- so it is a Σ over a proposition, exactly as in Lean's subtype.
------------------------------------------------------------------------

TargetFiber : {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt}
            → (q : X → Y) (t : X → T) (y : Y) → Type (ℓ-max (ℓ-max ℓx ℓy) ℓt)
TargetFiber {X = X} {T = T} q t y =
  Σ[ v ∈ T ] ∥ Σ[ x ∈ X ] ((q x ≡ y) × (t x ≡ v)) ∥₁

------------------------------------------------------------------------
-- 5.  The zero-error side-information bound
--
-- Setting: an observer sees `q x`, a helper sends `c x`, and a decoder
-- `decode` must reproduce `t x` exactly (`replay`).  This is the
-- distribution-free core of `|C| ≥ max_y |t(q⁻¹ y)|`.
--
-- See the disclosure at the top of the file: Lean's injection
-- `TargetFiber ↪ C` is choice-shaped; the choice-free content is the
-- sandwich  C ↩ SideUsed ↠ TargetFiber.
------------------------------------------------------------------------

module SideInformation
  {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt} {C : Type ℓc}
  (q : X → Y) (t : X → T) (c : X → C)
  (decode : Y → C → T)
  (replay : (x : X) → decode (q x) (c x) ≡ t x)
  where

  -- The side letters actually realized inside the fiber over y.  A
  -- subtype of C, and no more than a subtype: the second component is
  -- a proposition, so nothing has been added to C.
  SideUsed : Y → Type (ℓ-max (ℓ-max ℓx ℓy) ℓc)
  SideUsed y = Σ[ k ∈ C ] ∥ Σ[ x ∈ X ] ((q x ≡ y) × (c x ≡ k)) ∥₁

  sideUsed↪C : (y : Y) → SideUsed y ↪ C
  -- (v0.5 skew: `isEmbeddingFstΣProp` is stated pointwise, with the two
  -- endpoints implicit, rather than as `isEmbedding fst`.)
  sideUsed↪C y = fst , λ _ _ → isEmbeddingFstΣProp (λ _ → isPropPropTrunc)

  -- The decoder, read on the letters that occur, lands in the target
  -- fiber.
  sideDecode : (y : Y) → SideUsed y → TargetFiber q t y
  sideDecode y (k , w) =
    decode y k , PT.map (λ u → fst u , (fst (snd u) , hit u)) w
    where
      hit : (u : Σ[ x ∈ X ] ((q x ≡ y) × (c x ≡ k))) → t (fst u) ≡ decode y k
      hit u = sym (replay (fst u)) ∙ cong₂ decode (fst (snd u)) (snd (snd u))

  -- … and it hits every target value in the fiber.  This is the honest
  -- replacement for Lean's `targetFiber_injects_side`.
  sideDecode-isSurjection : (y : Y) → isSurjection (sideDecode y)
  sideDecode-isSurjection y (v , w) =
    PT.rec isPropPropTrunc
      (λ u →
        ∣ (c (fst u) , ∣ fst u , (fst (snd u) , refl) ∣₁)
        , Σ≡Prop (λ _ → isPropPropTrunc)
            (sym (cong₂ decode (fst (snd u)) (refl {x = c (fst u)}))
              ∙∙ replay (fst u) ∙∙ snd (snd u)) ∣₁)
      w

  sideUsed↠targetFiber : (y : Y) → SideUsed y ↠ TargetFiber q t y
  sideUsed↠targetFiber y = sideDecode y , sideDecode-isSurjection y

  -- The port map's literal §3.3 statement, `decode-covers-fiber`: every
  -- value alive in a fiber is named by some side letter.  (It is the
  -- surjection above, forgetting which letters are realized.)
  decode-covers-fiber :
    (y : Y) (v : T)
    → ∥ Σ[ x ∈ X ] ((q x ≡ y) × (t x ≡ v)) ∥₁
    → ∥ Σ[ k ∈ C ] (decode y k ≡ v) ∥₁
  decode-covers-fiber y v =
    PT.map (λ u → c (fst u)
      , (sym (cong₂ decode (fst (snd u)) (refl {x = c (fst u)}))
          ∙∙ replay (fst u) ∙∙ snd (snd u)))

  -- The quantitative content Lean's injection was a proxy for, proved
  -- rather than remarked: for finite alphabets, the side alphabet is at
  -- least as large as any single observer fiber's target set.
  targetFiber-card≤ :
    (y : Y)
    (finSide : isFinSet (SideUsed y))
    (finFiber : isFinSet (TargetFiber q t y))
    (finC : isFinSet C)
    → card (TargetFiber q t y , finFiber) ≤ card (C , finC)
  targetFiber-card≤ y finSide finFiber finC =
    ≤-trans
      (card↠Inequality' (SideUsed y , finSide) (TargetFiber q t y , finFiber)
        (sideDecode y) (sideDecode-isSurjection y))
      (card↪Inequality' (SideUsed y , finSide) (C , finC)
        (fst (sideUsed↪C y)) (snd (sideUsed↪C y)))

  -- THE LITERAL LEAN STATEMENT, with the choice it silently performs
  -- promoted to a visible hypothesis.  `pick` IS `Classical.choose` for
  -- this family; supplying it, the Lean proof transcribes verbatim.
  -- Nothing else in this module depends on it.
  targetFiber-injects-side-given-choice :
    (y : Y)
    (pick : (u : TargetFiber q t y) → Σ[ x ∈ X ] ((q x ≡ y) × (t x ≡ fst u)))
    → Σ[ encode ∈ (TargetFiber q t y → C) ]
        ((u v : TargetFiber q t y) → encode u ≡ encode v → u ≡ v)
  targetFiber-injects-side-given-choice y pick = encode , inj
    where
      wit : TargetFiber q t y → X
      wit u = fst (pick u)

      wit-q : (u : TargetFiber q t y) → q (wit u) ≡ y
      wit-q u = fst (snd (pick u))

      wit-t : (u : TargetFiber q t y) → t (wit u) ≡ fst u
      wit-t u = snd (snd (pick u))

      encode : TargetFiber q t y → C
      encode u = c (wit u)

      inj : (u v : TargetFiber q t y) → encode u ≡ encode v → u ≡ v
      inj u v hc = Σ≡Prop (λ _ → isPropPropTrunc)
        ( sym (wit-t u)
        ∙∙ ( sym (replay (wit u))
           ∙∙ cong (λ w → decode w (c (wit u))) (wit-q u)
           ∙∙ cong (decode y) hc )
        ∙∙ ( cong (λ w → decode w (c (wit v))) (sym (wit-q v))
           ∙∙ replay (wit v)
           ∙∙ wit-t v ) )
