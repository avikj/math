{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.PMCokernel
--
-- WHAT THIS PROVES.  `notes/PM_SECTION_VS_COCYCLE.md` (absent from this repository) ends with:
-- "The natural checked target: `coker(δ) ≅ F₂` and the exactness step —
-- pure finite linear algebra over F₂, no matrices over ℤ[i] needed."
-- This module is that target, carried out on the PHYSICAL index sets
-- (the nine observables, the six contexts) and against the derived sign
-- vector `s = (+,+,+ | +,+,−)`, i.e. `s = (0,0,0,0,0,1)` additively:
--
--   (i)   `parity-δ` : the all-ones functional on contexts,
--         `total : F₂⁶ → F₂`, vanishes identically on im δ.  Every
--         element of the image has even total weight, because each
--         observable lies in exactly TWO contexts.
--   (ii)  `total-s : total s ≡ true` — the Peres–Mermin sign vector has
--         ODD total weight; hence `s-not-in-image`, hence
--         `no-global-section`.
--
-- That pair IS the theorem of §1 of the note: the parity functional
-- separates s from the image, so `[s] = 1` in coker δ, and section
-- failure and nonzero class are the same fact seen through exactness.
-- Nothing here is a search: (ii) is one `refl` on a six-term sum, and
-- (i) is an algebraic identity (transposing a 3 × 3 array preserves its
-- total sum) valid for ALL 512 assignments at once.  Contrast
-- `formal/cubical/PMNoSection.agda`, which establishes the same
-- non-existence by a typechecker-run 512-fold exhaustion: same
-- conclusion, no invariant.  Here the invariant is the content, and it
-- is what survives to other scenarios.
--
-- ALSO PROVED (all finite, all as terms):
--
--   * `each-obs-twice : (o : Obs) → occurrences o ≡ 2` — the hypothesis
--     of (i), CHECKED rather than transcribed: membership is computed
--     from `PMTorus.pmContexts` through a certified equality test on
--     contexts (`eqCtx-refl`, `eqCtx-sound`, `inCtx-sound`), so the
--     count counts genuine memberships.
--   * `column-is-incidence : (o : Obs) (c : Ctx) → δ (eqObs o) c ≡
--     inCtx c o` — δ's columns ARE the incidence data, so (i) and
--     `each-obs-twice` are about one map and not two.
--   * `even-total-is-image` / `image-is-even-total` — EXACTNESS, both
--     inclusions: im δ is EXACTLY ker(total).  With `total-onto` this
--     is coker δ ≅ 𝔽₂𝔽₂F with `total` as the class evaluator.
--   * `local-section` — each context separately admits an assignment
--     with the prescribed parity (the obstruction is global, not local).
--   * `rows-only-section` — the rows-only cover admits a global
--     section, so the class is a property of the COVER (note, claim 2).
--     Trivial for this s, and flagged as such: all three row signs are
--     +, so the zero assignment works.
--   * `twisted-sections≃F₂⁴` — flipping the identification of ZZ
--     between its row and its column occurrence (a one-edge
--     local-system twist, `twist`) makes the twisted section set
--     equivalent to `Fin 4 → Bool`: exactly 2⁴ = 16 twisted sections,
--     the note's claim 3, with the count derived from
--     `PMTorus.cycleEquiv` rather than measured.  `kernelIso` is the
--     bridge: ker δ ≃ PMTorus.Cycle.
--
-- (no SetQuotient), exactly as in `PMTorus`; "coker δ ≅ F₂" is
-- delivered in its usable form — im δ = ker total (both inclusions)
-- together with total onto.  The sign vector s enters here as a DATUM,
-- transcribed from the note.  What is proved is
-- everything downstream of s.
--
-- Reuses `NaturalMachine.PMTorus` (same square, same F₂ toolkit, same
-- conventions) and duplicates none of it: PMTorus works on the
-- anonymous graph (Edge = Fin 3 × Fin 3, Vertex = Fin 3 ⊎ Fin 3) and
-- has no sign vector; this module works on Obs/Ctx with the physical
-- signs, and imports the algebra.
--
-- NOT VACUOUS, and the reader can check it in one edit: replacing
-- `s C2 = true` by `s C2 = false` makes `total-s` fail to typecheck
-- (`false != true of type Bool`).  Nothing here would prove an
-- obstruction for an even sign vector — for that s the zero assignment
-- is a global section, by `even-total-is-image`.
--
-- TOOLCHAIN CAVEAT (Agda 2.6.3 / cubical v0.5), the same one PMTorus
-- records: case-splitting an indexed `FinData.Fin` at a LITERAL index
-- raises `UnsupportedIndexedMatch` ("relies on injectivity of suc").
-- Only `∂-δ` below does this, and only to compare two definitionally
-- equal six-clause functions; nothing in this module transports along a
-- path in `Fin n`, so no proof depends on those clauses computing under
-- transport.
------------------------------------------------------------------------

module NaturalMachine.PMCokernel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; _+_)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Data.Empty as ⊥

open import NaturalMachine.PMTorus

------------------------------------------------------------------------
-- 1.  The incidence map δ : 𝔽₂⁹ → 𝔽₂⁶.
--
-- Nine observables, six contexts; a vector on observables goes to the
-- vector of its six context-sums.  Read off the same grid as PMTorus,
--   [[XI, IX, XX], [IY, YI, YY], [XY, YX, ZZ]],
-- rows R0 R1 R2 and columns C0 C1 C2.
------------------------------------------------------------------------

δ : (Obs → Bool) → (Ctx → Bool)
δ x R0 = sum3 (x XI) (x IX) (x XX)
δ x R1 = sum3 (x IY) (x YI) (x YY)
δ x R2 = sum3 (x XY) (x YX) (x ZZ)
δ x C0 = sum3 (x XI) (x IY) (x XY)
δ x C1 = sum3 (x IX) (x YI) (x YX)
δ x C2 = sum3 (x XX) (x YY) (x ZZ)

-- δ is 𝔽₂-linear (additive; over 𝔽₂ that is linearity).
_⊕ᵒ_ : (Obs → Bool) → (Obs → Bool) → (Obs → Bool)
(x ⊕ᵒ y) o = x o ⊕ y o

δ-additive : (x y : Obs → Bool) (c : Ctx) → δ (x ⊕ᵒ y) c ≡ δ x c ⊕ δ y c
δ-additive x y R0 = sum3-add (x XI) (x IX) (x XX) (y XI) (y IX) (y XX)
δ-additive x y R1 = sum3-add (x IY) (x YI) (x YY) (y IY) (y YI) (y YY)
δ-additive x y R2 = sum3-add (x XY) (x YX) (x ZZ) (y XY) (y YX) (y ZZ)
δ-additive x y C0 = sum3-add (x XI) (x IY) (x XY) (y XI) (y IY) (y XY)
δ-additive x y C1 = sum3-add (x IX) (x YI) (x YX) (y IX) (y YI) (y YX)
δ-additive x y C2 = sum3-add (x XX) (x YY) (x ZZ) (y XX) (y YY) (y ZZ)

------------------------------------------------------------------------
-- 2.  The incidence datum, certified: each observable lies in exactly
-- two contexts.
--
-- Membership is NOT a table typed in here: `inCtx` asks whether the
-- context is one of the two that `PMTorus.pmContexts` assigns to the
-- observable, through an equality test on contexts that is itself
-- certified sound and reflexive.  So `each-obs-twice` counts genuine
-- memberships.
------------------------------------------------------------------------

eqVertex : Vertex → Vertex → Bool
eqVertex (inl i) (inl j) = eq3 i j
eqVertex (inr i) (inr j) = eq3 i j
eqVertex (inl _) (inr _) = false
eqVertex (inr _) (inl _) = false

eqVertex-refl : (v : Vertex) → eqVertex v v ≡ true
eqVertex-refl (inl i) = eq3-refl i
eqVertex-refl (inr i) = eq3-refl i

eqVertex-sound : (u v : Vertex) → eqVertex u v ≡ true → u ≡ v
eqVertex-sound (inl i) (inl j) h = cong inl (eq3-sound i j h)
eqVertex-sound (inr i) (inr j) h = cong inr (eq3-sound i j h)
eqVertex-sound (inl _) (inr _) h = ⊥.rec (false≢true h)
eqVertex-sound (inr _) (inl _) h = ⊥.rec (false≢true h)

eqCtx : Ctx → Ctx → Bool
eqCtx c d = eqVertex (ctxToVertex c) (ctxToVertex d)

eqCtx-refl : (c : Ctx) → eqCtx c c ≡ true
eqCtx-refl c = eqVertex-refl (ctxToVertex c)

eqCtx-sound : (c d : Ctx) → eqCtx c d ≡ true → c ≡ d
eqCtx-sound c d h =
    sym (Iso.leftInv ctxIso c)
  ∙ cong vertexToCtx (eqVertex-sound (ctxToVertex c) (ctxToVertex d) h)
  ∙ Iso.leftInv ctxIso d

-- Likewise on observables, through PMTorus's certified `eq3` and the
-- bijection Obs ≃ Edge.
eqObs : Obs → Obs → Bool
eqObs o p =
      eq3 (fst (obsToEdge o)) (fst (obsToEdge p))
  and eq3 (snd (obsToEdge o)) (snd (obsToEdge p))

eqObs-refl : (o : Obs) → eqObs o o ≡ true
eqObs-refl o =
  cong₂ _and_ (eq3-refl (fst (obsToEdge o))) (eq3-refl (snd (obsToEdge o)))

eqObs-sound : (o p : Obs) → eqObs o p ≡ true → o ≡ p
eqObs-sound o p h =
    sym (Iso.leftInv obsIso o)
  ∙ cong edgeToObs
      (ΣPathP ( eq3-sound _ _ (fst (and-both _ _ h))
              , eq3-sound _ _ (snd (and-both _ _ h)) ))
  ∙ Iso.leftInv obsIso p

-- "Observable o lies in context c."
inCtx : Ctx → Obs → Bool
inCtx c o = eqCtx c (fst (pmContexts o)) or eqCtx c (snd (pmContexts o))

or-split : (a b : Bool) → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-split true  b _ = inl refl
or-split false true  _ = inr refl
or-split false false h = ⊥.rec (false≢true h)

-- A positive membership really is one of the two contexts of the grid.
inCtx-sound : (c : Ctx) (o : Obs) → inCtx c o ≡ true
            → (c ≡ fst (pmContexts o)) ⊎ (c ≡ snd (pmContexts o))
inCtx-sound c o h with or-split _ _ h
... | inl p = inl (eqCtx-sound c (fst (pmContexts o)) p)
... | inr q = inr (eqCtx-sound c (snd (pmContexts o)) q)

ind : Bool → ℕ
ind true  = 1
ind false = 0

occurrences : Obs → ℕ
occurrences o =
    ind (inCtx R0 o)
  + (ind (inCtx R1 o)
  + (ind (inCtx R2 o)
  + (ind (inCtx C0 o)
  + (ind (inCtx C1 o)
  +  ind (inCtx C2 o)))))

-- THE HYPOTHESIS OF (i), CHECKED: each observable lies in exactly two
-- of the six contexts.  Nine closed terms.
each-obs-twice : (o : Obs) → occurrences o ≡ 2
each-obs-twice XI = refl
each-obs-twice IX = refl
each-obs-twice XX = refl
each-obs-twice IY = refl
each-obs-twice YI = refl
each-obs-twice YY = refl
each-obs-twice XY = refl
each-obs-twice YX = refl
each-obs-twice ZZ = refl

-- ... and δ's columns ARE that incidence datum: δ applied to the unit
-- vector at o is the membership column of o.  Fifty-four closed terms;
-- this is what ties `each-obs-twice` to δ rather than to a second,
-- unrelated table.
column-is-incidence : (o : Obs) (c : Ctx) → δ (eqObs o) c ≡ inCtx c o
column-is-incidence XI R0 = refl
column-is-incidence XI R1 = refl
column-is-incidence XI R2 = refl
column-is-incidence XI C0 = refl
column-is-incidence XI C1 = refl
column-is-incidence XI C2 = refl
column-is-incidence IX R0 = refl
column-is-incidence IX R1 = refl
column-is-incidence IX R2 = refl
column-is-incidence IX C0 = refl
column-is-incidence IX C1 = refl
column-is-incidence IX C2 = refl
column-is-incidence XX R0 = refl
column-is-incidence XX R1 = refl
column-is-incidence XX R2 = refl
column-is-incidence XX C0 = refl
column-is-incidence XX C1 = refl
column-is-incidence XX C2 = refl
column-is-incidence IY R0 = refl
column-is-incidence IY R1 = refl
column-is-incidence IY R2 = refl
column-is-incidence IY C0 = refl
column-is-incidence IY C1 = refl
column-is-incidence IY C2 = refl
column-is-incidence YI R0 = refl
column-is-incidence YI R1 = refl
column-is-incidence YI R2 = refl
column-is-incidence YI C0 = refl
column-is-incidence YI C1 = refl
column-is-incidence YI C2 = refl
column-is-incidence YY R0 = refl
column-is-incidence YY R1 = refl
column-is-incidence YY R2 = refl
column-is-incidence YY C0 = refl
column-is-incidence YY C1 = refl
column-is-incidence YY C2 = refl
column-is-incidence XY R0 = refl
column-is-incidence XY R1 = refl
column-is-incidence XY R2 = refl
column-is-incidence XY C0 = refl
column-is-incidence XY C1 = refl
column-is-incidence XY C2 = refl
column-is-incidence YX R0 = refl
column-is-incidence YX R1 = refl
column-is-incidence YX R2 = refl
column-is-incidence YX C0 = refl
column-is-incidence YX C1 = refl
column-is-incidence YX C2 = refl
column-is-incidence ZZ R0 = refl
column-is-incidence ZZ R1 = refl
column-is-incidence ZZ R2 = refl
column-is-incidence ZZ C0 = refl
column-is-incidence ZZ C1 = refl
column-is-incidence ZZ C2 = refl

------------------------------------------------------------------------
-- 3.  The parity functional on contexts, and CLAIM (i).
--
-- `total` is the all-ones functional on 𝔽₂⁶: the sum of all six
-- context-sums.  Since each observable lies in exactly two contexts it
-- contributes 0 to that sum, so `total` kills the whole image.  In
-- coordinates this is the identity "the row sums and the column sums of
-- a 3 × 3 array have the same total", `PMTorus.sum9-transpose`, which
-- holds for every one of the 512 assignments at once — an identity, not
-- an enumeration.
------------------------------------------------------------------------

total : (Ctx → Bool) → Bool
total y = sum3 (y R0) (y R1) (y R2) ⊕ sum3 (y C0) (y C1) (y C2)

total-additive : (y z : Ctx → Bool)
               → total (λ c → y c ⊕ z c) ≡ total y ⊕ total z
total-additive y z =
    cong₂ _⊕_ (sum3-add (y R0) (y R1) (y R2) (z R0) (z R1) (z R2))
              (sum3-add (y C0) (y C1) (y C2) (z C0) (z C1) (z C2))
  ∙ ⊕-inter (total-rows y) (total-rows z) (total-cols y) (total-cols z)
  where
  total-rows total-cols : (Ctx → Bool) → Bool
  total-rows w = sum3 (w R0) (w R1) (w R2)
  total-cols w = sum3 (w C0) (w C1) (w C2)

-- CLAIM (i).  The all-ones functional on contexts vanishes on im δ.
parity-δ : (x : Obs → Bool) → total (δ x) ≡ false
parity-δ x =
    cong (sum3 (δ x R0) (δ x R1) (δ x R2) ⊕_)
         (sym (sum9-transpose (x XI) (x IX) (x XX)
                              (x IY) (x YI) (x YY)
                              (x XY) (x YX) (x ZZ)))
  ∙ ⊕-self (sum3 (δ x R0) (δ x R1) (δ x R2))

Image : (Ctx → Bool) → Type₀
Image y = Σ[ x ∈ (Obs → Bool) ] (δ x ≡ y)

image-is-even-total : (y : Ctx → Bool) → Image y → total y ≡ false
image-is-even-total y (x , q) = subst (λ z → total z ≡ false) q (parity-δ x)

------------------------------------------------------------------------
-- 4.  The Peres–Mermin sign vector, and CLAIM (ii).
--
-- s = (+,+,+ | +,+,−): the three rows and the first two columns
-- multiply to +1, the third column to −1.  Additively over 𝔽₂ that is
-- (0,0,0,0,0,1) — transcribed from notes/PM_SECTION_VS_COCYCLE.md (absent from this repository),
-- where it is derived from the exact Weyl cocycle.  It is the only
-- physical input to this module.
------------------------------------------------------------------------

s : Ctx → Bool
s R0 = false
s R1 = false
s R2 = false
s C0 = false
s C1 = false
s C2 = true

-- CLAIM (ii), first half: s has ODD total weight.  One `refl`.
total-s : total s ≡ true
total-s = refl

-- ... hence s is not in the image: the parity functional separates
-- them.  This is `[s] = 1` in coker δ ≅ 𝔽₂.
s-not-in-image : ¬ (Image s)
s-not-in-image (x , q) =
  false≢true (sym (image-is-even-total s (x , q)) ∙ total-s)

------------------------------------------------------------------------
-- 5.  Sections.
--
-- A global section is an 𝔽₂-valued assignment to the nine observables
-- whose six context-sums are the prescribed signs.  Because each
-- observable lies in exactly two contexts, a compatible family of local
-- assignments IS such a global one (note, claim 1), so this type being
-- empty is precisely the section failure.
------------------------------------------------------------------------

Section : Type₀
Section = Σ[ v ∈ (Obs → Bool) ] ((c : Ctx) → δ v c ≡ s c)

no-global-section : ¬ Section
no-global-section (v , p) = s-not-in-image (v , funExt p)

-- Local sections exist context by context: the obstruction is global.
zeroObs : Obs → Bool
zeroObs _ = false

local-section : (c : Ctx) → Σ[ v ∈ (Obs → Bool) ] (δ v c ≡ s c)
local-section R0 = zeroObs , refl
local-section R1 = zeroObs , refl
local-section R2 = zeroObs , refl
local-section C0 = zeroObs , refl
local-section C1 = zeroObs , refl
local-section C2 = eqObs XX , refl

-- The rows-only cover admits a global section (note, claim 2: the class
-- is a property of the COVER, not of the operator set).  Trivial for
-- this s — all three row signs are + — and recorded as such.
rows-only-section :
  Σ[ v ∈ (Obs → Bool) ]
    ((δ v R0 ≡ s R0) × ((δ v R1 ≡ s R1) × (δ v R2 ≡ s R2)))
rows-only-section = zeroObs , refl , refl , refl

------------------------------------------------------------------------
-- 6.  EXACTNESS: im δ is exactly ker(total), and total is onto.
--
-- Together: coker δ ≅ 𝔽₂ with `total` as the class evaluator.
-- The hard inclusion is imported from `PMTorus.even-kernel-is-image` along
-- the graph identification of §7 — no second preimage construction.
------------------------------------------------------------------------

-- δ and PMTorus's ∂ are the same map, read through Obs ≃ Edge and
-- Ctx ≃ Vertex.  Two six-clause checks.
∂-δ : (x : Obs → Bool) (v : Vertex)
    → ∂ (λ e → x (edgeToObs e)) v ≡ δ x (vertexToCtx v)
∂-δ x (inl k0) = refl
∂-δ x (inl k1) = refl
∂-δ x (inl k2) = refl
∂-δ x (inr k0) = refl
∂-δ x (inr k1) = refl
∂-δ x (inr k2) = refl

δ-∂ : (y : Edge → Bool) (c : Ctx)
    → δ (λ o → y (obsToEdge o)) c ≡ ∂ y (ctxToVertex c)
δ-∂ y R0 = refl
δ-∂ y R1 = refl
δ-∂ y R2 = refl
δ-∂ y C0 = refl
δ-∂ y C1 = refl
δ-∂ y C2 = refl

-- `total` on contexts is `PMTorus.parity` on vertices, definitionally.
total-parity : (y : Ctx → Bool) → total y ≡ parity (λ v → y (vertexToCtx v))
total-parity y = refl

-- ker total ⊆ im δ.
even-total-is-image : (y : Ctx → Bool) → total y ≡ false → Image y
even-total-is-image y h = pre , funExt lemma
  where
  y' : Vertex → Bool
  y' v = y (vertexToCtx v)

  pull : Σ[ x' ∈ (Edge → Bool) ] (∂ x' ≡ y')
  pull = even-kernel-is-image y' h

  pre : Obs → Bool
  pre o = fst pull (obsToEdge o)

  lemma : (c : Ctx) → δ pre c ≡ y c
  lemma c =
      δ-∂ (fst pull) c
    ∙ funExt⁻ (snd pull) (ctxToVertex c)
    ∙ cong y (Iso.leftInv ctxIso c)

-- total is onto, so the quotient it computes is 𝔽₂ and not 0.
total-onto : (b : Bool) → Σ[ y ∈ (Ctx → Bool) ] (total y ≡ b)
total-onto false = (λ _ → false) , refl
total-onto true  = s , total-s

------------------------------------------------------------------------
-- 7.  The kernel, and the local-system twist (note, claim 3).
--
-- Twisting the identification of ZZ between its row and its column
-- occurrence adds 1 to exactly one of the two context-sums ZZ enters —
-- here the column C2.  The twisted section condition is then
-- δ v c ⊕ twist c ≡ s c, and since twist = s pointwise this says
-- v ∈ ker δ.  So the twisted sections are the cycle space of the
-- graph: `Fin 4 → Bool`, i.e. 2⁴ = 16 of them, against 0 untwisted.
-- The dimension 4 is imported from `PMTorus.cycleEquiv`.
------------------------------------------------------------------------

Kernel : Type₀
Kernel = Σ[ v ∈ (Obs → Bool) ] ((c : Ctx) → δ v c ≡ false)

isPropKernelLaw : (v : Obs → Bool) → isProp ((c : Ctx) → δ v c ≡ false)
isPropKernelLaw v = isPropΠ (λ c → isSetBool (δ v c) false)

kernelIso : Iso Kernel Cycle
Iso.fun kernelIso (x , p) =
  (λ e → x (edgeToObs e)) , λ v → ∂-δ x v ∙ p (vertexToCtx v)
Iso.inv kernelIso (y , q) =
  (λ o → y (obsToEdge o)) , λ c → δ-∂ y c ∙ q (ctxToVertex c)
Iso.rightInv kernelIso (y , q) =
  Σ≡Prop isPropCycleLaw (funExt (λ e → cong y (Iso.rightInv obsIso e)))
Iso.leftInv kernelIso (x , p) =
  Σ≡Prop isPropKernelLaw (funExt (λ o → cong x (Iso.leftInv obsIso o)))

-- dim ker δ = 4, i.e. 16 elements.
kernelEquiv : Kernel ≃ (Fin 4 → Bool)
kernelEquiv = compEquiv (isoToEquiv kernelIso) cycleEquiv

-- The one-edge local system: the sign picked up when ZZ's two
-- occurrences are identified with a flip.
twist : Ctx → Bool
twist R0 = false
twist R1 = false
twist R2 = false
twist C0 = false
twist C1 = false
twist C2 = true

twist-is-s : (c : Ctx) → twist c ≡ s c
twist-is-s R0 = refl
twist-is-s R1 = refl
twist-is-s R2 = refl
twist-is-s C0 = refl
twist-is-s C1 = refl
twist-is-s C2 = refl

TwistedSection : Type₀
TwistedSection = Σ[ v ∈ (Obs → Bool) ] ((c : Ctx) → δ v c ⊕ twist c ≡ s c)

isPropTwistedLaw : (v : Obs → Bool)
                 → isProp ((c : Ctx) → δ v c ⊕ twist c ≡ s c)
isPropTwistedLaw v = isPropΠ (λ c → isSetBool (δ v c ⊕ twist c) (s c))

-- b ⊕ a ≡ a  ⟺  b ≡ false.  No case analysis: `⊕-cancel` and
-- `⊕-self` from PMTorus do it.
⊕-cancelR : (b a : Bool) → b ⊕ a ≡ a → b ≡ false
⊕-cancelR b a p = sym (⊕-cancel b a) ∙ cong (_⊕ a) p ∙ ⊕-self a

⊕-cancelR⁻ : (b a : Bool) → b ≡ false → b ⊕ a ≡ a
⊕-cancelR⁻ b a p = cong (_⊕ a) p

twistedIso : Iso TwistedSection Kernel
Iso.fun twistedIso (v , p) =
  v , λ c → ⊕-cancelR (δ v c) (s c)
              (cong (δ v c ⊕_) (sym (twist-is-s c)) ∙ p c)
Iso.inv twistedIso (v , p) =
  v , λ c → cong (δ v c ⊕_) (twist-is-s c)
              ∙ ⊕-cancelR⁻ (δ v c) (s c) (p c)
Iso.rightInv twistedIso (v , p) = Σ≡Prop isPropKernelLaw refl
Iso.leftInv  twistedIso (v , p) = Σ≡Prop isPropTwistedLaw refl

-- CLAIM 3 of the note, in the checked lane: 16 twisted sections where
-- there were 0 untwisted ones.  Contextuality is carried by the gluing
-- datum, not by the values.
twisted-sections≃F₂⁴ : TwistedSection ≃ (Fin 4 → Bool)
twisted-sections≃F₂⁴ = compEquiv (isoToEquiv twistedIso) kernelEquiv
