{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- PMTorus
--
-- The Peres-Mermin incidence graph, in the proof language.
--
-- Source of the claims: `machinery/pm_torus.py` (absent from this repository), whose four assertions
-- were established by exact finite computation in Python
-- (the 9 observables of the Peres-Mermin square, the 6 contexts, and the
-- incidence map δ : F₂⁹ → F₂⁶ whose cokernel carries the obstruction).
-- This module re-establishes them as kernel-checked terms.
--
-- WHAT IS PROVED.
--
--  (a) THE INCIDENCE GRAPH IS K₃,₃.  Proved, in the strong form: the
--      nine observables `Obs` and six contexts `Ctx` are declared as
--      bare enumerations, the incidence datum `pmContexts` is read off
--      the physical grid (each observable's row and column), and then
--      `obsEquiv : Obs ≃ Edge`, `ctxEquiv : Ctx ≃ Vertex` and
--      `pm-is-K33` exhibit a graph isomorphism onto
--      K₃,₃ := (Vertex = Fin 3 ⊎ Fin 3, Edge = Fin 3 × Fin 3,
--      endpoints (i , j) = (inl i , inr j)).  `pm-cell-unique` is the
--      "each row meets each column in exactly one cell" reading:
--      contractibility of the fibre of the cell map, obtained from the
--      equivalence rather than from a search.
--
--  (b) NONPLANARITY — ARITHMETIC OBSTRUCTION ONLY.
--      What is proved is the arithmetic that obstructs it:
--      `bipartite-bound-violated : ¬ (E + 4 ≤ℕ 2 · V)` for the certified
--      cardinalities E = 9, V = 6 (the subtraction-free form of
--      E ≤ 2V − 4), together with its contrapositive packaging
--      `not-K33 : (v e : ℕ) → e + 4 ≤ℕ 2 · v → ¬ ((v ≡ V) × (e ≡ E))`.
--      The Euler-bound theorem itself — "a simple planar bipartite graph
--      satisfies E ≤ 2V − 4" — is a topological input.
--      Read (b) as: any graph obeying that bound is not this
--      one.
--
--  (c) TOROIDAL ROTATION SYSTEM — COMBINATORICS ONLY.  Proved:
--      `face-closed`, the three listed hexagons really are closed walks
--      in the graph (each consecutive pair of the six vertices is an
--      edge, so the walks alternate sides and never leave the graph);
--      `each-edge-twice : (e : Edge) → traversals e ≡ 2`, a finite
--      decidable check over all nine edges, proved as a term — and the
--      equality test the count is built from is itself certified
--      (`sameEdge-refl`, `sameEdge-sound`), so the count counts edge
--      equalities and not the entries of an uninterpreted table;
--      `faces-distinct`, the three faces are pairwise distinct (so
--      F = 3 counts three things); and the Euler arithmetic
--      `euler-characteristic : (pos V - pos E) + pos F ≡ pos 0` in ℤ.
--
--  (d) CYCLE SPACE, RANK 4, AND THE COKERNEL.  Proved, as linear
--      algebra over 𝔽₂ = Bool with ⊕, not as arithmetic on literals:
--        `cycleEquiv  : Cycle ≃ (Fin 4 → Bool)` — the cycle space
--          ker ∂ is 4-dimensional, E − V + 1 = 4, with
--          `read-additive` and `read-scalar` certifying that the
--          equivalence is 𝔽₂-linear (over 𝔽₂ an additive bijection is
--          linear; the scalar law is checked anyway);
--        `parity-∂` and `even-kernel-is-image` — the image of ∂ is
--          EXACTLY the kernel of the parity functional, both inclusions,
--          the second by explicit construction of a preimage;
--        `parity-onto` — parity is surjective, so the quotient it
--          computes is 𝔽₂, not 0;
--        `evenEquiv : Even ≃ (Fin 5 → Bool)` — hence rank ∂ = 5 and
--          coker ∂ has dimension 6 − 5 = 1.
--
-- No floating point, no search, no printout: every finite check below is
-- a closed term the type-checker reduced.
--
-- TOOLCHAIN CAVEAT (Agda 2.6.3 / cubical v0.5).  Case-splitting an
-- indexed `FinData.Fin` at a LITERAL index raises Cubical Agda's
-- `UnsupportedIndexedMatch` warning ("relies on injectivity of suc"):
-- the resulting functions are sound and reduce on closed terms — every
-- `refl` below did reduce — but they do not compute when applied to a
-- transport.  Nothing here transports along a path in `Fin n`, so no
-- proof below depends on that.  The same warning is already emitted by
-- `NaturalMachine/SmithPathCountedExecution.agda`.
------------------------------------------------------------------------

module PMTorus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; _+_ ; _·_ ; snotz ; znots)
open import Cubical.Data.Nat.Order using (¬m<m) renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.Int using (ℤ ; pos) renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_)
open import Cubical.Data.FinData using (Fin) renaming (zero to fz ; suc to fs)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Data.Empty as ⊥

-- Readable names for the finitely many indices used below.
pattern k0 = fz
pattern k1 = fs fz
pattern k2 = fs (fs fz)
pattern k3 = fs (fs (fs fz))
pattern k4 = fs (fs (fs (fs fz)))
pattern k5 = fs (fs (fs (fs (fs fz))))
pattern k6 = fs (fs (fs (fs (fs (fs fz)))))
pattern k7 = fs (fs (fs (fs (fs (fs (fs fz))))))
pattern k8 = fs (fs (fs (fs (fs (fs (fs (fs fz)))))))

------------------------------------------------------------------------
-- 0.  𝔽₂ toolkit.
--
-- Bool with ⊕ is the additive group of 𝔽₂.  Everything below is derived
-- from the library's ⊕-assoc / ⊕-comm / ⊕-identityʳ / ⊕-invol; only
-- `⊕-self` needs a case split, and that one is two clauses.
------------------------------------------------------------------------

⊕-self : (a : Bool) → a ⊕ a ≡ false
⊕-self false = refl
⊕-self true  = refl

-- Transpose the last two summands of a left-nested chain.
⊕-swap : (a b c : Bool) → (a ⊕ b) ⊕ c ≡ (a ⊕ c) ⊕ b
⊕-swap a b c =
  sym (⊕-assoc a b c) ∙ cong (a ⊕_) (⊕-comm b c) ∙ ⊕-assoc a c b

-- Middle-four interchange.
⊕-inter : (a b c d : Bool) → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-inter a b c d =
    ⊕-assoc (a ⊕ b) c d
  ∙ cong (_⊕ d) (⊕-swap a b c)
  ∙ sym (⊕-assoc (a ⊕ c) b d)

⊕-cancel : (u a : Bool) → (u ⊕ a) ⊕ a ≡ u
⊕-cancel u a = sym (⊕-assoc u a a) ∙ cong (u ⊕_) (⊕-self a) ∙ ⊕-identityʳ u

⊕-cancel₂ : (u a b : Bool) → (((u ⊕ a) ⊕ b) ⊕ a) ⊕ b ≡ u
⊕-cancel₂ u a b =
    cong (_⊕ b) (⊕-swap (u ⊕ a) b a)
  ∙ cong (λ w → (w ⊕ b) ⊕ b) (⊕-cancel u a)
  ∙ ⊕-cancel u b

-- Over 𝔽₂, "sums to zero" is "equal".
⊕-solve : (u c : Bool) → u ⊕ c ≡ false → u ≡ c
⊕-solve u c p = sym (⊕-cancel u c) ∙ cong (_⊕ c) p

-- The three-term sum, left-nested; this is how ∂ and parity are built.
sum3 : Bool → Bool → Bool → Bool
sum3 a b c = (a ⊕ b) ⊕ c

sum3-add : (a b c a' b' c' : Bool)
         → sum3 (a ⊕ a') (b ⊕ b') (c ⊕ c') ≡ sum3 a b c ⊕ sum3 a' b' c'
sum3-add a b c a' b' c' =
    cong (_⊕ (c ⊕ c')) (⊕-inter a a' b b')
  ∙ ⊕-inter (a ⊕ b) (a' ⊕ b') c c'

-- Transposing a 3 × 3 array does not change its total sum.  Four
-- interchanges; no case analysis.
sum9-transpose : (a b c d e f g h i : Bool)
  → sum3 (sum3 a b c) (sum3 d e f) (sum3 g h i)
  ≡ sum3 (sum3 a d g) (sum3 b e h) (sum3 c f i)
sum9-transpose a b c d e f g h i =
    cong (_⊕ ((g ⊕ h) ⊕ i))
         (⊕-inter (a ⊕ b) c (d ⊕ e) f ∙ cong (_⊕ (c ⊕ f)) (⊕-inter a b d e))
  ∙ ⊕-inter ((a ⊕ d) ⊕ (b ⊕ e)) (c ⊕ f) (g ⊕ h) i
  ∙ cong (_⊕ ((c ⊕ f) ⊕ i)) (⊕-inter (a ⊕ d) (b ⊕ e) g h)

-- The one five-term rearrangement needed downstream, by four adjacent
-- transpositions.
⊕-perm5 : (a b c d e : Bool)
        → (((a ⊕ b) ⊕ c) ⊕ d) ⊕ e ≡ (((a ⊕ d) ⊕ e) ⊕ b) ⊕ c
⊕-perm5 a b c d e =
    cong (_⊕ e) (⊕-swap (a ⊕ b) c d)                     -- [a b d c e]
  ∙ cong (λ w → (w ⊕ c) ⊕ e) (⊕-swap a b d)              -- [a d b c e]
  ∙ ⊕-swap (((a ⊕ d) ⊕ b)) c e                           -- [a d b e c]
  ∙ cong (_⊕ c) (⊕-swap ((a ⊕ d)) b e)                   -- [a d e b c]

------------------------------------------------------------------------
-- 1.  K₃,₃ as a type, and the Peres-Mermin square as a graph.
------------------------------------------------------------------------

-- The two sides of the bipartition: rows on the left, columns on the
-- right.  This IS K₃,₃: an edge is a (row, column) pair, so each row
-- meets each column in exactly one edge by construction.
Vertex : Type₀
Vertex = Fin 3 ⊎ Fin 3

Edge : Type₀
Edge = Fin 3 × Fin 3

endpoints : Edge → Vertex × Vertex
endpoints (i , j) = (inl i , inr j)

-- The nine Peres-Mermin observables and the six contexts, as bare
-- enumerations carrying no structure at all.
data Obs : Type₀ where
  XI IX XX IY YI YY XY YX ZZ : Obs

data Ctx : Type₀ where
  R0 R1 R2 C0 C1 C2 : Ctx

-- The physical datum: which row and which column each observable lies
-- in.  Transcribed from the grid of machinery/pm_torus.py (absent from this repository)
--   [[XI, IX, XX], [IY, YI, YY], [XY, YX, ZZ]].
pmContexts : Obs → Ctx × Ctx
pmContexts XI = (R0 , C0)
pmContexts IX = (R0 , C1)
pmContexts XX = (R0 , C2)
pmContexts IY = (R1 , C0)
pmContexts YI = (R1 , C1)
pmContexts YY = (R1 , C2)
pmContexts XY = (R2 , C0)
pmContexts YX = (R2 , C1)
pmContexts ZZ = (R2 , C2)

-- Independently declared relabellings.
ctxToVertex : Ctx → Vertex
ctxToVertex R0 = inl k0
ctxToVertex R1 = inl k1
ctxToVertex R2 = inl k2
ctxToVertex C0 = inr k0
ctxToVertex C1 = inr k1
ctxToVertex C2 = inr k2

vertexToCtx : Vertex → Ctx
vertexToCtx (inl k0) = R0
vertexToCtx (inl k1) = R1
vertexToCtx (inl k2) = R2
vertexToCtx (inr k0) = C0
vertexToCtx (inr k1) = C1
vertexToCtx (inr k2) = C2

ctxIso : Iso Ctx Vertex
Iso.fun ctxIso = ctxToVertex
Iso.inv ctxIso = vertexToCtx
Iso.rightInv ctxIso (inl k0) = refl
Iso.rightInv ctxIso (inl k1) = refl
Iso.rightInv ctxIso (inl k2) = refl
Iso.rightInv ctxIso (inr k0) = refl
Iso.rightInv ctxIso (inr k1) = refl
Iso.rightInv ctxIso (inr k2) = refl
Iso.leftInv ctxIso R0 = refl
Iso.leftInv ctxIso R1 = refl
Iso.leftInv ctxIso R2 = refl
Iso.leftInv ctxIso C0 = refl
Iso.leftInv ctxIso C1 = refl
Iso.leftInv ctxIso C2 = refl

ctxEquiv : Ctx ≃ Vertex
ctxEquiv = isoToEquiv ctxIso

obsToEdge : Obs → Edge
obsToEdge XI = (k0 , k0)
obsToEdge IX = (k0 , k1)
obsToEdge XX = (k0 , k2)
obsToEdge IY = (k1 , k0)
obsToEdge YI = (k1 , k1)
obsToEdge YY = (k1 , k2)
obsToEdge XY = (k2 , k0)
obsToEdge YX = (k2 , k1)
obsToEdge ZZ = (k2 , k2)

edgeToObs : Edge → Obs
edgeToObs (k0 , k0) = XI
edgeToObs (k0 , k1) = IX
edgeToObs (k0 , k2) = XX
edgeToObs (k1 , k0) = IY
edgeToObs (k1 , k1) = YI
edgeToObs (k1 , k2) = YY
edgeToObs (k2 , k0) = XY
edgeToObs (k2 , k1) = YX
edgeToObs (k2 , k2) = ZZ

obsIso : Iso Obs Edge
Iso.fun obsIso = obsToEdge
Iso.inv obsIso = edgeToObs
Iso.rightInv obsIso (k0 , k0) = refl
Iso.rightInv obsIso (k0 , k1) = refl
Iso.rightInv obsIso (k0 , k2) = refl
Iso.rightInv obsIso (k1 , k0) = refl
Iso.rightInv obsIso (k1 , k1) = refl
Iso.rightInv obsIso (k1 , k2) = refl
Iso.rightInv obsIso (k2 , k0) = refl
Iso.rightInv obsIso (k2 , k1) = refl
Iso.rightInv obsIso (k2 , k2) = refl
Iso.leftInv obsIso XI = refl
Iso.leftInv obsIso IX = refl
Iso.leftInv obsIso XX = refl
Iso.leftInv obsIso IY = refl
Iso.leftInv obsIso YI = refl
Iso.leftInv obsIso YY = refl
Iso.leftInv obsIso XY = refl
Iso.leftInv obsIso YX = refl
Iso.leftInv obsIso ZZ = refl

obsEquiv : Obs ≃ Edge
obsEquiv = isoToEquiv obsIso

-- The endpoint map of the Peres-Mermin incidence graph, read off the
-- physical datum and nothing else.
pmEndpoints : Obs → Vertex × Vertex
pmEndpoints o =
  (ctxToVertex (fst (pmContexts o)) , ctxToVertex (snd (pmContexts o)))

------------------------------------------------------------------------
-- CLAIM (a).  The square's incidence graph IS K₃,₃: the pair of
-- bijections (obsEquiv on edges, ctxEquiv on vertices) commutes with the
-- endpoint maps.  That is a graph isomorphism, checked on all nine
-- observables.
------------------------------------------------------------------------

pm-is-K33 : (o : Obs) → pmEndpoints o ≡ endpoints (obsToEdge o)
pm-is-K33 XI = refl
pm-is-K33 IX = refl
pm-is-K33 XX = refl
pm-is-K33 IY = refl
pm-is-K33 YI = refl
pm-is-K33 YY = refl
pm-is-K33 XY = refl
pm-is-K33 YX = refl
pm-is-K33 ZZ = refl

-- "Every row meets every column in exactly one cell": the fibre of the
-- cell map over any (row, column) pair is contractible.  This is the
-- equivalence, not a search over 9 × 9 possibilities.
pm-cell-unique : (i j : Fin 3) → isContr (fiber obsToEdge (i , j))
pm-cell-unique i j = equiv-proof (snd obsEquiv) (i , j)

------------------------------------------------------------------------
-- 2.  Certified cardinalities.  V and E below are not literals chosen to
-- make the arithmetic work: they are the cardinalities of the vertex and
-- edge types, exhibited by explicit bijections (`vertexCount`,
-- `edgeCount`).  F is the number of faces of the rotation system of §3;
-- its certificate is `faces-distinct` there (three, pairwise distinct),
-- not a bijection here.
------------------------------------------------------------------------

V E F : ℕ
V = 6
E = 9
F = 3

vertexToFin : Vertex → Fin 6
vertexToFin (inl k0) = k0
vertexToFin (inl k1) = k1
vertexToFin (inl k2) = k2
vertexToFin (inr k0) = k3
vertexToFin (inr k1) = k4
vertexToFin (inr k2) = k5

finToVertex : Fin 6 → Vertex
finToVertex k0 = inl k0
finToVertex k1 = inl k1
finToVertex k2 = inl k2
finToVertex k3 = inr k0
finToVertex k4 = inr k1
finToVertex k5 = inr k2

vertexIso : Iso Vertex (Fin V)
Iso.fun vertexIso = vertexToFin
Iso.inv vertexIso = finToVertex
Iso.rightInv vertexIso k0 = refl
Iso.rightInv vertexIso k1 = refl
Iso.rightInv vertexIso k2 = refl
Iso.rightInv vertexIso k3 = refl
Iso.rightInv vertexIso k4 = refl
Iso.rightInv vertexIso k5 = refl
Iso.leftInv vertexIso (inl k0) = refl
Iso.leftInv vertexIso (inl k1) = refl
Iso.leftInv vertexIso (inl k2) = refl
Iso.leftInv vertexIso (inr k0) = refl
Iso.leftInv vertexIso (inr k1) = refl
Iso.leftInv vertexIso (inr k2) = refl

vertexCount : Vertex ≃ Fin V
vertexCount = isoToEquiv vertexIso

edgeToFin : Edge → Fin 9
edgeToFin (k0 , k0) = k0
edgeToFin (k0 , k1) = k1
edgeToFin (k0 , k2) = k2
edgeToFin (k1 , k0) = k3
edgeToFin (k1 , k1) = k4
edgeToFin (k1 , k2) = k5
edgeToFin (k2 , k0) = k6
edgeToFin (k2 , k1) = k7
edgeToFin (k2 , k2) = k8

finToEdge : Fin 9 → Edge
finToEdge k0 = (k0 , k0)
finToEdge k1 = (k0 , k1)
finToEdge k2 = (k0 , k2)
finToEdge k3 = (k1 , k0)
finToEdge k4 = (k1 , k1)
finToEdge k5 = (k1 , k2)
finToEdge k6 = (k2 , k0)
finToEdge k7 = (k2 , k1)
finToEdge k8 = (k2 , k2)

edgeIso : Iso Edge (Fin E)
Iso.fun edgeIso = edgeToFin
Iso.inv edgeIso = finToEdge
Iso.rightInv edgeIso k0 = refl
Iso.rightInv edgeIso k1 = refl
Iso.rightInv edgeIso k2 = refl
Iso.rightInv edgeIso k3 = refl
Iso.rightInv edgeIso k4 = refl
Iso.rightInv edgeIso k5 = refl
Iso.rightInv edgeIso k6 = refl
Iso.rightInv edgeIso k7 = refl
Iso.rightInv edgeIso k8 = refl
Iso.leftInv edgeIso (k0 , k0) = refl
Iso.leftInv edgeIso (k0 , k1) = refl
Iso.leftInv edgeIso (k0 , k2) = refl
Iso.leftInv edgeIso (k1 , k0) = refl
Iso.leftInv edgeIso (k1 , k1) = refl
Iso.leftInv edgeIso (k1 , k2) = refl
Iso.leftInv edgeIso (k2 , k0) = refl
Iso.leftInv edgeIso (k2 , k1) = refl
Iso.leftInv edgeIso (k2 , k2) = refl

edgeCount : Edge ≃ Fin E
edgeCount = isoToEquiv edgeIso

-- ... and the same counts for the physical objects, by composition.
obsCount : Obs ≃ Fin E
obsCount = compEquiv obsEquiv edgeCount

ctxCount : Ctx ≃ Fin V
ctxCount = compEquiv ctxEquiv vertexCount

------------------------------------------------------------------------
-- CLAIM (b).  The bipartite Euler bound is violated — ARITHMETIC ONLY.
--
-- A simple planar bipartite graph satisfies E ≤ 2V − 4.  That theorem is
-- topological input.  What is proved is
-- that these numbers cannot satisfy it, in the subtraction-free form
-- E + 4 ≤ 2·V (equivalent over ℕ for 2V ≥ 4).
------------------------------------------------------------------------

bipartite-bound-violated : ¬ (E + 4 ≤ℕ 2 · V)
bipartite-bound-violated = ¬m<m

-- Contrapositive packaging: whatever graph satisfies the bipartite
-- planar bound, its vertex and edge counts are not ours.
not-K33 : (v e : ℕ) → (e + 4 ≤ℕ 2 · v) → ¬ ((v ≡ V) × (e ≡ E))
not-K33 v e bound (pv , pe) =
  bipartite-bound-violated (subst2 (λ a b → a + 4 ≤ℕ 2 · b) pe pv bound)

------------------------------------------------------------------------
-- 3.  CLAIM (c).  The three-hexagon rotation system.
--
--   F_t :  r0 → c_t → r1 → c_{t+1} → r2 → c_{t+2} → r0.
------------------------------------------------------------------------

-- Cyclic successor on the three columns, and on the six positions of a
-- hexagonal boundary walk.
rot : Fin 3 → Fin 3
rot k0 = k1
rot k1 = k2
rot k2 = k0

next6 : Fin 6 → Fin 6
next6 k0 = k1
next6 k1 = k2
next6 k2 = k3
next6 k3 = k4
next6 k4 = k5
next6 k5 = k0

-- The boundary walk of the t-th face, as a map from its six positions.
walk : Fin 3 → Fin 6 → Vertex
walk t k0 = inl k0
walk t k1 = inr t
walk t k2 = inl k1
walk t k3 = inr (rot t)
walk t k4 = inl k2
walk t k5 = inr (rot (rot t))

-- A pair of vertices spans an edge only when it is a row and a column;
-- `nothing` records a step that leaves the graph.
step : Vertex → Vertex → Maybe Edge
step (inl i) (inr j) = just (i , j)
step (inr j) (inl i) = just (i , j)
step (inl _) (inl _) = nothing
step (inr _) (inr _) = nothing

-- The edge traversed at position k of face t.
faceStep : Fin 3 → Fin 6 → Edge
faceStep t k0 = (k0 , t)
faceStep t k1 = (k1 , t)
faceStep t k2 = (k1 , rot t)
faceStep t k3 = (k2 , rot t)
faceStep t k4 = (k2 , rot (rot t))
faceStep t k5 = (k0 , rot (rot t))

-- Each hexagon really is a closed walk in the graph: every consecutive
-- pair of its six vertices spans an edge, and that edge is `faceStep`.
-- Checked for all six positions, uniformly in t.
face-closed : (t : Fin 3) (k : Fin 6)
            → step (walk t k) (walk t (next6 k)) ≡ just (faceStep t k)
face-closed t k0 = refl
face-closed t k1 = refl
face-closed t k2 = refl
face-closed t k3 = refl
face-closed t k4 = refl
face-closed t k5 = refl

-- Counting traversals.  The equality test is CERTIFIED — `sameEdge`
-- returns 1 only on equal edges and does return 1 on every edge — so
-- `each-edge-twice` below is a statement about edge equality and not
-- about an uninterpreted table.
eq3 : Fin 3 → Fin 3 → Bool
eq3 k0 k0 = true
eq3 k0 k1 = false
eq3 k0 k2 = false
eq3 k1 k0 = false
eq3 k1 k1 = true
eq3 k1 k2 = false
eq3 k2 k0 = false
eq3 k2 k1 = false
eq3 k2 k2 = true

eq3-refl : (i : Fin 3) → eq3 i i ≡ true
eq3-refl k0 = refl
eq3-refl k1 = refl
eq3-refl k2 = refl

eq3-sound : (i j : Fin 3) → eq3 i j ≡ true → i ≡ j
eq3-sound k0 k0 _ = refl
eq3-sound k0 k1 p = ⊥.rec (false≢true p)
eq3-sound k0 k2 p = ⊥.rec (false≢true p)
eq3-sound k1 k0 p = ⊥.rec (false≢true p)
eq3-sound k1 k1 _ = refl
eq3-sound k1 k2 p = ⊥.rec (false≢true p)
eq3-sound k2 k0 p = ⊥.rec (false≢true p)
eq3-sound k2 k1 p = ⊥.rec (false≢true p)
eq3-sound k2 k2 _ = refl

and-both : (a b : Bool) → a and b ≡ true → (a ≡ true) × (b ≡ true)
and-both true  true  _ = refl , refl
and-both true  false p = ⊥.rec (false≢true p)
and-both false true  p = ⊥.rec (false≢true p)
and-both false false p = ⊥.rec (false≢true p)

if-one : (b : Bool) → (if b then 1 else 0) ≡ 1 → b ≡ true
if-one true  _ = refl
if-one false p = ⊥.rec (znots p)

sameEdge : Edge → Edge → ℕ
sameEdge (i , j) (i' , j') = if (eq3 i i') and (eq3 j j') then 1 else 0

sameEdge-refl : (e : Edge) → sameEdge e e ≡ 1
sameEdge-refl (i , j) =
  cong (λ b → if b then 1 else 0) (cong₂ _and_ (eq3-refl i) (eq3-refl j))

sameEdge-sound : (e f : Edge) → sameEdge e f ≡ 1 → e ≡ f
sameEdge-sound (i , j) (i' , j') p =
  ΣPathP ( eq3-sound i i' (fst (and-both _ _ (if-one _ p)))
         , eq3-sound j j' (snd (and-both _ _ (if-one _ p))) )

countFace : Fin 3 → Edge → ℕ
countFace t e =
    sameEdge (faceStep t k0) e
  + (sameEdge (faceStep t k1) e
  + (sameEdge (faceStep t k2) e
  + (sameEdge (faceStep t k3) e
  + (sameEdge (faceStep t k4) e
  +  sameEdge (faceStep t k5) e))))

traversals : Edge → ℕ
traversals e = countFace k0 e + (countFace k1 e + countFace k2 e)

-- THE ROTATION-SYSTEM CHECK: every edge is traversed exactly twice.
-- Nine closed terms; the type-checker did the counting.
each-edge-twice : (e : Edge) → traversals e ≡ 2
each-edge-twice (k0 , k0) = refl
each-edge-twice (k0 , k1) = refl
each-edge-twice (k0 , k2) = refl
each-edge-twice (k1 , k0) = refl
each-edge-twice (k1 , k1) = refl
each-edge-twice (k1 , k2) = refl
each-edge-twice (k2 , k0) = refl
each-edge-twice (k2 , k1) = refl
each-edge-twice (k2 , k2) = refl

-- F = 3 counts three distinct faces: their traversal vectors differ.
faces-distinct : (¬ (countFace k0 ≡ countFace k1))
               × (¬ (countFace k0 ≡ countFace k2))
               × (¬ (countFace k1 ≡ countFace k2))
faces-distinct =
    (λ p → snotz (cong (λ f → f (k1 , k0)) p))
  , (λ p → snotz (cong (λ f → f (k0 , k0)) p))
  , (λ p → snotz (cong (λ f → f (k0 , k0)) p))

-- The Euler arithmetic of the rotation system, in ℤ.  χ(torus) = 0.
euler-characteristic : (pos V -ℤ pos E) +ℤ pos F ≡ pos 0
euler-characteristic = refl

-- The same statement without subtraction.
euler-characteristic-ℕ : V + F ≡ E
euler-characteristic-ℕ = refl

-- Eighteen edge-slots in all, i.e. 2E.  Definitional bookkeeping
-- (`refl` on literals); the theorem behind it is `each-edge-twice`.
slot-count : F · 6 ≡ 2 · E
slot-count = refl

------------------------------------------------------------------------
-- 4.  CLAIM (d).  The 𝔽₂ chain complex of the graph.
--
--   ∂ : 𝔽₂^E → 𝔽₂^V  sends an edge to the sum of its two endpoints;
--   here, in coordinates, a 3 × 3 Bool matrix to its row and column
------------------------------------------------------------------------

∂ : (Edge → Bool) → (Vertex → Bool)
∂ x (inl i) = sum3 (x (i , k0)) (x (i , k1)) (x (i , k2))
∂ x (inr j) = sum3 (x (k0 , j)) (x (k1 , j)) (x (k2 , j))

-- The cycle space: ker ∂.
Cycle : Type₀
Cycle = Σ[ x ∈ (Edge → Bool) ] ((v : Vertex) → ∂ x v ≡ false)

isPropCycleLaw : (x : Edge → Bool) → isProp ((v : Vertex) → ∂ x v ≡ false)
isPropCycleLaw x = isPropΠ (λ v → isSetBool (∂ x v) false)

-- Four free coordinates: the top-left 2 × 2 block.
readCycle : Cycle → (Fin 4 → Bool)
readCycle (x , _) k0 = x (k0 , k0)
readCycle (x , _) k1 = x (k0 , k1)
readCycle (x , _) k2 = x (k1 , k0)
readCycle (x , _) k3 = x (k1 , k1)

-- ... and the unique completion of such a block to a cycle.
fillCycle : (Fin 4 → Bool) → (Edge → Bool)
fillCycle u (k0 , k0) = u k0
fillCycle u (k0 , k1) = u k1
fillCycle u (k0 , k2) = u k0 ⊕ u k1
fillCycle u (k1 , k0) = u k2
fillCycle u (k1 , k1) = u k3
fillCycle u (k1 , k2) = u k2 ⊕ u k3
fillCycle u (k2 , k0) = u k0 ⊕ u k2
fillCycle u (k2 , k1) = u k1 ⊕ u k3
fillCycle u (k2 , k2) = (u k0 ⊕ u k2) ⊕ (u k1 ⊕ u k3)

fillCycle-law : (u : Fin 4 → Bool) (v : Vertex) → ∂ (fillCycle u) v ≡ false
fillCycle-law u (inl k0) = ⊕-self (u k0 ⊕ u k1)
fillCycle-law u (inl k1) = ⊕-self (u k2 ⊕ u k3)
fillCycle-law u (inl k2) = ⊕-self ((u k0 ⊕ u k2) ⊕ (u k1 ⊕ u k3))
fillCycle-law u (inr k0) = ⊕-self (u k0 ⊕ u k2)
fillCycle-law u (inr k1) = ⊕-self (u k1 ⊕ u k3)
fillCycle-law u (inr k2) =
    cong (_⊕ ((u k0 ⊕ u k2) ⊕ (u k1 ⊕ u k3)))
         (⊕-inter (u k0) (u k1) (u k2) (u k3))
  ∙ ⊕-self ((u k0 ⊕ u k2) ⊕ (u k1 ⊕ u k3))

makeCycle : (Fin 4 → Bool) → Cycle
makeCycle u = fillCycle u , fillCycle-law u

cycleIso : Iso Cycle (Fin 4 → Bool)
Iso.fun cycleIso = readCycle
Iso.inv cycleIso = makeCycle
Iso.rightInv cycleIso u = funExt lemma
  where
  lemma : (k : Fin 4) → readCycle (makeCycle u) k ≡ u k
  lemma k0 = refl
  lemma k1 = refl
  lemma k2 = refl
  lemma k3 = refl
Iso.leftInv cycleIso (x , p) = Σ≡Prop isPropCycleLaw (funExt lemma)
  where
  row0 : x (k0 , k0) ⊕ x (k0 , k1) ≡ x (k0 , k2)
  row0 = ⊕-solve _ _ (p (inl k0))
  row1 : x (k1 , k0) ⊕ x (k1 , k1) ≡ x (k1 , k2)
  row1 = ⊕-solve _ _ (p (inl k1))
  col0 : x (k0 , k0) ⊕ x (k1 , k0) ≡ x (k2 , k0)
  col0 = ⊕-solve _ _ (p (inr k0))
  col1 : x (k0 , k1) ⊕ x (k1 , k1) ≡ x (k2 , k1)
  col1 = ⊕-solve _ _ (p (inr k1))
  col2 : x (k0 , k2) ⊕ x (k1 , k2) ≡ x (k2 , k2)
  col2 = ⊕-solve _ _ (p (inr k2))

  lemma : (e : Edge) → fillCycle (readCycle (x , p)) e ≡ x e
  lemma (k0 , k0) = refl
  lemma (k0 , k1) = refl
  lemma (k0 , k2) = row0
  lemma (k1 , k0) = refl
  lemma (k1 , k1) = refl
  lemma (k1 , k2) = row1
  lemma (k2 , k0) = col0
  lemma (k2 , k1) = col1
  lemma (k2 , k2) =
      sym (⊕-inter (x (k0 , k0)) (x (k0 , k1)) (x (k1 , k0)) (x (k1 , k1)))
    ∙ cong₂ _⊕_ row0 row1
    ∙ col2

-- THE RANK STATEMENT: dim ker ∂ = 4 = E − V + 1.
cycleEquiv : Cycle ≃ (Fin 4 → Bool)
cycleEquiv = isoToEquiv cycleIso

-- E − V + 1 = 4, subtraction-free.
cycle-rank : E + 1 ≡ V + 4
cycle-rank = refl

------------------------------------------------------------------------
-- The equivalence is 𝔽₂-LINEAR, which is what makes "dimension 4" mean
-- what it says.  Over 𝔽₂ an additive bijection is automatically linear;
-- the scalar law is checked as well.
------------------------------------------------------------------------

_⊞_ : (Edge → Bool) → (Edge → Bool) → (Edge → Bool)
(x ⊞ y) e = x e ⊕ y e

∂-additive : (x y : Edge → Bool) (v : Vertex) → ∂ (x ⊞ y) v ≡ ∂ x v ⊕ ∂ y v
∂-additive x y (inl i) =
  sum3-add (x (i , k0)) (x (i , k1)) (x (i , k2))
           (y (i , k0)) (y (i , k1)) (y (i , k2))
∂-additive x y (inr j) =
  sum3-add (x (k0 , j)) (x (k1 , j)) (x (k2 , j))
           (y (k0 , j)) (y (k1 , j)) (y (k2 , j))

_⊞c_ : Cycle → Cycle → Cycle
(x , p) ⊞c (y , q) =
  (x ⊞ y) , λ v → ∂-additive x y v ∙ cong₂ _⊕_ (p v) (q v)

scale : Bool → (Edge → Bool) → (Edge → Bool)
scale false x = λ _ → false
scale true  x = x

scale-law : (s : Bool) (x : Edge → Bool)
          → ((v : Vertex) → ∂ x v ≡ false)
          → (v : Vertex) → ∂ (scale s x) v ≡ false
scale-law false x p (inl i) = refl
scale-law false x p (inr j) = refl
scale-law true  x p v = p v

_·c_ : Bool → Cycle → Cycle
s ·c (x , p) = scale s x , scale-law s x p

scaleB : Bool → Bool → Bool
scaleB false b = false
scaleB true  b = b

read-additive : (z w : Cycle) (k : Fin 4)
              → readCycle (z ⊞c w) k ≡ readCycle z k ⊕ readCycle w k
read-additive (x , _) (y , _) k0 = refl
read-additive (x , _) (y , _) k1 = refl
read-additive (x , _) (y , _) k2 = refl
read-additive (x , _) (y , _) k3 = refl

read-scalar : (s : Bool) (z : Cycle) (k : Fin 4)
            → readCycle (s ·c z) k ≡ scaleB s (readCycle z k)
read-scalar false (x , _) k0 = refl
read-scalar false (x , _) k1 = refl
read-scalar false (x , _) k2 = refl
read-scalar false (x , _) k3 = refl
read-scalar true  (x , _) k0 = refl
read-scalar true  (x , _) k1 = refl
read-scalar true  (x , _) k2 = refl
read-scalar true  (x , _) k3 = refl

------------------------------------------------------------------------
-- The cokernel side: parity is the class evaluator.
------------------------------------------------------------------------

parity : (Vertex → Bool) → Bool
parity y =
  sum3 (y (inl k0)) (y (inl k1)) (y (inl k2))
    ⊕ sum3 (y (inr k0)) (y (inr k1)) (y (inr k2))

-- im ∂ ⊆ ker parity.  Each edge meets exactly two vertices, so the total
-- vertex-sum of a boundary is zero — here, the row sums and the column
-- sums of a 3 × 3 matrix agree.
parity-∂ : (x : Edge → Bool) → parity (∂ x) ≡ false
parity-∂ x =
    cong (sum3 (∂ x (inl k0)) (∂ x (inl k1)) (∂ x (inl k2)) ⊕_)
         (sym (sum9-transpose (x (k0 , k0)) (x (k0 , k1)) (x (k0 , k2))
                              (x (k1 , k0)) (x (k1 , k1)) (x (k1 , k2))
                              (x (k2 , k0)) (x (k2 , k1)) (x (k2 , k2))))
  ∙ ⊕-self (sum3 (∂ x (inl k0)) (∂ x (inl k1)) (∂ x (inl k2)))

-- ker parity ⊆ im ∂, by explicit construction of a preimage.
preimage : (y : Vertex → Bool) → Edge → Bool
preimage y (k0 , k0) = sum3 (y (inr k0)) (y (inl k1)) (y (inl k2))
preimage y (k0 , k1) = y (inr k1)
preimage y (k0 , k2) = y (inr k2)
preimage y (k1 , k0) = y (inl k1)
preimage y (k1 , k1) = false
preimage y (k1 , k2) = false
preimage y (k2 , k0) = y (inl k2)
preimage y (k2 , k1) = false
preimage y (k2 , k2) = false

even-kernel-is-image : (y : Vertex → Bool) → parity y ≡ false
                     → Σ[ x ∈ (Edge → Bool) ] (∂ x ≡ y)
even-kernel-is-image y h = preimage y , funExt lemma
  where
  r0 = y (inl k0)
  r1 = y (inl k1)
  r2 = y (inl k2)
  c0 = y (inr k0)
  c1 = y (inr k1)
  c2 = y (inr k2)

  rc : sum3 r0 r1 r2 ≡ sum3 c0 c1 c2
  rc = ⊕-solve _ _ h

  lemma : (v : Vertex) → ∂ (preimage y) v ≡ y v
  lemma (inl k0) =
      ⊕-perm5 c0 r1 r2 c1 c2
    ∙ cong (λ w → (w ⊕ r1) ⊕ r2) (sym rc)
    ∙ ⊕-cancel₂ r0 r1 r2
  lemma (inl k1) = cong (_⊕ false) (⊕-identityʳ r1) ∙ ⊕-identityʳ r1
  lemma (inl k2) = cong (_⊕ false) (⊕-identityʳ r2) ∙ ⊕-identityʳ r2
  lemma (inr k0) = ⊕-cancel₂ c0 r1 r2
  lemma (inr k1) = cong (_⊕ false) (⊕-identityʳ c1) ∙ ⊕-identityʳ c1
  lemma (inr k2) = cong (_⊕ false) (⊕-identityʳ c2) ∙ ⊕-identityʳ c2

-- ... and the converse inclusion, packaged as the other direction.
image-is-even-kernel : (y : Vertex → Bool)
                     → Σ[ x ∈ (Edge → Bool) ] (∂ x ≡ y) → parity y ≡ false
image-is-even-kernel y (x , q) = subst (λ z → parity z ≡ false) q (parity-∂ x)

-- parity is onto, so the quotient it computes is 𝔽₂ and not 0.
unitVertex : Vertex → Bool
unitVertex (inl k0) = true
unitVertex (inl k1) = false
unitVertex (inl k2) = false
unitVertex (inr k0) = false
unitVertex (inr k1) = false
unitVertex (inr k2) = false

parity-onto : (b : Bool) → Σ[ y ∈ (Vertex → Bool) ] (parity y ≡ b)
parity-onto false = (λ _ → false) , refl
parity-onto true  = unitVertex , refl

------------------------------------------------------------------------
-- The even subspace — equal to im ∂ by the two inclusions above — has
-- dimension 5.  With V = 6 this is dim coker ∂ = 1, and with E = 9 it is
-- rank-nullity: 9 = 5 + 4.
------------------------------------------------------------------------

Even : Type₀
Even = Σ[ y ∈ (Vertex → Bool) ] (parity y ≡ false)

isPropEvenLaw : (y : Vertex → Bool) → isProp (parity y ≡ false)
isPropEvenLaw y = isSetBool (parity y) false

readEven : Even → (Fin 5 → Bool)
readEven (y , _) k0 = y (inl k0)
readEven (y , _) k1 = y (inl k1)
readEven (y , _) k2 = y (inl k2)
readEven (y , _) k3 = y (inr k0)
readEven (y , _) k4 = y (inr k1)

fillEven : (Fin 5 → Bool) → (Vertex → Bool)
fillEven u (inl k0) = u k0
fillEven u (inl k1) = u k1
fillEven u (inl k2) = u k2
fillEven u (inr k0) = u k3
fillEven u (inr k1) = u k4
fillEven u (inr k2) = (u k3 ⊕ u k4) ⊕ sum3 (u k0) (u k1) (u k2)

fillEven-law : (u : Fin 5 → Bool) → parity (fillEven u) ≡ false
fillEven-law u =
    cong (sum3 (u k0) (u k1) (u k2) ⊕_)
         (⊕-invol (u k3 ⊕ u k4) (sum3 (u k0) (u k1) (u k2)))
  ∙ ⊕-self (sum3 (u k0) (u k1) (u k2))

evenIso : Iso Even (Fin 5 → Bool)
Iso.fun evenIso = readEven
Iso.inv evenIso u = fillEven u , fillEven-law u
Iso.rightInv evenIso u = funExt lemma
  where
  lemma : (k : Fin 5) → readEven (fillEven u , fillEven-law u) k ≡ u k
  lemma k0 = refl
  lemma k1 = refl
  lemma k2 = refl
  lemma k3 = refl
  lemma k4 = refl
Iso.leftInv evenIso (y , h) = Σ≡Prop isPropEvenLaw (funExt lemma)
  where
  lemma : (v : Vertex) → fillEven (readEven (y , h)) v ≡ y v
  lemma (inl k0) = refl
  lemma (inl k1) = refl
  lemma (inl k2) = refl
  lemma (inr k0) = refl
  lemma (inr k1) = refl
  lemma (inr k2) =
      cong ((y (inr k0) ⊕ y (inr k1)) ⊕_) (⊕-solve _ _ h)
    ∙ ⊕-invol (y (inr k0) ⊕ y (inr k1)) (y (inr k2))

evenEquiv : Even ≃ (Fin 5 → Bool)
evenEquiv = isoToEquiv evenIso

-- Bookkeeping only — `refl` on literals, certifying nothing beyond the
-- definitions of V and E.  The content is upstream: dim ker ∂ = 4 is
-- `cycleEquiv`, rank ∂ = dim (ker parity) = 5 is `evenEquiv` together
-- with the two image inclusions, and dim coker ∂ = 1 is what these two
-- lines then say about the certified counts V = 6 and E = 9.
rank-nullity : E ≡ 5 + 4
rank-nullity = refl

cokernel-dimension : V ≡ 5 + 1
cokernel-dimension = refl
