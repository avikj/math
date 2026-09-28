{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- GterTwoCoordinate
--
-- D0026 §7.3, Deltas 37–38,
-- `collab/upstream/raw/D0026-owner-egb-core-transmission-v2-2026-08-16.md` (absent from this repository)
-- lines 2456–2700.
--
-- WHAT IS BEING SETTLED.  D0026 §7.3 asserts, with no proof and no
-- witness, that the two coordinates of the Gter defect
-- 𝔤(P,Σ) = (E(P), ⋏_Σ) are independent:
--
--     "A state space can be fully separated while its boundary
--      description fails to compose.  A cut can compose perfectly while
--      its probes collapse distinct states."
--
-- The source note replaces the assertion by a SURJECTIVITY theorem onto
-- a 2×2 grid (its Theorem 4), on the shape (|Σ₀|,|Σ₁|,|Σ₂|) = (1,2,1),
-- with both of D0026's requested witnesses appearing as two of the four
-- cells.  Everything in it is decidable on a two-element carrier, hence
-- refl after Boolean evaluation.  That is this module.
--
-- THE ENCODING (source note Definition 4.1, taken literally).  A finite
-- cut system is 𝔖 = (Σ₀,Σ₁,Σ₂ ; 𝔗₀₁, 𝔗₁₂, 𝔗₀₂) with the 𝔗 relations,
-- and here relations are Bool-valued tables on finite index types:
-- Rel A B = A → B → Bool.  The glued realization is relational
-- composition, which over a two-element cut is a binary `or` — that is
-- the (−1)-truncation of the coend ∫^{Σ₁} 𝔗₀₁ ⊗ 𝔗₁₂, existential
-- quantification over Σ₁ = {b₁,b₂}.  The probe pool is the
-- INTERFACE-INTRINSIC one of Definition 4.2 (the two profile maps L and
-- R), which is the pool with the greatest separating power available at
-- the interface; any smaller pool only makes the theorem easier.
--
-- Σ₀ = Σ₂ = Unit and Σ₁ = Bool, with b₁ := true and b₂ := false.  Both
-- coordinates are then functions of the SAME data (𝔗₀₁, 𝔗₁₂), which is
-- the whole point of §4.1: the independence is not manufactured by
-- letting probes and gluing range over unrelated parameters.
--
-- WHAT THE FOUR CELLS SAY:
--
--     𝔖₁  S_L = S_R = {b₁}       sep = T , comp = T
--     𝔖₂  S_L = {b₁}, S_R = {b₂} sep = T , comp = F   witness (i)
--     𝔖₃  S_L = S_R = {b₁,b₂}    sep = F , comp = T   witness (ii)
--     𝔖₄  S_L = S_R = ∅          sep = F , comp = F
--
--   witness (i)  — a perfect instrument on a broken interface: the
--     probes separate the two cut states completely, yet no cut state
--     carries the direct a ⇝ c process, so the tear is nonzero.
--   witness (ii) — a perfect interface on a blind instrument: the
--     gluing reproduces 𝔗₀₂ exactly, so the tear vanishes, while the
--     probes cannot tell b₁ from b₂ at all.
--
-- CONTENTS
--
--   §1  Rel, Σ₀/Σ₁/Σ₂, _⊙_   the relational cut system and the glued
--                            realization.
--   §2  L, R, sep, comp,     Definition 4.2's intrinsic probes, the two
--       tear, cell           coordinates, and the tear against a
--                            declared direct realization.
--   §3  𝔖₁ … 𝔖₄              the four systems of the Theorem 4 table.
--   §4  row1 … row4          the table, four refls; `theorem4`, the
--       theorem4             four-cell surjectivity assembled from them.
--   §5  wit-i-*, wit-ii-*    Corollary 5's two witnesses.  The two sep
--                            statements are NOT new refls — each is a
--                            projection (`cong fst`) of its row, which
--                            is the honest bookkeeping: the witnesses
--                            ARE rows 2 and 3.  Two further refls carry
--                            the tear values.
--   §6  sep-not-a-function-  Theorem 4's stated consequence: neither
--       of-comp, and dually  coordinate is a function of the other.
--
--   SIX refl clauses in total (four rows, two tears), exactly as §4.7
--   predicted; everything else is derived from them.
--
-- Theorem 4 in full, as a surjectivity statement onto
--   Bool × Bool with an explicit cut system in every fiber; both of
--   D0026's witnesses, including their tear values against the declared
--   direct realization 𝔗₀₂ = {(a,c)}; and the two non-functionality
--   corollaries.  The relational composite is defined once, generally,
--   and the four systems are the only data supplied — every value below
--   is a kernel reduction, not a transcribed table.
--
--   Nothing here is measured, fitted, or floating-point: the carrier has
--   two elements and every verdict is a kernel reduction.
--
-- No postulates, no holes, no TERMINATING, no primTrustMe.
------------------------------------------------------------------------

module GterTwoCoordinate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; _and_ ; _or_ ; true≢false)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (_×_ ; Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- §1  The relational cut system (Definition 4.1)
--
-- Relations are Bool-valued tables on finite index types.  The shape is
-- (|Σ₀|,|Σ₁|,|Σ₂|) = (1,2,1), the minimal shape the source note's
-- Theorem 6 identifies.
------------------------------------------------------------------------

Rel : Type₀ → Type₀ → Type₀
Rel A B = A → B → Bool

Σ₀ Σ₁ Σ₂ : Type₀
Σ₀ = Unit
Σ₁ = Bool          -- the cut states {b₁ , b₂}, b₁ := true, b₂ := false
Σ₂ = Unit

-- The glued realization: relational composition through Σ₁.  Over a
-- two-element cut the existential ∃ b ∈ Σ₁ is a binary `or`, so this is
-- the (−1)-truncation of the coend ∫^{Σ₁} 𝔗₀₁ ⊗ 𝔗₁₂ written out.
_⊙_ : Rel Σ₀ Σ₁ → Rel Σ₁ Σ₂ → Rel Σ₀ Σ₂
(s ⊙ t) a c = ((s a false) and (t false c)) or ((s a true) and (t true c))

-- A cut system, with 𝔗₀₂ left off: Theorem 4 is proved BEFORE 𝔗₀₂ is
-- chosen, which is what makes it sharp — the independence is not an
-- artifact of the direct realization being a free datum.
CutSystem : Type₀
CutSystem = Rel Σ₀ Σ₁ × Rel Σ₁ Σ₂

------------------------------------------------------------------------
-- §2  The interface-intrinsic probes and the two coordinates
--
-- Definition 4.2.  L(b) = { a : (a,b) ∈ 𝔗₀₁ } and R(b) = { c : (b,c) ∈
-- 𝔗₁₂ }; over Σ₀ = Σ₂ = Unit each profile is a single Bool, so
-- E(P_can) = Δ_{Σ₁} exactly when the two cut states differ in at least
-- one profile.
------------------------------------------------------------------------

eqb : Bool → Bool → Bool
eqb true  c = c
eqb false c = not c

L : Rel Σ₀ Σ₁ → Σ₁ → Bool
L s b = s tt b

R : Rel Σ₁ Σ₂ → Σ₁ → Bool
R t b = t b tt

-- sep 𝔖  ⟺  E(P_can) = Δ_{Σ₁}: the probes {L,R} separate b₁ from b₂.
sep : Rel Σ₀ Σ₁ → Rel Σ₁ Σ₂ → Bool
sep s t = not ((eqb (L s false) (L s true)) and (eqb (R t false) (R t true)))

-- compCut 𝔖  ⟺  𝔗₀₁ ⊙ 𝔗₁₂ ≠ ∅: some cut state carries the a ⇝ c
-- composite.  D0026 §7.3 calls this coordinate `comp`; it is `compCut`
-- here because a top-level `comp` collides with `comp` from
-- `Cubical/Core/Primitives.agda:16`, which every `--cubical` module has
-- in scope, and the collision is FATAL, not shadowing.
compCut : Rel Σ₀ Σ₁ → Rel Σ₁ Σ₂ → Bool
compCut s t = (s ⊙ t) tt tt

-- The tear ⋏(𝔖) = (𝔗₀₂ ≠ 𝔗₀₁ ⊙ 𝔗₁₂), at the relational truncation
-- level.
tear : Rel Σ₀ Σ₁ → Rel Σ₁ Σ₂ → Rel Σ₀ Σ₂ → Bool
tear s t d = not (eqb ((s ⊙ t) tt tt) (d tt tt))

-- The two-coordinate defect 𝔤 of D0026 §7.3, as one map.
cell : CutSystem → Bool × Bool
cell (s , t) = sep s t , compCut s t

sepOf compOf : CutSystem → Bool
sepOf  𝔖 = fst (cell 𝔖)
compOf 𝔖 = snd (cell 𝔖)

------------------------------------------------------------------------
-- §3  The four systems of the Theorem 4 table
--
-- A subset S ⊆ Σ₁ is its characteristic function; 𝔗₀₁ and 𝔗₁₂ are that
-- subset read as a relation against the one-point Σ₀, resp. Σ₂.
------------------------------------------------------------------------

χ-b₁ χ-b₂ χ-both χ-none : Σ₁ → Bool
χ-b₁   b = b            -- { b₁ }
χ-b₂   b = not b        -- { b₂ }
χ-both _ = true         -- { b₁ , b₂ }
χ-none _ = false        -- ∅

asL : (Σ₁ → Bool) → Rel Σ₀ Σ₁
asL χ _ b = χ b

asR : (Σ₁ → Bool) → Rel Σ₁ Σ₂
asR χ b _ = χ b

𝔖₁ 𝔖₂ 𝔖₃ 𝔖₄ : CutSystem
𝔖₁ = asL χ-b₁   , asR χ-b₁          -- S_L = {b₁}      S_R = {b₁}
𝔖₂ = asL χ-b₁   , asR χ-b₂          -- S_L = {b₁}      S_R = {b₂}
𝔖₃ = asL χ-both , asR χ-both        -- S_L = {b₁,b₂}   S_R = {b₁,b₂}
𝔖₄ = asL χ-none , asR χ-none        -- S_L = ∅         S_R = ∅

------------------------------------------------------------------------
-- §4  Theorem 4: four-cell surjectivity
--
-- The four rows of the source note's table, each a kernel reduction,
-- and then the surjectivity statement they assemble into.  Note that
-- `theorem4` introduces no new equation: it is the table, re-indexed by
-- its own image.
------------------------------------------------------------------------

row1 : cell 𝔖₁ ≡ (true  , true )
row1 = refl

row2 : cell 𝔖₂ ≡ (true  , false)
row2 = refl

row3 : cell 𝔖₃ ≡ (false , true )
row3 = refl

row4 : cell 𝔖₄ ≡ (false , false)
row4 = refl

theorem4 : (v : Bool × Bool) → Σ[ 𝔖 ∈ CutSystem ] cell 𝔖 ≡ v
theorem4 (true  , true ) = 𝔖₁ , row1
theorem4 (true  , false) = 𝔖₂ , row2
theorem4 (false , true ) = 𝔖₃ , row3
theorem4 (false , false) = 𝔖₄ , row4

------------------------------------------------------------------------
-- §5  Corollary 5: D0026's two asserted witnesses
--
-- Adjoin the direct realization 𝔗₀₂ = {(a,c)} to rows 2 and 3.  The two
-- separation facts are projections of the rows above rather than fresh
-- refls: the witnesses ARE those rows, and saying so costs nothing and
-- keeps the certificate count honest.
------------------------------------------------------------------------

𝔗₀₂ : Rel Σ₀ Σ₂
𝔗₀₂ _ _ = true

-- Witness (i): separated, tear ≠ 0.  A perfect instrument on a broken
-- interface — b₁ meets the left boundary only, b₂ the right only, so no
-- cut state carries the direct a ⇝ c process that 𝔗₀₂ declares.
wit-i-sep : sep (fst 𝔖₂) (snd 𝔖₂) ≡ true
wit-i-sep = cong fst row2

wit-i-tear : tear (fst 𝔖₂) (snd 𝔖₂) 𝔗₀₂ ≡ true
wit-i-tear = refl

-- Witness (ii): tear = 0, probes collapse distinct states.  A perfect
-- interface on a blind instrument — the gluing reproduces 𝔗₀₂ exactly,
-- while E(P_can) = Σ₁ × Σ₁.
wit-ii-collapse : sep (fst 𝔖₃) (snd 𝔖₃) ≡ false
wit-ii-collapse = cong fst row3

wit-ii-notear : tear (fst 𝔖₃) (snd 𝔖₃) 𝔗₀₂ ≡ false
wit-ii-notear = refl

------------------------------------------------------------------------
-- §6  "Neither coordinate is a function of the other"
--
-- Theorem 4's stated consequence, and the exact content of D0026 §7.3's
-- independence claim.  Rows 1 and 3 agree on comp and differ on sep;
-- rows 1 and 2 agree on sep and differ on comp.
------------------------------------------------------------------------

sep-not-a-function-of-comp :
  ¬ ((𝔖 𝔖' : CutSystem) → compOf 𝔖 ≡ compOf 𝔖' → sepOf 𝔖 ≡ sepOf 𝔖')
sep-not-a-function-of-comp h = true≢false (h 𝔖₁ 𝔖₃ refl)

comp-not-a-function-of-sep :
  ¬ ((𝔖 𝔖' : CutSystem) → sepOf 𝔖 ≡ sepOf 𝔖' → compOf 𝔖 ≡ compOf 𝔖')
comp-not-a-function-of-sep h = true≢false (h 𝔖₁ 𝔖₂ refl)
