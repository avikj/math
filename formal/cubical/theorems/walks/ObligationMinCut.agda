{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ObligationMinCut
--
-- Executes OBLIGATION.md (absent from this repository) §7 (the min-cut extraction specified there)
-- for the tractable self-application subgraph: the 1-neighbourhood
-- own model of its dependency structure applied to the note that defines it.
--
-- The full extraction (869 nodes / 1292 clean edges, mode census, the
-- corpus audit-burden interval [115,222], and Cor. O2.4's exact path count
-- 133) is computed by exact integer algorithms elsewhere.  The checked
-- part: a concrete finite network on which a feasible integer flow and an
-- s⋆–t⋆ cut are exhibited, and the weak-duality equality
--
--     value(flow)  ≡  capacity(cut)  ≡  2
--
-- is checked by the kernel.  By max-flow/min-cut weak duality
-- (value f ≤ cap C for EVERY feasible f and EVERY cut C), an equality
-- certifies both optima at once: the flow is maximum and the cut is
-- minimum.  So the audit burden of the OBLIGATION self-network, under the
-- pessimistic reading of the one UNKNOWN edge (THRESHOLD→OBLIGATION taken as
-- a STATEMENT conduit), is exactly 2, with no floating point anywhere.
--
-- Nothing is postulated; there are no holes; --safe is on.
------------------------------------------------------------------------

module ObligationMinCut where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat            using (ℕ; zero; suc; _+_; snotz)
open import Cubical.Data.Nat.Order      using (_≤_; _<_)
open import Cubical.Data.Empty          using (⊥) renaming (rec to ⊥-elim)
open import Cubical.Data.Sum            using (_⊎_; inl; inr)

------------------------------------------------------------------------
-- §1  The extracted network.
--
-- Vertices.  s⋆ = super-source, t⋆ = super-sink; O = OBLIGATION.md (absent from this repository),
-- H = THRESHOLD_GENERATION_DICHOTOMY.md (absent from this repository), R = RESEARCH_SYSTEM.md (absent from this repository).
-- O and H are the open-obligation packets (mechanical openness grep hits);
-- R is a conduit source but carries no open obligation, so no s⋆→R edge.
-- Target set T = { O }: the note whose soundness §7 is certifying.

data V : Type where
  s⋆ O H R t⋆ : V

-- Edges of the repair network N (Theorem O3 construction).
--   e1 : s⋆ → O   discharge-arc for the open obligation O          cap 1
--   e2 : s⋆ → H   discharge-arc for the open obligation H          cap 1
--   e3 : H  → O   conduit  THRESHOLD→OBLIGATION (STATEMENT, pess.) cap 1
--   e4 : R  → O   conduit  RESEARCH_SYSTEM→OBLIGATION (STATEMENT)  cap 1
--   e5 : O  → t⋆  target-arc  O ∈ T                                cap ∞
data E : Type where
  e1 e2 e3 e4 e5 : E

src : E → V
src e1 = s⋆
src e2 = s⋆
src e3 = H
src e4 = R
src e5 = O

tgt : E → V
tgt e1 = O
tgt e2 = H
tgt e3 = O
tgt e4 = O
tgt e5 = t⋆

-- ∞ on the target-arc is any capacity exceeding the total finite capacity;
-- 3 > 2 suffices and keeps every number concrete.
cap : E → ℕ
cap e1 = 1
cap e2 = 1
cap e3 = 1
cap e4 = 1
cap e5 = 3

-- The exhibited flow.  Two unit routes s⋆→O→t⋆ and s⋆→H→O→t⋆.
flow : E → ℕ
flow e1 = 1
flow e2 = 1
flow e3 = 1
flow e4 = 0
flow e5 = 2

------------------------------------------------------------------------
-- §2  Feasibility of the flow.

-- (a) capacity respect  0 ≤ flow e ≤ cap e  (lower bound is automatic in ℕ).
cap-e1 : flow e1 ≤ cap e1
cap-e1 = 0 , refl                      -- 0 + 1 ≡ 1

cap-e2 : flow e2 ≤ cap e2
cap-e2 = 0 , refl

cap-e3 : flow e3 ≤ cap e3
cap-e3 = 0 , refl

cap-e4 : flow e4 ≤ cap e4
cap-e4 = 1 , refl                      -- 1 + 0 ≡ 1

cap-e5 : flow e5 ≤ cap e5
cap-e5 = 1 , refl                      -- 1 + 2 ≡ 3

-- (b) conservation: total in ≡ total out, at every internal vertex.
--     inflow(v)  = Σ flow over edges with tgt ≡ v
--     outflow(v) = Σ flow over edges with src ≡ v
-- Edges into O: e1,e3,e4.  Out of O: e5.
cons-O : flow e1 + flow e3 + flow e4 ≡ flow e5
cons-O = refl                          -- 1 + 1 + 0 ≡ 2

-- Into H: e2.  Out of H: e3.
cons-H : flow e2 ≡ flow e3
cons-H = refl                          -- 1 ≡ 1

-- Into R: none.  Out of R: e4.
cons-R : 0 ≡ flow e4
cons-R = refl                          -- 0 ≡ 0

------------------------------------------------------------------------
-- §3  The flow value, measured on both sides.

-- Value out of the source = Σ flow over edges leaving s⋆ (e1,e2).
value-source : ℕ
value-source = flow e1 + flow e2

-- Value into the sink = Σ flow over edges entering t⋆ (e5).
value-sink : ℕ
value-sink = flow e5

value-balanced : value-source ≡ value-sink
value-balanced = refl                  -- 2 ≡ 2  (global conservation)

------------------------------------------------------------------------
-- §4  The cut C = { e1 , e2 } and its validity.

-- Capacity of the cut = Σ cap over its edges.
cutCap : ℕ
cutCap = cap e1 + cap e2

-- C is an s⋆–t⋆ cut: it contains EVERY edge leaving the source, so deleting
-- C isolates s⋆ and no s⋆⇝t⋆ path can survive.  Proven by the fact that the
-- only edges e with src e ≡ s⋆ are e1 and e2.
code : V → ℕ
code s⋆ = 0
code O  = 1
code H  = 2
code R  = 3
code t⋆ = 4

-- discriminator: H, R, O, t⋆ are not the source.
notSrc-e3 : src e3 ≡ s⋆ → ⊥
notSrc-e3 p = snotz (cong code p)   -- code H ≡ code s⋆  ⇒  2 ≡ 0

notSrc-e4 : src e4 ≡ s⋆ → ⊥
notSrc-e4 p = snotz (cong code p)   -- code R ≡ 0

notSrc-e5 : src e5 ≡ s⋆ → ⊥
notSrc-e5 p = snotz (cong code p)   -- code O ≡ 0

-- Every source-boundary edge is in the cut {e1,e2}.
cut-covers-source : (e : E) → src e ≡ s⋆ → (e ≡ e1) ⊎ (e ≡ e2)
cut-covers-source e1 _ = inl refl
cut-covers-source e2 _ = inr refl
cut-covers-source e3 p = ⊥-elim (notSrc-e3 p)
cut-covers-source e4 p = ⊥-elim (notSrc-e4 p)
cut-covers-source e5 p = ⊥-elim (notSrc-e5 p)

------------------------------------------------------------------------
-- §5  THE CERTIFICATE:  value(flow) ≡ capacity(cut).
--
-- Weak duality gives  value(flow) ≤ cutCap  a priori; the reverse holds
-- here by the computed equality, so the flow is a maximum flow and the cut
-- is a minimum cut, and their common value — the audit burden of the
-- OBLIGATION self-network — is 2.

audit-burden : ℕ
audit-burden = 2

flow-is-max-cut-is-min : value-source ≡ cutCap
flow-is-max-cut-is-min = refl          -- 2 ≡ 2

certified-burden-source : value-source ≡ audit-burden
certified-burden-source = refl

certified-burden-cut : cutCap ≡ audit-burden
certified-burden-cut = refl

-- Positivity: the burden is not vacuous — at least one audit is unavoidable
-- (Cor. O3.1's lower bound, here k = 2 edge-disjoint routes).
burden-positive : 0 < audit-burden
burden-positive = 1 , refl             -- 1 + 1 ≡ 2, i.e. suc 0 ≤ 2
