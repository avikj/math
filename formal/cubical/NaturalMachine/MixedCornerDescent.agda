{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.MixedCornerDescent
--
-- Factory IV §X, Theorem 70 — "mixed-corner descent" — as a checked
-- well-founded descent, i.e. as the SPECIFICATION its compiler would
-- have to meet, with nothing arithmetic smuggled in.
--
-- WHERE THIS COMES FROM.  The owner's delta
-- `collab/upstream/library/raw/ETERNAL_GOLDEN_BRAID_THEOREM_FACTORY_IV_2026-08-14.md` (absent from this repository)
-- §X ("The mixed radius–charge compiler") sets e = Ω − 1 ∈ {0,1}, takes
-- the state space V_R = {1,…,R} × {0,1} with (r,0) an exact prime pair at
-- radius r and (r,1) a prime–semiprime pair at radius r, target (1,0),
-- and defines the boxed rank
--
--     κ(r,e) = 2(r−1) + e,          unique zero (1,0).
--
-- Theorem 70 then reads: if every reachable non-target state has a
-- bounded proof-carrying transition v → v′ with κ(v′) < κ(v) and the
-- center strictly increasing, then twin primes are infinite.  Its whole
-- mathematical content is the descent — "the natural-number rank
-- strictly decreases; the process terminates at its unique rank-zero
-- state" — and that content is finite, decidable, and belongs in a
-- proof assistant rather than in prose.
-- In this module the
-- descent half is proved, the arithmetic half is a hypothesis, and the
-- interface between them is a type, so that an edge theorem composes
-- with this for free.  Sibling formalizations of the same §: `ChenProjector.agda`
-- (Theorem 58, the charge projector), `CornerProjectors.agda` (§XI,
-- P_r P_c = P_c P_r together with the marginal-to-joint counterexample),
-- `ThreeChannels.agda` (the channel refinement of the projector).
--
-- THE HILBERT MOVE.  Axiomatize, then decide.  Everything Theorem 70
-- says about *arithmetic* is quarantined into one abstract datum
--
--     Descent = (s : State) → ¬ (κ s ≡ 0) → Σ[ t ∈ State ] (κ t < κ s)
--
-- — "every non-corner state has a next state, carrying a proof that the
-- rank drops" — and everything it says about *termination* is then a
-- theorem with no hypotheses left to argue about.  The Σ is the point:
-- the transition and its certificate travel together, so the compiler
-- cannot emit an edge it has not justified.  Factory IV's own gain over
-- Factory III is visible in this type and only here: Factory III
-- admitted (r,0) → (s,0) with s < r; the mixed datum admits
-- (r,0) → (r−1,1), trading one unit of charge for one unit of radius and
-- purifying later through (1,1) → (1,0).  Both are instances of the same
-- Descent, which is why the mixed compiler is strictly more permissive
-- and terminates just as surely.
--
-- COORDINATES.  State = ℕ × Bool with the first coordinate r ∸ 1 (so
-- Factory IV's radius-one target is our 0) and the second coordinate the
-- charge defect e as a Bool.  Then κ(r,e) = 2·r + e is `rank`, defined by
-- structural recursion so that it computes, and the corner is (0,false).
-- Reindexing by r ∸ 1 is not cosmetic: it makes "unique zero" a statement
-- about ℕ's own zero, so rank-zero uniqueness is three pattern matches
-- rather than an inequality argument, and it removes the bound R, which
-- Theorem 70 never uses (the descent is well-founded on all of ℕ × Bool;
-- R is a bookkeeping convenience in the source).
--
-- WHY FUEL, AND NOT WELL-FOUNDED RECURSION.  The trajectory is built by
-- structural recursion on a fuel argument k with the invariant κ s ≤ k,
-- started at k = κ s and closed by ≤-refl — the choice, and the discipline
-- of *proving that the chosen fuel suffices* rather than assuming it,
-- is taken from `formal/pairfield/Pairfield/WalkFalsifier.lean`, whose
-- header states it exactly: "everything here is written by structural
-- recursion on fuel, not by well-founded recursion, precisely so that
-- `decide` can reduce it in the kernel.  A well-founded definition would
-- be executable by `#eval` and *not* provable by `decide`.  Choosing fuel
-- is choosing which of the three modes the object supports."  The same
-- trade holds here with `refl` in place of `decide`: because `descend`
-- recurses structurally on fuel and every ingredient computes, the
-- trajectory of a concrete start state is available BY EVALUATION
-- (`example-trajectory` below is a `refl`), which an accessibility-based
-- definition would not give under `--safe` without extra work.  Fuel is
-- not a weakening: `fuel-suffices` is the theorem that κ(start) is enough,
-- so nothing is assumed that is not proved.
--
-- WHAT THIS MODULE PROVES (no holes, no postulates, --safe):
--
--   State, corner, rank, κ   the mixed state space and Factory IV's rank
--   rank-zero-unique         κ s ≡ 0 → s ≡ (0,false): the corner is the
--                            unique zero of the rank — Theorem 70's
--                            "its unique rank-zero state"
--   corner-rank              κ corner ≡ 0, the converse half
--   rank-zero-contr          the two together, sharpened: the fiber of κ
--                            over 0 is CONTRACTIBLE, so "the target" is
--                            well-defined as a type, not merely as a
--                            named element
--   Descent                  the proof-carrying transition datum (Σ-data:
--                            next state ⊗ certificate that κ drops)
--   Reaches                  the reachability predicate generated by a
--                            Descent: arrived at rank 0, or one certified
--                            step and then reachability
--   descend, fuel-suffices   fuel-based structural recursion, plus the
--                            proof that fuel κ(start) suffices
--   descent-theorem          Theorem 70's descent half: from ANY start
--                            state, a Descent reaches the corner
--   traj                     the trajectory as a List State
--   endpoint, endpoint-corner, traj-last
--                            the endpoint proof: the last entry of the
--                            trajectory is the corner (0,false)
--   steps-bound              at most κ(start) transitions
--   traj-length, traj-bound  hence the trajectory has at most κ(start)+1
--                            states — the bound is attained, see the
--                            example
--   mixedStep, mixedDescent  Factory IV's own edges as an INHABITANT of
--                            Descent: (r,0) → (r−1,1) mixed, (r,1) → (r,0)
--                            purifying
--   example-trajectory       (2,true) ↦ radius 3, charge defect 1, κ = 5:
--                            the six-state trajectory computes by refl,
--                            saturating traj-bound
------------------------------------------------------------------------

module NaturalMachine.MixedCornerDescent where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz ; isSetℕ)
open import Cubical.Data.Nat.Order
  using (_≤_ ; _<_ ; ≤-refl ; ≤-trans ; suc-≤-suc ; pred-≤-pred
        ; zero-≤ ; ≤0→≡0 ; <≤-trans)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- §1  The mixed state space and Factory IV's rank.
--
-- Factory IV's V_R = {1,…,R} × {0,1} is reindexed by r ↦ r ∸ 1 and
-- unbounded (the bound R plays no role in the descent).  The charge
-- defect e = Ω − 1 is a Bool because it is a two-valued coordinate and
-- nothing here does arithmetic with it beyond "is it set".
--
-- κ(r,e) = 2·r + e is defined by structural recursion rather than as
-- `2 * r + …` so that it computes on constructors: every statement below
-- about a concrete state is then closed by refl, which is the whole
-- reason the fuel discipline is worth its cost (see the header).
------------------------------------------------------------------------

State : Type
State = ℕ × Bool

-- Factory IV's target (1,0), in the reindexed coordinates.
corner : State
corner = (0 , false)

rank : ℕ → Bool → ℕ
rank zero    false = zero
rank zero    true  = suc zero
rank (suc r) e     = suc (suc (rank r e))

κ : State → ℕ
κ (r , e) = rank r e

-- The one arithmetic fact about the rank that the descent needs: raising
-- the charge defect costs exactly one, which is why a mixed edge
-- (r,0) → (r−1,1) is a strict gain (two units of radius bought, one unit
-- of charge spent).  Everything else follows from this by pattern match.
rank-true : (r : ℕ) → rank r true ≡ suc (rank r false)
rank-true zero    = refl
rank-true (suc r) = cong (λ n → suc (suc n)) (rank-true r)

------------------------------------------------------------------------
-- §2  Rank-zero uniqueness — Theorem 70's "unique rank-zero state".
--
-- Stated in three forms of increasing strength: the implication, the
-- converse, and the two combined as contractibility of the fiber.  The
-- third is the form that makes "the target" a well-defined object rather
-- than a chosen element, which is what one wants before quantifying over
-- descents that are supposed to land on it.
------------------------------------------------------------------------

rank-zero-unique : (s : State) → κ s ≡ 0 → s ≡ corner
rank-zero-unique (zero  , false) _ = refl
rank-zero-unique (zero  , true)  h = Empty.rec (snotz h)
rank-zero-unique (suc r , e)     h = Empty.rec (snotz h)

corner-rank : κ corner ≡ 0
corner-rank = refl

-- The fiber of κ over 0 is contractible: the corner exists, is unique,
-- and its rank-zero certificate is unique too (ℕ is a set).
rank-zero-contr : isContr (Σ[ s ∈ State ] (κ s ≡ 0))
rank-zero-contr = (corner , corner-rank) , contract
  where
    contract : (x : Σ[ s ∈ State ] (κ s ≡ 0)) → (corner , corner-rank) ≡ x
    contract (s , p) =
      ΣPathP ( sym (rank-zero-unique s p)
             , isProp→PathP
                 (λ i → isSetℕ (κ (sym (rank-zero-unique s p) i)) 0)
                 corner-rank p )

-- Contrapositive, in the form the descent consumes: away from the corner
-- the rank is positive, so there is something to spend.
non-corner : (s : State) → ¬ (s ≡ corner) → ¬ (κ s ≡ 0)
non-corner s ne h = ne (rank-zero-unique s h)

------------------------------------------------------------------------
-- §3  The descent datum.
--
-- Theorem 70's hypothesis, and nothing else: to every non-corner state,
-- a next state TOGETHER WITH a certificate that the rank strictly drops.
-- Carried as Σ-data so the two cannot be separated — an edge without its
-- certificate is not an element of this type, which is the formal content
-- of "proof-carrying transition".
--
-- Note what is deliberately absent: any bound on the transition (Factory
-- IV's "bounded"), any center, any arithmetic.  The bound and the center
-- are what make the produced family cofinal; they are orthogonal to
-- termination.
------------------------------------------------------------------------

Descent : Type
Descent = (s : State) → ¬ (κ s ≡ 0) → Σ[ t ∈ State ] (κ t < κ s)

-- Projections, for readability at use sites.
nextOf : (D : Descent) (s : State) → ¬ (κ s ≡ 0) → State
nextOf D s nz = fst (D s nz)

dropOf : (D : Descent) (s : State) (nz : ¬ (κ s ≡ 0))
       → κ (nextOf D s nz) < κ s
dropOf D s nz = snd (D s nz)

------------------------------------------------------------------------
-- §4  Reachability, generated by a descent datum.
--
-- `arrived` is the corner (recognised by its rank, per §2); `onward`
-- takes one certified step and continues.  This is the predicate the
-- descent theorem inhabits; the trajectory in §6 is read off from it, so
-- the list and its endpoint proof are the same object seen twice and
-- cannot drift apart.
------------------------------------------------------------------------

data Reaches (D : Descent) : State → Type where
  arrived : {s : State} → κ s ≡ 0 → Reaches D s
  onward  : {s : State} (nz : ¬ (κ s ≡ 0))
          → Reaches D (nextOf D s nz) → Reaches D s

------------------------------------------------------------------------
-- §5  The descent theorem, by fuel.
--
-- `rankDec` is the decision "am I at the corner", by pattern match — it
-- computes, which is what lets §7's example reduce.  `descend` recurses
-- structurally on the fuel k under the invariant κ s ≤ k; the fuel-zero
-- non-corner case is impossible and is discharged, which is precisely the
-- statement that the invariant is doing work.  `fuel-suffices` then feeds
-- κ(start) and ≤-refl: the chosen fuel is PROVED sufficient, never
-- assumed (WalkFalsifier.lean's discipline, cited in the header).
------------------------------------------------------------------------

rankDec : (s : State) → (κ s ≡ 0) ⊎ (¬ (κ s ≡ 0))
rankDec (zero  , false) = inl refl
rankDec (zero  , true)  = inr snotz
rankDec (suc r , e)     = inr snotz

descend : (D : Descent) (k : ℕ) (s : State) → κ s ≤ k
        → (κ s ≡ 0) ⊎ (¬ (κ s ≡ 0)) → Reaches D s
descend D k       s h (inl z)  = arrived z
descend D zero    s h (inr nz) = Empty.rec (nz (≤0→≡0 h))
descend D (suc k) s h (inr nz) =
  onward nz
    (descend D k (nextOf D s nz)
       (pred-≤-pred (<≤-trans (dropOf D s nz) h))
       (rankDec (nextOf D s nz)))

-- κ(start) units of fuel suffice.  (The invariant closes with ≤-refl;
-- that this is the *least* sufficient fuel is §6's steps-bound.)
fuel-suffices : (D : Descent) (s : State) → Reaches D s
fuel-suffices D s = descend D (κ s) s ≤-refl (rankDec s)

-- Theorem 70, descent half: from ANY start state, a proof-carrying
-- descent reaches the corner.  (`descent-theorem` returns the
-- reachability witness; §6 turns it into a trajectory landing on
-- (0,false), which is the statement in Factory IV's words: "the process
-- terminates at its unique rank-zero state".)
descent-theorem : (D : Descent) (s : State) → Reaches D s
descent-theorem = fuel-suffices

------------------------------------------------------------------------
-- §6  The trajectory, its endpoint, and its bound.
--
-- Read off the reachability witness by structural recursion — no fuel
-- needed here, because the witness is already the finite object.  The
-- bound is proved on the witness too, so it holds for EVERY descent, not
-- only the one fuel produced.
------------------------------------------------------------------------

traj : {D : Descent} {s : State} → Reaches D s → List State
traj {s = s} (arrived _)  = s ∷ []
traj {s = s} (onward _ r) = s ∷ traj r

steps : {D : Descent} {s : State} → Reaches D s → ℕ
steps (arrived _)  = 0
steps (onward _ r) = suc (steps r)

endpoint : {D : Descent} {s : State} → Reaches D s → State
endpoint {s = s} (arrived _)  = s
endpoint         (onward _ r) = endpoint r

-- The endpoint is the corner: rank-zero uniqueness (§2) applied at the
-- one place the descent stops.
endpoint-corner : {D : Descent} {s : State} (r : Reaches D s)
                → endpoint r ≡ corner
endpoint-corner {s = s} (arrived z)  = rank-zero-unique s z
endpoint-corner         (onward _ r) = endpoint-corner r

-- …and the endpoint really is the last entry of the trajectory list.
-- (`lastOf` takes a default; the lemma is proved for an arbitrary
-- default, which is what makes the induction go through, since the
-- trajectory of the tail starts at the successor state.)
lastOf : State → List State → State
lastOf d []       = d
lastOf d (x ∷ xs) = lastOf x xs

traj-last : {D : Descent} {s : State} (d : State) (r : Reaches D s)
          → lastOf d (traj r) ≡ endpoint r
traj-last d (arrived _)  = refl
traj-last {s = s} d (onward _ r) = traj-last s r

-- The two combined: every trajectory ends at Factory IV's target.
traj-ends-at-corner : {D : Descent} {s : State} (r : Reaches D s)
                    → lastOf s (traj r) ≡ corner
traj-ends-at-corner {s = s} r = traj-last s r ∙ endpoint-corner r

-- Trajectory bound.  At most κ(start) transitions…
steps-bound : {D : Descent} {s : State} (r : Reaches D s) → steps r ≤ κ s
steps-bound (arrived _) = zero-≤
steps-bound {D = D} {s = s} (onward nz r) =
  ≤-trans (suc-≤-suc (steps-bound r)) (dropOf D s nz)

-- …and the list has exactly one more entry than there are transitions…
traj-length : {D : Descent} {s : State} (r : Reaches D s)
            → length (traj r) ≡ suc (steps r)
traj-length (arrived _)  = refl
traj-length (onward _ r) = cong suc (traj-length r)

-- …so the trajectory has at most κ(start) + 1 states.  This is the
-- quantitative form of Theorem 70's "the process terminates".
traj-bound : {D : Descent} {s : State} (r : Reaches D s)
           → length (traj r) ≤ suc (κ s)
traj-bound r =
  subst (_≤ suc (κ _)) (sym (traj-length r)) (suc-≤-suc (steps-bound r))

------------------------------------------------------------------------
-- §7  Factory IV's own edges, as an inhabitant of the specification.
--
--   (r,1) → (r,0)     purification: spend the charge defect, keep the
--                     radius.  At r = 0 this is Factory IV's
--                     (1,1) → (1,0), the step its §XII calls the full
--                     problem.
--   (r+1,0) → (r,1)   the MIXED edge, the one Factory III forbade: buy
--                     one unit of radius by incurring one unit of charge.
--                     κ drops by exactly one (rank-true), which is why
--                     the trade is admissible at all.
--
-- The corner has no outgoing edge, and the clause that would need one is
-- discharged from its own non-corner hypothesis — so `mixedDescent` is
-- total without ever pretending the corner steps anywhere.
------------------------------------------------------------------------

mixedStep : State → State
mixedStep (r     , true)  = (r , false)
mixedStep (zero  , false) = corner
mixedStep (suc r , false) = (r , true)

mixedDescent : Descent
mixedDescent (r     , true)  nz = (r , false) , (0 , sym (rank-true r))
mixedDescent (zero  , false) nz = Empty.rec (nz refl)
mixedDescent (suc r , false) nz = (r , true) , (0 , cong suc (rank-true r))

-- The datum's transitions are `mixedStep`, wherever `mixedStep` is
-- defined to move at all.
mixedDescent-step : (s : State) (nz : ¬ (κ s ≡ 0))
                  → nextOf mixedDescent s nz ≡ mixedStep s
mixedDescent-step (r     , true)  nz = refl
mixedDescent-step (zero  , false) nz = Empty.rec (nz refl)
mixedDescent-step (suc r , false) nz = refl

------------------------------------------------------------------------
-- §8  The specification, evaluated.
--
-- Start at (2,true): radius 3 with charge defect 1, κ = 5.  The mixed
-- compiler purifies, then alternates buy/purify down to the corner.  The
-- trajectory is obtained BY EVALUATION — the proof below is `refl` — and
-- has six states, saturating `traj-bound` at κ + 1 = 6.  That the bound
-- is attained (not merely valid) is the check that the fuel is the right
-- fuel rather than a generous one.
------------------------------------------------------------------------

example-run : Reaches mixedDescent (2 , true)
example-run = descent-theorem mixedDescent (2 , true)

example-trajectory :
    traj example-run
  ≡ (2 , true) ∷ (2 , false) ∷ (1 , true) ∷ (1 , false)
              ∷ (0 , true) ∷ corner ∷ []
example-trajectory = refl

example-steps : steps example-run ≡ 5
example-steps = refl

example-endpoint : endpoint example-run ≡ corner
example-endpoint = endpoint-corner example-run
