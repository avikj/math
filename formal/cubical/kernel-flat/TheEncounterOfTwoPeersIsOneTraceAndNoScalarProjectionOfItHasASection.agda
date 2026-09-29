{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection
--
-- TERM.  परस्परोपग्रहो जीवानाम् · parasparopagraho jīvānām -- "mutual
-- assistance is the function of living beings", Umsvti, *Tattvrthastra*
-- 5.21 (~2nd-5th c. CE).  What is
-- borrowed is the stra's SHAPE: that the characteristic act is not a
-- property of either party but of the pair.
-- The word
-- names the primitive because the primitive is a two-place one.
--
------------------------------------------------------------------------
-- WHAT THIS ADDS TO THE KERNEL, IN ONE LINE.
--
-- `TheKernelIsAnInteractiveSystem…` has ONE party and a machine.  Its
-- `Session` is a caller's transcript: the caller offers, the machine
-- executes, the transcript retires into one operation.  That is a dialogue
-- with an oracle, and every state in it is somebody's local state --
-- but there is only ever one somebody.
--
-- Here there are two, and neither is the machine.  The transition is
--
--     (state_A , state_B)  ⟶  (state′_A , state′_B , τ)
--
-- and it is `interact` below: a total function, no `Maybe`, no protocol, no
-- third party, no authoritative copy.  τ is one object wearing five hats --
-- it is the execution (constructing it performs the transport), the
-- provenance (its type names both endpoints), the proof (`derivation-sound`
-- reads it), the transport (`⊕` and `rev` move along it), and the program
-- (`install` makes it a move).  Nothing here is a bridge between five
-- subsystems.  There is one object and five projections of it.
--
--   §1  THE PRIMITIVE.  `Encounter`, `τ`, `interact`, and the two
--       dispositions a peer may take toward what it has just certified:
--       `interact` (transport and retain) and `receive` (retain only).
--       Both are total; both keep each peer's own origin.
--   §2  THE TWO RESULTS NEED NOT AGREE, and that is not a defect awaiting
--       reconciliation.  Witness: after one certified encounter the peers
--       stand at provably distinct terms, with no repair pending.
--   §3  REVELATION AND GENERATION, separated.  A gains a capability that
--       was B's (revelation, with a before/after where "before" is ⊥), and
--       the pair gains one whose endpoints are neither peer's (generation).
--   §4  CONSERVATIVITY.  The prior trace survives as a prefix ON THE NOSE,
--       the prior position is recoverable through `rev`, and the prior
--       library is still enabled at everything it was enabled at.
--   §5  LOSSLESS IS NOT UNCHANGED.  The round trip's MEANING is `refl` and
--       the round trip is NOT `done`: information preserved, representation
--       not.  Both halves are checked here and they are different halves.
--   §6  THE FABRIC COMPOSES STRICTLY.  Two encounters sharing a peer make a
--       third, and the association of three is equality of DATA, not of
--       meaning -- which is what lets three peers concatenate in any order
--       and get the same object rather than merely the same fact.
--   §7  THE CROSSING.  Two encounters at disjoint sites, run in the two
--       orders: same endpoints, same cost, PROVABLY DIFFERENT TRACES.
--   §8  WEIGHTS ⇒ TRACES, PRICED.  `len` is additive over `⊕` -- the scalar
--       says the value of an encounter is the sum of its parts -- and §7
--       says the scalar is therefore blind to the crossing.  Hence
--       `no-section-for-any-order-blind-projection`: no reconstruction of
--       the trace from any projection that the crossing does not move.
--       trace → score is a function; score → trace is not, and this is the
--       exact price.
--   §9  THE BOUNDARY.  What crosses is `CheckedFuture` -- Type₀, and it
--       mentions neither the operation nor the caller's evidence.  The
--       receipt a peer demanded to permit the step does not travel with the
--       step's result.
--
-- WHAT IS NEW HERE AND WHAT IS NOT.  `TheDerivationCarriesNoMeaning…` §3-4
-- already proves that no function OF THE MEANING separates two routes, and
-- that `len` does not factor through the truncation of the derivation type.
-- Both are about what a semantic reading loses.  §8 is a different
-- statement and neither implies it: `len` is not a function of the meaning,
-- it DOES separate direct from detour, and it is still not invertible --
-- because two independent encounters commute, so the route-sensitive scalar
-- has a collision it cannot avoid.  The blindness is not the semantics'.
-- It is the SCALAR'S, and it survives every refinement that stays scalar.
------------------------------------------------------------------------

module TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; _+_ ; znots)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List using (List ; [] ; _∷_)

open import Kernel.RewriteCertificate
open import Kernel.ControlledGrammar
open import Kernel.Vyapti_TheInstalledOperationHasNoneSoTheKernelMemorisesAndTheSchemaIsWhatMakesItGeneralise
  using (SomeEnabled)
open import Kernel.Residue_TheDerivationCarriesNoMeaningAtAllSoAllOfItIsRemainderAndNoSemanticCriterionSelectsTheShortOne
  using (len ; meanings-are-equal)
open import Kernel.Interaction_TheKernelIsAnInteractiveSystemAndTheSessionRetiresIntoOneOperation
  using (_⊕_ ; Session ; session ; demand ; every-operation-that-exists-is-sound)
open import Kernel.Avirodha_TheKernelIsAReversibleGroupoidWhoseJoinIsConflictFreeSoConsensusOnMeaningIsVacuous
  using (rev ; ⊕-assoc ; merge ; join-keeps-the-left ; round-trip-is-the-identity)

open Session

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1.  THE PRIMITIVE.
--
-- A peer is a `Session` and nothing else: its own origin, where it stands,
-- the trace between, and what it has learned.  There is no field naming a
-- server, a version vector, a clock or a quorum, and there is no type in
-- this file whose inhabitants are "the state of the system".
--
-- An encounter is two peers and an OVERLAP: a term both can talk about,
-- with each peer holding a certified stretch to it.  That is the whole
-- precondition.  Neither peer needs the other's history, neither needs to
-- know the other's library, and no completeness of either peer's knowledge
-- is required anywhere -- partial is the normal state, and the type says so
-- by never mentioning totality.
------------------------------------------------------------------------

Peer : Type₁
Peer = Session

record Encounter : Type₁ where
  constructor encounter
  field
    A B     : Peer
    meeting : Tm                            -- the overlap, and only it
    mine    : Derivation (here A) meeting   -- A's certified stretch to it
    theirs  : Derivation meeting (here B)   -- B's certified stretch from it

open Encounter

-- τ.  Constructing it IS the transport; its type IS the provenance; reading
-- it with `derivation-sound` IS the proof; `install`ing it IS the program.
τ : (E : Encounter) → Derivation (here (A E)) (here (B E))
τ E = mine E ⊕ theirs E

-- and it is sound, as everything constructible in this kernel is.
τ-is-sound : (E : Encounter) (ρ : Env)
  → eval (here (A E)) ρ ≡ eval (here (B E)) ρ
τ-is-sound E ρ = derivation-sound (τ E) ρ

-- WHAT EACH PEER LEARNS.  Two operations: the other's stretch, and the
-- joint route.  Both are `install`ed, so both carry their certificate.
gain : (E : Encounter) → List NativeOperation → List NativeOperation
gain E L = install (theirs E) ∷ install (mine E) ∷ install (τ E) ∷ L

-- DISPOSITION ONE: transport.  The peer travels the route it just
-- certified, and keeps everything.
A′ : Encounter → Peer
A′ E = session (origin (A E)) (here (B E))
               (trace (A E) ⊕ τ E)
               (gain E (library (A E)))

B′ : Encounter → Peer
B′ E = session (origin (B E)) (here (A E))
               (trace (B E) ⊕ rev (τ E))
               (gain E (library (B E)))

-- THE TRANSITION.  (state_A , state_B) ⟶ (state′_A , state′_B , τ).
interact : (E : Encounter)
  → Peer × Peer × Derivation (here (A E)) (here (B E))
interact E = A′ E , B′ E , τ E

-- DISPOSITION TWO: receive.  Take the capability, do not move.  The peer's
-- boundary is its own: what it retains and what it transports are separate
-- decisions, and both outcomes are certified.  Nothing in this file, and
-- nothing in the kernel, prefers one.
receive : Encounter → Peer → Peer
receive E P = session (origin P) (here P) (trace P) (gain E (library P))

-- LOCAL-FIRST, AS A TYPE.  Neither result mentions the other peer's origin,
-- and neither peer's own origin moves.  There is no privileged state to
-- reconcile against because there is no term of any type here that could be
-- one: `interact` takes two locals and returns two locals.
each-peer-keeps-its-own-origin :
  (E : Encounter)
  → (origin (A′ E) ≡ origin (A E)) × (origin (B′ E) ≡ origin (B E))
each-peer-keeps-its-own-origin E = refl , refl

receiving-moves-nobody : (E : Encounter) (P : Peer) → here (receive E P) ≡ here P
receiving-moves-nobody E P = refl

------------------------------------------------------------------------
-- §2.  THE TWO RESULTS NEED NOT AGREE.
--
-- The witness is two terms with two independent redexes, which is also the
-- object §7 turns on.  A stands at the unreduced term, B at the reduced
-- one, and they overlap at the term reached by contracting the left redex.
------------------------------------------------------------------------

a₀ : Tm                                     -- where A stands
a₀ = add (add var zero) (add yvar zero)

mL : Tm                                     -- left redex contracted
mL = add var (add yvar zero)

mR : Tm                                     -- right redex contracted
mR = add (add var zero) yvar

b₀ : Tm                                     -- where B stands
b₀ = add var yvar

stepL : Step a₀ mL
stepL = add-left (add-zero var) (add yvar zero)

stepR : Step a₀ mR
stepR = add-right (add var zero) (add-zero yvar)

stepL′ : Step mR b₀
stepL′ = add-left (add-zero var) yvar

stepR′ : Step mL b₀
stepR′ = add-right var (add-zero yvar)

-- TWO PROBES, and they are the only inequality machinery in this file.
leftIsVar : Tm → Bool
leftIsVar (add var _) = true
leftIsVar _           = false

rightIsAdd : Tm → Bool
rightIsAdd (add _ (add _ _)) = true
rightIsAdd _                 = false

a₀≢mL : a₀ ≡ mL → ⊥
a₀≢mL p = true≢false (sym (cong leftIsVar p))

mL≢b₀ : mL ≡ b₀ → ⊥
mL≢b₀ p = true≢false (cong rightIsAdd p)

a₀≢b₀ : a₀ ≡ b₀ → ⊥
a₀≢b₀ p = true≢false (sym (cong leftIsVar p))

-- The two peers, each knowing only its own side.
peerA : Peer
peerA = session a₀ a₀ (done a₀) []

peerB : Peer
peerB = session b₀ b₀ (done b₀) []

meetingLeft : Encounter
meetingLeft =
  encounter peerA peerB mL
            (then-step stepL (done mL))
            (then-step stepR′ (done b₀))

-- AND THEY END SOMEWHERE ELSE FROM EACH OTHER.  Both are correct, both
-- carry a certificate for how they got there, and nothing is pending.
-- `TheKernelIsAReversibleGroupoid…` §4 proves they cannot disagree about
-- what is TRUE; this says they need not agree about where they STAND, and
-- the second is not a weaker form of the first -- it is the part consensus
-- was invented for and the part this kernel does not need it for.
the-two-results-need-not-agree :
  here (A′ meetingLeft) ≡ here (B′ meetingLeft) → ⊥
the-two-results-need-not-agree p = a₀≢b₀ (sym p)

-- and there is no repair pending: each result is sound where it stands.
both-results-are-sound :
  (ρ : Env)
  → (eval (origin (A′ meetingLeft)) ρ ≡ eval (here (A′ meetingLeft)) ρ)
  × (eval (origin (B′ meetingLeft)) ρ ≡ eval (here (B′ meetingLeft)) ρ)
both-results-are-sound ρ =
  derivation-sound (trace (A′ meetingLeft)) ρ ,
  derivation-sound (trace (B′ meetingLeft)) ρ

------------------------------------------------------------------------
-- §3.  REVELATION, AND GENERATION, AND THEY ARE NOT THE SAME EVENT.
------------------------------------------------------------------------

-- REVELATION.  Before the encounter A cannot act at the meeting point --
-- its library is empty and `SomeEnabled [] t` is ⊥, so this is not "could
-- not be shown to", it is ⊥.
A-could-not-act-at-the-meeting : SomeEnabled (library peerA) mL → ⊥
A-could-not-act-at-the-meeting e = e

-- After it, A can, with the certificate that was B's.
A-can-now-act-at-the-meeting : SomeEnabled (library (A′ meetingLeft)) mL
A-can-now-act-at-the-meeting = inl refl

-- and what crossed is exactly B's stretch -- endpoints on the nose.
what-crossed-is-what-B-had :
  (E : Encounter)
  → (NativeOperation.source (install (theirs E)) ≡ meeting E)
  × (NativeOperation.target (install (theirs E)) ≡ here (B E))
what-crossed-is-what-B-had E = refl , refl

-- GENERATION.  The joint route's endpoints are the OUTER pair, and that
-- pair is neither peer's: A's stretch runs (here A , meeting), B's runs
-- (meeting , here B), and this runs (here A , here B).  Stated in general
-- as the structural fact, and then discriminated at the witness.
the-generated-endpoints-are-the-outer-pair :
  (E : Encounter)
  → (NativeOperation.source (install (τ E)) ≡ here (A E))
  × (NativeOperation.target (install (τ E)) ≡ here (B E))
the-generated-endpoints-are-the-outer-pair E = refl , refl

-- It is not A's stretch: same source, different target.
generated≢mine :
  NativeOperation.target (install (τ meetingLeft))
    ≡ NativeOperation.target (install (mine meetingLeft)) → ⊥
generated≢mine p = mL≢b₀ (sym p)

-- It is not B's stretch: different source.
generated≢theirs :
  NativeOperation.source (install (τ meetingLeft))
    ≡ NativeOperation.source (install (theirs meetingLeft)) → ⊥
generated≢theirs p = a₀≢mL p

-- and neither peer held it before, because neither peer held anything.
neither-peer-held-it :
  (SomeEnabled (library peerA) a₀ → ⊥) × (SomeEnabled (library peerB) a₀ → ⊥)
neither-peer-held-it = (λ e → e) , (λ e → e)

-- but the pair holds it after, on both sides.  This is the encounter
-- computing something that was in neither participant: K_A ⊗ K_B ⟶ K_C
-- with K_C in neither.
the-pair-holds-it-after :
  SomeEnabled (library (A′ meetingLeft)) a₀
  × SomeEnabled (library (B′ meetingLeft)) a₀
the-pair-holds-it-after = inr (inr (inl refl)) , inr (inr (inl refl))

------------------------------------------------------------------------
-- §4.  CONSERVATIVITY.  Learning does not destroy what was valid.
--
-- Three separate obligations, and each is discharged separately because
-- they are three different claims.  The representation is changed -- §5.
------------------------------------------------------------------------

-- (i) THE PRIOR TRACE SURVIVES AS A PREFIX, AS DATA.  Not "is recoverable
-- from"; not "means the same as".  It is literally the left factor.
the-prior-trace-is-a-prefix :
  (E : Encounter) → trace (A′ E) ≡ trace (A E) ⊕ τ E
the-prior-trace-is-a-prefix E = refl

-- (ii) THE PRIOR POSITION IS RECOVERABLE, and the recovery is not a promise
-- but a term: `rev` is total because `reverse` is a CONSTRUCTOR.  Whatever
-- an encounter did, the way back exists and is certified.
undo : (E : Encounter) → Derivation (here (A′ E)) (here (A E))
undo E = rev (τ E)

the-recovery-is-certified :
  (E : Encounter) (ρ : Env)
  → eval (here (A′ E)) ρ ≡ eval (here (A E)) ρ
the-recovery-is-certified E ρ = derivation-sound (undo E) ρ

-- (iii) THE PRIOR LIBRARY IS STILL ENABLED AT EVERYTHING IT WAS ENABLED AT.
-- Growing by three operations cannot remove a capability, and this is the
-- join theorem of `TheKernelIsAReversibleGroupoid…` §3 applied at the one
-- place a peer's library actually changes.
nothing-a-peer-could-do-is-lost :
  (E : Encounter) (t : Tm)
  → SomeEnabled (library (A E)) t → SomeEnabled (library (A′ E)) t
nothing-a-peer-could-do-is-lost E t e = inr (inr (inr e))

-- and the same for the peer that chose not to move.
receiving-loses-nothing :
  (E : Encounter) (P : Peer) (t : Tm)
  → SomeEnabled (library P) t → SomeEnabled (library (receive E P)) t
receiving-loses-nothing E P t e = inr (inr (inr e))

-- The general form, for a peer merging an arbitrary batch rather than one
-- encounter's three: the same theorem, unchanged, which is the point.
a-merge-of-any-size-loses-nothing :
  (L M : List NativeOperation) (t : Tm)
  → SomeEnabled L t → SomeEnabled (merge L M) t
a-merge-of-any-size-loses-nothing = join-keeps-the-left

------------------------------------------------------------------------
-- §5.  LOSSLESS IS NOT UNCHANGED, and both halves are checked.
--
-- Go and come back.  The MEANING is `refl` -- nothing was lost.  The
-- OBJECT is not `done` -- the representation did not survive.  These are
-- two different statements about one term and a system that conflates them
-- either forbids rewriting or forgets what it rewrote.
------------------------------------------------------------------------

round-trip : (E : Encounter) → Derivation (here (A E)) (here (A E))
round-trip E = τ E ⊕ rev (τ E)

-- The information half.
the-round-trip-preserves-the-meaning :
  (E : Encounter) (ρ : Env) → derivation-sound (round-trip E) ρ ≡ refl
the-round-trip-preserves-the-meaning E ρ = round-trip-is-the-identity (τ E) ρ

-- The representation half.  Four steps out and back, and `done` has zero.
the-round-trip-costs-four : len (round-trip meetingLeft) ≡ 4
the-round-trip-costs-four = refl

the-round-trip-is-not-done : round-trip meetingLeft ≡ done a₀ → ⊥
the-round-trip-is-not-done p = znots (sym (cong len p))

------------------------------------------------------------------------
-- §6.  THE FABRIC COMPOSES, AND STRICTLY.
--
-- Two encounters sharing a peer make a third.  `⊕-assoc` is equality of
-- DATA, so three peers who each concatenate their segment get the same
-- object, not merely one with the same endpoints and the same meaning --
-- which is what makes a distributed history a groupoid rather than a set of
-- claims about one.
------------------------------------------------------------------------

chain : (E F : Encounter) → here (B E) ≡ here (A F)
  → Derivation (here (A E)) (here (B F))
chain E F q = τ E ⊕ subst (λ t → Derivation t (here (B F))) (sym q) (τ F)

the-fabric-composes-strictly :
  {a b c z : Tm}
  (τ₁ : Derivation a b) (τ₂ : Derivation b c) (τ₃ : Derivation c z)
  → (τ₁ ⊕ τ₂) ⊕ τ₃ ≡ τ₁ ⊕ (τ₂ ⊕ τ₃)
the-fabric-composes-strictly = ⊕-assoc

-- and however the three associate, the fact is one fact -- free, because
-- `TheDerivationCarriesNoMeaning…` says the meaning is a proposition.
-- The same theorem that makes routes indistinguishable makes long histories
-- cheap to extend; it is one fact read at two altitudes.
the-fact-does-not-depend-on-the-association :
  {a b c z : Tm}
  (τ₁ : Derivation a b) (τ₂ : Derivation b c) (τ₃ : Derivation c z)
  → derivation-sound ((τ₁ ⊕ τ₂) ⊕ τ₃) ≡ derivation-sound (τ₁ ⊕ (τ₂ ⊕ τ₃))
the-fact-does-not-depend-on-the-association τ₁ τ₂ τ₃ =
  meanings-are-equal ((τ₁ ⊕ τ₂) ⊕ τ₃) (τ₁ ⊕ (τ₂ ⊕ τ₃))

------------------------------------------------------------------------
-- §7.  THE CROSSING.  Two encounters at disjoint sites, in two orders.
--
-- `a₀` has two redexes that do not touch: the left summand's `add x zero`
-- and the right summand's.  Contract them in either order and the endpoints
-- agree.  The traces do not, and `the-two-orders-differ` is a term.
------------------------------------------------------------------------

left-then-right : Derivation a₀ b₀
left-then-right = then-step stepL (then-step stepR′ (done b₀))

right-then-left : Derivation a₀ b₀
right-then-left = then-step stepR (then-step stepL′ (done b₀))

midpoint : {x y : Tm} → Derivation x y → Tm
midpoint (done t)              = t
midpoint (then-step {y = y} _ _) = y

the-two-orders-differ : left-then-right ≡ right-then-left → ⊥
the-two-orders-differ p = true≢false (cong leftIsVar (cong midpoint p))

-- Same endpoints, by the types above; same cost, by computation.
both-orders-cost-the-same : len left-then-right ≡ len right-then-left
both-orders-cost-the-same = refl

-- and same meaning, forced, because the meaning is a proposition.
both-orders-mean-the-same :
  derivation-sound left-then-right ≡ derivation-sound right-then-left
both-orders-mean-the-same = meanings-are-equal left-then-right right-then-left

------------------------------------------------------------------------
-- §8.  WEIGHTS ⇒ TRACES, AND THE PRICE OF THE OTHER DIRECTION.
--
-- trace → score is a function and always was: `len`.  The claim is about
-- the converse, and it is not "hard", it is not "lossy in practice", and it
-- is not a statement about how much information a number holds.  It is that
-- NO section exists, for ANY projection the crossing does not move.
--
-- The additivity is what does it.  A scalar that reports the value of an
-- encounter as the sum of the values of its parts has, by that very law,
-- given the same number to both orders of two independent encounters -- so
-- the order is not recoverable from it, and the order is a real difference
-- between two real objects.  Read as an accounting: a ledger of node
-- weights and edge sums is not an approximation of a ledger of the
-- interactions.  It is provably not invertible to one.
------------------------------------------------------------------------

-- The scalar is additive: V(A ⊕ B) = V(A) + V(B), on the nose.
the-scalar-is-additive :
  {a b c : Tm} (d : Derivation a b) (e : Derivation b c)
  → len (d ⊕ e) ≡ len d + len e
the-scalar-is-additive (done a)        e = refl
the-scalar-is-additive (then-step p d) e = cong ℕ.suc (the-scalar-is-additive d e)

-- THE NO-GO.  Any projection at any level that the crossing does not move
-- admits no reconstruction of the trace.  Not a bound, not an estimate:
-- the type is empty.
no-section-for-any-order-blind-projection :
  {X : Type ℓ} (π : Derivation a₀ b₀ → X)
  → π left-then-right ≡ π right-then-left
  → Σ[ r ∈ (X → Derivation a₀ b₀) ]
      ((d : Derivation a₀ b₀) → r (π d) ≡ d)
  → ⊥
no-section-for-any-order-blind-projection π blind (r , inv) =
  the-two-orders-differ
    (sym (inv left-then-right) ∙ cong r blind ∙ inv right-then-left)

-- The cost is such a projection, by `both-orders-cost-the-same`.
the-scalar-cannot-be-inverted :
  Σ[ r ∈ (ℕ → Derivation a₀ b₀) ]
    ((d : Derivation a₀ b₀) → r (len d) ≡ d)
  → ⊥
the-scalar-cannot-be-inverted =
  no-section-for-any-order-blind-projection len both-orders-cost-the-same

-- and so is the meaning, and so is every function of the meaning -- which
-- recovers `TheDerivationCarriesNoMeaning…`'s reading as a special case of
-- this one rather than as a separate argument.
the-meaning-cannot-be-inverted :
  {C : Type ℓ}
  (score : ((ρ : Env) → eval a₀ ρ ≡ eval b₀ ρ) → C)
  → Σ[ r ∈ (C → Derivation a₀ b₀) ]
      ((d : Derivation a₀ b₀) → r (score (derivation-sound d)) ≡ d)
  → ⊥
the-meaning-cannot-be-inverted score =
  no-section-for-any-order-blind-projection
    (λ d → score (derivation-sound d))
    (cong score both-orders-mean-the-same)

-- THE DIRECTION THAT DOES EXIST, so the asymmetry is exhibited and not
-- merely asserted: from the trace, every one of these projections.
the-trace-gives-the-score : Derivation a₀ b₀ → ℕ
the-trace-gives-the-score = len

the-trace-gives-the-meaning :
  Derivation a₀ b₀ → ((ρ : Env) → eval a₀ ρ ≡ eval b₀ ρ)
the-trace-gives-the-meaning = derivation-sound

------------------------------------------------------------------------
-- §9.  THE BOUNDARY.  What crosses does not carry why it was allowed.
--
-- `demand R d` is the kernel's open control: a peer may require ANY
-- evidence at all before its operation fires -- a receipt, an authority, a
-- payment, a session identity.  `execute` then drops the operation and the
-- evidence and keeps the target and the derivation, descending Type₁ → Type₀.
--
-- So the object that crosses the boundary is replayable by someone who was
-- not there and mentions nothing about who asked.  Below: two peers holding
-- DIFFERENT receipts, with the same identification, produce the same
-- crossing object -- the receipt leaves no residue in the result.
------------------------------------------------------------------------

gated : {lhs rhs : Tm} (R : Type₀) (d : Derivation lhs rhs)
  (t : Tm) → t ≡ lhs → R → EnabledFuture t
gated R d t p r = record { operation = demand R d ; control = (p , r) }

the-receipt-does-not-cross :
  {lhs rhs : Tm} {R : Type₀} (d : Derivation lhs rhs)
  (t : Tm) (p : t ≡ lhs) (r₁ r₂ : R)
  → execute (gated R d t p r₁) ≡ execute (gated R d t p r₂)
the-receipt-does-not-cross d t p r₁ r₂ = refl

-- and what did cross is still certified, whoever produced it: soundness is
-- local to the operation and travelled with it.
what-crossed-is-still-true :
  {lhs rhs : Tm} {R : Type₀} (d : Derivation lhs rhs)
  (t : Tm) (p : t ≡ lhs) (r : R) (ρ : Env)
  → eval (NativeOperation.source (demand R d)) ρ
    ≡ eval (NativeOperation.target (demand R d)) ρ
what-crossed-is-still-true {R = R} d t p r =
  every-operation-that-exists-is-sound (demand R d)
