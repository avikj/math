# Witnessed effects, authority and cuts — executable contract

This supplies the machine rules requested in V23's author-dependency report. It is cumulative with `FOUNDATION-ROUTE.md` and `LIVE-CUT-ADOPTION.md`. It specifies the generic local realization and its network-refinement obligation; it does not claim that V23 implements these rules. The records below are descriptors and jobs of the existing machine. Their mathematical payloads are existing scoped core references, checked by the existing kernel. No Nat, Bool, account, payment or agent-specific reduction primitive is introduced.

The mathematical interface is forced by boundary-preserving witnessed transitions. The reservation layout below is a concrete implementation choice realizing that interface, not a claim that this is the unique representation derivable from mathematics. It permits independently owned components to advance independently and permits one interaction to consume several components atomically.

## 1. The typed source and the two distinct judgments

For a checked parameter telescope Γ and face κ, declare core references for

\[
S:\mathcal U_s,\qquad R:S\to S\to\mathcal U_r.
\]

`R(s,t)` is the admissibility type of an edge from source state `s` to target state `t`. Commands, the actor's authorization, outputs and conservation evidence can be dependent fields of `R`; they are not extra evaluator cases. Its finite interface includes an input resource boundary and output resource boundary. For several components, `S` is their dependent product with the stated joining paths. Existing Π/Σ/Path/Glue constructions express these data.

There are two judgments:

1. **Mathematical admission:** `Γ;κ ⊢ p : R(s,t)` with a committed checker verdict and proof-use audit. An unresolved or recursively pending proof is not admitted as an unconditional witness. An explicitly assumed premise remains in the certificate and must be supplied by the occurrence's admitted boundary.
2. **Operational acceptance:** the currently owned input occurrences named in the proposal are consumed by this particular accepted event, producing its output occurrences.

The first is reusable evidence. The second is a transition of the actual source. Copying or deriving the first does not execute the second. This distinction is necessary even when both judgments and their computations inhabit one machine: a proof that a transfer is permitted does not assert that the transfer already happened.

A pure receipt payload can be represented by `Σ(s:S).Σ(t:S).R(s,t)` and its full typed boundary. An **accepted receipt** additionally names the actual committed occurrence record. An arbitrary term of that Σ type cannot fabricate that occurrence. Receipt observation exposes the core fields lazily; acceptance checking also looks up the occurrence. No new definitional equality equates those two judgments.

## 2. Stable identities and immutable records

All vectors below are arbitrary finite paged sequences. Mathematical quantities use exact naturals/signed differences; a native handle is an address of a live record, not an upper bound on a mathematical value. Stable identities must include the lifetime/namespace needed to prevent aliasing after reuse. On the network, exact identity equality is a protocol premise; a hash match alone is not exact equality.

| Record | Required fields and meaning |
|---|---|
| `EffectSchema` | The declaration-closed Γ, κ, exact levels, `S`, `R`, typed input/output interface recipes, and the admitted interpretation into port boundaries. All these fields belong to its semantic key. |
| `Authority` | A stable identity; schema and immutable policy; a maintained head cell; initial-state witness; current implementation/refinement boundary. Possessing its address supplies no implicit authorization. |
| `Head` | Authority identity, immutable occurrence identity, core state reference and its typed context/face, accepted predecessor or genesis certificate. A successor is a new head even if its state value is convertible to an earlier state. |
| `Proposal` | Stable request identity; schema instance; one simultaneous parameter map; exact expected input heads; desired output states/ports; core edge witness; explicit authorization premises; result/continuation interface. Fields are inert references until demanded. |
| `Prepared` | Proposal; committed mathematical admission certificate; retained dependency/environment snapshot; exact interface matching; reserved immutable output/receipt storage. It owns no accepted output merely by existing. |
| `Commit` | Prepared record; sorted unique input-head cells; per-input reservation cursor; preconstructed successor heads and output ports; state `RESERVING`, `COMMITTED` or `ABORTED`; cleanup cursor; joined waiters. |
| `Occurrence` | Immutable identity of this commit; the prepared witness; exact consumed input occurrences and produced output occurrences; admitted premises; causality links; work-event links. It becomes accepted at the commit transition below. |
| `Receipt` | Occurrence identity plus its retained record and a checked observation/transport view. It is immutable; copying it preserves identity. |
| `Port` | Identity `(issuing occurrence, slot)`; endpoint/interface; core payload reference and type/level/face; receiving authority/policy; its unique consumption boundary. A transport packet is a copy of a description of this port, not another port. |

A head cell contains either `AVAILABLE(head)` or `RESERVED(commit, input_slot)`. A reserved cell is interpreted by the commit's state: while reserving, its input is unavailable; if committed, its logical value is the designated successor; if aborted, its logical value is the former input. Materializing that interpretation is bounded cleanup, not a second acceptance.

Publication of a new authority, a port-consumption cell or a successor uses immutable prepared records. Such records are never installed with partially initialized fields. A private loser of an interning/publication race releases its own allocations normally.

The request index is `(authority/interface namespace, request identity) → Proposal/Commit/outcome`. Repeating an identical request joins its existing job or returns its existing outcome. Reusing a request identity with different anchored proposal data is a request conflict. Identical pure mathematical payloads with **different** request identities need not denote the same intended effect. Pure validation is still shared by its mathematical key.

For the local acceptance witness, genesis creates an owner capability descriptor associated with the authority and a specified permission. Capability descriptors are issued by that boundary and cannot be fabricated by constructing an integer or a core tuple; the acceptance operation validates the descriptor in its owning registry. Delegation is an explicit admitted transition/policy rule. A remote caller's claimed numeric handle is never accepted as a capability. The network adapter must authenticate/interpret its authorization evidence under the declared authority interface. This fixes the local test's authorization behavior while leaving cryptographic/network realizations subject to the stated refinement contract.

## 3. Exact preparation premises

`PREPARE_EFFECT(P)` is a shared, resumable job. It performs these obligations through existing kernel requests, one retained frame at a time:

1. Validate the schema, parameter map, context and face structurally, including all stored syntax and retained annotations. Apply the map simultaneously; do not reindex images a second time.
2. Validate each input head's state at the instantiated source type and each proposed output at its instantiated target type. Check declared levels exactly.
3. Check the proposed witness at `R(s,t)` and audit its proof use. Preserve the certificate's hypotheses and dependency snapshot. A host authorization premise is identified as such; it is not silently promoted to a closed core proof.
4. Check the input/output interface recipes at these states. Each input consumption occurrence is unique in the input list. Every internal match carries the required typed compatibility/transport. Output slot identities are fresh relative to this new occurrence, even when output payloads are identical.
5. Check each required authorization against the explicitly supplied authority boundary/policy. In the local reference implementation this includes a valid owner-issued capability or an equivalent admitted policy witness. A public reference to a head, a copied proof, or a repeated network message does not manufacture that capability.
6. Pin the immutable declarations, proof premises and external state snapshot used by the preparation. Any mutable condition whose continued truth is needed for acceptance is represented by an expected input head, rather than a free-standing Boolean remembered from earlier.
7. Prepare the immutable occurrence, all output records and all per-input reservation nodes before attempting acceptance. Allocation/resource suspension keeps this job and its existing work; it publishes no success.

Preparation succeeds with `PREPARED`. `INVALID` requires a settled failed admission. `UNRESOLVED`, a waiting proof or an unavailable resource remains pending with its continuation. A stale expected head is an operational conflict, not a proof of mathematical inequality.

Historical acceptance retains the admitted snapshot. Editing a later environment cannot rewrite what evidence an old event used. Fresh proposals requesting the new environment use fresh validity checks. This is the same dependency-sensitive reuse principle already required for evaluator and checker facts.

## 4. Local agent rules and complete replacements

The following are local job/descriptor rules in the existing scheduler. `K` is a single-use continuation; copying a descriptor copies its handle, not its acceptance right. Administrative receipt delivery uses the same counted request/delivery discipline as other jobs.

| Active demand / condition | Replacement and ownership effect |
|---|---|
| `EFFECT_REQUEST(P,K)`, request index absent | Install one proposal job, attach K, enqueue `PREPARE_EFFECT(P)`. No input is consumed. |
| Same indexed P still preparing/reserving | Attach K to that existing job. No second prepare or commit owner. |
| Same indexed P accepted | Deliver a handle to the same accepted Receipt to K. No second effect occurrence. |
| Same indexed P aborted/invalid | Deliver that recorded outcome to K. No acceptance. A budget suspension is not such a settled outcome. |
| Same request identity, different anchored P | Deliver `REQUEST_CONFLICT`; preserve the existing record. |
| `PREPARE_EFFECT` returns prepared D | Enqueue `RESERVE_NEXT(D,0)`; all variable checking/allocation is already represented by retained jobs. |
| `RESERVE_NEXT(D,k)`, matching `AVAILABLE(h_k)` | With one cell lock/CAS, install its preallocated `RESERVED(D,k)` and advance k. Unlock before scheduler work. |
| Cell reserved by another pending descriptor | Register a predicate wait naming that descriptor's actual progress owner, or service it through the shared scheduler; recheck this cell on delivery. Do not consume the other descriptor's result as D's witness. |
| Cell denotes a terminal reservation | Perform one finalization step, then retry this input. |
| Cell available at a different head | Set D `ABORTED` if still reserving. Enqueue rollback of already reserved cells; report conflict after its owned rollback obligations are detached safely. |
| All required cells reserved by D | Atomically change `RESERVING → COMMITTED`. **This is the one acceptance event.** The already allocated immutable Occurrence becomes readable as accepted. Enqueue cell finalization, receipt deliveries and declared output emission. |
| `FINALIZE(D,k)`, D committed | Replace `RESERVED(D,k)` by its preconstructed successor head if still present; release this reservation ownership; advance the cleanup cursor. |
| `FINALIZE(D,k)`, D aborted | Replace `RESERVED(D,k)` by the original input head if still present; release this reservation ownership; advance the cursor. |
| `RECEIPT_OBSERVE(E,K)` | Check E is an accepted occurrence, then return its requested core field or checked view as an ordinary reference. No acceptance transition is rerun. |
| `EMIT(E,slot)` | Expose the committed output port and its occurrence identity to its endpoint/outbox. Repeated delivery of its description names the same port. Emission bookkeeping and actual packet sends retain their own work events. |
| Duplicate input-port receive | If already consumed, return its recorded receipt/status; do not credit/perform the effect again. If reserved, join the existing consumer. |
| Private proposal retirement | Release only its private/unpublished data. Never retract a committed event or return a consumed input to availability. |
| `DUP` meeting an authority/port/receipt/proposal descriptor | Produce two handles to the same immutable descriptor and retain their ownership. No new authority cell, output port, request identity or accepted event is minted. |
| `ERASE` meeting such a descriptor | Release that handle. Its final reclamation follows the reachability/ownership graph; it does not undo acceptance or cancel other clients. |
| `REINDEX` meeting a proposal recipe | Compose its scoped maps and return the interned recipe view. It has no acceptance side effect. |
| `REINDEX` meeting an accepted receipt | Return a receipt-view request with the same occurrence anchor and the explicit interface-transport obligation described below. If that obligation is pending, suspend; if invalid, reject the view. |

Input reservation order is a fixed exact total order on authority/cell identities. One descriptor cannot reserve the same cell twice. Every descriptor reserves in that order. Therefore two descriptors cannot form a reservation cycle: a wait after holding smaller inputs requires a strictly larger next cell; a cycle would require a strict order cycle. Reads of an already completed descriptor are helped/finalized, not waited on indefinitely. Arbitrarily many inputs are processed one per frame, not by locking an arbitrarily long array.

All effect-request waiters refer to a shared descriptor; none decides whether it commits. Each committed descriptor publishes one occurrence irrespective of waiter count or delivery order. Same-proposal concurrent clients receive the same receipt. Conflicting proposals may have different accepted outcomes under different external-choice schedules; the confluence theorem for a fixed pure net does not identify these distinct choices.

Commit is allowed only after every required input is reserved and every admission premise is retained. Terminal descriptor state never returns to RESERVING. Rollback cannot run after COMMITTED. Failed private allocation, a lost reservation race and a suspended proof never expose an accepted receipt.

The commit-state word is the atomic point of the multi-input interaction. During finalization, a reader must resolve `RESERVED(D,k)` through D's state. Reading the physical cells as unrelated available values would expose an invalid half-committed state and is prohibited.

## 5. How this is represented in terms, scopes and substitutions

Effect schemas, source/target states, core witnesses, policies and receipt payloads are ordinary core constructions. Runtime-produced proofs enter `PREPARE_EFFECT` in exactly the same way as presented proofs. Their discovery time does not change the typing or action rule.

The network carries `AUTHORITY`, `PROPOSAL`, `ACCEPTED_RECEIPT` and `PORT` descriptors with those references as fields. These extend the existing descriptor/operation protocol, like contextual scopes and template environments; they do not require a separate checker, interpreter or cash VM. A first-class program may construct a proposal recipe and supply its continuation at runtime. Only the acceptance rule operates on the live authority cells.

An ordinary pure receipt **payload term** and an accepted-receipt descriptor are deliberately different projections of one retained source. Exposing a descriptor to a core computation gives its typed fields plus its anchored occurrence parameter in the occurrence context. It does not add an unchecked core proof that an arbitrary proposed event was accepted. The operational `accepted(E)` judgment remains checkable against the retained occurrence record. Any reflected representation of that judgment must include this registry/trace witness, not erase it.

Reindexing an unaccepted schema or proposal recipe composes all reference, interval, face, scope and level parameters using existing simultaneous maps. It does not evaluate them or allocate an effect occurrence. Any concrete request subsequently issued at the instantiated boundary gets its actual request identity and current input heads.

An accepted occurrence identity is anchored. Substitution can transport its **description**, through a checked boundary map, while retaining the same occurrence identity. It cannot change the historical inputs/outputs or use the receipt to accept a different specialized event. The admissible receipt-view record is

\[
\operatorname{ReceiptView}(E,\sigma,\eta),
\]

where σ is a valid scoped map and η witnesses the commuting interface transport, including the same authority and port occurrence anchors. `reindex(view(E,σ,η),τ)` composes σ and η; it never allocates a new accepted event. A map that changes the resource amount or recipient without the required boundary transport is not a view of that accepted occurrence. It can still instantiate a new **proposal**.

Describing the same actual event in two contexts shares its retained history. Independently accepting two equal payloads produces two event identities. This is the occurrence distinction already needed to count two consumer deliveries of one pure producer.

Identity application to a live component uses a boundary-preserving equivalence `E_b:X(b)≃Y(b)` where b includes its authority heads, accepted ports, guards and outstanding obligations. The contextual action is `(b,x,k)↦(b,E_b(x),k)`. A loop may be invisible to an observation of b while remaining in its retained fibre. An equivalence over a smaller boundary cannot erase commitments absent from that boundary's specification.

## 6. Pending transfers and electronic cash as an instance

This instance adds no money opcode. Instantiate the state and edge families with exact nonnegative quantities, ownership and the equations below. The ordinary kernel checks their witnesses; the generic acceptance rule maintains unique consumption.

For the integration test, a quantity can use the existing core Church-numeral construction at an explicit universe level, with addition expressed by its ordinary lambda body. A send supplies a remainder r and a path `add(r,q)=a`; thus no native subtraction or comparison handler is needed to establish nonnegativity. Fixed concrete test quantities make these arithmetic paths ordinary reduction/reflexivity witnesses. An alternative quantity representation requires its admitted interpretation and arithmetic witnesses, not an unchecked equality between a C integer and a core numeral. Host exact naturals are available for the ledger's reading of the same quantities. This specifies the test instance without making its particular numeral encoding a kernel primitive.

A send consumes the source account head at balance a and produces a source head at balance `a−q` plus one transfer port `m=(E,slot)` of quantity q, with evidence `q≤a` and the specified recipient/consumption authority. The sender's pending table may point to m; that pointer is metadata, not a second quantity q.

A receive consumes m together with the recipient head at balance b and produces a recipient head at `b+q`. Its acceptance descriptor reserves m's consumption cell and the recipient head, then commits once. An incompatible second receive cannot reserve the consumed port. A retransmitted packet merely names m again.

If refund/cancellation is offered, it is a competing transition consuming **that same transfer-port cell**, with its stated authorization and source-account input. Delivery and refund cannot both commit because they contend for the same occurrence. A local timeout alone does not prove non-delivery and cannot mint a refund. An acknowledgment is an observation of the accepted receive; it does not credit the amount again.

There are two meanings often confused by “pending”:

- Before send acceptance, the proposal owns no transfer port and no spend has occurred.
- After send acceptance but before receive/refund acceptance, the transfer port is an unconsumed output on the current cut. Its quantity remains there while the computation or network is suspended.

For a cut F, define

\[
V(F)=\sum_{\text{account heads on }F}\!\operatorname{balance}
     +\sum_{\text{unconsumed transfer ports on }F}\!\operatorname{quantity}.
\]

Send gives `(a−q)+q−a=0`; receive gives `(b+q)−b−q=0`; refund has the analogous zero boundary. By internal cancellation, every finite causally closed region conserves V, apart from explicitly authorized creation/destruction boundary events. Initial issuance is part of genesis, not an unchecked hidden rule. Negative intermediate values are rejected by the typed transition premise; arithmetic is exact.

An agent may send q around a cycle and return all external balances to their initial values. Its accepted occurrence history, learned receipts and pure-computation facts can still differ. The observer's balance quotient is not the full source; retaining that fibre is the point of the construction.

## 7. Network refinement, agency and external effects

A local authority can be replaced by a subnetwork implementing the same external interface. Its obligation is an emission-preserving trace map π from each permitted concrete history to a permitted abstract authority history:

\[
\pi(\epsilon)=\epsilon,\qquad \pi(h;k)=\pi(h);\pi(k).
\]

Internal steps may map to stuttering. Every externally usable accepted receipt must map to its actual abstract acceptance event; an external output cannot map to stuttering. Composed boundary transports and event identities must agree. Two incompatible externally accepted successors would therefore project to two incompatible successors in one abstract local history, contradicting the reservation/unique-consumption invariant. Composition of trace maps gives nested network replacement.

The transport interface carries an occurrence identity, immutable witnessed payload and interface interpretation. It permits delay, duplication and reordering. Input admission checks the same typed boundary and consumption cell as local delivery. A socket message, signature or hash is not on its own evidence of the exclusion invariant. A replicated implementation must supply the stated trace/refinement condition; the in-process realization supplies it by the commit descriptor above. This contract does not silently select a blockchain, quorum, trusted party or synchronization assumption.

For irreversible external devices, “committed command” and “device action acknowledged” are separate retained boundary facts unless the adapter supplies an atomic refinement identifying them. Its outbox is keyed by the accepted occurrence, and retries preserve that identity. A crash after issuing a device command with an unknown result remains an unresolved external obligation. The runtime must not invent success or issue a distinct logical action merely to retry. A durable adapter must preserve committed occurrence identities across restart; forgetting its spent set is not a refinement. These are exact adapter premises, not extra pure reduction axioms.

Nondeterministic agency is an explicit choice of permitted outgoing edge. Independent disjoint accepted interactions commute as state transitions. Incompatible choices need not have a joining path. If an optimality or random-descent theorem compares only one fixed externally chosen history, that choice must be included in its starting boundary. A theorem about that comparison cannot silently quantify over mutually exclusive agent choices.

## 8. Stokes and the common execution record

Give each actual event e its oriented port boundary `∂e=out(e)−in(e)`. An internal connection is the same port occurrence, with opposite signs. For a finite causally closed region H, linearity cancels every such internal pair:

\[
\partial H=F_{out}-F_{in}.
\]

For a valuation cochain a, `⟨a,∂H⟩=⟨da,H⟩`. For cubical compatibility cells the usual alternating face boundary satisfies `∂²=0`. No equation claims that all cycles are boundaries or that every boundary-zero cycle is observationally trivial. Their retained fibres and higher evidence remain available.

One occurrence/derivation DAG supplies (i) core evidence, (ii) open/closed ports, (iii) dependency snapshots, and (iv) actual work. Their readings commute with the same composition. The event-set work reading uses union on genuinely identical historical events; it does not double-count a shared producer because two receipts reference it. Present receipt requests, adaptation, checking and delivery still perform their own actual work.

For an identity cell α between histories γ and γ′ at the complete compared boundary,

\[
W(\gamma')-W(\gamma)=\langle\omega,\partial\alpha\rangle
                         =\langle d\omega,\alpha\rangle.
\]

Zero-defect commuting cells support the equal-cost comparison. Shortcuts with nonzero defect retain that exact signed difference. Neither accepted occurrences nor positive executed work disappear because a quotient observation returns to its original value.

Every preparation, reservation, wait/recheck, commit, finalization, outbox action and retirement is in the fine transition inventory. Fixed-size commit does not conceal variable preparation. A vector of k input heads takes k reservation frames; a proof or map traversal takes its existing retained kernel frames. Host acquisition/network/device actions have their explicit external boundary; no bound on OS latency is inferred from a C instruction count.

## 9. Retirement and live-prefix interaction

Pure prefix adoption can shorten a proposal's preparation by reusing a valid certificate or specialized residual. It cannot change an already accepted effect, transfer a capability to another occurrence, or release a port merely because an old computation continuation becomes obsolete.

While the machine is live, a pending accepted output remains owned by its port/outbox/receipt boundary. Releasing one client handle does not cancel it. A closed-session destructor may stop and destroy unneeded pure continuations without evaluating them to a result. It must discharge their owned allocations/wait registrations and join worker threads; parking a detached native thread forever is not destruction. Committed external obligations require their explicitly retained durable/host boundary before in-memory teardown. Do not apply pure cancellation rules to those commitments.

The `LIVE-CUT-ADOPTION.md` ticket-generation rule still governs which pure child delivery may resume a cut. Obsolete deliveries retain their administrative ownership until consumed. A stale ticket cannot perform a second acceptance: effect requests have their own stable request/commit identity and the authority cells enforce unique consumption independently of continuation scheduling.

## 10. Required implementation witness and assertions

Implement one in-process network with two agent endpoints and the generic authority/port records, using an exact-number cash state as a supplied schema instance. This is the acceptance witness for the common foundation, not a separate financial runtime. The run must include all of the following and expose one retained execution from which each assertion is read:

1. A core computation produces identity evidence at runtime. Apply it through the existing generic action and use its result in an effect proposal. No new compiled-record publication is required merely because the proof was computed at runtime.
2. A generic pure producer stays pending after exposing a finite prefix. Two consumers specialize/use that prefix; the historical producing event is shared, while both present request/delivery occurrences remain counted. Include a consumer already waiting before publication, using the carried live-cut rules.
3. Send q from A to B. Stop immediately after send acceptance. Assert source balance `a−q`, recipient balance b, and one open transfer port q. Assert exact total `a+b` from the cut.
4. Deliver the same port concurrently to two clients, plus a duplicate/reordered transport packet. Assert one accepted receive, one recipient credit, the same receipt for duplicate requests, and distinct counted client deliveries.
5. Race delivery against an authorized refund of a different pending port. Assert precisely one of those conflicting consumes commits; neither result is manufactured while its required proof is pending. Repeat with reversed request order.
6. Send q back from B to A and receive it. Assert initial external balances, a changed retained accepted history, and the retained computed identity/facts. Reassociation or a compatible identity transport preserves the current heads and ports.
7. Copy and reindex receipt observations through valid contextual maps. Assert the event identity is unchanged. Reject an attempted receipt view that changes its resource occurrence/recipient without a checked boundary transport. A new compatible proposal may still be constructed normally.
8. Attempt a second incompatible acceptance from a consumed head/port. Assert conflict and no second emission. Also check equal pure payloads with distinct, valid input occurrences can produce distinct legitimate effects.
9. Exercise suspension before preparation, during proof checking, between reservations, after commit but before physical finalization, and before receipt delivery. All cut valuations and ownership invariants hold at each point; no partially accepted multi-head state is observed.
10. Compare the core result, interface/cut, premises, historical sharing and exact work readings of this same event DAG. A standalone numeric balance test or a second reconstructed event history is insufficient.

The schema payloads, admitted assumptions and chosen external choices must be included with the test output. The worker can implement this boundary without guessing what a pending transfer or accepted receipt means. It remains necessary for the author to prove the full chosen machine's claimed overlap/optimality/reflection properties; these local effect rules do not by themselves prove those stronger claims.
