# Executable continuation protocol for live reuse

This completes the operational prescription for adopting a newly available
fact at an already RUNNING consumer's committed cut. It applies to the same
reference, scope, receipt and shared-job machinery as V22. It creates no
second evaluator, plan space, branch-and-bound algorithm or distinction
between a presented identity and evidence obtained during execution.

The supplied `prefix-integration.patch` implements immutable historical
lookup, exact subscription catch-up, premise inheritance and guarded joins.
The state and transitions below specify the remaining live-adoption change.
Implement them in the current continuation path. They are not implemented by
the patch and are not a claim that the entire cumulative specification is
closed.

## 1. Boundary and records

A committed fact has judgment

\[
P=(\Gamma,\phi,s,r,\rho,\Delta):\quad
\Gamma;\phi\vdash s\Longrightarrow^*r.
\]

The exact boundary includes types, declarations, scopes, levels, required
faces and the dependency-closed free identities. `Δ` contains the immutable
revision and admission premises actually used by `ρ`. The reference to `ρ`
retains the derivation; it does not reexecute its events.

Turn each outstanding logical request slot into the following owned record.
This includes the child of an eliminator, a forwarding request, each separate
join slot, and a shared operation's suspended subrequest. The parent producer
itself retains its existing canonical key and single publication right.

```
Cut:
    owner producer and logical slot
    source boundary, source reference s0, occurrence face ψ
    immutable resume recipe K
    state = WAITING | RESUMING | CLOSED
    current generation token g
    current residual r
    committed receipt q : s0 ⇒* r at ψ
    committed dependency certificate Δq
    outstanding-ticket ownership and subscriber ownership

Ticket:
    retained Cut handle
    generation token
    requested residual and its complete observation key
    immutable prefix receipt from s0 to that residual
    immutable prefix dependency certificate
    one ordinary request/delivery obligation

Proposal:
    retained Cut handle and captured generation token
    pinned fact and exact boundary correspondence / simultaneous map
    prepared residual, composed receipt and dependency certificate
    validated snapshot stamp
```

`K` is a persistent typed recipe containing the original eliminator fields,
family, endpoints, scope and guard, or a retained join-slot handle. It is not
a raw pointer to a continuation or join that another delivery can free.
Use reference-counted/shared record handles for this retained ownership.

A generation token is a fresh stable identity. Do not introduce another
fixed-width semantic counter limit, bounded global continuation array or
native-thread-per-cut requirement. The existing arbitrary-finite-storage
contract governs allocation, collections and exact quantities. Allocation
failure means actual inability to provide storage, not a chosen dimension,
depth or live-ticket cap.

## 2. Opening a request slot

1. Construct `K` and the source boundary using the existing typed opening and
   substitution rules. Commit `Cut(s0, ψ, K, WAITING, g, s0, REFL, Δboundary)`.
2. Register its indexed fact subscriptions. Capture an immutable history
   boundary while registering, so existing facts are replayed and subsequent
   publication notifies it. Use the publication/registration partition proved
   in `REVIEW.md` R2. Process one index edge, subscriber or historical fact
   per retained bounded step.
3. Issue the ordinary request through a ticket for generation `g`.
   Registration watches facts; it does not demand a generic source computation
   merely to wait for that source to supply a better answer.

Subscriptions concern the current residual's structural observation key and
the source keys connected by already recorded instantiation/correspondence
edges. Maintain the reverse index as those edges are committed. A new edge
registers its applicable source watch using the same history/publication
partition. Do not enumerate arbitrary equal terms or all possible maps.

This is availability of the indexed relation already built by the machine.
It is not a proof that every mathematical equality has already been found.
Runtime evidence can add an edge through the same checked action mechanism;
provenance does not create a compile/run boundary.

## 3. Preparing an adoption

A notification creates or joins the shared preparation operation keyed by
the immutable fact, captured current cut boundary and correspondence. It
does not directly change the Cut under the notification lock.

For captured `r, ψ, g`, prepare:

\[
\psi\vdash r\Longrightarrow^*v,\qquad
q' = q\,;\,\rho_{r\to v},\qquad
\Delta' = \Delta_q\cup\Delta_{r\to v}.
\]

The source of the instantiated fact must match `r` at its full boundary.
Alternatively the proposal must include an explicit checked connector from
`r` to the instantiated fact's source. Two derivations sharing only an
earlier source do not supply this connector. In particular, knowledge of
`s0⇒u` and `s0⇒v` does not authorize replacing a current cut at `u` by `v`.

Apply the existing map validation, single-lookup simultaneous substitution,
required-face entailment and structural checks. Require
`ψ ⊢ φ[σ]`; observe the adapted residual under the destination's projected
face. A prefix fact does not import the source's old neutral/WHNF
classification. Reject a proposal whose residual observation key is the
unchanged current key. Do not wait for its source's final publication.

Revision/admission premises are prepared against one snapshot. If environment
mutation is possible during preparation, commit against its captured stamp;
a changed stamp triggers dependency revalidation through the same retained
operation before retrying. This is not whole-environment invalidation of an
already committed fact. The machine's established closed-session/reset
preconditions remain in force.

Guarded context construction is exact:

* For ordinary eliminator or forwarding contexts, retain the parent and
  continuation guards and intersect them with the child's fact guard.
* For a system branch, also retain the selected branch guard and the receipt
  of the scrutinee that established the branch recipe. A branch fact is not
  a completed join and has no premise on an unobserved sibling result.
* For a composition family bound at `j`, use `∀j φ` before transporting the
  fact to the outer composition context. A bound coordinate cannot escape
  through a guard or be specialized outside its scope.

All variable-size validation, dependency unions, receipt construction,
instantiation and index work are shared retained jobs. The commit section
below is a bounded installation of prepared handles, not a place to perform
those traversals.

## 4. Committing an adoption

With the Cut's lock held, require:

```
Cut.state == WAITING
Cut.generation == Proposal.captured_generation
the prepared snapshot is still the validated snapshot
```

If any check fails, release this proposal's ownership. Its already computed
pure preparation result remains shareable in its normal cache. Do not alter
the cut or charge another execution of that preparation.

Otherwise install fresh generation `g'`, residual `v`, receipt `q'` and
certificate `Δ'` atomically. Reserve the replacement request's launch before
unlocking, then enqueue it after unlocking. The corresponding immutable
prefix must be fully prepared and committed before it is observable in the
fact index; notification uses the existing bounded publication protocol.

Issue an ordinary request for `v` through a new ticket carrying `g', q', Δ'`.
This creates a new real consumer occurrence. The owner producer's canonical
key, publication right and result type do not change. No new semantic
producer is made merely by replacing this slot's waiting continuation.
The requested child uses the usual single-producer cache for its own key.

The previous ticket remains live. Its requested producer may serve other
clients. Do not cancel it, free its retained recipe prematurely, or pretend
its work and request never happened. Repeated proposals captured at the old
generation fail the installation check; they cannot install the same cut
transition twice.

## 5. Receiving a delivery

Every published child answer delivers once to each of its registered
tickets through the existing scheduler. A child that remains pending does
not promise an eventual answer: its ticket remains owned and pending.
For an actual delivery, record that event and consume the ticket once.
Then inspect the Cut:

```
if Cut.state != WAITING or Ticket.generation != Cut.generation:
    release the ticket's retained ownership
    perform no semantic resume and no parent publication
else:
    atomically change WAITING -> RESUMING
    detach this generation's live subscription rights
    transfer K and the ticket's receipt/dependencies to one resume job
```

The resume job composes the ticket's prefix with the child's returned
receipt and dependencies, then executes `K` once. Ordinary checking of a
result class and the existing invalid/stuck rules are unchanged. If `K`
needs another child, that request has a new committed Cut. When this resume
is complete, close this Cut and release the transferred ownership.

For a join slot, the winning resume fills that slot once. The join still
publishes only when its existing completion condition is satisfied. Old
tickets retain their own handles until their eventual deliveries; a join
may not free storage still reachable from those handles. A copied bare
`Gather*` is insufficient ownership.

Adoption and delivery are therefore linearized by the same Cut lock. If the
delivery wins, the proposal cannot install over RESUMING. If adoption wins,
the old generation's delivery is consumed without semantic resume. The new
generation alone can resume that slot. This resolves the duplicate-resume
race without deleting already executed work.

Stuck/cyclic children still have no invented answer. A valid new fact can
make the current slot executable without requiring its old pending child to
finish. Teardown drives or retires retained obligations through the actual
dependency protocol; it cannot block in allocation order waiting for work
that only teardown could service. Apply the existing V21 teardown correction.

An answered root certifies its current result and current active demand cone.
It does not certify that every superseded historical request has answered.
Keep those pending occurrences and any continuing shared producers in the
retained state. Accordingly, the old fixed-recipe statement that a successful
root leaves no RUNNING entry in its network applies to its active dependency
cone, not the union of all historical abandoned cuts. Record active-slot
edges separately from historical request edges; neither is inferred by
deleting events from the latter. This distinction is necessary once live
adoption is allowed, and is an explicit refinement of that earlier statement.

Machine teardown requires the existing host condition that no client can
still use its objects. It may then retire unanswered occurrences as part of
destroying that machine, without issuing fictitious semantic deliveries or
declaring them successful. Closing one client's handle does not establish
that condition for other clients or their shared work.

## 6. Events, ownership and the whole-state reading

Use the common event ledger for fact commitment, subscription, preparation,
installation, request, delivery and retirement. Each actual bounded step
has one execution owner; global counter differences spanning other jobs are
diagnostics, not that owner's work. Reusing a derivation points to its
existing event identities. It adds the actual adaptation events, but not a
second charge for the original beta or projection.

A superseded ticket's delivery still exists. Its semantic-resume decision
may be empty; its physical execution and ownership release are not erased.
Retain that information in the witnessed state/fibre. The external result,
local incidence boundary, effect/resource reading and work reading must all
come from this same state. This is the connection to the cumulative Stokes
contract: internal incidence cancellation does not discard internal events
or their costs.

These transitions concern pure derivations and pure observation requests.
An accepted effect occurrence, transfer or cash resource cannot be cloned
or undone by copying a fact or superseding a ticket. Its accepted-occurrence
identity and authority stay in the maintained state specified by
`FOUNDATION-ROUTE.md`. Network delivery and local receipt of a proof are not
new acceptance of the same resource-consuming action.

Independent Cut installations commute. Publication versus subscription has
the two-order correspondence proved above. Adoption versus delivery on the
same Cut has an exclusive winning order, with the losing ticket/proposal
still accounted for. These facts prove the stated ownership and semantic
safety properties. They do not prove equal actual work across arbitrary
adaptive choices. Retain nonzero cost differences in the valuation; do not
declare them zero by hiding the superseded requests in a quotient.

The larger whole-machine optimality/refinement obligation remains immediate
author work. This continuation protocol supplies concrete transitions for
that argument; it does not substitute a claim of optimality for the argument.

## 7. Required integration cases

Gate these through the actual producer/continuation path, with sequential
policies and multiple workers:

1. Start an instance before its generic source commits a useful fact. Keep
   the instance pending, then commit the fact. The instance adopts it and
   finishes without waiting for the generic suffix or replaying the prefix.
2. Pause after proposal preparation and advance the Cut through an ordinary
   delivery. Resuming the proposal must fail the generation check, preserving
   the already advanced result and all actual event charges.
3. Reverse that race: install adoption first, then deliver the old ticket.
   Exactly one resume fills the logical slot; both real deliveries are
   consumed and counted. Repeat with a join slot and a pending sibling.
4. Deliver several proposals for the same captured generation. At most one
   installs. Distinct clients of the adapted key still share its producer
   while retaining their distinct requests and deliveries.
5. Invalidate a used premise before installation and revalidate. Do not use
   the stale proposal. A structural prefix unaffected by the changed body
   remains available when its own premises still hold.
6. Exercise guarded branch adoption and composition-family guards, including
   a face depending on the bound dimension. Neither a partial equation nor
   a bound dimension escapes into an outer total observation.
7. Suspend each variable-size preparation/index/retirement phase with budget
   one. Preserve the same continuation and completed work, release locks
   before suspension, and charge events to their actual owner.
8. Release clients, then drain/free with old and current tickets pending.
   No leaked owner, stale join dereference, premature free or dependency-order
   deadlock is allowed. Keep the same accepted effect occurrence throughout;
   a superseded pure ticket must not repeat that effect.

These cases extend the existing semantic, sanitizer and exact-work gates.
They do not create another approval boundary. Continue the complete scope
in `IMMEDIATE-SCOPE.md`; none of its requirements becomes optional because
the evaluator prefix integration is now more precisely specified.
