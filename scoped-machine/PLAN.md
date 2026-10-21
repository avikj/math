# PLAN — converting the one execution system to bounded steps (agreed 18 Oct 2026, 14:47)

This file is the working contract. Every step re-reads it. Nothing here is optional.

Standing rules: design each family completely before writing it; no defect-driven development;
no subagents; work only from the shared specifications; no second engine/store/continuation form.

## 3. The requirement

(a) Every counted step is bounded: `Instr ≤ c·N + d`, N = steps. Any code inside one step whose
work depends on the size of a term, map, face, set, field list, waiter list or table is incorrect.

(b) The fine steps are steps of the relation with the diamond: §§26–27 (one producer per key,
linear continuations, exhaustive request/publication overlaps). So every computation over
variable data is a producer keyed by (operation family, operands) in the one protocol of
`eval.c`, executed as bounded steps, each delivery its own step. A memo computed twice
(wordmap_get / compute / wordmap_put race) is incorrect.

Representation consequences:
- variable records = bounded-arity interned sequences (maps, interval/face clauses, dim/var
  sets, origin field lists, template environments, scope telescopes, contexts, system branches);
- hash collisions advance one probe per step; table growth migrates a bounded number of slots per step;
- fixed-size nodes from free lists, refilled by a counted step (malloc is not a bounded primitive);
- entry state by compare-and-swap (U→R installs the evaluator; waiter push on a lock-free stack;
  R→D swaps the stack); interning inserts by CAS; per-worker deques. No critical section holds
  unbounded work.

## 5. What stays / what changes

Stays: all mathematics and laws (C[ρ][σ]=C[ρ;σ], single-lookup substitution, dependency-closed
restriction, opening without evaluation, (t, π_S χ) key and projection theorem, capture/apply/∀
laws, reindex(TVIEW(Q,E),σ)=TVIEW(Q,E[σ]), cubical clauses, template library programs, compiler
emission, certificate tags, checker and conversion rules); the REQ/EVAL/PUB/DELIVER protocol and
§27 overlaps; the test suite as semantic regressions.

Changes: execution form. Every computation over variable data is a family: entry key = (family,
operands), a frame with cursor/locals, a step function doing one bounded increment then requesting a
child key, continuing, or publishing.

One representation: raw origin = constant-field instance of the constructor-program
representation (reduction handoff §4.4), binders by (depth, slot) as in scopes. Gives alpha
identity, raw = template-view identity, and removes the VIEW/TVIEW branch in every head operation.

## 6. Scope after §59

Included: §60 (readings of protocol events: per-family step counters, per-entry counts, folds);
§65 (this plan); §75 (= families); §76 (by representation); §77 (actions keyed by content; checker/
conversion requests keyed by dependency-closed context restriction); §79 (global reads record
revisions; reuse under a later environment when all match); §§80, 83–84, 96 (fixed templates per
level tuple: Maps, presentation composition, dependent singleton with h,k, zero, node, generic
action F/G with middle inverse paths, groupoid laws via J and K(w); compiler exports diagrams as
these values); §88 proof use (judgment family; SCC iteratively, one edge per step; CORE, ASSUMED,
PENDING, INVALID, UNRESOLVED); witnessed-source readings (exact counts: low digit + carry blocks,
CONTINUATION-AND-COUNT-CLOSURE §C; per-producer event support; W(H) by support union; folds as
families); EFFECT-AUTHORITY §§2–9 + §10 witness (proposals, ordered reservations, one atomic commit,
lazy finalization, receipts, duplicate delivery = same receipt, conflict on second consume, cash
instance) as job families; CUBICAL-STOKES-ADDENDUM §10 interface (cube maps and face composition
from substitution, ∂, ∂²=0, cochains/pairing, relative cuts, resource map B, defects of supplied
comparison cells; production cells only from actual rules or checked supplied witnesses).

Excluded: §§61–64, 66–73 (plan comparison/selection — the detour).

Adoption of a pending prefix (completion handoff §10) is a represented transition, never a recipe
consulting whether a result exists; its races are comparison cells whose actual-work defect is computed.

## 9. Corrections adopted from the 14:54 attachment (binding on all later steps)

1. No representation may insert a dependency absent from the object. Variable records are NOT
   converted to cons sequences: reaching field k must not require traversing fields 0..k-1.
   Records stay contiguous (O(1) access to any field); what becomes stepped is their
   construction and interning: hashing, trie descent and full-key comparison of a variable
   record are a family advancing a bounded number of words per step. (Sequence module removed.)
2. Judgments depend on their actual premises, not on admission of everything registered.
   Whole-environment admission (§57 R1 / §59.4 freeze-reopen lifecycle) is replaced by validity
   of the judgment's dependency closure: the symbols its context, type and term actually reach,
   with their declarations/bodies checked as premises (a cyclic dependency such as bad/dependent
   still rejects when used). No global freeze, no session qualification of cached judgments.
3. One route for identity actions. TRANSFORM_CALL, CompiledTransform, GraphPairTemplate,
   certificate re-emission and APPLY_TRANSFORM/CONTINUE_REFERENCE are identified with the
   ordinary generic action (§83.4 F/G on Diagram values). The host compiler becomes an input
   adapter that builds Diagram values (with diagnostics); it defines no second semantic route.
   This replaces "compiler as families" in step 5 and reduces it.
4. Readings are folds of the local records of the steps that ran. No central event journal
   into which subsystems report; no global serialization of histories.

## 10. Rule from the 15:23 attachment (binding)

5. No host distinction may change the dependency, admissibility or compositional behaviour of the
   represented construction. Concretely: no phase barrier (check-then-run, finish-workload-then-
   reuse, register-then-publish); no privileged preparatory language with its own state or
   authority; a derived value (identity p, transform, receipt, completed prefix) acts through the
   generic action wherever its type permits, as soon as it exists, with no "install" event between;
   one judgment is executed once — the checker and the evaluator request the same keys rather than
   re-deriving. Ability of an added mechanism to solve the problems it introduced is no defence of it.

## 11. The protocol as corrected (review 5886af7) — binding

1. Producer rule. A request of key K: U — install exactly one producer and attach the requester;
   R — attach the requester to that producer, never run a second body; D — deliver the published
   value through the same delivery rule. A producer requesting its own key is an unresolved
   dependency (the request stays a waiter), never a private recomputation.
2. Synchronous API. `family_call`, `family_run`, `whnf` are root-driving only: an external caller
   requests the root key with a host frame as its waiter and drives the ordinary scheduler until the
   key is published. Inside a counted step every request suspends the frame (FR_AWAIT, FR_CALL);
   `family_call` refuses to run there. Root driving creates no barrier. The frame is the only
   continuation form; the entry is the only box a value is returned to.
3. Frames. A step ends in exactly one of request / call / yield / finish; after the frame is
   handed to the queue or a waiter stack its former owner does not touch it (the kept flag belongs
   to the executing job). One FR_* macro per line, never inside a nested switch.
4. Independent demands are launched (U → R(∅), one launch per step) and then awaited in launch
   order; a frame awaits every key it launched before it finishes, so a parent publishes only after
   every child it launched has delivered, and a failure is selected in branch order.
5. Canonical record construction obeys the same law (INTERNING.md): a small record is one bounded
   unit; a large record is its canonical tree of small records (units fixed by its length), and its
   contiguous record is the value of the one owner keyed by (table, tree root). Inside a step only
   small records are interned synchronously. Published values are complete: a record found by
   content counts only when its side data is published.
6. Revisions and binding views (replaces the superseded pin-set closure, deleted with pins.c).
   A revision is the immutable record (s, body), body 0 opaque. A binding view V is an
   immutable map symbol ↦ revision (a substitution record); a declaration or a body replaces
   the machine's current view by one persistent set; a pending computation keeps its own
   view, readable after later publications. Keys: a pure family is keyed by its operands; a
   relative family (one that reads revisions, directly or through a child: observation,
   the judgments that observe, body validity, the proof-use audit, effect preparation) is
   requested through the resolver (f, a, b, V), which requests the node (f, a, b, ∅) and,
   while the node's derivation read revisions differing from V's, the node whose path adds
   those symbols at V's revisions (path: a substitution record), and publishes the agreeing
   node's value. A node's key holds no view; its frames read through the view of the
   requester that installed it. An occurrence (an effect) is one node. A read of s is the
   dependency read(s, V); its value is the revision; the unfold step requests
   unfold(reference, body) at exactly that revision, and the body judgment body(revision)
   checks that same record. A use of s in a typing judgment (decl) reads s's declaration,
   which never changes once s is declared; it reads no revision.
   The revisions a derivation read are reads(entry), from its recorded dependencies (a
   resolver contributes its chosen node). Within one view every key is fixed; across views,
   which view's request installed a node can depend on the schedule: the value cannot, the
   work (reuse or recomputation) can — the scope of the schedule claim (HANDOFF §78.5).
   The public checking API, proof use and effect preparation request one judgment,
   judge.admit (check.c): its derivation by kind, and the body of every revision it read,
   of the revision in its view of every symbol whose declaration it used, and (for proof use)
   of every revision the conservative audit reached validated, closed under the reads and
   uses of those body judgments; its result names the validated revisions.
   Raw observation reads only what its reduction unfolds; the conservative stored-syntax
   audit exists only inside proof use.
7. Bounded steps (replaces the superseded charging of CAS retries to concurrent successes).
   Every callback, including its synchronous helpers, does work bounded by a constant.
   Registration (request_entry): a waiter joins by one exchange of the entry head and writes
   its link after it (PENDING until then); the exchange that finds U launches; an exchange
   that finds READY restores READY by a second exchange and delivers what it took back; a
   launch is one CAS from U, never retried; one job is reserved across the operation.
   Overlaps: request/request — exchanges serialize, each joiner is linked below the
   previous head, none retries; request/publish — publish exchanges the chain for READY
   once; a joiner whose exchange found READY returns everything pushed since to READY and
   delivers it; launch/request — the CAS from U succeeds for one launcher, a joiner that
   finds U is the launcher; publish/delivery — the chain is handed one delivery per job;
   the joiner writes its link by an exchange; a delivery reaching a link still PENDING
   exchanges in TAKEN and ends, and the joiner whose link exchange returns TAKEN hands the
   chain on and resumes its frame (exactly one side acts; neither waits); handed-off frames — after enqueueing
   or handing off a frame its former job never touches it (the kept flag is the executing
   thread's). The small-record interner's retries are bounded by its stream length (a slot
   changes only empty → leaf → inner node), so each unit is bounded by a constant
   (INTERNING.md). Host resource boundary: one fixed-size host block per pool refill or per
   count carry (2^64 events), outside every counted transition. The host frame of a root
   request is the external caller receiving its answer: its resumption is not a step of the
   source; every counted step belongs to exactly one producer. A budget is a host control
   bound on the jobs executed during a root-driving call, never a reading or a verdict.
8. One interpretation. A node in an environment is interpreted the same way for both node kinds:
   a construction's closed constant (X_CONST) is substituted by the environment's atoms; fields,
   binders and heads go through ENVSET/INTERP over the reference's environment, which is its
   interpretation record. One instance family (template.view) forms every reference: its
   required face is the node's interpreted required face strengthened by each reference image's
   requirement unless the slot's declared guard entails it. No ambient face (κ) enters a
   definition, a clause or a key; a scope is guarded by the face its body is defined on.

## 12. Step 8 design (EFFECT-AUTHORITY §§1–10, CUBICAL-STOKES-ADDENDUM §§1–11)

Every record is an interned immutable record of the one record table or a published value of the
existing producer protocol; the one new mutable state is the authority cell, which the effect
rules require (operational acceptance is a transition of the actual source, not a function of a key).

8a. Per-producer readings. Entry.work: exact count (count.h) of the steps of the entry's frame and
    its subroutines (single writer: the entry's one producer), frozen once it publishes.
    Entry.deps: the entries its producer requested or launched. support(H) is the family
    history.support over the published dependency closure of H's entries (a pending
    dependency is a live obligation, not history); W(H) = the family history.work summing the
    frozen counts over the union, exactly — a producer shared by two consumers is counted
    once while their two deliveries remain two RD_DELIVER events. The query is later work.
    (Supersedes the host scan of live counters, deleted.)
8b. Exact signed coefficients (interned limb records, sign; z.add, z.mul, z.neg one limb per
    step) and chains: an interned sorted list of (generator, coefficient), generator = (kind, id)
    for cube cells, product cells, ports, heads, occurrences, units. Families: chain.add (merge),
    chain.scale, BOUNDARY (cursor over terms and coordinates, one face per step), PAIR(a, c) (one
    generator value per step), COB(a) = c ↦ PAIR(a, BOUNDARY(c)). A cochain is a
    finitely supported table or COB of one; its values are module elements, the 0-chains over unit
    generators (summed and scaled by chain.add and chain.scale).
8c. Cube cells. CubeView(root scope with n dimension locals, dimension map: root local ↦ D(J)
    element over canonical coordinates c_1..c_m, parameter map). FACE(C, i, ε) substitutes c_i ↦ ε
    and renumbers c_{k>i} ↦ c_{k−1} in the images: both deletion orders of a codimension-two face
    give the same interned map, hence the same generator, hence ∂² = 0 by cancellation of identical
    generators. FACE is CUBE_REINDEX at that endpoint map; PRODUCT(x, y) is a cell whose faces i ≤ p are x's and
    i > p are y's, so the generic BOUNDARY gives Leibniz with sign (−1)^p.
8d. Effects. (Preparation's mathematical premises are judge.admit requests — the state type at
    its level, each state, and the witness's proof use — the judgments the public API decodes;
    the occurrence retains the admitted proof-use result. Supersedes the partial validator.) Cell table (non-moving, one atomic word per cell): AVAILABLE(head|port) |
    RESERVED(D, k) | CONSUMED(occurrence). Authority and capability records are interned; a
    capability is valid when its owning authority's registry issued it (genesis or an admitted
    delegation). PREPARE(P) is a pure keyed family (schema, states and witness checked by check()
    and proof_use(); capabilities against the registry). EFFECT(rid, P) is a non-pure keyed
    producer: same (rid, P) joins by the R/D rules (one receipt, distinct deliveries); its first
    step claims rid in the request index (rid ↦ P, one CAS) and publishes REQUEST_CONFLICT when rid
    is claimed by another P. Then PREPARE; then one reservation per step in the fixed total cell
    order (a cell RESERVED by another descriptor D' is awaited by requesting D''s own key, then
    rechecked; a stale head aborts with rollback one cell per step); then the one acceptance CAS
    RESERVING → COMMITTED; then finalization one cell per step (successor heads, CONSUMED ports,
    fresh output port cells); its value is the Occurrence record (the accepted receipt). Readers
    of a RESERVED cell resolve it through D's state word.
    Cash instance: Church naturals N in the core; send/receive/refund edge types are Σ/Path types
    over add; witnesses are checked by the kernel; V(F) reads balances and pending port
    quantities from the cut exactly (host exact natural of the normal form).
8e. Realization: the resource map (occurrence ↦ degree-1 generator, ports/heads ↦ degree-0)
    with ∂_res[e] = produced − consumed, B_0 of a cut; the work cochain from 8a; READ_DEFECT.
    Witness: one execution run for EFFECT-AUTHORITY §10 items 1–10 and ADDENDUM §11 checks 1–10;
    suspension points are taken by driving the effect root one budgeted step at a time and
    checking every cut valuation and ownership invariant between steps.

