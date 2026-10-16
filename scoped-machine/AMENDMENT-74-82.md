## 74. Uniform reuse: authority, scope, and the next implementation

This amendment follows the source/code assessment of `3a0d7c40816ad93e90e42c8f08a94379fbf151dc`. Implement it on that construction. It supersedes earlier statements that make the exact `RefId`, source declaration name, entire occurrence context, global environment counter, or host operation handle an unavoidable boundary of pure computation sharing. It preserves the earlier typing, scope, face, universe, simultaneous-substitution, ownership, and concurrency requirements. Section 73's exclusion of automatic plan search remains in force.

The immediate deliverable is **persistent computation reuse under structural identity, contextual weakening, valid specialization, and dependency-preserving environment extension**, covering all eight measured cases in the accompanying assessment. It also exposes the existing proof-parameterized identity action as an ordinary open term (§80). These are implementation requirements, not requests to choose an architecture.

An occurrence retains its original typed declaration and provenance. Its computation may be shared with other occurrences through a structural identification or an established typed reduction. Do not weaken admission by deleting metadata from occurrence records. Do not introduce a privileged learned-operation category or require a runtime proof to be registered before it can act.

This amendment specifies this increment. It does not certify arbitrary identity discovery, complete self-representation of the compiler, or a universal optimality theorem. In particular, §80's runtime proof parameter is not claimed to be the full construction of arbitrary diagram syntax inside the object language.

### 74.1 Four records and their meanings

Use the following distinctions; equivalent concrete struct layouts are permitted, their meanings are not optional:

* `Occurrence`: original reference, occurrence context, ambient face, admission/validation evidence, provenance. Keep all existing negative validation cases.
* `Computation`: an immutable operation and its mathematical operands, with a persistent producer cell. Caller ids, host phase names and traversal marks are not operands.
* `Answer`: immutable result data plus the dependency evidence required for reuse. For evaluation it also has the residual and reduction receipt of §78.
* `Delivery`: a consumer's view of an answer at its own occurrence boundary. Distinct consumers still receive distinct delivery events; they do not run separate producers.

These are implementation records over existing constructions, not new logical primitives. The same result ownership and U/R/D protocol applies to all pure request families. Diagnostic/session wrappers may be short-lived; reachable mathematical answers are not owned by a caller's temporary handle.

### 74.2 Counter contract

Retain the existing event vector and add per-operation producer execution counts and per-evaluator-rule counts. At minimum expose beta, fst, snd, path-beta, endpoint, global-unfold, Glue/unglue, system, composition expansion, and identity-action application counts. Count a rule when it actually executes, not when its cached result is delivered. Separately count shape construction, dependency validation, receipt instantiation, lookup, and delivery.

The acceptance condition is no repetition of the completed producer/rule work. It is not zero C instructions, zero adaptation frames, or zero consumer deliveries. Do not satisfy tests by relabeling repeated beta/proof/reduction work as a cache hit.

The accompanying `reuse_stats.h` fixes the public counter ABI used by the acceptance sources. Implement its reader against real production counters, with concurrent increments synchronized and counts monotone until machine teardown. Existing equivalent counters may back it. The first execution in these tests must increment the corresponding producer/rule counter; an all-zero implementation is not instrumentation.

## 75. Persistent pure-operation producers

### 75.1 Exact keys

Introduce a machine-lifetime memo index keyed by operation family and immutable operands. The following are complete keys for the listed operations, before adding actual external dependency versions where applicable:

| Request | Key |
| --- | --- |
| Formula constructor | tag, ordered/canonically ordered operands according to the existing constructor law |
| Restrict/substitute/map formula | input formula, atom/map/set operand, replacement bit where present |
| Support / Must | operation tag, formula |
| Set operation | operation tag, set operands |
| Set cost | set, immutable cost-model content |
| Direct formula reduction | formula, immutable cost-model content, fixed rule-set version |
| Check a supplied lower proof | proof record, immutable cost-model content, fixed proof-rule version |
| Antichain / family operation | operation tag, immutable operands |
| Realization / full certificate check | immutable prepared problem, supplied support/certificate |
| Specialization | input record, substitution restricted to its dependency-closed free boundary, any target judgment boundary actually used |

The model content includes weights, overrides and completed resources to the extent read by the operation; retaining the whole immutable model is a sound initial key. A display name alone is not a model distinction. Distinct declared mathematical rule sets are distinctions. Numeric registry ids may name already interned immutable content; they must not stand for a fresh copy of identical content.

Mutable demand graphs and geodesic builders are not cached by a mutable id alone. Freeze an immutable snapshot or use a builder revision which changes on every mutation. Successful checks concern that snapshot. The same principle applies to any externally mutable input.

### 75.2 State machine and handle behavior

Use `ABSENT`, `RUNNING(owner, waiters)`, `READY(answer)`; stable invalid results may be stored with their exact immutable premises. Resource exhaustion, suspension and unresolved cyclic demand are not cached as mathematical invalidity.

`request(key, consumer)` atomically creates one owner, joins the running owner, or delivers the ready answer. Publish once after the result and its dependencies are complete. Deliver after releasing locks. A running hit from another client is not a proof cycle. Detect a cycle in the actual producer dependency graph, rather than by the existence of a RUNNING cell alone.

`op_step(handle, budget)` advances at most the requested bounded frame work. A handle refers to a shared producer; stepping two handles must not execute two copies of that producer. Producer work is charged once. Each handle's request/delivery work is charged separately. Budget exhaustion leaves the shared continuation resumable. Releasing one handle neither cancels another consumer's work nor destroys a READY answer.

Completed children are independently persistent even if the parent suspends. Per-traversal visited marks remain valid for local iteration/cycle bookkeeping; they are not the only storage for completed results.

Implement suspension by producer continuations, not a blocking call while holding the work-store mutex. A producer requesting a child records its resume state, registers as a consumer, and yields. A ready child enqueues that resume. A bounded driver services enabled jobs in the requested handle's dependency cone, with one job owner at a time; it charges every serviced frame against that call's budget, including child frames. A waiting handle does not manufacture a second stack for an already owned child. With no enabled job and no completed root, return retained suspension; do not spin or declare a successful result. Existing synchronous wrappers drive this same graph until completion or a genuine unresolved/resource state.

Checking a structurally cyclic finite certificate may return INVALID for malformed certificate syntax. A recursive evaluator request remains suspended/stuck, and unresolved conversion remains unresolved. Preserve these existing family-specific meanings; RUNNING by itself establishes none of them.

### 75.3 Concrete `work.c` changes

Replace the `K_MARK, o->mark, 7, F` completed-result lookup in `step_reduce` and `reduction_record` with the key in §75.1. Include the model explicitly. Remove fresh sequence numbers from the identity of an otherwise identical immutable reduction answer. The answer contains the resulting formula, reduced flag, bound, proof and attaining support.

Similarly replace the completed-proof memo under `K_MARK, o->mark, 6, proof` with a persistent proof/model/rules key. Keep cycle detection distinct from ready-result reuse. A proof checked under one model must not be reused under changed weights without validation.

Apply the same rule to the other pure families in the table. Existing persistent support, restriction and cost caches may be retained. Audit constructors which return sequence-qualified records: retain occurrence/history identities where they identify an actual event, but intern mathematical result content independently.

## 76. Structural computation identity across references and binders

### 76.1 Structural normal form, not evaluation

Define `shape(t, rho)` as the interned structural description of an opened construction, with locally bound identities represented by depth/slot and free identities left anchored. `rho` is the bound-identity environment, restricted to the reachable typed boundary. Memoize this operation; build its result in bounded frames over a shared DAG.

This is alpha/view normalization of syntax, not beta normalization, theorem search, evaluation at a generic point, or unfolding of GLOBAL bodies. It must not execute a term to discover its shape. A finite syntax traversal can inspect inactive stored syntax, as structural validation already does, but must not semantically evaluate it. Charge the traversal; do not hide it inside a nominal constant-time hash operation.

Record all constructor fields, their sorts and order, packed levels, required-face data, binder-slot relationships and typed scope metadata. Use the existing interval/face normal forms, with bound atoms renamed consistently. Preserve distinct free variable identities. Preserve proof terms: equal endpoints do not identify different proofs.

For a nonbinder reference field, recursively obtain its shape. For a binder field, resolve the binder using the existing owner/slot API, extend `rho` with the resulting concrete identity mapped to the canonical local slot, and shape the opened body. Multiple fields under the same binder slot use that same local identity; this is essential for the composition family and tube. The domain is shaped in its prefix context, not in the context extended by its own binder. Nested scopes use their actual telescope stack and prefix rules.

For VAR, emit the local bound token when present in `rho`, otherwise the anchored free identity and its relevant typed declaration. For GLOBAL, retain the symbol identity and parameter images; its body is not part of syntax expansion. For TCALL, use the semantic action identity of §77 rather than the source declaration label. VIEW and TVIEW are opened through their existing correct APIs; their administrative reference kind and original construction-site id do not distinguish equal opened constructions.

The structural description has no new term constructors: its tags are the existing core signature and its scopes. It is an implementation normal form of those descriptors, not a second evaluator or an untyped replacement language.

### 76.2 Identities required of shape

For well-formed occurrences with the same typed data, require:

* alpha-renamed bound identities give the same shape;
* nested views and a composed view give the same shape;
* constructing a node at specialized fields and specializing its open construction give the same shape;
* raw constructors and template views with the same opened annotated construction give the same shape;
* changing a level, required face, actual free input, proof path or computational payload does not disappear merely because it is inconvenient for sharing.

These are structural statements. Additional proven identifications use receipts/transport; they are not assumed by the shape interner. Do not normalize all terms to decide whether to share them.

### 76.3 Producer identity and answers

Observation lookup starts from the structural computation identity and projected observation face. Validity across environments is decided by §79, not an unconditional whole-environment-version suffix. An exact structural hit shares the existing producer, including a running producer.

Canonical bound names used by a producer are derived from its structural descriptor and binder slot. Reify/open the descriptor with the existing typed scope machinery; all views of that producer see corresponding binder instances. A consumer receives an answer view adapted to its occurrence, not an unaccounted copy of the producer's graph.

Keep the original `RefId` and validation metadata available. If the public API needs the occurrence's original neutral or introduction reference, provide it in the delivery view. Internally use the residual of §78 for further computation. Do not expose another occurrence's private binder identities without the renaming/view which relates them.

Construction and shape computation are themselves memoized pure operations. Memoize each DAG node/environment pair and reuse its children. Do not flatten shared syntax into repeated trees, recursively expand globals, or rescan all unrelated terms to build a key.

## 77. Source provenance, compiled actions, and checker weakening

### 77.1 Two source declarations, one action

Separate the immutable semantic action record from its source receipts. The action key contains its typed parameter telescope, required face, domain/codomain and levels, proof-relevant inputs, argument slots up to bound renaming, and forward/reverse bodies. It excludes `IdentityDecl.id`, source locations and caller ids. Interpret term fields through §76; preserve the actual evidence, not just its endpoints.

`compile_identity` still validates every submitted occurrence. Once validated, an identical action obtains the same action handle; add the new source declaration/certificate association to a separate provenance index. Both orientations are built before a new action is published. Duplicate concurrent submissions join the same action producer.

Generic call construction uses the semantic action handle. Thus changing only the source label yields the same call computation and no second APPLY_TRANSFORM after the first application is ready. Keep distinct consumer/provenance receipts. Existing certificate verification re-emits and compares semantic content, while source associations remain inspectable.

### 77.2 Project the context of a judgment

For each checking/conversion request, compute the dependency-closed free declarations of all its operands, expected type, universe/face obligations and retained scope signatures. Restrict the context in its original telescope order to those declarations; close transitively under their declaration types and required faces. Keep their instantiated declaration data. Normalize the judgment face only with the existing support law.

This restricted judgment boundary is the semantic memo key. It must not bypass checking that the public occurrence/context is valid. Separate the admission of the whole supplied context from the pure judgment whose premises use only its restriction. Internal checking rules already operating under a validated context may pass that evidence directly.

Weakening by an unused declaration reuses the same judgment producer. A changed relevant declaration type or required face does not. A proof established under stronger assumptions is not reused at a weaker face without evidence. Continue to keep provisional recursive-symbol premises until their component is committed; a restricted key does not make those premises disappear.

## 78. Completed reductions are reusable under substitution and restriction

### 78.1 Answer data

An evaluation answer retains:

```text
source construction and typed boundary
ambient validity face
residual reference (or guarded system of residual references)
result class at the evaluated face
shared reduction receipt
actual dependency versions
```

The residual is the expression after the established reduction prefix. It is not necessarily a weak-head normal form after a later substitution or stronger face. The result class is not transported blindly.

A receipt is an immutable DAG recording existing kernel computation rules, their premises and composition. It has checked source/target/face indices. Kernel-produced receipts are valid by construction; unchecked imported receipts go through validation. The receipt is not a copied chronological log of allocations or queue events. Retain children by handle. Administrative work is accounted separately.

### 78.2 Emission table

| Existing evaluator behavior | Required receipt/residual |
| --- | --- |
| Introduction or free neutral with no reduction | Reflexive receipt, original construction as residual |
| Global with body | Unfold rule with the specific observed body version, followed by the child's receipt |
| Opaque global | Reflexive residual plus dependency on the observed absence of a body |
| Application whose function reduces to a lambda | Congruence for the function reduction, beta to the instantiated body, then child receipt |
| Application with neutral function | Rebuild APP around the function's residual, retain the original argument; congruence receipt |
| fst/snd of a pair | Scrutinee congruence, projection, child receipt |
| Neutral fst/snd | Rebuild projection around the residual scrutinee |
| Path endpoint | Endpoint rule with its entailed face, then endpoint receipt |
| Path beta / neutral path elimination | Scrutinee congruence and beta, or the rebuilt neutral PAPP retaining all family/endpoints/level data |
| Glue, glue or unglue face collapse | Existing rule with its positive face premise and subsequent receipt |
| Neutral unglue | Rebuild the eliminator around the residual scrutinee |
| Covered system / distributed eliminator | Guarded branch receipts and their reconstructed system; preserve coverage/overlap evidence |
| Covered comp | Existing tube rule and subsequent receipt |
| Comp by a family head | Family congruence, exact fixed-clause instantiation with shared dimension, subsequent receipt |
| Neutral comp family | Rebuild comp with the retained residual family scope; do not re-evaluate the family at an endpoint |
| TCALL | Exact instantiated action-body rule with its proof parameter, followed by the body's receipt |

An invalid observation has no successful reduction receipt. A suspended/cyclic computation has no fabricated completed receipt. All existing structural checks still inspect malformed inactive syntax independently of semantic faces.

### 78.3 The specialization rule

For `d : Gamma;phi |- t =>* u` and a valid simultaneous map `sigma : (Delta;psi) -> (Gamma;phi)`, construct the shared receipt view `d[sigma]`. A request for `t[sigma]` can continue by requesting `u[sigma]` under `psi`. Composition of receipt views is composition of scope maps. Do not replay d's beta/projection/transport steps.

After specialization, observe the residual normally: a formerly neutral path can reach an endpoint; a formerly uncollapsed Glue can collapse; a variable can become a redex. If the receipt is reflexive and its residual is the same request, it provides no forward progress: do not install a self-wait or treat its former class as a final specialized answer.

For a system residual, specialize the faces and branch references, retain the original coverage obligation, and execute the existing system observation under the target face. Do not reuse a branch outside its validity guard.

Restriction to a stronger face is the identity substitution with an entailment premise. In particular a completed reduction under true is available under i=0, although its residual may reduce further there. Invalid results are not generalized by this rule.

### 78.4 Finding existing reusable facts

Record a structural instantiation edge whenever existing APIs construct `reindex(t,sigma)`, compose views, or instantiate a template: destination computation, source construction, restricted map. This is metadata about work already requested from the construction system, not evaluation. Compose maps lazily and intern duplicate edges. An ordinary direct construction with the same structural computation identity sees those same recorded edges.

Keep a receipt index by source construction/structural identity and valid face, and a reverse index from an instance to its recorded instantiations. On an exact miss, consult these known edges and the same-construction stronger-face index. Reuse a matching completed receipt only after checking its map, face and dependency premises. This lookup does not synthesize a substitution, enumerate programs, or search for an unknown theorem. Explicitly supplied typed identity applications remain ordinary terms.

Cache the resolved forwarding adapter for the exact instance and its dependency premises. Deduplicate candidate edges and track visited instance/map pairs so administrative cycles cannot hang lookup. Skip reflexive self-adapters. Do not replay a failed candidate's mathematical computation while looking for a reusable receipt.

The index implements reuse along known constructions and supplied identities. It is not presented as an algorithm deciding whether any two arbitrary terms admit some undiscovered identification.

### 78.5 Concurrency and schedule claims

An adapter is itself a fixed pure computation once its source receipt, map and target boundary are chosen. It uses the ordinary one-producer protocol. It cannot overwrite an unrelated evaluator entry with a face-specific answer. If it targets its own running producer without a completed progress receipt, preserve suspended/cyclic status.

Record the actual selected reuse edge. For multiple eligible completed receipts, use the retained index order consistently and count index inspection; never select by inspecting waiter count or a requesting consumer's private face. A producer's chosen recipe is fixed at its creation.

Do not extend the old fixed-recipe schedule theorem to opportunistic receipt discovery without an argument. A generic receipt becoming available earlier can save work that another schedule already performed. Compare exact event vectors for a fixed initial ready set and fixed selected receipt/dependency graph; require equal mathematical outcomes and one producer per immutable key under general concurrent discovery. Record distinct selected graphs rather than claiming they were the same fixed computation. This is an explicit correction to the scope of the counter claim, not permission to hide duplicated same-key producers.

## 79. Dependency validity and environment lifetime

### 79.1 Version what can change

Give each symbol declaration/body slot a stable identity and revision. An opaque observation records the revision with an absent body. Setting that body changes its revision. Reading declared type/parameters records their relevant revision if the interface permits them to change. Machine generation still separates destroyed/recreated arenas.

All global reads in evaluation, checking, template interpretation and action construction must go through dependency-recording accessors. Audit `global_body`, `global_type`, parameter/dimension metadata and direct DEF reads. A producer's dependency set is the union of its direct reads and its child answer dependencies. Provisional symbol assumptions are retained as conditional dependencies until committed; cyclic mutually recursive validation commits as before.

### 79.2 Lookup and reuse

Index ready candidates by semantic request independently of the whole environment version. A candidate is reusable when every recorded dependency revision agrees with the current immutable environment snapshot and its admission premises remain committed. Empty dependency sets survive unrelated registration. Multiple historical answers may coexist under the same base request with different dependency sets.

Validate dependency sets by a memoized, bounded traversal; its result may be keyed by the immutable environment snapshot. That validation key does not force the mathematical producer to rerun. Do not replace exact revision checks by a probabilistic digest.

Running computations remain tied to their captured environment snapshot until their dependency set is complete. Preserve the existing host rule forbidding concurrent mutation/reset of an active environment. The increment does not introduce concurrent mutation of globals. Consequently the eight required cases do not need speculative cross-snapshot joining.

### 79.3 Admission and reclamation

`observe_checked` and compiler publication still require the current admission transaction and the validity of the submitted occurrence. A cache hit does not admit an invalid signature. This permits a conservative whole-signature admission gate while reusing independent successful mathematical work behind it.

Change `check_open_environment` so it opens a new admission session without destroying persistent mathematical answers. It may retire session-facing verdict/diagnostic handles. Persistent answers own stable dependency certificates and any diagnostic content they need; do not keep dangling pointers into the old session. Existing public pointer-lifetime documentation may continue to say old handles are invalid. New handles can refer to reused underlying answers.

`machine_free` still destroys the machine and its retained store after clients/work drain. Machine restart must not alias prior identities. A successful immutable answer may be reclaimed only under the existing ownership/reachability rules; a temporary operation handle is not its sole owner while other consumers or the memo store retain it.

The new environment tests must distinguish unrelated declaration additions from changing a dependency actually read, including the transition from opaque to defined. Both are mandatory; deleting `env_version` from keys without dependency evidence fails this section.

## 80. Runtime identities use the existing ordinary action term

Expose the graph-pair template as a reusable open core term over its complete telescope, including the proof parameter P and realization argument r. For a fixed pair of checked diagrams, its two bodies are exactly the existing forward/reverse expressions. No new logical rule is introduced.

Provide this constructor-level interface (names may be adapted, argument meanings may not):

```text
identity_action(pair_template, direction, sigma, proof_in_target, argument_in_target)
    -> RefId
```

Here `sigma` maps the diagram/common-output parameter context into the target. Proof and argument are already in that target. Build one simultaneous map extending sigma by P -> proof and r -> argument, restricted to the open body's complete typed boundary. Return the resulting view. Do not apply sigma again inside those supplied images. The checker validates the proof at the instantiated path type and the argument at the instantiated realization type.

This constructor can be used once to build an ordinary lambda over P/r. Subsequent in-language calls compute P and execute the action with no host callback, transform publication, environment reopening, or special learning event. The evidence term stays lazy until demanded by the body. Unresolved/cyclic proof computation remains ordinary suspended computation.

Retain the host declaration compiler for importing/validating diagram declarations and caching their structural templates. The no-publication test must exercise actual runtime proof computation through the open term. Do not misdescribe a host test which evaluates a proof and then calls `compile_identity` as satisfying this requirement.

This interface removes a needless per-proof compilation boundary for existing diagram families. Full internal construction of arbitrary new diagram descriptions is a separate capability; the worker must not claim it from this narrower test. No additional representation choice for that capability is silently introduced here.

## 81. Accounting and bounded execution

### 81.1 Charge the new work

Add bounded frame families for structural description, dependency validation, receipt construction/instantiation, producer lookup and alias delivery. Keep the existing coarse kernel events as projections. Consumers have distinct request/delivery occurrences even when their producers are identified.

Work atoms representing producer work refer to the actual shared producer instance, not an obsolete `(raw RefId, whole env version)` tuple which can split reused work. Preserve requested occurrence/provenance separately. Specializing an old work annotation is not a claim that all its old events execute again: extract new actual work using completed receipt cuts plus the adapter's real work.

### 81.2 No opaque unbounded frame

The `kernel_calls` field may remain a diagnostic. It is not the fine cost of its callees. Any path claimed to have bounded C work per fine frame must lower variable-length key hashing/comparison, face/interval normalization, scope/map traversals, checking and receipt operations into counted resumable steps, or charge them to a separately proved accounting bound. Whole loops cannot be covered by incrementing one counter around the call.

For `step(handle,budget)`, a synchronous helper that performs additional variable work inside one outer step violates the budget contract even if it increments counters afterward. Suspend inside that work or explicitly use a synchronous API which makes no bounded-step claim. Table growth, bulk copies and releases need incremental chunks for the bounded API. Ordinary allocation can be charged in words using the stated allocator model; do not claim constant wall-clock latency for an OS allocation.

The worker must provide a table of every synchronous kernel/helper call reachable from the bounded API and either its fixed bound, its resumable replacement, or the accounting lemma used. A nonempty list of unaccounted variable helpers blocks a claim of the §65 constant-factor refinement. It need not block separately delivering the correct sharing changes.

Choose a fixed compile-time chunk bound (for example 32 machine words) and document it. A copy, initialization, comparison or release frame handles at most that many words; the next frame retains its cursor. A recursive graph walk retains an explicit stack and handles a bounded number of fields/edges per frame. Table relocation uses the same chunks. State the word size, overflow outcomes, and allocator contract used by the deterministic backend. These constants may differ between backends; they may not grow with the input while being called one primitive.

### 81.3 Reuse and temporal availability

Previously completed work is an explicit initial resource. Work done before an identity became available is not retroactively deleted from a trace. A newly supplied receipt can cut subsequent work. This preserves both universal availability of known results and honest accounting of the work that actually occurred.

Use fixed-input/fixed-reuse-graph tests for balanced semantic event vectors. Fine hash, scheduling and synchronization counts are measured actual costs and are not silently asserted equal under every policy. Do not delete their costs to obtain a desired equality.

## 82. Implementation order, acceptance, and delivery

### 82.1 Ordered implementation

1. **Persistent work and action producers:** §75 and §77.1. Eliminate per-handle result loss, preserve proof/model separation, unify identical action bodies across source labels, add concurrent same-key tests.
2. **Restricted judgments and retained dependency evidence:** §77.2 and §79. Preserve old admission regressions, add unrelated-versus-relevant mutation tests, keep answers alive across session wrappers.
3. **Structural identity:** §76. Add the structural descriptor, its memoized construction, bound renaming and occurrence delivery views. Close direct/view, alpha, and raw/template cases.
4. **Residual receipts:** §78. Emit receipts at all evaluator rule sites, rebuild residual neutrals, record known instantiation edges, add face/substitution reuse and cycle controls.
5. **Ordinary proof-parameter action:** §80. Demonstrate the fixed diagram family's runtime proof action without host publication.
6. **Complete cost accounting for the claimed bounded API:** §81. Integrate actual reuse work into extraction; remove opaque variable-work steps from that API and document the bound.

Do not add a planner, general theorem search, fallback cofactor solver, or a `learn`/`retire` subsystem. Keep the accepted cubical formulas and scope construction. Each commit should include its focused regressions; deliver the final tree after integration gates.

### 82.2 Acceptance matrix

| Case | Required result |
| --- | --- |
| A1 Direct construction vs a specialized view | Same structural computation; the second demand repeats no native body/beta work; both occurrence checks remain valid |
| A2 Alpha-renamed lambdas and nested binders | Shared structural computation and application work; capture/slot/depth negatives still reject |
| A3 Raw node vs equal TVIEW | Shared computation after separate occurrence validation; wrong annotation/guard/level still rejects |
| A4 Generic completed beta, then specialization | No repeat of the generic beta; observe the specialized residual only |
| A5 Specialization turns neutral residual into redex | New residual reduction occurs and produces the correct answer; no stale NEUTRAL publication |
| A6 Stronger face with unused dimension | Reuse completed reduction; no repeat of its beta; keep separate deliveries |
| A7 Generic path/Glue then endpoint/face restriction | Correct endpoint/collapse after residual observation; stronger-face answer never leaks to a weaker face |
| A8 Unrelated global addition/session opening | Closed/independent answers reused; public admission of the new environment still runs |
| A9 Actual dependency changes, including opaque -> body | Old answer not reused as current without valid adaptation; new answer and checker result correct |
| A10 Identity source-label change | One semantic action/call producer; source receipts retained; second identical call has zero additional APPLY_TRANSFORM |
| A11 Same action endpoints, distinct proof paths | Proof-relevant evidence and any different action retained; no endpoint-only merging |
| A12 Repeat formula reduction / supplied-proof check | No repeated semantic producer work for same inputs; nonzero lookup/delivery accounting remains |
| A13 Changed cost model | Correct recomputation/validated reuse; no stale proof bound or attaining set |
| A14 Concurrent duplicate requests | One producer, all consumers delivered once; one caller's release/budget exhaustion does not cancel another |
| A15 Weakening by unused declarations | Reuse the pure conversion judgment; malformed supplied contexts and changed relevant declarations still reject |
| A16 Nested neutral eliminators | Residual drops the already reduced prefix; later substitution resumes from that residual |
| A17 Receipt maps compose | Two successive adaptations agree with one composed map, including dimension/face and dependent type data |
| A18 Reflexive receipt / cyclic runtime proof | No self-wait introduced by a no-progress receipt; genuine cycles stay unresolved/stuck |
| A19 Runtime proof parameter | One ordinary core program computes its proof and applies the fixed diagram action; no host compilation/registration during evaluation |
| A20 Accounting integration | Actual shared producer counted once; consumer and adaptation work counted; ready receipts cut already completed work |
| A21 Bounded API | Budget can suspend within hashing, traversal, validation and release; no variable-length hidden helper inside one claimed bounded frame |

Use the supplied eight diagnostics as inputs, not as permission to hardcode their expressions. Retain their positive correctness assertions and turn their misses into semantic producer/rule-count regressions. Do not require the old total frame deltas to become exactly zero: new lookup/adapter work is legitimate and must be visible.

Keep all existing sanitizer suites and review regressions, adapting assertions only where an explicitly superseded representation identity or event claim changes. Every such adaptation must name this amendment's clause and preserve the original mathematical/validation assertion. Run the new concurrent cases under TSan and ownership/lifetime cases under ASan/LSan on the worker's supported host.

### 82.3 Worker response format

Return the commit, section-to-function/test table, exact before/after semantic producer counts for A1–A20, sanitizer logs, and the §81 bounded-helper table. State separately whether the fine-cost obligation is complete; do not treat the old 198 accounting tests as proof of it. Include a single end-to-end run combining generic reduction, specialization, runtime proof action, a reused checker judgment and actual work extraction.

No instruction in this amendment authorizes replacing the construction with an external optimizer or declaring the whole original system complete on the strength of these finite regressions. It gives the worker an implementable next increment with explicit correctness and reuse obligations.
