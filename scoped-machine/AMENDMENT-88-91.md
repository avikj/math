## 88. Executable distinction between a checked program and established evidence

This section supplies an immediate conservative implementation for the proof-admission issue in §86.1. It preserves general recursive execution, the ordinary runtime constructions in §§83–84, and the existing compiler. It does not introduce a second object language or a compile-time-only proof facility.

### 88.1 What the existing certificate actually verifies

On source `3a0d7c4`, the following construction passes `check`, `compile_equivalence` and `certificate_verify`:

1. In context `A:U₀, a:A, b:A`, define `f = λx:A. a`.
2. Let `K = Πy:A. Contr(Fib(A,A,f,y))`.
3. Register `k:K` with body `k`.
4. Construct `e = (f,k) : Equiv(A,A)`.

The compiled forward call at b returns a. The reverse call at a remains stuck. The evidence itself has a PAIR weak-head form. These observations hold with one and four workers. `review_certificate_boundary.c` reproduces all of them. Interpreting A as a discrete two-point type and a,b as distinct points makes the constant forward map noninvertible. This is a counterexample to an unconditional equivalence interpretation, not merely a slow reverse computation.

Thus neither successful program typing, successful compiler re-emission, nor successful WHNF observation establishes that e is a mathematical equivalence. In this example the entire alleged inverse justification resides in a circular declaration. The forward computation remains a valid partial-program computation; it is not evidence that the declared equivalence has been proved.

The distinction is operationally significant: a future identity-reuse mechanism must not use this certificate to identify mathematical results, discharge a proof obligation, or erase a residual as contractible. Executing its typed forward code is a different operation and remains permitted.

### 88.2 The immediate, exact result contract

Add a proof-use result for the complete judgment `(Γ, φ, e, E, definition dependencies)`. Keep `check` and `certificate_verify` as their existing program-typing and compiler-derivation operations. Never reinterpret their existing VALID bit as the new result.

The attached `proof_boundary.h/.c` implements these statuses against the current public C interfaces:

| Status | Meaning | Permitted mathematical use |
| --- | --- | --- |
| `PB_CORE` | The existing checks succeed and the audited dependency closure expands into the acyclic cubical core. | Evidence of E relative to the retained Γ and φ and the soundness of the core checking rules. |
| `PB_ASSUMED` | The same check has explicit reachable opaque declarations. | Evidence relative to Γ, φ **and those declarations**; retain them as hypotheses. |
| `PB_PENDING` | The finite audit reaches a cyclic declaration/body component. | No unconditional mathematical certificate. Retain the pending dependency; execution remains allowed. |
| `PB_INVALID` | A required structural, formation or typing check rejects. | No evidence. |
| `PB_UNRESOLVED` | An existing check is interrupted or unresolved. | No verdict on the proposition. |

`PB_CORE` does not mean that an arbitrary supplied Γ is inhabited. It means the ordinary sequent under that context. Likewise a judgment under false is local to false; it cannot be published as evidence under true. The result retains the context, face, evidence, expected type and snapshot identity, as well as the opaque and cyclic dependencies.

This is a conservative certificate boundary, not a termination decider. A syntactically recursive total program may remain pending. No pending outcome is cached as refutation or inequality. There is no claim here that every total recursive function can be recognized by this audit.

### 88.3 Finite algorithm and its coverage

First run the current admission transaction, context validation, formation of E and checking of e:E. Failure and interruption retain their existing meanings. For a successfully checked judgment under false, record the vacuous face-local judgment; preserve the face.

For a nonfalse judgment, collect dependencies from the complete context declarations, E and e using a memoized finite stored-syntax walk. The implementation deliberately does not reuse the substitution traversal, does not evaluate, and does not open a scope outside its telescope.

The required cases are:

| Record | Dependencies traversed |
| --- | --- |
| Ordinary variable | Its declared type; a bound scope atom is handled through its enclosing scope's declarations. |
| Raw view | Every stored reference field, every term image of its map, binder domain declarations, and the types of retained free variables. Inactive branches are included. |
| Template view | All retained reference and scope values in its declaration-closed environment. |
| Scope | Every local declaration type, the reference body and the declared reference result type; nested scopes recurse through their containing views/environments. |
| Global occurrence | Record the symbol; inspect its type, parameter declarations and body when building the symbol dependency graph. |
| Transform call | Both stored transform bodies, domain/codomain, parameter context and the ordinary call fields/images. Decode the payload as `2*id + direction`. |
| Interval, face, level | These contain no global-reference constructor. Structural validation still checks them; they introduce no additional symbol edges. |

For the present fixed template interpreter, all reference inputs come from its retained typed environment. The expression opcode table has no embedded literal-reference/global opcode. This fact is part of the audit argument. If an extension adds such an opcode or permits new program constants, its constants and their declarations must become explicit traversal edges before that extension can receive `PB_CORE`.

For each reached global s, its outgoing edges are all globals reached in its declaration, parameter types and body. No body gives an explicit opaque assumption. Compute the strongly connected components of the reached graph. A component is cyclic exactly when it has at least two vertices or has a self-edge. Any reached cyclic component yields `PB_PENDING`; otherwise reachable opaque declarations yield `PB_ASSUMED`; otherwise return `PB_CORE`.

The supplied C uses a finite DFS/Tarjan implementation. Its roots and edge sets are explicit; global bodies are not unfolded recursively into syntax. The stored-syntax walk intentionally retains some dependencies which substitution or reduction can later remove. This conservatism can delay a certificate, but cannot justify an unsupported proof. It must not be advertised as minimal logical support. The worker's measured dependency projection may refine this traversal only with a preservation argument; dropping declarations, inactive syntax or scope metadata without that argument repeats earlier review failures.

Soundness of the acyclic case is by topological expansion: immutable ordinary syntax, scope records and the fixed template programs are finite; nonrecursive global bodies and their types can be expanded in dependency order; compiled calls expand through their stored checked bodies. The resulting term belongs to the existing cubical core under Γ plus the explicit opaque declarations. Its proof claim is therefore the claim supplied by that core's typing rules. This argument adds no general recursion rule to the logical core and makes no new claim that the C checker itself has been formally verified.

The scan includes the expected type and context, not just the evidence's executable fields. Otherwise an apparently harmless term could rely on a circular type-level definition. Existing face, scope and universe checks remain prerequisites.

### 88.4 Runtime-produced proofs follow the same rule

Suppose a recursive producer evaluates to a finite residual r. Submit `(Γ,φ,r,E)` to exactly the same proof-use operation used for supplied evidence. Its computation history does not itself become an assumption of r.

The test uses `(λz:P. refl(a)) loop`, where `loop:P` is circular. The conservative source audit is pending. Evaluation returns the finite reflexivity term; its audit is `PB_CORE`. No host identity compiler, environment reset, alternate evidence encoding or special trusted producer is involved.

Conversely, `λx. loop` remains pending despite being a lambda WHNF; a pair retaining a circular contraction proof also remains pending. Inspect all retained proof data, including under binders. Inspecting only the head is insufficient.

An already established proof in Γ is usable as a variable under that Γ. Importing an opaque symbol does not turn it into a newly proved theorem. Discharging an opaque assumption requires a checked replacement in the same typed context; apply ordinary simultaneous substitution and certify the resulting judgment. Do not flip a flag or use a successful partial-program typecheck as the discharge.

This keeps production and consumption in the same running language. It distinguishes unfinished evidence from established evidence; it does not distinguish evidence by whether it was written before or during execution.

### 88.5 Integration into identity compilation and reuse

The existing compiler may continue publishing a well-typed executable transform record, including a partial transform. Keep `certificate_verify` explicitly documented as verification of the compiler derivation. Attach the new proof-use result to any request to use the record as an established mathematical identity/equivalence.

For each evidence schema, the root audit includes its actual evidence and expected type: the identity path, the equivalence value, the terminal residual equivalence, or the pointwise contraction. CUT_TO_PATH's generic construction has its ordinary core proof. Checking only the emitted forward body would miss an unused inverse obligation.

Mathematical reuse is authorized only by `PB_CORE`, or by `PB_ASSUMED` with every recorded hypothesis explicitly retained in the occurrence context. `PB_PENDING`, `PB_INVALID` and `PB_UNRESOLVED` authorize no unconditional theorem use. They do not prohibit evaluation of well-typed code or reuse of genuine operational reduction receipts.

A proof-use result is immutable. Cache its complete judgment and dependency certificate under the same producer discipline as other work. A caller's budget interruption does not destroy completed audit work or become a mathematical result. The supplied integration module records the current environment version because that is the base ABI; integration with §§74–82 must use its exact immutable definition revisions and dependency-closed context, rather than reintroducing whole-environment invalidation for independent results.

Do not confuse an operational prefix receipt `t ⇒* u` in the partial language with an unconditional logical inhabitant of every proposition that t was assigned as a program type. A returned finite proof u may be checked independently. The prefix receipt itself justifies the recorded reduction/reuse under its actual operational definitions.

### 88.6 What the code closes

The new finite algorithm and eleven positive/negative cases are executable now. The strong compiler reproduction additionally asserts that both the alleged equivalence and its compiled forward call receive `PB_PENDING`. The existing partial behavior is preserved.

This closes a concrete unsafe interpretation of the existing VALID/certificate bits. It does not supply universal termination recognition, a new coinduction principle, or proof of every implementation function. Such claims cannot be obtained merely by broadening the meaning of VALID.

## 89. Measured correction to the C-work claim

### 89.1 A counterexample in the actual C evaluator

`review_frame_cost.c` checks a system whose first branch is total and whose remaining branches have false faces. Every branch contains the same well-typed variable. After admission it explicitly resets the evaluator and measures a fresh observation.

On `3a0d7c4`, with one and four workers:

| System branches | Stored fields opened | REQUEST | EVAL | PUB | DELIVER |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 2 | 4 | 2 | 2 |
| 64 | 128 | 2 | 4 | 2 | 2 |
| 1,024 | 2,048 | 2 | 4 | 2 | 2 |

`open_ref` allocates the head-field array and iterates over every field before the evaluator selects the first branch. Consequently those four evaluator frames perform work increasing with the branch count. This is a structural counterexample to a size-independent constant-factor C-work bound based only on the current event vector. It does not depend on timing noise, a hypothetical optimizer, or the v10 abstract scheduling example.

Admission is excluded explicitly in this experiment, not silently declared free. Counting admission as well requires charging its own walks and conversions.

### 89.2 Exact unit required for the transfer theorem

Retain the current event vector as a useful semantic diagnostic. It is not the full instruction-cost measure. Refine unbounded helpers into resumable frames whose elementary steps do a bounded number of machine-word operations. A word is of the implementation's declared width; arbitrary-precision values are sequences of words and their traversal is counted.

Use a small-step state `(pc, fixed registers, owned cursor/continuation handles, store)`. Each transition executes one fixed opcode case. The complete opcode families needed are word load/store, fixed-width arithmetic/comparison, bounded cell construction/retirement, cursor advance, branch, enqueue/dequeue, request/publication/delivery bookkeeping, and a single atomic attempt. Higher-level algorithms are loops over these operations. A bulk scan, hash, comparison, allocation or rewrite is not one step merely because C gives it one function name.

For the current source, the lowering obligations are:

| Existing operation | Work that must be exposed |
| --- | --- |
| `open_ref` / `tview_open` | Field cursor, per-field recipe interpretation and substitution work, bounded head-cell allocation. |
| Map construction/composition/reindex | Each visited image/declaration and each exact map lookup; all normalization and interning work. |
| Interval/face DNF | Atom/clauses examined, generated conjunction products, absorption/comparison work, quantifier and entailment traversal. Do not hide output-size growth. |
| Exact interning | Reading/hashing key words, bucket/trie traversal, collision comparisons, insertion and resize/copy work. A hash hit is not exact equality. |
| Request/publication | Each continuation registration, each waiter visited, each delivery and queue operation; an unbounded waiter list is not one constant-cost PUB implementation. |
| Net replacement | Each fixed-size agent action plus any descriptor/list traversal, validation or allocation it invokes. |
| Checker/compiler/audit | Every structural/typing frame, certificate dependency edge, emitted record and graph traversal; typechecking is not a free prelude to an end-to-end claim. |
| Memory/ownership | Cells allocated, released, scanned or copied; collection, arena growth, teardown, failed atomic attempts and retries when included in the claimed interval. |

Every loop in the counted path must either execute counted cursor steps or have a literal bound independent of input size. A pure helper called from several places has one shared implementation and the same accounting in every place. The coarse vector and the fine vector are separate reports: do not add both and charge one operation twice. A fixed-size allocation opcode must use bounded arena/free-list operations; arena growth, clearing and copying are separate counted loops. A host allocator call is not automatically a bounded primitive.

The useful simulation statement is:

`C_steps(run) ≤ c · microsteps(run) + c₀ · fixed_host_boundary_work`.

For an explicit interpreter performing one bounded dispatch per microstep, a corresponding lower bound holds for that implementation under its stated machine model. Constants may depend on the fixed program and word model, not the term size, map size, DNF size, waiter count or proof length. Variable-size input ingestion/output and teardown must be included or reported as separately counted intervals.

This is a straightforward implementation theorem only **after** the bounded-step machine has been implemented and the helpers audited. It is not already proved for the present C source by the words “interaction net.” The supplied cost reproduction must account for every field actually opened. There are two legitimate outcomes: retain the full head opening and count its growing work, or make opening demand-driven so the unused fields are not traversed. Do not require avoidable scans merely to satisfy a counter. In either case retain the result assertion and report the actual fine work alongside the coarse event vector.

Parallel contention also needs its own accounting. An adversarially scheduled retry loop can perform arbitrary attempts without a semantic reduction. Charge those attempts, or state a serialized-work bound and a separate contention bound. No statement about wall time or arbitrary OS scheduling follows from the semantic event count.

## 90. Exact scope of the diamond and identity-cost arguments

### 90.1 Preserve the theorem's actual hypotheses

The one-step diamond theorem proves random descent for the specified relation when a normal form is reachable. A one-producer memo table alone is not that hypothesis. Nor does the local confluence of APPLY_TRANSFORM prove the property of every checker, cache, adaptation and host helper around it.

The v10 ready-cache model establishes a failed implication, not a C-runtime counterexample. The C counterexample in §89 establishes a separate cost-granularity defect. Keep those findings separate. The current fixed-recipe scheduler's existing schedule tests remain useful evidence for that scheduler.

For a claimed fine-step diamond, enumerate reachable overlaps in the actual relation and supply a commuting square or an explicitly weighted commuting diagram. The relevant overlaps include request/publication, concurrent same-key interning, native evaluation/receipt adaptation, generic reduction/specialization, claim settlement/dependency invalidation, and subscription delivery/cancellation. Two transitions which inspect or modify a shared readiness fact are not disjoint merely because their application agents occupy different cells.

Each adaptation must retain the source, map, face, dependencies and exact operational/proof receipt. A failed or unfinished alternative does not become evidence. Do not add branch-and-bound or an outer planner to resolve this obligation.

### 90.2 Why forcing generic evaluation first is not a repair

The attached test now reproduces this on the C core. For a path p:a=b, endpoint application computes `p@0=a` without evaluating p. If p is an unproductive recursive path producer, generic application `p@i` can remain stuck while its endpoint instance returns immediately. Requiring a generic result before permitting every specialization therefore changes the evaluator's termination behavior.

More generally, a specializing face may make a branch unnecessary. A sharing policy may reuse an established generic receipt, but it may not force an otherwise unnecessary generic computation as a prerequisite to a terminating instance. This is already required by the path endpoint and face rules. Any stronger shared-redex representation must prove preservation of those demand rules.

### 90.3 An identity supplies a transformation, not zero-cost optimal selection

For proved `p:x=y`, transport in a family O supplies `O(x)→O(y)` and the inverse transport, with their homotopies. This is the concrete runtime operation in §84.2. It can transfer already computed evidence and its shared dependencies. It does not create a missing inhabitant of O(x), nor prove that discovering p has zero cost.

For a finite chain of certified rewrites with measured costs `w₀,…,wₙ`, record each difference `Δᵢ=wᵢ₊₁−wᵢ`. Then `ΣΔᵢ=wₙ−w₀` by telescoping. Shared costs must be measured on the relevant producer union and cache boundary, as in §§60–66; summing occurrence-local costs can double-count shared work.

A scalar potential on a connected undirected rewrite graph exists with those edge differences exactly when every closed walk has zero sum: necessity follows by telescoping; for sufficiency, define the potential by summing along a path from a chosen base and use the closed-walk condition for path independence. This is a cost-consistency theorem. It does not imply that every equivalent route is cheapest, that all primitive traces have equal length, or that the graph can be explored without cost.

Adding a compiled macro shortcut while charging it one step changes the relation and metric unless its constituent work is retained. If both a one-step shortcut and its longer original implementation are admitted as unit-cost paths to the same normal form, the equal-length conclusion fails. Lowering both to the same primitive rules can avoid that particular mismatch; it still requires the actual primitive overlap proof.

Accordingly the complete adaptive diamond is still an author-side theorem obligation. There is no honest implementation instruction that makes it proved by adding a counter or renaming an evaluator frame. The worker can implement the concrete reuse and proof-boundary contracts while that stronger claim remains explicitly unaccepted.

## 91. Completion criterion and the next worker pass

### 91.1 Concrete changes now ready for integration

Keep the accepted core. Continue the uniform reuse work in §§74–82 and the ordinary runtime construction work in §§83–84. Add the §88 evidence boundary at mathematical-certificate consumption, without rejecting general recursive program execution. Preserve ordinary proof values and the same runtime action for supplied and computed evidence.

Integrate the attached proof-boundary module or an equivalent implementation with the same traversed inputs and outcomes. Its conservative treatment of source syntax must be documented. Run `test_proof_boundary.c`, `review_certificate_boundary.c` and `review_frame_cost.c`; the supplied runner compiles the base source afresh. Keep the old program/compiler assertions and add the new evidence-boundary assertions. The reference module has no persistent memo of its own; integrate it with the existing producer/dependency protocol rather than copying this one-shot allocation policy into every runtime request.

For production integration, replace recursive host graph walks with suspendable frames or an explicit owned stack, account for that work under §89, and retain completed subresults across budget interruption. This is traversal of known finite records, not exploration of alternative programs. Its error and ownership behavior must be tested under the worker's full sanitizer gates.

Return an exact table of semantic-frame counts, fine-work counts and proof-use outcomes. Report the three different questions separately: whether the code is well typed, whether a mathematical certificate is established under its stated assumptions, and whether the requested observation completes.

### 91.2 What cannot be filled by an implementation choice

The existing constructors transform supplied realizations and proofs. They do not supply a universal terminating operation which, from an arbitrary mathematical specification, returns a witness or a finite proof that no witness exists.

The elementary obstruction is explicit: if a total effective procedure decided whether each program halts on its input, define D(x) to loop when that procedure says x halts on x and to return otherwise. Applying the procedure to D on D contradicts either answer. Describing a program's finite syntax and all of its reduction rules does not remove this construction. Supplying a non-effective oracle containing the needed answers changes the premise.

This does not prohibit partial inference, complete procedures for restricted classes, arbitrary improvement through discovered identities, or proof-producing programs with broad practical reach. It prevents declaring the unrestricted total answer-or-obstruction promise implemented by this kernel. The exact endpoint when a producer has not supplied a witness is a pending computation; quiescence, a budget or an unrecognized recursive proof is not a refutation.

Full object-language quotation and execution of the C checker/evaluator is also distinct from §83's semantic diagram values. An exported diagram is not the source code of the kernel. No reflected checker/evaluator has been produced in this pass; the handoff must not claim that feature has been supplied. Reflection would additionally require an explicit syntax encoding, typed decoding, a simulation and a level discipline. None is obtained simply by accepting the finite presentation witnesses.

### 91.3 Validation and exact status of this pass

The six fresh-build runs of the new C witnesses (three binaries, one/four workers) pass ASan/UBSan against `3a0d7c4`. Leak detection was disabled because the preceding attempt in this host failed in LeakSanitizer's process-inspection environment; this pass does not claim LSan or TSan success. The worker must run those gates on its supported host. No production branch was changed or pushed in this pass.

The result is concrete progress: an executable conservative proof-use boundary, a stronger compiler-level reproduction, a real C cost counterexample, and explicit implementation constraints. It is not a proof that the complete intended adaptive optimal machine already exists. Universal finite inference in the unrestricted sense is an invalid completion requirement; full reflection and the whole-machine diamond/cost simulation remain substantive uncompleted work, rather than unspecified details for a worker to guess.
