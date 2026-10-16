# Post-§59 implementation direction: retain the construction, remove automatic plan search

This is the normative §73 amendment to `scoped-cubical-machine-handoff.md`. It supersedes the instruction to implement all of §§60–72 as an automatic selector. The accepted baseline is `24b2bfb6182c193d23551ea3a0228519504a8ec6`.

## 73. Corrected implementation disposition after §59 acceptance

### 73.1 Decision and mathematical boundary

**Proceed with the work below now. Do not pause the whole increment. Do not implement the §68 automatic cofactor solver or the §69 frontier/incumbent machinery as a required component.** Removing branch-and-bound alone would retain exhaustive plan search and would not correct the architectural detour.

The existing identity compiler gives checked executable transformations. The next authorized work makes the retained sharing, demand, specialization and cost structure explicit around those actual transformations and executions. The author-added comparison of independently prepared programs is not substituted for normalization of a posed declaration.

The source's §5.28 identifies its claimed minimum over identity-application orders from the same posed declaration. Keep that comparison domain explicit. Resource equalities, interaction diamonds and concrete implementation costs each require their own stated interpretation; a cost formula is not permission to change a kernel reference's recipe. This amendment gives an implementable infrastructure increment, not a new proof or implementation of the source's full declaration-to-answer claim.

### 73.2 Exact section disposition

| Material | Required action |
| --- | --- |
| §60 | Implement demand extraction with ready-key cuts, required dependency occurrences, one shared producer and separate consumers. Obtain demand premises from the admitted recipe and actual observation; retain unresolved guarded demand rather than inventing dependencies. |
| §61 | Implement the finite resource algebra and valid subset-absorption checks. Retain factored DAGs. An expanded antichain is a semantic normal form, not a requirement to enumerate a family or choose a program. |
| §62 | Implement typed specialization, work-key identification and Boolean direct image before cache cuts/cost calculation. Re-establish applicable guard/head premises. |
| §63 | Implement the contextual work annotations and differences of two supplied, compatible realizations. Retain both source expressions, connecting evidence and starting state. A difference is an annotation; executing a transport has its actual nonnegative cost. |
| §64 | Retain the transition-domain, lower-bound, attainment and progress certificate contracts. Validate supplied finite certificates against their stated domain. Do not add shortest-path search or the sorting-policy recurrence as a runtime requirement. The mathematical lemmas remain reference material. |
| §65 | Implement the bounded-step refinement and backend-accounting obligations. Count helper work and actual initial resources. The transfer lemma remains conditional on its displayed coverage and optimality premises. |
| §66 | Implement the declared boundary, recipe, consumer, expression, cost-model and certificate records and their direct operations. The word `Plan` in a record name does not require a planner. A record may describe an existing checked construction or actual execution. |
| §67 | Retain finite expression/compatibility validation and the shared positive formula representation as resource annotations. Keep typed witnesses and connector costs. Do not enumerate realizations or make preparation of a plan family a prerequisite for ordinary machine execution. |
| §68.1 | Implement formula interning, stated constructor simplifications, stable atom order and `restrict` as a syntactic operation. |
| §68.2 | Automatic `solve(F,i)`, recursive OMIT/TAKE exploration and the selection memo table are excluded from this increment. |
| §68.3 | Retain realization reconstruction when a checked support/witness is supplied. Reconstruction does not create or search for that witness. |
| §68.4 | Retain specialization and environment invalidation laws for work annotations and supplied certificates. |
| §69.1 and §69.4 | Retain verification of supplied finite proof DAGs and upper witnesses, including exact arithmetic and boundary checks. Checking a supplied SPLIT proof does not launch a search for its children. No certificate is synthesized by assuming its desired conclusion. |
| §69.2–§69.3 | Remove the required SearchCell frontier, incumbent, pruning and selector-state API. Suspension is ordinary continuation suspension, with no inferred mathematical verdict. |
| §70 | Implement Must, mandatory factoring, disjoint-support checks, the displayed directly derivable resource equalities, and instantiation of supplied scoped schemas. A rule fires only when its checked premises hold. An unreduced resource expression is retained; it does not trigger fallback enumeration. |
| §71 | Implement bounded continuation frames, memo reuse and the actual total-work ledger for the retained operations. Omit SOLVE and FRONTIER frame families. Count certificate checking and any explicitly requested resource analysis where they actually run. |
| §72 | Replace the automatic selector API and selection acceptance interpretation with §73.3–§73.5 below. The non-search invariants remain required. |

The old algorithm text is retained as reference material so the change is explicit and lossless. It is not an active implementation mandate.

### 73.3 Operations and integration

Expose the direct operations already defined in §66: specialize, demand, compatible compose, form supplied alternatives, justified absorb, extract work, and check supplied cost/optimality evidence. Add the formula and proof operations retained in the table. These are explicit requests over existing checked records; none implicitly invokes an optimizer.

Connect them to the accepted identity-compiler and evaluator APIs:

1. A compiled identity transformation retains its complete instantiated boundary and connecting evidence. Its actual application/receiver and evaluator work use the existing counted producer/consumer occurrences.
2. Work annotations retain operation and operand identity. Coincident output values do not identify unrelated work. Two requests for the same producer retain two request/delivery pairs.
3. For actual-run reporting, use the actual execution trace and its initial resources. For symbolic recipe accounting, retain the recipe's guard/head premises and certify its relationship to that trace before describing it as an exact execution prediction.
4. Resource simplification never overwrites an ordinary evaluator key with a different recipe. Any executable change uses an existing checked transformation and carries the required connection to its consumer boundary.
5. Finite certificate verification accepts an exact supplied domain with all required edges/alternatives, or instantiated schema evidence for that domain. Incomplete coverage is not silently treated as complete. Checking a lower bound, a successful trace, or an empty supplied family does not establish uninhabitability of an arbitrary declaration.

For bounded execution of these host operations, use the ordinary operation handle and continuation discipline: RUNNING with retained state; COMPLETE with a result; RESOURCE_LIMIT with resumable retained state where resumption is supported; INVALID with a diagnostic. These are operational states, not new object-language datatypes or additional logical answers. `step(handle,budget)` advances only counted bounded frames and does not create an incumbent or a search frontier.

The §72 names `begin_selection`, `step_selection` and `commit_selection` are not required. Ordinary execution continues through the accepted machine; an explicitly supplied checked transformation or witness is instantiated through its existing interface.

### 73.4 Work accounting and sharing

Retain §60's demand closure and §65's instruction-accounting refinement as distinct levels. The coarse event vector remains available. The fine ledger exposes bounded word/key/set/limb/allocator steps, including table probes and variable-length comparisons. Merely incrementing a counter once around an unbounded C helper does not implement this requirement.

Use the deterministic executor for the bounded-backend correspondence. Record the actual synchronization and scheduling work of parallel executions. Require schedule independence only for the event classes whose balance has been established; do not silently infer it for all fine administrative work.

Charge each phase that actually executes: annotation preparation, explicit resource rewriting, certificate checking, transformation instantiation/commitment and ordinary execution. Record reuse with its lookup/delivery cost. The source expressions, typed evidence and complete relevant environment/resource snapshot remain available after a derived scalar is calculated.

### 73.5 Acceptance and delivery

Keep every existing accepted regression and full sanitizer gate. Add these concrete cases, using the existing compiler/runtime for integration:

1. Two consumers of one producer yield one producer's work and two request/delivery occurrences.
2. A ready root cuts its prerequisite cone; a ready intermediate cuts only the demand paths that pass through it.
3. Substitution that identifies work keys deduplicates before costs/cache cuts; a stale annotation/certificate is not reused after its premises change.
4. Resource equalities include `(a OR b) AND b = b` and `(a OR b) AND (b OR c) = b OR (a AND c)`, with witnesses/connectors preserved. At positive distinct-atom weights, the latter has cost `min(w[b], w[a]+w[c])` by the displayed equality. Implement that supplied derivation without a general recursive decision procedure.
5. Incompatible composition rejects; omitted connector work or evidence rejects. Formula equality alone does not merge proof witnesses or kernel references.
6. Supplied lower-bound/attainment certificates check. Corrupted cofactors, arithmetic, weights, domain coverage, connectors or boundary evidence reject. Checking an explicit proof never fills missing nodes by search.
7. Mandatory-work and disjoint-support rewrites preserve their resource meaning. Re-establish disjointness after specialization.
8. Suspend and resume each retained bounded-frame operation at internal phases. Its completed result agrees with uninterrupted execution, while budget exhaustion produces no false impossibility or optimality verdict.
9. Every actual helper loop and memory-management operation in the claimed fine ledger is accounted for. Repeated memoized calls include lookup/delivery cost and do not rerun an already completed producer.
10. Execute the accepted associativity transformations in both orientations, with repeated and overlapping demands. Exercise capture/reindexing, extract the actual work record and validate its annotation. An extra typed example should exercise identity-related work expressions and a supplied resource/cost derivation; it must execute its actual transformation through the accepted net/evaluator path.

Deliver the implementation, section-to-function/test mapping, full sanitizer results and commit identifier. Identify this deliverable as **identity-execution accounting and cost refinement**. It closes these retained post-§60 obligations. Acceptance of it does not silently relabel the excluded finite selector as the original invention or certify the full declaration-to-answer construction.

This is an implementation instruction, not a request for another choice between search and a total hold.
