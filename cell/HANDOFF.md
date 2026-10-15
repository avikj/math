# Scoped cubical interaction machine and identity compiler

Implementation handoff — 14 October 2026

Identity-to-agent compiler completion — 14 October 2026

## 1. Scope and central invariant

The machine represents a construction by an immutable origin and a simultaneous substitution into that origin. Substitution changes a reference; it does not evaluate the construction. Evaluation observes that reference under a face assumption and caches its result for that assumption. These operations must remain distinct:

```text
reference = VIEW(origin, substitution)
specialization = reindex(reference, substitution)
observation = whnf(reference, ambient_face)
```

This distinction fixes the concrete Glue failure motivating the implementation change. A composition evaluator must open its family at a fresh symbolic dimension, retain the exposed component references, and specialize those references. Re-evaluating the entire family at an endpoint to rediscover a component can collapse Glue and discard the base family needed by the composition rule.

The evaluation key is

\[
K(t,\chi)=(t,\pi_{S(t)}(\chi)),
\]

where \(S(t)\) is the free dimension support of the **instantiated, typed boundary** of \(t\), and \(\pi\) deletes irrelevant literals from a normalized face DNF. The evaluator executes under the projected face. An immutable reference is never overwritten with a result valid only on one face.

The scope operations, face algorithms, cache contract, and their local correctness arguments are specified below. The cubical clauses are included to make their use by the evaluator explicit. This is a specification and derivation, not a report of a compiled or tested implementation. The face-projection theorem proves the stated cache optimization under the evaluator invariants; it is not, by itself, a proof of every cubical clause or a certification of an existing codebase.

Sections 25–31 extend the construction with an explicit event protocol and derive random descent and geodesic optimality for the combined abstract interaction machine. They specify the counted elementary events, close the cache's overlapping transitions, and state how a demand-driven root observation reaches a complete normal form of its demand network. This establishes interaction-work optimality for a fixed initial configuration and reduction relation; it does not equate that cost with elapsed time, arbitrary C instruction counts, or the cost of arbitrary alternative source programs.

Sections 32–38 settle the runtime implementation scope: checking the annotated core against its declared global signature, a configurable concurrent worker pool, explicit ownership and teardown, and exact comparison modulo generated-name renaming. Structural scope checking alone does not certify a typed occurrence. Partition refinement alone does not certify graph isomorphism.

Sections 39–48 supply the identity-to-agent compiler: checked diagram declarations, generated realization maps, exact application wiring, an internal call instruction, and an end-to-end associativity instance. These sections are additive to the existing runtime.

The most recent assistant reply and the worker's report are reproduced verbatim in the appendices. The preceding assistant reply is available in the current context only as a detailed retained summary. Its technical content is reconstructed explicitly and is not labelled a verbatim transcript. Accordingly, exact textual preservation is claimed only for the two available messages, not for the unavailable original wording.

## 2. Signature and identity

The object language uses universes, dependent functions, dependent pairs, dependent paths, Glue, face systems, and composition. Naturals, booleans, and similar datatypes do not acquire primitive runtime handlers merely because a program uses them. Host-language enum tags used by the evaluator are not object-language types.

Use distinct handle types:

```c
typedef uint64_t TermVarId;
typedef uint64_t DimVarId;
typedef uint64_t ContextId;
typedef uint64_t OriginId;
typedef uint64_t RefId;
typedef uint64_t MapId;
typedef uint64_t IntervalId;
typedef uint64_t FaceId;
typedef uint64_t SymbolId;
typedef uint32_t BinderSlot;
typedef uint32_t FieldIndex;
```

An implementation may use another handle width without changing the mathematics. Equality of interned records is structural equality, with hash collisions resolved by comparing records. Hash equality alone is not equality. Printed names are presentation data, not binding identities.

```text
Context:
    ordered declarations DIM(i) or TERM(x, type_ref)
    assumption: FaceId

Reference:
    VAR(x)
    VIEW(origin, map)

Occurrence:
    reference: RefId
    context: ContextId

Origin:
    tag
    scalar_payload
    fields[]
    binders[]
    free_term_boundary[]
    free_dimension_boundary[]
    required_face
    typing_annotation
```

The occurrence context is not part of `RefId`. A closed reference weakened into another context remains the same reference. An occurrence is valid when its context supplies the declared variables with compatible types and entails the reference's required face.

The boundary includes dependencies appearing in field types, required faces, retained path endpoints, and types of free term variables. Close this dependency set transitively. Remove locally bound variables at the enclosing binder. This is a finite structural dependency calculation, not normalization or an oracle for semantic independence.

Origins, maps, references, and global-definition bodies are immutable. Recursive definitions unfold through `GLOBAL` references; they are not implemented by constructing cyclic substitution records. A live machine uses one immutable definition environment, or separates caches by definition-environment identity when supporting replacement of definitions.

## 3. Canonical interval representation

Intervals form the free De Morgan algebra on dimension identities. Represent an interval as an antichain of finite clauses. A clause is a sorted set of signed dimension atoms; it denotes their meet. The collection of clauses denotes their join.

```text
0       = []
1       = [[]]
i       = [[+i]]
not i   = [[-i]]
```

Normalize a clause by sorting and removing repeated atoms. Normalize a DNF by removing repeated clauses and removing every clause that strictly contains another clause. Use a fixed lexicographic order for the remaining clauses. The antichain is a canonical representation.

**Do not discard a clause containing both `+i` and `-i`.** The interval algebra is not Boolean. In particular, neither \(i\wedge\neg i=0\) nor \(i\vee\neg i=1\) is an interval identity.

```text
join(r, s):
    return normalize_interval(concatenate(r.clauses, s.clauses))

meet(r, s):
    return normalize_interval([union(C,D) for C in r for D in s])

negate(r):
    out = 1
    for C in r:
        one_clause_complement = 0
        for atom in C:
            one_clause_complement = join(one_clause_complement,
                                         singleton(flip_sign(atom)))
        out = meet(out, one_clause_complement)
    return out
```

The empty-loop conventions give \(\neg0=1\) and \(\neg1=0\). Idempotence is structural: normalizing \(i\wedge i\) returns the same `IntervalId` as \(i\).

Interval substitution inserts the image of each original dimension once. A positive atom inserts its interval image; a negative atom inserts the negation of that image. Combine the results by the original meets and joins and normalize. Do not recursively apply the same substitution to dimensions inside an inserted image.

## 4. Canonical faces and endpoint tests

A face literal is `(i=0)` or `(i=1)`. Represent a face as a DNF antichain of finite sets of endpoint literals. Use the same sorting, duplicate elimination, and absorption as for intervals, with one additional rule: discard any clause containing both `(i=0)` and `(i=1)`.

```text
false = []
true  = [[]]
```

The disjunction \((i=0)\vee(i=1)\) does not equal true. A symbolic dimension has an interior; endpoint coverage is not whole-interval coverage.

Face join is concatenation followed by face normalization. Face meet is pairwise clause union followed by face normalization. Contradictory clauses are discarded before any projection of dimensions.

For an interval DNF \(r\), its endpoint faces are

\[
(r=1)=\bigvee_{C\in r}\bigwedge_{a\in C}(a=1),
\qquad
(r=0)=\bigwedge_{C\in r}\bigvee_{a\in C}(a=0).
\]

For a negated atom,

\[
(\neg i=\varepsilon)=(i=1-\varepsilon).
\]

These formulas, including empty joins and meets, give `(0=0)=true`, `(0=1)=false`, `(1=1)=true`, and `(1=0)=false`.

```text
endpoint(r, 1):
    return OR over C in r of (AND over atom a in C of atom_endpoint(a,1))

endpoint(r, 0):
    return AND over C in r of (OR over atom a in C of atom_endpoint(a,0))

substitute_face(phi, sigma):
    replace each original literal (i=epsilon)
        by endpoint(dimension_image(sigma,i), epsilon)
    combine by the original joins and meets
    normalize_face
```

Entailment is decidable by clause containment:

```text
entails(chi, phi):
    return every clause C of chi has some clause D of phi with D subset C
```

This includes false entailing every face, and every face entailing true. All inputs are normalized.

## 5. Quantification and projection are different operations

Cubical universal quantification is

```text
forall_dimension(i, phi):
    retain precisely the clauses of normalized phi containing no literal on i
    normalize and intern
```

It produces the largest face independent of \(i\) that entails \(\phi\). For example,

\[
\forall i((i=0)\vee(j=0))=(j=0).
\]

Cache projection is

```text
project_face(chi, S):
    chi = normalize_face(chi)
    clauses = []
    for C in chi:
        clauses.append({literal in C | dimension(literal) in S})
    return intern_face(normalize_face(clauses))
```

It produces the strongest consequence of \(\chi\) expressible using dimensions in \(S\). It deletes literals inside clauses, whereas universal quantification deletes clauses containing the quantified dimension. For example,

\[
\pi_{\{j\}}((i=0)\wedge(j=0))=(j=0),
\quad
\forall i((i=0)\wedge(j=0))=\bot.
\]

For every \(\phi\) with free dimensions contained in \(S\),

\[
\chi\Rightarrow\phi\quad\Longleftrightarrow\quad
\pi_S(\chi)\Rightarrow\phi.
\]

**Proof.** Entailment holds exactly when every clause \(C\) of \(\chi\) contains a clause \(D\) of \(\phi\). Since \(D\) uses only dimensions in \(S\), \(D\subseteq C\) exactly when \(D\subseteq C|_S\). Absorption of redundant clauses preserves the represented face. Contradictory clauses must already have been removed. This proves both implications.

Consequences:

\[
\chi\Rightarrow\pi_S\chi,\qquad
\pi_S\pi_S\chi=\pi_S\chi.
\]

For consistent \(\chi\), \(\pi_\varnothing\chi=\top\). For false, \(\pi_S\bot=\bot\). If \(T\subseteq S\), then \(\pi_T\pi_S\chi=\pi_T\chi\).

Normalizing after projection alone is insufficient: projecting the unnormalized contradictory clause `(i=0) AND (i=1)` to empty support would incorrectly give true.

## 6. Simultaneous substitutions and interning

```text
RawMap:
    term_images: sorted list of (TermVarId, RefId)
    dimension_images: sorted list of (DimVarId, IntervalId)

TypedMap:
    source_context: Delta
    target_context: Gamma
    raw_map: sigma
```

A map \(\sigma:\Delta\to\Gamma\) supplies values in \(\Delta\) for the variables of \(\Gamma\). Missing entries mean identity. Remove explicit identity entries. The empty map is identity. Typed validity includes the dependent typing of every image and entailment of the substituted target assumption by the source assumption.

```text
term_image(sigma,x):
    return sigma.term_images[x] if present else VAR(x)

dimension_image(sigma,i):
    return sigma.dimension_images[i] if present else interval_variable(i)

make_view(C,sigma):
    sigma = restrict_keys_to_typed_free_boundary(C,sigma)
    sigma = remove_identity_entries(sigma)
    return intern_reference(VIEW(C,intern_map(sigma)))
```

The restriction uses the origin's complete typed boundary, including dependencies through types. It does not drop a variable merely because that variable is absent from the unannotated term body.

Substitution is simultaneous. With `[x -> y, y -> z]`, substituting into `x` returns `y`, not `z`. A second substitution is a separate operation.

```text
reindex(t,sigma):
    if sigma is identity: return t
    if t is VAR(x): return term_image(sigma,x)
    let t = VIEW(C,tau)
    rho = empty map
    for x in C.free_term_boundary:
        rho[x] = reindex(term_image(tau,x),sigma)
    for i in C.free_dimension_boundary:
        rho[i] = substitute_interval(dimension_image(tau,i),sigma)
    return make_view(C,rho)
```

This traverses finite image records, not the body of `C`. It performs no beta reduction, Glue collapse, global unfolding, or face-based evaluation. Memoizing `(RefId, MapId) -> RefId` is sound independently of the evaluation cache.

Write \(\sigma;\tau\) for applying \(\sigma\) and then \(\tau\):

\[
t[\sigma;\tau]=(t[\sigma])[\tau].
\]

```text
compose(sigma,tau):
    out = empty map
    for x in union(term_keys(sigma),term_keys(tau)):
        out[x] = reindex(term_image(sigma,x),tau)
    for i in union(dimension_keys(sigma),dimension_keys(tau)):
        out[i] = substitute_interval(dimension_image(sigma,i),tau)
    return intern_map(remove_identity_entries(out))
```

Keys present only in `tau` must be included because `sigma` acts as identity there. Typed composition has \(\sigma:\Delta\to\Gamma\), \(\tau:\Theta\to\Delta\), and \(\sigma;\tau:\Theta\to\Gamma\).

Weakening changes the occurrence context and retains the same reference. Restricting \(\sigma\) along a face \(\phi\) gives a map from \((\Delta,\phi[\sigma])\) to \((\Gamma,\phi)\) with the same raw substitution. Neither operation copies the represented construction.

## 7. Support after instantiation

The cache support is the dimension support of the reference's full instantiated boundary. It includes dependencies introduced by substitution images, their types, face guards, and endpoint annotations. It must be computed from immutable records, without evaluating the term to discover its support.

Let `FD(C)` and `FT(C)` denote the origin's dependency-closed free dimension and term boundaries. For a view `VIEW(C,sigma)`, a safe structural support is the union of:

```text
dimensions occurring in dimension_image(sigma,i), for every i in FD(C)
support(term_image(sigma,x)), for every x in FT(C)
```

Here `support(VAR(x))` includes the dimension dependencies of its declaration type and its declaration's required face, transitively through the typed declaration context. Explicit typing and guard records must be included in the origin's boundary closure, so their substituted dimensions are accounted for by this union. If the representation keeps additional boundary annotations outside that closure, include their instantiated supports explicitly.

A structural superset of the actual dependencies is sound but may create unnecessary cache entries. An under-approximation is unsound. This distinction is about a structural implementation optimization, not about requiring a semantic minimal-support oracle.

Example: if the origin depends on `x`, and `sigma[x]` depends on `j`, then `j` belongs to the instantiated support even if no dimension called `j` appeared in the origin.

Store or memoize support with each interned immutable reference. Freeze the declaration environment that supplies variable types. Do not let the support of an existing reference change after interning.

## 8. Binders and partial references

Each origin binder declares its sort, formal variable, slot, and, for a term binder, domain type. The instantiated binder identity is interned from `(owner_RefId, binder_slot, sort)`.

The owner and its images exist before this identity is minted; immutable image records cannot contain a future owner-generated identity. Reopening the same owner and slot gives the same binder identity. This provides freshness relative to the owner's free boundary. Binder opening is performed in the owner's dependency context; callers must not interpret the opened variable using an unrelated ambient assumption about an identically reused binder identity. The evaluator's projected context and ordinary binder lifting enforce this discipline.

```text
BinderHandle:
    owner: RefId
    binder_slot: BinderSlot
    body_field: FieldIndex

Partial:
    face: FaceId
    term: RefId

PartialDimBinder:
    binder: BinderHandle
    guard_field
```

Resolving a term binder with formal `x:A` in owner `VIEW(C,sigma)`:

```text
x_new = instantiated_binder(owner,slot,TERM)
A_new = reindex(A,sigma)
lifted = sigma with any entry for x removed, then x -> VAR(x_new)
body = reindex(C.field[body_field],lifted)
return (x_new,A_new,body)
```

Resolving a dimension binder uses the same operation with formal `i` mapped to the fresh interval variable `j`. All fields governed by the same binder slot use the same lift. In particular, a composition's family and tube share the same `j`.

```text
reindex_binder((owner,slot,field),sigma):
    return (reindex(owner,sigma),slot,field)

apply_term_binder(h,a):
    (x,A,body) = resolve_term_binder(h)
    return reindex(body,[x -> a])

apply_dim_binder(h,r):
    (j,body) = resolve_dim_binder(h)
    return reindex(body,[j -> r])

reindex_partial((phi,t),sigma):
    return (substitute_face(phi,sigma),reindex(t,sigma))
```

Applying a partial dimension binder substitutes into both its body and guard. A composition's tube face is independent of its composition dimension, so its guard is unchanged by that dimension application. A partial value may be used as a total value under `chi` only when `entails(chi,phi)` succeeds. A failed coverage test returns control status; it does not fabricate a value or erase the retained partial reference.

## 9. Opening origins

`open` exposes one constructor and its immediate fields. It does not evaluate. Every head recipe retains its owner reference, allowing later reindexing to recover the original construction rather than an already specialized observation.

| Origin tag | Opened fields |
| --- | --- |
| `UNIVERSE` | level |
| `PI`, `SIGMA` | domain reference; term binder for codomain |
| `LAM` | domain reference; term binder for body |
| `APP` | function reference; argument reference |
| `PAIR` | first and second field references |
| `FST`, `SND` | scrutinee reference |
| `PATH` | dimension binder for family; two endpoint references |
| `PLAM` | dimension binder for body |
| `PAPP` | family binder; two endpoints; path reference; interval |
| `GLUE_TYPE` | base reference; face; partial fibre and equivalence references |
| `GLUE_INTRO` | same type data; partial fibre term; base term |
| `UNGLUE` | same type data; value reference |
| `COMP` | family binder; face; partial tube binder; cap reference |
| `SYSTEM` | finite ordered list of face/reference branches |
| `GLOBAL` | symbol; owner with instantiated parameter boundary |

`VAR(x)` opens to `HEAD_VAR(x)`. Ordinary term fields are reindexed by the owner's map. Interval and face fields use their respective substitution operations. Binder fields become handles. Partial fields carry their substituted guards.

There are no additional origin tags solely for neutral applications or neutral compositions. Neutrality is an evaluation result for an existing construction.

```text
reindex_head(head,sigma):
    return open(reindex(head.owner,sigma))

unfold_global(VIEW(global_origin,sigma)):
    return reindex(definition(global_origin.symbol).body,sigma)
```

Global unfolding is an evaluation action, not part of `reindex`. Fixed library definitions retain fixed origins, and their uses are instantiated views. Sharing these definitions does not require copying their syntax at each call.

## 10. Face sensitive evaluation cache

```text
EvalKey:
    reference: RefId
    face: FaceId

EvalEntry:
    state: UNEVALUATED | RUNNING | READY
    result: present exactly when READY
    waiters: suspended evaluation continuations

EvalResult:
    evaluated reference / retained owner
    head description
    classification: INTRODUCTION | NEUTRAL | SYSTEM
```

`READY` means weak-head observation is complete under the entry's face. It does not mean the entire term has a normal form. A neutral result is different from an evaluation still running. A system result retains its covered branches.

```text
whnf_request(t,chi,continuation):
    chi = normalize_face(chi)
    validate_occurrence(t,chi)
    if chi == false:
        continuation(NO_OBSERVATION_ON_EMPTY_FACE)
        return
    eta = project_face(chi,support(t))
    key = (t,eta)
    entry = intern_evaluation_entry(key)
    atomically under entry lock:
        if entry.state == READY:
            result = retain(entry.result)
            deliver_after_unlock(continuation,result)
        else if entry.state == RUNNING:
            entry.waiters.append(continuation)
        else:
            entry.state = RUNNING
            entry.waiters.append(continuation)
            enqueue_after_unlock(EVALUATE(key))

publish(key,result):
    atomically under entry lock:
        require entry.state == RUNNING
        entry.result = retain(result)
        entry.state = READY
        waiters = detach_all(entry.waiters)
    deliver result to each waiter
```

`EVALUATE(key)` evaluates under `key.face`, not under the ambient face of whichever request happened to win the race. Results, entries, and suspended continuations remain rooted until their consumers release them. Publication must make the completed result visible before readers observe `READY`; use locks or corresponding acquire/release atomics. Waiter registration and readiness checks must be in the same synchronization protocol to avoid a lost wakeup.

If evaluation requires another key, suspend a continuation and request that key. Do not block a scheduler worker while waiting for another runnable task. A reentrant request for a running key is not a neutral term and must never be published as one. Recursive demand may represent divergence. An idle queue containing only suspended cyclic demands is not successful normalization. Cancellation or allocation failure is host control state, not a cubical value; never publish an incomplete result as `READY`.

No entry forwards the source `RefId` unconditionally to a face-specific result. No source origin is rewritten to record that result. A forwarding relationship, if stored, belongs to the particular evaluation entry. Reindexing always starts from the immutable reference or retained owner.

### Why the cache key is sufficient

The projection theorem preserves all entailment tests on faces formed from the reference's typed boundary. Free dependencies of fields come from that boundary and its substitution images. Opening binders introduces fresh symbolic dimensions, not additional information from the discarded ambient context. Restriction adds explicit local guards, and recursive evaluation projects again for the child reference.

Thus an evaluator using only these operations cannot distinguish two ambient faces with the same projection onto the reference support. For branching under a guard whose dimensions are retained, forgetting unrelated literals commutes with that restriction. Fresh dimensions contribute no pre-existing ambient constraints. Induction over a finite evaluation derivation then gives the same weak-head observation, modulo the specified nominal binder identities.

This is a sufficiency theorem for an evaluator satisfying the support, freshness, immutability, and face-test contracts. It does not justify an evaluator consulting hidden mutable context data or undeclared dimensions.

### Why an unconditional cache is insufficient

For a neutral path \(p:a_0=a_1\), the same reference \(p@i\) is neutral at true, reduces to \(a_0\) under \(i=0\), and reduces to \(a_1\) under \(i=1\). A single unconditional WHNF attached to `RefId` cannot store these observations correctly.

### Sharing remains structural

If `x` is absent from the complete typed boundary of `R`, then `R[x -> a]` and `R[x -> b]` intern to the same `RefId`. If the dimension support of `R` is empty, every consistent ambient face projects to true. Both requests therefore use one evaluation entry. Copying a descriptor copies a handle, not the represented construction or its evaluation state.

This establishes sharing by identical instantiated boundary and observation face. It does not establish that all definitionally equal references are identical, nor that this cache alone proves every possible notion of optimal reduction cost.

## 11. Substitution must rebuild the observation key

After reindexing, compute support and the cache key again from the new reference and the actual target occurrence context. Do not obtain the new key by substituting into an old projected cache face. Projection can have discarded a dimension that the new substitution makes relevant.

For example, let `t = p@i`, with endpoints independent of `i` and `k`, and let the ambient face be `(k=0)`. The old support is `{i}`, so its projected face is true. Reindex by `[i -> k]`. The new reference `p@k` under `(k=0)` must reduce to the left endpoint. Substituting into the old projected face would leave true and lose the endpoint information.

The correct sequence is:

```text
t_new = reindex(t,sigma)
chi_new = the valid ambient face of the target occurrence
          // often a substituted old face together with target assumptions
whnf_request(t_new,chi_new,continuation)
```

Substitution of a face-specific reduction result can be used only together with its transported validity condition. The baseline evaluator does not need that additional optimization: it reindexes the source reference and requests its new observation.

## 12. Evaluator dispatch and rule precedence

All demands below use the cache protocol. `open` itself remains pure. A retained neutral construction includes every original operand and annotation needed by a later substitution to unblock it.

| Head or operation | Required action |
| --- | --- |
| `VAR` | Return neutral variable. |
| `UNIVERSE`, `PI`, `SIGMA`, `LAM`, `PAIR`, `PATH`, `PLAM` | Return the introduction/type head without evaluating fields unnecessarily. |
| `GLOBAL` | Unfold its fixed body reference under its parameter substitution; demand that reference. |
| `APP(f,a)` | Demand `f`; for a lambda apply its retained term binder to `a`, then demand the result; distribute over a system; otherwise retain a neutral application. |
| `FST(p)`, `SND(p)` | Demand `p`; select an existing pair field; distribute over a system; otherwise retain a neutral projection. |
| `PAPP(B,l,r,p,s)` | Test the faces `(s=0)` and `(s=1)` first and demand the corresponding endpoint if entailed; otherwise demand `p`, apply a path binder when present, distribute over a system, or retain the complete neutral application. |
| `GLUE_TYPE(A,alpha,T,e)` | If the ambient face entails `alpha`, demand `T`; otherwise expose the Glue type head with all component references retained. |
| `GLUE_INTRO(...,t,a)` | If `alpha` is entailed, demand `t`; otherwise retain the Glue introduction. |
| `UNGLUE(...,v)` | On `alpha`, compute `e.map(v)`; otherwise demand `v` and return its base component if it is a Glue introduction; distribute over a system; otherwise retain neutral unglue. |
| `SYSTEM` | Select a branch whose guard is entailed; otherwise retain the covered, compatible branch system. |
| `COMP` | Test tube coverage first; if covered, use the tube at endpoint 1. Otherwise open the family at one fresh symbolic dimension and dispatch on its head using the clauses below. |

The priority of path endpoint tests applies even to neutral paths. The priority of composition tube coverage avoids demanding a family head when the answer is already determined by the tube.

A neutral `COMP` retains its family binder, tube binder, face, and cap. Removing the old implementation's artificial `gen` case does not remove genuine neutral composition on an unknown type family.

### Face systems

A system consists of branches `(phi_k,t_k)` with the appropriate agreement on overlaps. Its occurrence is valid only where the ambient face entails the union of guards. Drop branches inconsistent with the current ambient face. If a single branch covers the ambient face, select it; retain the other immutable source information through the original owner rather than modifying the source system.

If no single branch covers but the union covers, keep a system result. An eliminator acts branchwise under `chi AND phi_k`, keeping the same other argument references and reconstructing the guarded result. Do not choose an arbitrary branch outside its guard. Agreement on overlaps is a typing premise, not something inferred from pointer equality.

For a type-family system exposed at fresh `j`, a composition branch must be available along the whole `j` line. Use `forall_dimension(j,phi_k)` as its outer guard, not `phi_k` with an unbound `j` leaked outside. For a valid covered system under a `j`-independent ambient face these outer guards cover: universal quantification retains the `j`-free DNF clauses and distributes over finite face joins. Under each such guard, retain the corresponding family branch and apply composition to it. Endpoint-only branches do not cover an entire symbolic interval.

The result of evaluation may be a system rather than one globally uniform constructor. A consumer must handle that result explicitly; a system is not an error or a neutral variable.

## 13. Composition and the retained family components

Write

\[
\operatorname{comp}^{i}A_i[\phi\mapsto u_i]a_0:A_1.
\]

The ambient face and tube face \(\phi\) are independent of the bound composition dimension \(i\). The tube has type \(A_i\) on \(\phi\), and \(u_0=a_0\) there.

Opening a composition uses one owner-generated dimension `j` for its family and tube. Evaluate the family reference at this symbolic dimension under the outer ambient face. If its head is Glue, retain the references for its base, fibre, equivalence, and face. If its head is a dependent product, retain its domain and codomain binder; similarly for the other heads.

For any retained component `C` with `j` free,

```text
C_at_r = reindex(C,[j -> r])
```

does not evaluate. A later demand of `C_at_r` may legitimately collapse a Glue at that endpoint. Never rediscover a component using `component(whnf(original_family_at_r))`: the original family's endpoint head may no longer be Glue at all.

The dummy constant `gen`, non-collapsing Glue codes, non-collapsing universe codes, and special neutral cases invented solely around that dummy are unnecessary in this representation. A genuine fresh symbolic dimension, genuine neutral values, and the ordinary universe clause remain necessary.

## 14. Derived filling and transport

The following are library definitions over the core signature, not additional primitive datatype handlers. Their syntax is compiled once into fixed origins; invocation supplies references and substitutions. Distinct occurrences of a shared intermediate in a clause refer to the same reference.

\[
\operatorname{fill}^{i}A_i[\phi\mapsto u_i]a_0(r)
=\operatorname{comp}^{j}A_{r\wedge j}
[\phi\mapsto u_{r\wedge j},(r=0)\mapsto a_0]a_0.
\]

The dimension \(j\) is fresh. Homogeneous composition `hcomp` is composition in a constant family. Transport from 0 to 1 is composition with an empty tube; backward transport uses the reversed family. A line from interval expression \(r\) to \(s\) is

\[
\ell(j)=(r\wedge\neg j)\vee(s\wedge j).
\]

Do not introduce a judgmental rule saying all composition in a constant family is the cap, or all equal-endpoint transport is the identity, unless that additional regularity is explicitly part of the calculus. The definitions above do not silently supply such a rule.

### Dependent function clause

For \(A_i=\Pi(x:D_i).E_i(x)\), cap \(f_0\), and tube \(u_i\), return

\[
\lambda x_1.\operatorname{comp}^{i}E_i(v(i))
[\phi\mapsto u_i(v(i))]\,f_0(v(0)),
\]

where the shared backward filler is

\[
v(r)=\operatorname{fill}^{j}D_{\neg j}[]x_1(\neg r).
\]

Here \(v(1)=x_1\); all occurrences of \(v\) use the same constructed reference and specialize it.

### Dependent pair clause

For \(A_i=\Sigma(x:D_i).E_i(x)\) and cap \(z_0\), let

\[
a(r)=\operatorname{fill}^{i}D_i
[\phi\mapsto\operatorname{fst}u_i](\operatorname{fst}z_0)(r),
\]

\[
b_1=\operatorname{comp}^{i}E_i(a(i))
[\phi\mapsto\operatorname{snd}u_i](\operatorname{snd}z_0).
\]

Return \((a(1),b_1)\). The first-component filler is constructed once and referenced by both output components.

### Dependent path clause

For \(A_i=\operatorname{PathP}^{j}B(i,j)\,l_i\,r_i\), return

\[
\langle j\rangle\operatorname{comp}^{i}B(i,j)
[\phi\mapsto u_i@j,(j=0)\mapsto l_i,(j=1)\mapsto r_i](p_0@j).
\]

The three tube branches agree on overlaps by the path endpoint and original composition boundary conditions.

## 15. Equivalences and contractible extension

Use explicit equivalence data:

\[
\operatorname{Contr}(X)=\Sigma(c:X).\Pi(x:X).\operatorname{Path}_X(c,x),
\]

\[
\operatorname{fib}(f,y)=\Sigma(x:X).\operatorname{Path}_Y(fx,y),
\]

\[
\operatorname{Equiv}(X,Y)=\Sigma(f:X\to Y).\Pi(y:Y).\operatorname{Contr}(\operatorname{fib}(f,y)).
\]

An equivalence supplies the contractibility witnesses used below. No global inverse-search procedure or proof-irrelevance rule is introduced.

For an identity function fibre, use centre `(y,refl)` and, for `(x,p)` with `p:x=y`, the contraction

\[
\langle i\rangle\bigl(p(\neg i),\langle j\rangle p(\neg i\vee j)\bigr).
\]

It starts at `(y,refl)` and ends at `(x,p)`.

For `Contr(X)=(c,k)` and a partial value `v:X` on face \(\theta\), define

\[
\operatorname{ExtendContr}(c,k;\theta,v)
=\operatorname{hcomp}^{j}_{X}[\theta\mapsto k(v)@j]c.
\]

This extends `v` because composition returns its tube endpoint on \(\theta\). Applying this construction to the supplied contraction of an equivalence fibre gives `EquivExtend`.

## 16. Glue computation and composition

For

\[
G=\operatorname{Glue}[\alpha\mapsto(T,e)]A,
\]

on face \(\alpha\): `G` reduces to `T`, `glue t a` reduces to `t`, and `unglue v` reduces to `e.map(v)`. Globally, `unglue(glue t a)` reduces to `a`. Glue eta identifies `glue[alpha -> v](unglue v)` with `v` at the Glue type. These equations have their ordinary typing and face premises.

For a family

\[
G_i=\operatorname{Glue}[\alpha_i\mapsto(T_i,e_i)]A_i,
\]

write the composition face as \(\psi\), tube as \(u_i\), cap as \(u_0\), and \(f_i=e_i.\mathrm{map}\). The references \(A_i,T_i,e_i,\alpha_i\) are those retained from opening the generic family head.

First form the base filler:

\[
a_0=\operatorname{unglue}u_0,\qquad
a(r)=\operatorname{fill}^{i}A_i
[\psi\mapsto\operatorname{unglue}u_i]a_0(r),\qquad a_1=a(1).
\]

Let

\[
\delta=\forall i\,\alpha_i.
\]

On \(\delta\), the fibre family and equivalence are available along the whole line. Form

\[
t(r)=\operatorname{fill}^{i}T_i[\psi\mapsto u_i]u_0(r),
\qquad t'_1=t(1).
\]

Still on \(\delta\), define a path \(\omega:f_1(t'_1)=a_1\) by

\[
\omega(q)=\operatorname{comp}^{i}A_i
[\psi\mapsto a(i),(q=0)\mapsto f_i(t(i)),(q=1)\mapsto a(i)]a_0.
\]

On \(\psi\), this path is constant at \(a_1\). Under \(\alpha_1\), extend the partial fibre element

\[
[\delta\mapsto(t'_1,\omega),\ \psi\mapsto(u_1,\operatorname{refl})]
\]

in \(\operatorname{fib}(f_1,a_1)\), using the fibre contraction supplied by \(e_1\). Call the extension \((t_1,p)\), with \(p:f_1(t_1)=a_1\). Then repair the base endpoint:

\[
a'_1=\operatorname{hcomp}^{q}_{A_1}
[\alpha_1\mapsto p(\neg q),\psi\mapsto a_1]a_1.
\]

Return

\[
\operatorname{glue}[\alpha_1\mapsto t_1]a'_1.
\]

The base family is used generally; `T` and `e` are used only on their guards; \(\delta\) authorizes whole-line fibre use; \(\alpha_1\) authorizes endpoint extension. The evaluator's initial `psi`-coverage test returns `u_1` directly whenever that face covers the ambient context.

The quantifier commutes with reindexing when its bound dimension is fresh and the substitution is lifted correctly:

\[
\delta[\sigma]=\forall j\bigl(\alpha[\sigma^\uparrow]\bigr).
\]

The `j` here is a bound symbolic dimension. It is not the former dummy `gen` value.

## 17. Universe composition and univalence data

For a line of types \(X_j\), define

\[
\operatorname{LineEquiv}(X_j)
=\operatorname{coe}^{0\to1}_{j\mapsto\operatorname{Equiv}(X_0,X_j)}
(\operatorname{IdEquiv}(X_0)).
\]

This uses the existing type formers and their composition; it is not a new primitive handler. Its endpoints have type `Equiv(X0,X1)`. Do not silently identify its first projection judgmentally with every independently written raw transport expression.

The universe clause is

\[
\operatorname{comp}^{i}U_\ell[\phi\mapsto U_i]A_0
\;\longrightarrow\;
\operatorname{Glue}[\phi\mapsto
(U_1,\operatorname{LineEquiv}(j\mapsto U_{\neg j}))]A_0.
\]

On \(\phi\), the starting tube type \(U_0\) agrees with \(A_0\), so the equivalence has the required target. This is the ordinary universe computation; it does not require a special non-collapsing U code.

For \(e:\operatorname{Equiv}(X,Y)\), the Glue path is

\[
\operatorname{ua}(e)=\langle i\rangle
\operatorname{Glue}[(i=0)\mapsto(X,e),(i=1)\mapsto(Y,\operatorname{id})]Y.
\]

The Glue composition of transport along this path supplies paths relating the transported result to `e.map(x)`. If the base filler gives `a:e.map(x)=a1` and the final identity-fibre extension gives `p:t1=a1`, then `a · p^{-1}` witnesses `e.map(x)=t1`. This is explicit path data, not an assertion that all these expressions are syntactically the same.

## 18. Paths and naturality

Reflexivity is the constant path. Reversal is `p(not i)`. Application of a function to a path is `f(p(i))`. One composition definition is

\[
p\cdot q=\langle i\rangle\operatorname{hcomp}^{j}_{A}
[(i=0)\mapsto x,(i=1)\mapsto q(j)](p(i)).
\]

For the singleton \(\Sigma(x:A).(a=x)\), the contraction from `(a,refl)` to `(b,p)` is

\[
i\mapsto\bigl(p(i),\langle j\rangle p(i\wedge j)\bigr).
\]

These constructions supply higher witnesses where necessary; they do not assume all groupoid laws are strict rewrite identities.

Reindex the complete dependent context, all types, values, faces, and witness data together. With a fresh lifted dimension,

\[
(\operatorname{comp}^{i}A[\phi\mapsto u]a_0)[\sigma]
=\operatorname{comp}^{j}A[\sigma^\uparrow]
[\phi[\sigma]\mapsto u[\sigma^\uparrow]]a_0[\sigma].
\]

The structural clauses above are built from substitution-respecting constructors and fixed definitions. Their uses inherit this naturality with the indicated binder lifting. No bespoke reindexing handler is added for a library datatype.

## 19. Scope agent replacements

Scope agents operate on immutable handles. This layer does not require the old lambda net's levelled fans, brackets, or croissants to carry reference sharing. Existing allocation and scheduling code may be reused if it respects the new ownership and cache protocols; the old representation is not the authority for the mathematics.

A data descriptor has a positive principal port and an immutable payload. Descriptor kinds include `REF`, `MAP`, `INTERVAL`, `FACE`, `TERM_BINDER`, `DIM_BINDER`, `PARTIAL`, `PARTIAL_DIM_BINDER`, `CONTEXT`, `HEAD_RECIPE`, `DIMSET`, and `EVAL_RESULT`.

A one-result operation agent has a negative principal port, a positive result auxiliary port, and immutable parameter handles. If `OP.p` meets `DATA.p`, let `r` be the surviving endpoint attached to `OP.result`. For every pure one-result rule below:

```text
compute the indicated finite operation
allocate a result descriptor D
connect D.principal to r
retire OP and its consumed input descriptor
```

This describes the complete boundary wiring of the replacement. The represented immutable values are retained/released according to handle ownership; retiring a descriptor does not delete another descriptor's referenced object.

| Active operation and input | Result descriptor |
| --- | --- |
| `REINDEX_TERM(sigma)` with `REF(t)` | `REF(reindex(t,sigma))` |
| `REINDEX_INTERVAL(sigma)` with `INTERVAL(r)` | `INTERVAL(substitute_interval(r,sigma))` |
| `REINDEX_FACE(sigma)` with `FACE(phi)` | `FACE(substitute_face(phi,sigma))` |
| `COMPOSE_MAP(sigma)` with `MAP(tau)` | `MAP(compose(sigma,tau))` |
| `RESTRICT_MAP(phi)` with typed `MAP(sigma)` | Same raw map with source face strengthened by `phi[sigma]` and target face by `phi` |
| `LIFT_TERM(owner,slot)` with `MAP(sigma)` | Typed lifted map from section 8, using that owner and formal term binder |
| `LIFT_DIMENSION(owner,slot)` with `MAP(sigma)` | Typed lifted dimension map from section 8 |
| `OPEN` with `REF(t)` | `HEAD_RECIPE(open(t))` |
| `UNFOLD_GLOBAL` with a global `REF(t)` | `REF(unfold_global(t))` |
| `REINDEX_TERM_BINDER(sigma)` with `TERM_BINDER(h)` | `TERM_BINDER(reindex_binder(h,sigma))` |
| `REINDEX_DIM_BINDER(sigma)` with `DIM_BINDER(h)` | `DIM_BINDER(reindex_binder(h,sigma))` |
| `REINDEX_PARTIAL_DIM_BINDER(sigma)` with `PARTIAL_DIM_BINDER(h)` | Reindexed owner and unchanged field/slot identities, preserving guard data |
| `REINDEX_PARTIAL(sigma)` with `PARTIAL(phi,t)` | `PARTIAL(phi[sigma],t[sigma])` |
| `APPLY_TERM_BINDER(a)` with `TERM_BINDER(h)` | `REF(apply_term_binder(h,a))` |
| `APPLY_DIM_BINDER(r)` with `DIM_BINDER(h)` | `REF(apply_dim_binder(h,r))` |
| `APPLY_PARTIAL_DIM_BINDER(r)` with a partial binder | `PARTIAL` with body and guard both specialized at `r` |
| `FORALL_DIMENSION(i)` with `FACE(phi)` | `FACE(forall_dimension(i,phi))` |
| `PROJECT_FACE(S)` with `FACE(chi)` | `FACE(project_face(chi,S))` |
| `FACE_COVERAGE(chi)` with `FACE(phi)` | Host status `COVERED` or `NOT_COVERED` |
| `USE_PARTIAL(chi)` with `PARTIAL(phi,t)` | `REF(t)` when covered; otherwise a tagged `NOT_COVERED` result retaining the partial payload |
| `GET_SUPPORT` with `REF(t)` | `DIMSET(support(t))` |
| `REINDEX_HEAD(sigma)` with `HEAD_RECIPE(h)` | `HEAD_RECIPE(open(reindex(h.owner,sigma)))` |

Sort mismatches and invalid typed maps are validation errors. They are not neutral object-language values. A typed lift must use the map belonging to the given owner, or a separately verified matching instance; an arbitrary unrelated owner/map pairing is not a valid lift.

The descriptor encoding may call these algorithms directly in C. It need not expand DNF normalization into object-language agents. Those host operations have real finite costs; they are not claimed to be zero-cost interactions.

### Materializing a head

For an `n`-field recipe of tag `K`, allocate a positive-principal `HEAD_K` with `n` negative auxiliary ports. Attach each auxiliary to the positive principal of that field's descriptor. Attach `HEAD_K.principal` to the result endpoint. Retain the owner in the head record.

A system's variable-length branch sequence can be represented by `BRANCH_NIL` and `BRANCH_CONS`, where a cons has negative branch and tail auxiliaries, and a `BRANCH` has negative face and term auxiliaries attached to `FACE` and `REF` descriptors. All principal ports are positive. This fixes the variable-length wiring without inventing a source-language list primitive.

### Duplication and erasure

When a negative-principal duplicator meets any immutable data descriptor `D(v)`, replace it with two descriptors `D(v)` attached to the duplicator's two result endpoints. Both retain the same payload handle. Do not allocate copies of the origin, body, substitution images, or evaluation entries.

When an eraser meets a data descriptor, retire the descriptor and release its payload ownership. Reclaim the payload only when no live root, descriptor, cache entry, map, origin, or continuation retains it. A materialized constructor shell may be copied fieldwise using local duplicators, or represented by one duplicable immutable recipe handle; both preserve the same owner and shared references.

No scope rule compares fan labels or reconstructs lambda reduction families. This does not assert that routing labels in an existing unrelated net automatically become cubical dimensions.

### Evaluation agents

`EVAL(chi)` meeting `REF(t)` registers its result endpoint as a continuation of the key `(t,project_face(chi,support(t)))`. A ready entry immediately emits an `EVAL_RESULT` descriptor. A running entry retains that continuation as a waiter. An unevaluated entry creates exactly one evaluation task.

The request descriptors may retire after their payloads and continuation endpoint have transferred into the task/cache ownership. Publication emits one result descriptor for each live waiter, with all of them retaining the same immutable result payload. On the false face, emit an explicit host control result for no observation; do not fabricate a term of an arbitrary type.

Continuation kinds correspond to the finite dispatch cases in section 12: application-function, projection-scrutinee, path-scrutinee, unglue-scrutinee, composition-family, global-unfolding, and branchwise-system evaluation. Each stores the already retained arguments, its ambient face, and the destination entry. Resuming a continuation invokes the indicated rule and either requests the next reference or publishes the destination result. This is the asynchronous transcription of the dispatch table, not a new reduction calculus.

## 20. Graph replacement and memory discipline

A local rule must list every surviving boundary connection and every fresh port exactly once. Connect only opposite polarities. Removed principal ports are internal to the redex and are not surviving boundary ports.

For general multi-node replacements, compose the old boundary matching with the replacement matching. A saved old auxiliary's neighbour might itself be another removed auxiliary; blindly reconnecting all saved neighbours is unsafe. Use temporary connectors for removed auxiliary ports, combine the old and replacement matchings, and join the two surviving endpoints of each resulting path. Track connector-only cycles according to the representation's closed-wire-component convention.

A sequential evaluator may perform these operations without locks. A concurrent implementation must also protect the surviving endpoints it changes. Locking only the two redex owners is insufficient when neighbouring redexes share boundary edges. Pin memory before dereferencing, acquire affected owner locks in a consistent total order, revalidate the redex and boundary, install the replacement, publish and retire nodes, then enqueue new active pairs. Generational handles detect stale identity but do not by themselves prevent dereferencing freed memory.

Keep reference interning and cache-entry interning atomic with respect to concurrent creation. Otherwise two threads can create distinct records for the same structural reference or run the same key twice. Host failure and cancellation must release owned continuations and handles without corrupting a ready entry.

The graph scheduler's observation contract is explicit: a requested root may be ready while unrelated suspended or residual work remains. Conversely, an empty runnable queue does not prove the requested root has a normal form.

## 21. Why shared boundaries carry the mathematics

For a construction diagram `P` with boundary `beta`, write

\[
\operatorname{Real}(P,\beta)
=\Sigma_{\text{internal witnesses }w}\operatorname{Constraints}_P(\beta,w).
\]

The telescope includes dependent and higher-cell data. A local mathematical replacement has explicit evidence

\[
e_\beta:\operatorname{Real}(P,\beta)\simeq\operatorname{Real}(Q,\beta).
\]

In an external context, it acts as

\[
(\beta,p,c)\longmapsto(\beta,e_\beta(p),c).
\]

The same boundary and external context remain shared. The reference representation implements this by preserving boundary handles and changing the instantiated construction through the supplied map. It does not require reconstructing a second sharing graph to discover which retained boundary was common.

For a function `f:A -> B`, the fibre-augmented representation is

\[
A\simeq\Sigma(b:B).\Sigma(a:A).(f(a)=b).
\]

The forward map is `a -> (f(a),a,refl)`; the reverse forgets `b` and its witness and returns `a`. For `(b,a,p)`, the path

\[
i\mapsto(p(i),a,\langle j\rangle p(i\wedge j))
\]

supplies the appropriate homotopy from the round-trip result to the original point. If a reversible representation has shape `A ≃ Σ(b:B).T(b)`, its residual `T(b)` describes the fibre of the observed computation, with the equivalence required to respect the specified observation into `B`.

Erasing the residual by projecting `Σ(b:B).R(b) -> B` is an equivalence precisely when every `R(b)` is contractible. Physical garbage collection of an unreferenced handle is not permission to erase an arbitrary noncontractible mathematical residual.

### Identities induce the replacement map

For a function graph use `N_f(a,b) = (f(a)=b)`. For a binary operation use `N_m(a,b,c) = (m(a,b)=c)`. Wire composition has the equivalence

\[
\Sigma b.\,(f(a)=b)\times(g(b)=c)\simeq(g(f(a))=c),
\]

with forward `(b,s,t) -> ap_g(s) · t` and inverse `w -> (f(a),refl,w)`.

For a finite well-founded expression or acyclic circuit `C`, these contractions give

\[
c_C:\operatorname{Real}(C,\gamma,y)\simeq(C(\gamma)=y).
\]

For unary composition the path is `ap_f(c_A(r)) · s`; for binary composition it is `ap2_m(c_A(r_A),c_B(r_B)) · s`. A shared intermediate occurs once in the dependent telescope. This contraction is not asserted for an arbitrary cyclic diagram with additional higher constraints.

Given an identity `p:C_L(gamma)=C_R(gamma)`, its transport action is determined:

\[
F_p=c_R^{-1}\circ(q\mapsto p^{-1}\cdot q)\circ c_L,
\]

with inverse `c_L^{-1} ∘ (q -> p · q) ∘ c_R`. No unspecified extra handler is needed to choose the action of this given identity.

For associativity `alpha:(a*b)*c=a*(b*c)`, this specializes to

```text
left realization:  (u, s:a*b=u, t:u*c=y)
right realization: (v, s:b*c=v, t:a*v=y)

forward(u,s,t) = (b*c, refl, alpha^-1 · ap_(z -> z*c)(s) · t)
reverse(v,s,t) = (a*b, refl, alpha · ap_(z -> a*z)(s) · t)
```

Likewise,

\[
\Sigma z.\,(C=z)\times(D=z)\simeq(C=D)
\]

maps `(z,u,v)` to `u · v^{-1}`, with inverse `h -> (D,h,refl)`. Replacing the left side by `p:C=C'` sends `h` to `p^{-1}·h`; replacing the right by `r:D=D'` sends it to `h·r`.

A fixed path `p:x=y` identifies `Path(x,y)` with the loop space at `y` by `h -> p^{-1}·h`, with inverse `ell -> p·ell`. This does not make arbitrary loops trivial. A binary construction acting on independent paths produces the square `m(p(i),q(j))`; its diagonal is only one path through that square. Dependent inputs require the corresponding whole dependent-context cube.

## 22. What is necessary and what the construction establishes

For the cache optimization, the necessary semantic condition is that equality of cache keys imply interchangeable observations in every permitted use of the cached result. The projected-face key is a concrete sufficient construction under the stated dependency and evaluator invariants. It need not be the coarsest imaginable key: different faces can accidentally yield equal results without the machine needing to decide that equality.

For this implementation contract the following are required together:

1. Intern immutable origins, maps, references, intervals, and faces by structural equality.
2. Restrict maps to the complete typed free boundary, using simultaneous single-lookup substitution.
3. Include substitution images, declaration types and their required faces, endpoint data, and guard data in dimension support.
4. Keep occurrence contexts separate from reference identity; validate their typing and face entailments.
5. Open binders by retained owner/slot identity, lift correctly, and use one dimension for a composition's family and tube.
6. Keep interval DNF separate from face DNF; use the specified endpoint formulas, entailment, quantifier, and projection.
7. Evaluate under the projected cache face, with one owner of each running key and synchronized waiter publication.
8. Retain immutable source provenance; never globally replace a reference with a face-specific answer.
9. Rebuild observation keys after reindexing from the actual target ambient face.
10. Implement the dispatch priorities and all structural composition clauses, retaining genuine neutrals and covered systems.
11. Preserve shared handles in descriptor duplication and preserve surviving boundary wiring in replacements.
12. Preserve the typing premises, overlap compatibility, and supplied equivalence witnesses of the cubical rules.

Items 1–9 make the scope and face-sensitive memoization layer executable. Items 10–12 connect it to the stated cubical calculus and local realization replacements. These are implementable invariants, not an invitation to replace the construction with a new encoding or to add another theory of sharing.

The local arguments establish simultaneous substitution, capture-avoiding lifting relative to the recorded boundaries, face entailment and projection, and sharing of identical interned references at identical observation keys. Supplied realization equivalences establish the indicated local semantic replacements. They do not prove arbitrary equations by pointer identity, erase arbitrary path information, make all source programs terminate, or turn a specification into evidence that unreviewed C code implements it.

## 23. Concrete verification cases

These cases are useful acceptance checks for the transcription; passing them is not substituted for the proofs or the typing premises.

For this handoff, the DNF projection and universal-quantification entailment laws were also exhaustively checked over all 48 canonical faces on two dimensions, with 3,360 comparisons passing. Document section continuity, code-fence balance, and display-math delimiter balance were checked. These checks concern the written algorithms and document structure; no claim about execution of the worker's C implementation follows from them.

| Case | Required result |
| --- | --- |
| Interval `i AND i` | Same canonical interval as `i` |
| Interval `i AND NOT i` | Retained as an interval clause |
| Face `(i=0) AND (i=1)` | False |
| Face `(i=0) OR (i=1)` | Not true |
| Endpoint `(NOT i = epsilon)` | `(i = 1-epsilon)` |
| `x[x->y,y->z]` | `y` |
| `(x[x->y])[y->z]` | `z` |
| `R[x->a]`, `R[x->b]`, with `x` absent from typed boundary | Same `RefId` |
| Image of `x` introduces dimension `j` | Instantiated support includes `j` |
| Project `(i=0) AND (j=0)` onto `{j}` | `(j=0)` |
| Quantify `i` in the same face | False |
| Project false onto empty support | False |
| Closed reference under two consistent faces | Same projected-face cache entry |
| Neutral `p@i` under true / `i=0` / `i=1` | Neutral / left endpoint / right endpoint |
| Specialize retained Glue base at endpoint | Base reference survives even if the whole Glue type would collapse |
| Covered composition tube | Return tube at 1 before demanding family head |
| Two concurrent requests for one key | One evaluation task, both waiters receive its result |
| Running self-demand | No fabricated neutral or ready result |
| Reindex `p@i` to `p@k` under `k=0` | New key observes endpoint despite old projected face being true |

## 24. Reconstruction of the preceding assistant message

This section preserves the technical content retained for the assistant message immediately before the latest quoted reply. It is a reconstruction, not a claim to possess that message's original wording.

The worker's direction was accepted: replace the lambda-net representation with scoped references and an evaluator on those references. The specific correction was that weak-head results cannot be stored unconditionally by `RefId`; the ambient face can change the result, so the cache key must include the ambient face projected to the reference's full dimension support.

The proposed key was a record containing `reference: RefId` and `face: FaceId = project_face(ambient_face,support(reference))`. The entry states were `UNEVALUATED`, `RUNNING`, and `READY`, with a result exactly in the ready state and waiters while work is in progress. Running means pending computation, not a neutral value. Under false, no observation is required.

Projection starts with normalized face DNF, deletes literals outside support in each clause, and normalizes again. Its justification was the equivalence `chi entails phi` iff `project_face(chi,S) entails phi` for every face `phi` using only dimensions in `S`. The proof used DNF clause containment. A closed reference has empty support, so every consistent ambient face projects to true. False remains false because contradictions are eliminated before projection.

An evaluated result must not overwrite an origin or install an unconditional forwarding pointer on a reference. Reindexing must act on the original immutable reference rather than a head collapsed under an earlier face. Otherwise the original loss of the Glue base can reappear through caching. The example was a neutral path application `p@i`, neutral at true and equal to its respective endpoints under `i=0` and `i=1`.

The evaluator actions were: demand a function and apply its retained term binder; demand a pair and select its field; test path endpoints before demanding a path; collapse Glue type and introduction only when their face is entailed; apply the equivalence map on that face for unglue, otherwise perform introduction/elimination or preserve neutrality; select or distribute covered systems; test composition tube coverage first and then inspect the family at a fresh symbolic dimension; and unfold globals as views of fixed body origins.

For composition, extract component references once at the symbolic family head and specialize those references. Do not re-evaluate the whole family at points to recover components. In Glue composition, the base family is generally available; the fibre and equivalence are partial under their Glue face; universal quantification of that face authorizes whole-line use; and its endpoint instance authorizes endpoint fibre extension.

The artificial `gen` sentinel disappears, but a genuinely fresh symbolic dimension remains. Sentinel-specific neutral cases disappear, but genuine neutral terms and neutral composition retain all their family, tube, face, and cap data. Levelled fans, brackets, and croissants no longer carry sharing for this reference representation; this does not prevent reusing sound allocator and scheduler infrastructure.

The retained concluding sentence was: “With that cache rule, the worker’s proposed implementation follows the scope representation without losing the point-dependent cubical reductions that motivated it.” Its scope was this representation and cache correction, not a certification of every clause or of an implementation.

## 25. The interaction optimality theorem being inherited

An interaction net has one principal port per agent and at most one applicable deterministic rule for an active pair, including its immutable payload. Two distinct active pairs therefore have disjoint agent sets. Replacing one preserves the other's principal connection, and the two replacements commute after composing their boundary matchings. Allocation identities are compared up to renaming; immutable interned records are compared structurally.

The relevant property is the **exact residual diamond**:

\[
N\xrightarrow{a}N_a,\quad N\xrightarrow{b}N_b,\quad a\ne b
\quad\Longrightarrow\quad
N_a\xrightarrow{b/a}P,\quad N_b\xrightarrow{a/b}P.
\]

Each side takes exactly one residual step. The property is stronger than merely being able to join the two results after an arbitrary number of steps, and stronger than a diamond allowing a competing step to disappear. That distinction is what permits a cost theorem, rather than only uniqueness of answers.

The scope agents have deterministic rules on immutable payloads, and their distinct ordinary active pairs satisfy this property. Reindexing, binder resolution, DNF operations, and component retention do not introduce competing rewrite choices for one active pair. A chosen identity and its orientation are explicit construction data: distinct supplied identities do not become nondeterministic alternative rules for the same undecorated active pair.

The host cache is shared state, so ordinary disjoint-agent reasoning alone does not cover it. Its transitions must be made explicit and their overlaps checked. Sections 26–27 do precisely that, extending the same theorem to the combined machine.

## 26. Exact cache and delivery event protocol

For a key `K = (t,project_face(chi,support(t)))`, the evaluation input is determined by `K`. It must not also depend on the identity, original ambient face, or timing of the first requester.

Represent the operational state by the active graph, a map of cache entries, and a multiset of ready jobs. A request continuation has a unique identity and is consumed exactly once. The cache states are

```text
U          = UNEVALUATED
R(W)       = RUNNING with finite multiset W of waiting continuations
D(v)       = READY with immutable result v
```

Jobs include `REQ(K,c)`, an evaluator task `EVAL(K,frame)`, `PUB(K,v)`, and `DELIVER(c,v)`. Evaluation frames are linear: only one job owns a given frame at a time. A pending call owns its continuation until the result arrives. Independently evaluated children return to distinct single-consumer boxes; an explicit join becomes enabled only after its required boxes are full.

The exhaustive cache transitions are:

```text
REQ(K,c) + E[K]=U
    -> E[K]=R({c}) + EVAL(K,initial_frame)

REQ(K,c) + E[K]=R(W)
    -> E[K]=R(W multiset_union {c})

REQ(K,c) + E[K]=D(v)
    -> E[K]=D(v) + DELIVER(c,v)

PUB(K,v) + E[K]=R(W)
    -> E[K]=D(v) + { DELIVER(c,v) : c in W }

DELIVER(c,v)
    -> the uniquely specified resumed frame or root-result sink for c
```

Unmentioned graph and store components are unchanged. A missing entry is `U`. Only the unique evaluator task for `K` may eventually issue its publication job. Reentrant requests append waiters; they neither launch another evaluator nor synthesize a neutral value.

Each of these is an explicit elementary event. In particular, delivery is represented in both the already-ready and initially-waiting cases. Do not count an immediate cached return as one event while silently charging an additional event only to the waiting case. The uniform protocol is the operational refinement of section 10's `deliver_after_unlock` and `publish` descriptions.

The evaluator performs a deterministic elementary step on its owned frame and immutable inputs. When it needs another result, it emits a request with a retained continuation rather than inspecting a shared entry through an unaccounted shortcut. It evaluates using the projected face in `K`. The cubical dispatch and composition definitions determine these frame transitions.

Interning is structural canonicalization in this abstract machine. Two concurrent attempts to intern the same record denote the same mathematical record. Allocator identities, lock retries, hash bucket layouts, and queue ordering are implementation details, not alternative mathematical rule choices.

## 27. Exhaustive overlap analysis

Distinct ordinary active pairs commute by section 25. Operations on distinct cache keys commute because they update disjoint entries. Immutable arena extensions commute by union and canonical interning. Evaluator frames and continuation boxes have unique owners. The remaining shared-state overlaps are exactly the cases below.

### Two requests to the same unevaluated key

Starting with `REQ(K,a)`, `REQ(K,b)`, and `U`:

```text
a first: U -> R({a}) + EVAL(K) -> R({a,b}) + EVAL(K)
b first: U -> R({b}) + EVAL(K) -> R({a,b}) + EVAL(K)
```

Each side takes two request events, creates one evaluator task, and reaches the same state. No caller-dependent evaluator owner is recorded.

### Two requests to the same running key

Both orders produce `R(W multiset_union {a,b})`. Each side takes two request events.

### Two requests to the same ready key

Both orders retain `D(v)` and produce `DELIVER(a,v)` and `DELIVER(b,v)`. Each side takes two request events.

### Request and publication for the same key

Starting with `REQ(K,a)`, `PUB(K,v)`, and `R(W)`:

```text
request first:
    R(W) -> R(W union {a})
         -> D(v) + deliveries for W union {a}

publication first:
    R(W) -> D(v) + deliveries for W
         -> D(v) + deliveries for W + DELIVER(a,v)
```

Each side takes one request event and one publication event and reaches the same job multiset. Delivery order does not choose a result or alter a continuation's meaning.

### Request and an evaluator step for the same running key

The request changes only the waiter multiset. The evaluator step changes only its owned frame and emits its deterministic next jobs. It does not inspect waiter order or count to choose the term result. The two steps commute. The final publication step is already covered above.

There cannot be two competing publications for one key: the protocol creates exactly one evaluator task. There cannot be two valid deliveries consuming one continuation: continuation identities are linear. A join waiting for a missing child is not enabled before that child's delivery; delivery and that newly enabled join therefore form a causal sequence, not an unresolved overlap.

These cases exhaust the mutable resources of the specified abstract machine. Consequently, the combined scope, evaluation, memoization, and delivery relation has exact residual diamonds, modulo graph isomorphism and the canonical representation of immutable data.

The face-sensitive key is essential to this argument. If two requests sharing a key could produce different heads because their original faces differed, the unique evaluator task would not be determined by the key and the request/request diagram would fail. Projection and the support theorem remove that hidden caller dependence.

## 28. Random descent and fixed interaction work

Let `N ->* Z` be a finite reduction to a normal form, of length `n`. Exact residual diamonds imply:

\[
\forall(N\to M),\qquad M\to^{n-1}Z.
\]

Proof is by induction on `n`. Compare the chosen first step of the displayed reduction with `N -> M`. If they are the same event, the remaining path has length `n-1`. Otherwise the exact diamond supplies a common state after one residual step from each successor. Apply the induction hypothesis to the chosen successor, whose remaining path has length `n-1`; the common state then has a path of length `n-2` to `Z`. Prepending the residual step from `M` gives length `n-1`. When `n=1`, a distinct competing event would have to survive in the claimed normal form, which is impossible.

Therefore the number

\[
d(N)=\text{length of a complete reduction from }N\text{ to its normal form}
\]

is well defined whenever such a normal form exists, and

\[
N\to M\quad\Longrightarrow\quad d(N)=1+d(M).
\]

Every complete reduction has exactly `d(N)` elementary events. Every reduction sequence from a normalizing state is finite. A scheduler may delay work in wall-clock time, but it cannot create a longer sequence of valid mathematical reductions by choosing a bad redex order.

In particular,

\[
\min_{\rho:N\to^*Z}|\rho|
=\max_{\rho:N\to^*Z}|\rho|
=d(N).
\]

This is the interaction-net optimality inherited by the combined machine: the counted work for the fixed represented computation is independent of reduction order. It is stronger than merely saying repeated requests share a result.

## 29. Geodesic optimality in the reversible interaction graph

Consider the undirected graph obtained by also allowing each elementary reduction edge to be traversed backward. Keep the same states and elementary edges; do not add arbitrary semantic equivalences as new unit-cost shortcuts.

Every state in the connected component of a normalizing state has the same normal form and a well-defined rank `d`. A forward edge decreases `d` by one; a backward edge increases it by one.

For any zigzag from `N` to its normal form `Z`, let `f` and `b` be its numbers of forward and backward traversals. Then

\[
f-b=d(N),\qquad |\gamma|=f+b=d(N)+2b\ge d(N).
\]

A forward reduction reaches `Z` in exactly `d(N)` events and therefore attains the lower bound. Hence

\[
\boxed{d(N)=\operatorname{dist}(N,Z)}
\]

in this reversible interaction graph. Every complete forward computation is a geodesic. Reversibility of an elementary graph edge here means retaining enough state to traverse that edge backward; it is not a claim that a destructive C implementation automatically records all inverse information.

For weighted costs, require each residual diamond to preserve the sum of its edge weights. The cache diamonds preserve the event multiset: two requests on both sides, or one request and one publication on both sides. The ordinary local diamonds preserve the contracted local rule instances. Thus fixed nonnegative costs for these event classes give a well-defined weighted potential `D`:

\[
N\xrightarrow{e}M\quad\Longrightarrow\quad D(N)=w(e)+D(M).
\]

Every zigzag to the normal form has total weight

\[
W(\gamma)=D(N)+2\sum_{\text{backward edges }e}w(e)\ge D(N).
\]

Event-count vectors are also preserved when each diamond preserves their componentwise sum. One can therefore report semantic rule work separately from request, publication, delivery, and scope-operation work without conflating them. A chosen micro-operation expansion must satisfy the same local-rule conditions before its individual steps are included in this theorem.

In this vector, `REQUEST` is one event class regardless of whether the entry is unevaluated, running, or ready. Separate running-hit and ready-hit counters need not be schedule invariant: a request can cross a publication in the diamond above. They are diagnostic counters, not independent cost components unless their assigned weights satisfy the diamond balance equation.

## 30. Applying the theorem to a requested observation

A weak-head result can be obtained before unrelated computations finish in a general multi-root machine. The theorem concerns a complete normal form of the counted network, so the observation boundary must be explicit.

For a single requested observation, use its demand network:

1. The initial active work is the root request, against fixed quiescent initial cache contents and immutable definitions. Initial entries are unevaluated or ready; a pre-existing running producer would also have to be included in the workload.
2. Origin bodies and fields are inert references. Merely storing a reference does not launch evaluation.
3. Every spawned child demand is a required dependency of a retained parent continuation. No speculative demand is started and then discarded to obtain the parent result.
4. A parent publishes only after all child demands it actually launched for that result have delivered. Parallel children return to explicit join boxes.
5. Root completion is the delivery of its result together with completion of the corresponding mandatory delivery bookkeeping. No semantic job is canceled by opportunistic garbage collection.

Under these rules, an unfinished evaluator task cannot remain in the completed root's demand network: following its registered parent dependencies leads to a parent that could not have published, and ultimately to the root that could not have completed. Undemanded lambda bodies and system branches can remain as inert references; they are not unfinished evaluation tasks.

Thus a completed root observation is a normal form of its active demand computation. The random-descent and geodesic results apply to this weak-head demand, not only to recursively normalizing every stored term. Genuine neutral and system results are legitimate terminal observations. A suspended demand cycle without a root result is not a successful observation.

For multiple independent roots, apply the theorem to completion of the whole initial workload. For a separate root comparison, begin with the same quiescent cache snapshot and form that root's isolated demand network. Earlier computations may warm a cache, so cold and warm starting states are different initial configurations, not counterexamples to schedule independence. A concurrent workload's shared work must not be attributed to whichever caller happened to arrive first and then mistaken for an invariant per-caller cost.

## 31. Exact implementation consequence

The scope construction does not need a separate search for an optimal reduction order. Implement the deterministic local rules and the explicit cache protocol, preserve their residual diamonds, and interaction-work optimality follows by sections 28–29.

For the C transcription:

- Keep evaluator input determined by the canonical key, including its projected face.
- Use exactly one evaluator task and publication per key.
- Treat waiters as an unordered mathematical collection of unique continuations; never let arrival order choose a result.
- Represent delivery uniformly in ready-hit and waiting cases. An optimized inline path must correspond to the same formal events if those events are the reported cost.
- Keep continuations single-consumer and joins explicit.
- Use the graph boundary-splicing and atomicity discipline already specified. Do not expose partial replacements as additional semantic states.
- Keep allocation, reference counting, locking, and garbage collection semantically transparent. They may reclaim unreachable storage but may not introduce an unmodelled cancellation rule for live semantic work.
- Fix the compared initial configuration, terminal observation, and elementary cost model.

The resulting theorem is: **for every normalizing initial configuration of this abstract machine, every complete reduction has the same interaction-work vector, and every forward reduction to its normal form is a minimum-cost path in the reversible graph of the same elementary interactions, for every nonnegative diamond-balanced weighting.**

This states the inherited optimality positively and precisely. It neither needs nor asserts a separate theorem choosing the fastest arbitrary algorithm from all source programs. Elapsed time, memory peaks, processor scheduling, and raw C instruction counts are different observables. The interaction theorem does not identify them with the defined event cost.

## 32. Completion scope for the four reported gaps

Contexts and typing require checking the annotated core, including its declared definitional equality. This is not implicit type inference for a new surface language, unification, proof search, or conversion by arbitrary proved identities. The existing origin signature and typing annotations supply the checking boundary. Sections 33–34 specify the operations and constructor cases.

Concurrency is in scope. Implement a configurable worker pool, retaining one worker as the deterministic debugging mode. Its implementation can occupy a separate commit, but it is not an unanswered scope question or a reason to call a sequential-only build the completed concurrent machine. The exact quiescence protocol is in section 35.

Reclamation and the exact comparison harness are also in scope. Use the ownership rules in section 36 and the exact matching procedure in section 37. Complete these changes, run their relevant checks, and deliver the resulting code and current handoff together. No further permission checkpoint is introduced by this section.

## 33. Checking contexts and the annotated core

The kernel judgments are

\[
\Gamma;\chi\vdash A:U_\ell,\qquad
\Gamma;\chi\vdash t:A,\qquad
\Gamma;\chi\vdash t\equiv u:A,
\]

and validity of a typed substitution from a source occurrence context to a target context. Checking is relative to the declared, immutable global signature. Imported constant declarations are explicit assumptions; checking against that signature does not prove those assumptions or prove termination of recursive programs.

Expose the following operations:

```text
check_context(Gamma)
check_map(Delta,psi,sigma,Gamma,chi)
check_origin(C)
infer(Gamma,chi,t) -> checked type reference, or failure/unresolved
check(Gamma,chi,t,A)
convert_type(Gamma,chi,A,B)
convert_term(Gamma,chi,t,u,A)
```

Host outcomes distinguish `VALID`, `INVALID(reason)`, and `UNRESOLVED(reason)`. For conversion, use `EQUAL`, `UNEQUAL`, and `UNRESOLVED`. An interrupted or cyclic normalization does not establish inequality and is never accepted as a successful typing judgment.

### Context and map validation

1. Variable identities in a context are unique. Its assumption uses only declared dimension identities.
2. Process declarations in order. Each term declaration's type and required face use only its available prefix. Check that type is a type. When the context's final assumption mentions later dimensions, project that assumption to dimensions in the prefix for this check; do not make later declarations available to an earlier type.
3. A reference occurrence must find every dependency of its complete typed boundary in the occurrence context, with the recorded declaration identities and compatible types. Its required face must be entailed.
4. For a map `sigma : Delta -> Gamma`, each dimension image is an interval over dimensions of `Delta`. For each target term declaration `x:A`, check `term_image(sigma,x)` against `A[sigma]` under the source face. Since `A` uses only earlier target declarations, this is a dependent, ordered check even though the substitution itself is simultaneous.
5. Require `psi entails chi[sigma]`, including the target's required face obligations. Missing map entries mean identity and still require the corresponding source declarations to be available.

Never regard a reference's type annotation as a proof merely because it is present. Validate an origin against its annotation in its own declared parameter context and required face. After that validation, a checked typed map gives

\[
\Gamma_C\vdash C:A_C,\quad\sigma:\Delta\to\Gamma_C
\quad\Longrightarrow\quad
\Delta\vdash\operatorname{VIEW}(C,\sigma):A_C[\sigma].
\]

This is the substitution lemma applied to the representation. It avoids rechecking a copied body at every occurrence. Validation results can be memoized; a pending validation is not already a proof. Runtime origins generated by the fixed, validated clauses use the same typed constructors and maps.

### Universe and formation rules

Use the explicit predicative levels of the core: `U_l : U_(l+1)`. If `A:U_i` and `B:U_j` under `x:A`, then `Pi(x:A).B` and `Sigma(x:A).B` have type `U_max(i,j)`. A path family in `U_l` forms a path type in `U_l`. Glue has base and partial fibre in the same `U_l`, with the indicated equivalence between them.

Compare declared universe levels exactly. This specification does not introduce cumulativity, universe resizing, or conversion of equivalent types into definitionally identical types. In particular, univalence constructs paths in a universe; it does not change the universe-level conversion rule.

### Constructor rules

For each rule, scope and required-face checks are prerequisites. Type comparison means section 34's conversion, not pointer inequality. Checking-only constructors use their existing type annotations when a caller requests synthesis. An annotation must itself denote a checked type.

| Constructor | Required checks and resulting type |
| --- | --- |
| `VAR(x)` | Look up the checked declaration; return its type. |
| `UNIVERSE(l)` | Require a valid level; return `U_(l+1)`. |
| `PI(A,B)` | Check `A:U_i`; open `B` under fresh `x:A` and check it in `U_j`; return `U_max(i,j)`. |
| `SIGMA(A,B)` | The same formation premises and universe calculation as `PI`. |
| `LAM(A,h)` | Against a product `Pi(x:D).B`, require `A` convertible to `D`; apply the body handle and codomain handle to the same fresh `x:D`, and check the body against `B(x)`. |
| `APP(f,a)` | Infer and weak-head observe the checked type of `f` as `Pi(x:A).B`; check `a:A`; result type is `B(a)`. |
| `PAIR(a,b)` | Against `Sigma(x:A).B`, check `a:A` and `b:B(a)`. |
| `FST(p)` | Infer a pair type `Sigma(x:A).B` for `p`; result type is `A`. |
| `SND(p)` | Infer the same pair type; result type is `B(fst p)`. |
| `PATH(h,l,r)` | At fresh `j`, check the family `B(j):U_l`; check endpoints in `B(0)` and `B(1)`; result type is `U_l`. |
| `PLAM(h)` | Against `PathP(j.B(j),l,r)`, check the body at fresh `j` in `B(j)`; compare its endpoint specializations to `l` and `r` in their respective endpoint types. |
| `PAPP(B,l,r,p,s)` | Check the retained path type data; check `p` at that path type and `s` as an in-scope interval; result type is `B(s)`. |
| `GLUE_TYPE(A,alpha,T,e)` | Check `A:U_l`; under `chi AND alpha`, check `T:U_l` and `e:Equiv(T,A)`; result type is `U_l`. |
| `GLUE_INTRO(A,alpha,T,e,t,a)` | Validate the supplied Glue type data; check `a:A`; under `chi AND alpha`, check `t:T` and `e.map(t)` convertible to `a` in `A`; result is the supplied Glue type. |
| `UNGLUE(A,alpha,T,e,v)` | Validate the supplied Glue type data and check `v` at that Glue type; result type is `A`. |
| `COMP(hA,phi,hu,a0)` | At fresh `j`, check `A(j):U_l`; require `phi` independent of `j`; check `a0:A(0)` and, under `chi AND phi`, `u(j):A(j)` and `u(0)` convertible to `a0`; result type is `A(1)`. |
| `SYSTEM([(phi_k,t_k)])` | Against `A`, require coverage `chi entails OR_k phi_k`; check each branch in `A` under `chi AND phi_k`; check each pair of branches convertible in `A` on its overlap. |
| `GLOBAL(symbol,sigma)` | Require a declared symbol and a checked parameter substitution; return its declared type reindexed by that substitution. Validate a supplied definition body against its declaration according to the declared signature; unfolding is precisely the registered body, not an invented equation. |

For a general check `t:A`, synthesize a checked type where the constructor synthesizes; require it convertible to `A`. For lambdas, pairs, path lambdas, and systems, use the expected type directly. To synthesize one of those checking forms, use its stored annotation as the expected type and validate the form against it first.

Check Glue introductions and eliminations using their explicitly retained Glue data. Do not try to recover those data from a type already collapsed to its fibre on an entailed face. After deriving the supplied Glue type, compare it to the requested type under the actual face.

Under a false face, checking and conversion obligations are vacuous once the finite syntax and scope are valid. Do not demand a weak-head observation on the empty face. Under a nontrivial face, the clause procedure in section 34 handles conditional type heads, including systems.

For a system's overlap checks, false overlaps are skipped. The checks are finite in number; their conversion computations may still be nonterminating if the declared computation language admits general recursion. No total decision procedure for unrestricted recursive computation is asserted.

## 34. Definitional conversion procedure

Definitional conversion uses the registered computation rules, their congruence, the interval and face algebra, and the function, pair, path, and Glue eta rules stated here. A separately supplied path `p:A=B` is used through transport; it is not an instruction to add `A=B` as a global conversion rule.

The procedure is type directed. It runs on checked terms and types; conversion alone is not a substitute for checking their annotations and scope.

### Face clauses

Normalize `chi` to DNF. Conversion under `chi` requires conversion under every consistent clause `C` of that DNF. Keep the context and use `C` as the ambient face. Do not substitute endpoints through term-variable declarations and then silently forget their dependent contexts.

For comparing interval expressions under `C`, substitute the endpoints fixed by `C` into the interval expressions and compare their canonical De Morgan DNFs. For comparing faces `phi` and `psi`, compare the canonical DNFs of `C AND phi` and `C AND psi`.

A valid covered system always has an available branch under a single clause `C`: coverage entails that `C` contains a clause of some branch guard. The ordinary evaluator therefore selects such a branch under `C`. Its original branch order gives a deterministic selection; checked overlap compatibility makes the selection valid.

Conversion under false succeeds. For a disjunction of clauses, combine their outcomes in fixed clause/provenance order for diagnostics: all equal gives `EQUAL`; a witnessed mismatch gives `UNEQUAL`; otherwise unresolved obligations give `UNRESOLVED`. Parallel checking uses a full join before final diagnostics, as in the machine's system checks.

### Type conversion

Weak-head observe both type references under the clause. Equal references provide the reflexive fast path after their validity is established. Otherwise compare their exposed type constructors:

- Universes: compare level expressions.
- Products and sums: compare domains; introduce one fresh variable at the left domain and apply both codomain binders to that same variable; compare the resulting types.
- Path types: introduce one fresh dimension and compare the family bodies; compare endpoints at the respective family endpoints.
- Glue types: compare guards as faces under the clause; compare bases generally; on the common partial face compare fibre types and equivalence terms at `Equiv(T,A)` using term conversion.
- Neutral types: use neutral-spine comparison below.

Different irreducible constructor tags give `UNEQUAL`. A computation still awaiting a result does not count as an irreducible constructor. No type equivalence is accepted merely because an equivalence witness exists.

Fresh comparison variables and dimensions are keyed by an immutable comparison-request record and logical slot, in a distinct owner namespace. Construct that record first and mint identities fresh relative to both compared boundaries. Apply the two binders to the same fresh identity. Never identify their independently allocated binder numbers by numeric coincidence.

### Term conversion by expected type

Once both terms are checked at the expected type, identical reference handles give the reflexive `EQUAL` fast path. Otherwise weak-head observe the checked expected type and use the following extensional comparisons:

\[
\operatorname{Eq}_{\Pi(x:A).B}(f,g)
\iff\operatorname{Eq}_{B(x)}(f\,x,g\,x)
\quad(x\text{ fresh}),
\]

\[
\operatorname{Eq}_{\Sigma(x:A).B}(p,q)
\iff\operatorname{Eq}_{A}(\operatorname{fst}p,\operatorname{fst}q)
\ \land\
\operatorname{Eq}_{B(\operatorname{fst}p)}(\operatorname{snd}p,\operatorname{snd}q).
\]

The second pair comparison uses conversion of the already-compared first fields to identify the two dependent field types.

\[
\operatorname{Eq}_{\operatorname{PathP}(j.B,l,r)}(p,q)
\iff\operatorname{Eq}_{B(j)}(p@j,q@j)
\quad(j\text{ fresh}).
\]

At a non-collapsed Glue type `G = Glue[alpha -> (T,e)] A`, compare

\[
\operatorname{unglue}(u)\equiv\operatorname{unglue}(v):A
\quad\text{under }C,
\]

and

\[
u\equiv v:T\quad\text{under }C\wedge\alpha.
\]

These two comparisons are exactly the components of Glue eta and constructor congruence; arbitrary fibre information is not discarded. If the face already entails `alpha`, the expected type observes as `T` and the ordinary type-directed case applies. At a universe, term conversion is type conversion. At a neutral expected type, weak-head observe the terms and compare their neutral structures.

### Neutral-spine comparison

Neutral comparison is structural on the **neutral head and elimination spine**, with typed conversion for argument data. Do not eta-expand the neutral head again while recursively comparing its spine: that would turn comparing `f x` and `g x` into an artificial loop through comparing `f` and `g` extensionally again.

| Neutral form | Comparison |
| --- | --- |
| Free variable | Same declared identity; comparison-bound variables have already been aligned by the common fresh variable. |
| Application | Compare function neutral spines structurally; compare arguments at the checked function domain. |
| First or second projection | Require the same projection tag; compare the pair neutral spines structurally. |
| Path application | Compare path neutral spines structurally and intervals modulo the clause. Retained typing/endpoints have already been checked against that path's type. |
| Unglue | Compare the retained guards modulo the clause, the base types, and the fibre/equivalence data on their common guard; compare the value neutral spines structurally, without recursively invoking Glue eta on that spine head. |
| Blocked composition | Align the family binders at one fresh dimension; compare their type families, faces, caps, and tubes, with tube comparison on the common tube face. Families compare at their declared universe, caps at the starting type, and tubes at the generic family type. |
| Declared opaque constant, if present in the signature | Same symbol and compatible instantiated parameter data in declaration order. Transparent definitions unfold through ordinary evaluation. |

Different irreducible neutral heads or elimination tags give `UNEQUAL`. Redundant annotations are first validated; they are not unconstrained extra data permitted to alter an otherwise fixed path application's endpoint semantics. Semantic operands of blocked composition are all retained and compared.

### Scheduling and unresolved computations

Cache a conversion request by its mode, ordered input references, expected type when applicable, typed boundary/signature, and the face projected to their combined support. The request must retain all data on which its answer depends. Identical running requests wait through the same request/publication/delivery protocol; encountering a running request is not permission to assume equality or immediately return a timing-dependent failure.

An actual unresolved demand cycle is reported at workload quiescence. Resource exhaustion or an explicit budget interruption also yields `UNRESOLVED`, never `EQUAL` or a proved mismatch. An unresolved control outcome is not a permanent mathematical inequality cached for all future attempts. A finite successful checking derivation is the evidence for accepting a term; no coinductive assumption closes a circular typing proof.

Checking can be a separately measured admission phase, or its deterministic checking/conversion frames can use the same job protocol as evaluation. If end-to-end interaction costs include checking, count those frames explicitly. If reporting runtime-only costs, fix the post-validation starting state and cache snapshot. Do not silently precompute during validation and then describe the remaining runtime count as the total computation cost.

## 35. Concurrent worker pool and quiescence

Use a configurable positive worker count. One worker executes the same event protocol as multiple workers; it is a debugging and deterministic scheduling mode.

Every cache state transition and waiter-list mutation is protected by its entry lock. Publish a fully initialized immutable result before exposing `READY`. A requester retains the result before dropping the lock. Detach waiters while holding the entry lock, release it, and enqueue deliveries afterward. Keep the publishing job active until those deliveries have been enqueued.

Do not invoke arbitrary continuation code or recursively acquire interning/entry locks while holding an entry lock. Compute canonical keys and immutable payloads outside that lock. Canonical interning uses its own atomic lookup-or-insert protocol; losing private candidates are released without publishing duplicate canonical objects.

For scheduler quiescence maintain

\[
\operatorname{outstanding}
=\#\text{queued jobs}+\#\text{executing jobs}.
\]

```text
enqueue(job):
    under scheduler lock:
        outstanding += 1
        put job on queue
        signal waiting workers

take_job():
    under scheduler lock:
        remove one queued job
        // outstanding is unchanged: the job is now executing

finish_job():
    // all child jobs must already be enqueued
    under scheduler lock:
        outstanding -= 1
        if outstanding == 0:
            signal workload-quiescence observer
```

At a closed workload boundary, `outstanding == 0` is quiescence. An empty queue with an executing job is not quiescence. Workers wait rather than report `W_STUCK` while outstanding work remains. External workload admission and completion observation use the same admission/epoch synchronization; a benchmark workload closes admission after its initial roots are installed.

At true quiescence, inspect root and demand-network state. A completed root produces `W_OK`; an unresolved cyclic demand has no fabricated publication and produces `W_STUCK` or the checking layer's corresponding `UNRESOLVED` control result. Check the no-orphan-live-demand invariant for successful roots.

For branch joins, each child writes its original branch slot exactly once under the join's synchronization. Publish only when every launched slot is full. Select any failure diagnostic by original branch order, not arrival order; retaining the first arriving error until the join fills is still nondeterministic. Snapshot/retain the complete joined outcome before releasing the final join ownership.

Net replacement retains the pin, lock-in-total-order, revalidate, install, retire protocol from section 20, including surviving boundary endpoint owners. A stale redex retry is diagnostic work, not a successfully committed interaction. No observer may see a partially installed semantic replacement.

Check concurrency with actual simultaneous requests, publication/request races, and contended interning. Use a race detector for data races and separate address/undefined-behaviour/leak checks for their respective failure classes. A sequential schedule suite establishes neither race freedom nor correct memory publication. Compare the same semantic event vectors and exact results across the sequential policies and selected multi-worker runs.

## 36. Ownership, cache retention, and teardown

Keep an explicit ownership account:

| Holder | Required ownership |
| --- | --- |
| Intern arenas | Their immutable records and the referenced metadata required for the arena's lifetime. |
| Ready cache entry | Its immutable result until the counted workload ends or the entire owning machine is destroyed. |
| Running cache entry | Its waiter collection and associated live evaluation ownership. |
| Queue or executing worker | Each owned job and its captured payloads. |
| Continuation | Its parent/destination, arguments, and join ownership until consumed or safely torn down. |
| Join | All delivered slot values until its joined result/continuation has retained what it needs. |
| Descriptor or external root | Its referenced payload for as long as it is live. |

Transfer ownership when a continuation moves from a request into a waiter collection and later into a delivery job. Consume it once. Release join and argument ownership when that consumption is complete. Atomic reference counts or equivalent synchronized ownership are required for objects crossing worker boundaries.

Do not evict a ready memo entry during a counted workload and later rerun the same key. That would change the at-most-once property and the event system used by the optimality proof. Cache retention is part of the operational contract, not merely a performance hint. Arena-owned immutable records and memo tables may be reclaimed together at machine teardown; temporary job and continuation objects need not live that long.

Reference counting alone does not collect ownership cycles. In particular, a stuck demand may contain a waiter retaining a parent entry that reaches the same waiter. At closed-workload teardown, first stop/join workers and prevent further admission, then detach the suspended waiter/continuation ownership graph and release its payloads, then destroy cache and immutable arenas in their declared lifetime order. No live observer or queued job may retain an object after its arena is destroyed. Do not recursively free through an arena after its storage has already been released.

This teardown is not a new semantic cancellation rule inside a successful counted run. It disposes of a finished or explicitly abandoned workload after execution has stopped. Successful live work is never canceled by reclamation.

AddressSanitizer can expose invalid accesses; it does not establish the ownership proof or detect all logical retention problems. Use leak checking and teardown cases as well, including a stuck demand cycle. A completed run must release temporary continuations and joins, while intentional cache/arena retention remains owned until the declared teardown boundary.

## 37. Exact schedule comparison modulo renaming

Partition refinement is useful preprocessing, but iterated refinement alone is not a general exact canonical-labelling algorithm. Nonisomorphic graphs can retain the same refined colour classes. Unique provenance and input indices may resolve all classes for a particular graph; unresolved classes still require exact matching.

The harness needs pairwise exact comparison, not necessarily a universal canonical serializer. Compare the reachable result and reference graphs while preserving their sharing. Anchor input roots, original free-variable identities, source declarations, and global symbols by their known input identities. Generated identities may be renamed, but their owner/slot provenance must be preserved.

```text
match(left,right,bijection):
    if left is already mapped:
        require its image is right
        return
    require right has no different preimage
    require identical kinds and non-renamable scalar payloads
    extend the bijection with left -> right
    compare ordered fields by field position
    compare generated-identity provenance by owner, slot, and sort
    compare unordered collections as sets under the same bijection
    recursively check every referenced payload and incidence
```

For an unresolved unordered match, use exact backtracking: choose an unmatched left element, try the admissible right candidates in its refinement class, propagate the bijection and ordered/provenance constraints, and undo the tentative assignments on failure. Accept only after one complete bijection preserves every relevant label, field, edge, dimension expression, face clause, and sharing relationship. If no candidate yields such a bijection, reject.

Exact structural partitions and provenance propagation should resolve the common cases cheaply. Hashes may accelerate candidate lookup but never decide equality without exact verification. Numeric allocation order is not an anchor for a generated identity. Two references to one object must map to two references to one corresponding object, not to two separately matching copies.

Compare result classes and complete retained heads, not just constructor tags. For blocked results compare their retained operands and diagnostic state with the same identity discipline. Compare the balanced event vector separately. Counts of transient interned records and raw allocations remain diagnostics unless their creation is included in the specified invariant cost model; comparing reachable canonical structure is the semantic test.

## 38. Handoff checks for the completed scope

The relevant checks are finite and directed at the newly implemented obligations:

- Checking: accept beta and the stated product, pair, path, and Glue eta conversions; reject incompatible declared types and unbound dependencies; validate dependent substitution images, composition cap/tube agreement, path endpoints, Glue map agreement, system coverage and overlaps. Report unresolved conversion without accepting it or calling it proved unequal.
- Concurrency: exercise duplicate requests, request/publication races, unique interning, branch joins, and quiescence with an empty queue while another job is executing. Ensure fixed-order diagnostics and one evaluator/publication per key.
- Reclamation: consume each continuation once, release completed joins, preserve memo entries throughout the counted workload, and reclaim both successful and stuck workloads at teardown without invalid accesses or unintended retained ownership.
- Comparison: accept a consistent renaming with preserved sharing; reject a changed payload, endpoint, guard, or aliasing pattern. Include an ambiguous refinement case so equality cannot accidentally be decided by refinement colours or hashes alone.
- Scheduling: vary both job and active-pair policies, including mixed policies, from the same initial state; compare the balanced event vector and exact reachable result graph. Retain seeds and a useful first mismatch record.

Deliver the implementation, the current handoff, and the actual validation results together. Source changes can be separated into reviewable commits for checking, concurrency, ownership, and comparison; none of those four is left as an unanswered author decision by this specification. This section specifies the work and its checks; it does not assert that another agent's uninspected implementation has passed them.

## 39. Identity compiler: declarations and generated records

Sections 39–48 complete the executable connection between the realization equivalences of section 21 and the scope/evaluation agents of sections 19 and 26. They add a compiler and invocation rules while preserving the existing reference representation, cubical clauses, cache protocol, and ownership rules.

An identity is supplied evidence, not a request to search for an equation. Its orientation is explicit invocation data. Compiling identities must not register competing automatic rewrites for one undecorated constructor pair.

All types and terms below are annotated core references. The formulas are term-building specifications; section 40 defines their lowering. Host records and enums do not introduce object-language datatypes.

~~~c
struct IdentityDecl {
    DeclarationId id;        // stable source identity
    ContextId parameters;   // ordered dependent telescope Gamma
    FaceId required_face;   // phi in Gamma
    RefId result_type;      // B, a type in Gamma,phi
    DiagramId left;
    DiagramId right;
    RefId evidence;         // p : Path_B(C_left,C_right)
};
~~~

Introduce a fresh formal compiler parameter y:B, distinct from the parameters and diagram-local variables. The generated forward map has domain Real(left,Gamma,y) and codomain Real(right,Gamma,y); the reverse exchanges them. The entire boundary Gamma,y is retained.

A finite construction diagram has the following typed topological description:

~~~text
Diagram:
    parameter_context
    nodes[0..n-1]
    output_type B
    output_term o

Node k:
    stable_node_id
    value_variable x_k
    witness_variable e_k
    value_type A_k
    defining_term t_k : A_k
~~~

Check A_k and t_k in Gamma followed by all preceding node variables and witness declarations. Then add

    x_k : A_k
    e_k : Path_(A_k)(t_k,x_k).

Check the final output o:B in that extended context; B itself is in Gamma. Dependent data may be packaged in Sigma types. Necessary transports between dependent argument types are explicit annotated core syntax checked by the existing checker. The compiler does not silently replace propositional equality with definitional equality.

For an ordinary operation graph, t_k applies the operation to boundary values and predecessor variables. Multiple uses of one predecessor use the same variable. A shared node occurs once in the array. Source declaration order breaks ties between independent nodes; runtime allocation order does not determine graph order.

The output operation may be retained as o without a redundant final node. For example, m(m(a,b),c) can have one internal node u=m(a,b), followed by output m(u,c).

Construct the realization type by a right fold:

\[
R_n=\operatorname{Path}_{B}(o,y),\qquad
R_k=\Sigma(x_k:A_k).\Sigma(e_k:\operatorname{Path}_{A_k}(t_k,x_k)).R_{k+1}.
\]

Real(C,Gamma,y) is R_0. The tail retains its dependencies on x_k,e_k. For n=0 the realization is the output path type; no Unit or list primitive is needed.

Compute a canonical substitution without evaluating terms:

~~~text
nu := identity on Gamma
for k = 0 .. n-1:
    a_k := reindex(t_k,nu)
    nu := nu extended by x_k -> a_k, e_k -> refl(a_k)
C := reindex(o,nu)
~~~

Images are references, and reusing an image reuses its handle. This does not textually expand a shared DAG into a tree. Every extension uses simultaneous substitution. Check the declaration's evidence at Path_B(C_left,C_right) under its required face. INVALID or UNRESOLVED validation is not acceptance.

The generated immutable record is:

~~~c
struct CompiledTransform {
    DeclarationId id;
    ContextId parameters;
    FaceId required_face;
    RefId domain;
    RefId codomain;
    TermVarId forward_argument_slot;
    TermVarId reverse_argument_slot;
    RefId forward_body;
    RefId reverse_body;
    EvidenceKind evidence_kind;
    CertificateId certificate;
    GraphPairTemplateId identity_template; // present for identity declarations
};
~~~

For an identity declaration its parameters are Gamma,y. Its domain and codomain are the two realization types. The forward and reverse formal argument variables have distinct identities and their respective input types. The template bodies are free in the parameters and the appropriate argument variable.

The certificate records the checked declaration and the structural derivation below: typed singleton blocks, their order, generated maps, and the checked identity. It is not an unchecked assertion that arbitrary functions are inverses. Its verification reconstructs this finite compilation schema. A trusted compiler pass plus checking of its emitted types is an implementation of that verification; it does not require proof search.

The certificate is a tagged immutable record with exactly these cases:

| Tag | Retained input and verification |
| --- | --- |
| IDENTITY | IdentityDecl plus checked diagrams; reconstruct sections 41–42 |
| EQUIVALENCE | Context, face, X,Y,e; check e:Equiv(X,Y), reconstruct section 44's two maps |
| RESIDUAL_EQUIVALENCE | Two singleton-prefix descriptions with terminal types Z_L,Z_R and e; check e between their canonically instantiated terminal types, reconstruct collapse/equivalence/expand |
| CUT | Context, face, B,C,D; reconstruct CUT_TO_PATH and its section 44 inverse |
| CONTRACTIBLE_FIBRE | Context, face, B,R,k; check k:Pi(b:B).Contr(R(b)), reconstruct the projection and section |

Verification re-emits the prescribed templates using the same anchored formal identities and checks exact structural equality with the registered bodies, domain, codomain, and argument slots. Check all retained input types/evidence first. It does not merely check the bodies' function types and assume invertibility. Arbitrary user-supplied inverse functions require an actual EQUIVALENCE value; they do not qualify for a built-in schema tag.

For RESIDUAL_EQUIVALENCE the parameter context is the supplied common telescope. Each description contains the same node fields as Diagram and an explicitly typed terminal type instead of output_type/output_term. Its domain/codomain are the resulting folded realization types; no extra y is introduced unless it is already a parameter. Canonical substitution determines the two terminal types expected by e.

The registry retains its declarations, diagrams, certificates, templates, and all referenced data for the workload lifetime. No pending application may outlive its registry.

Publish the compiled record only after validation succeeds. The registry is immutable within a workload. Declaration replacement creates a new environment identity or begins a new workload, as for existing global definitions.

## 40. Exact lowering into the existing core

Compilation builds origin records and references directly. The following builder operations have exact expansions:

| Builder | Core expansion |
| --- | --- |
| lam(x:A,t) | LAM, domain A, term-binder body t |
| app(f,a) | APP(f,a) |
| pair(a,b) | PAIR(a,b), with checked expected Sigma type |
| fst(v), snd(v) | FST(v), SND(v) |
| path(A,a,b) | PATH with constant family A and endpoints a,b |
| pathp(i.A,a,b) | PATH with the indicated family binder |
| plam(i,t) | PLAM with dimension-binder body t |
| at(p,r) | PAPP retaining the checked family and both endpoints |
| refl(a) | plam(i,a) |
| inverse(p) | plam(i,at(p,not i)) |
| coe(i.A,a) | COMP, family i.A, false tube face, cap a |
| hcomp(j.A,branches,a) | COMP with constant family A and the specified tube |
| concat(p,q) | The section 18 hcomp definition below |
| sigma(x:A,D) | SIGMA with domain A and codomain binder D |
| substitute(t,sigma) | Existing reindex; no evaluation |

For p:x=y and q:y=z in A, concat generates exactly

\[
\langle i\rangle\operatorname{hcomp}^{j}_{A}
[(i=0)\mapsto x,\ (i=1)\mapsto q@j]\,(p@i).
\]

The fresh dimensions i,j have distinct binder slots. Families, guards, caps, endpoints, and tubes use the shared lifts required by section 8.

Generated formal binder identities are anchored in the owning template identity, compilation role, diagram node id, and local slot. Runtime opening still uses owner/slot identities. Compiler names are not runtime freshness.

Build terms in dependency order and intern complete immutable records with exact structural equality. Cache collapse/expand templates by the checked diagram, definition environment, and role; an unrelated identity declaration or proof is not part of that key. Cache the generic proof-parameterized map by the ordered diagram pair and environment. Source diagram identities anchor provenance, while an invocation supplies the proof and boundary through substitution. This allows different identities involving the same diagram to reuse the same realization maps. A hash match alone is not equality. Keep fixed bodies and instantiate their references at calls; do not copy their syntax.

All generated programs use these operations and existing type constructors. There is no native associativity oracle, special datatype handler, general proof-search step, or noncollapsing Glue representation.

## 41. Executable realization contraction and expansion

This gives the missing algorithms for c_C and its inverse. They operate on the dependent realization telescope without duplicating graph predecessors.

First remove one singleton block. Given

\[
t:A,\quad x:A,\quad e:\operatorname{Path}_{A}(t,x),\quad z:D(x,e),
\]

define the fixed template

\[
\begin{aligned}
x_i&=e@(\neg i),\\
e_i&=\langle j\rangle e@(\neg i\wedge j),\\
\operatorname{down}(A,t,D,x,e,z)
&=\operatorname{coe}^{i}D(x_i,e_i)\ z.
\end{aligned}
\]

At i=0, the family is D(x,e), using the specified path eta conversion. At i=1 it is D(t,refl(t)). Thus down has that latter type. Its code is one COMP with false tube, whose family simultaneously substitutes x_i,e_i into D. The images contain the original e reference; substitution must not recursively substitute inside an image.

The corresponding inclusion is

\[
\operatorname{up}(z_0)=(t,\operatorname{refl}(t),z_0).
\]

This triple means pair(t,pair(refl(t),z_0)), not a new primitive.

For a diagram, generate collapse and expand by the following recursions. At each stage prefix is the canonical substitution for all earlier nodes.

~~~text
emit_collapse(k,prefix,r):
    if k == n:
        return r
    A := reindex(A_k,prefix)
    t := reindex(t_k,prefix)
    D := reindex(R_(k+1),prefix)  // formal x_k,e_k remain free here
    x := fst(r)
    e := fst(snd(r))
    z := snd(snd(r))
    z0 := down(A,t,D,x,e,z)
    next := prefix extended by x_k -> t, e_k -> refl(t)
    return emit_collapse(k+1,next,z0)

emit_expand(k,prefix,q):
    if k == n:
        return q
    t := reindex(t_k,prefix)
    next := prefix extended by x_k -> t, e_k -> refl(t)
    z0 := emit_expand(k+1,next,q)
    return pair(t,pair(refl(t),z0))
~~~

These recursions emit syntax over a finite node array. They do not evaluate fst, coe, or an operation value during compilation. Generated subexpressions are retained references. The implementation may produce the stages iteratively to avoid host stack growth.

The emitted maps have types

\[
c_C:\operatorname{Real}(C,\gamma,y)\to(C(\gamma)=y),
\qquad
d_C:(C(\gamma)=y)\to\operatorname{Real}(C,\gamma,y).
\]

Here d_C is the inverse denoted c_C^{-1} in section 21.

For correctness, a singleton

\[
S=\Sigma(x:A).\operatorname{Path}_{A}(t,x)
\]

is contractible, with centre (t,refl) and contraction

\[
H((x,e),i)=(e@i,\langle j\rangle e@(i\wedge j)).
\]

For any dependent D over S, inclusion of the centre fibre D(t,refl) into Sigma(s:S).D(s) is an equivalence. Transport along H in reverse is the displayed down map. Transport equivalences and the lifted dependent paths supply its inverse homotopies. Equivalently, this is singleton path induction. It applies when D depends on the witness e as well as on x.

Remove each block by that equivalence and compose. The base case is the identity on the output path type. This proves that the generated c_C,d_C are inverse up to paths.

This is not a new definitional computation rule. Do not optimize constant-family coe to its argument unless the calculus separately supplies that regularity. Round trips are generally witnessed by paths, not identical RefIds. No proof irrelevance is introduced.

Dependent-tail handling is essential: down transports the complete R_(k+1), including later types, values, guards, and witnesses. Updating only value fields is incorrect.

The contraction applies to the displayed finite singleton telescope. Extra constraints must remain in its terminal type rather than being silently erased. Section 44 specifies that general case.

## 42. Complete identity compilation procedure

~~~text
compile_identity(d):
    validate parameter context, required face, and result type
    validate both typed diagram telescopes
    build R_left,R_right and canonical values C_left,C_right
    check evidence : Path_(result_type)(C_left,C_right)
    generate c_left,d_left,c_right,d_right using section 41

    introduce common parameter y : result_type
    introduce distinct formal arguments r_left:R_left, r_right:R_right
    introduce fresh P : Path_(result_type)(C_left,C_right)
    graph_pair_forward := d_right(concat(inverse(P),c_left(r_left)))
    graph_pair_reverse := d_left(concat(P,c_right(r_right)))
    retain GraphPairTemplate with P and these two generic bodies
    forward_body := reindex(graph_pair_forward,[P -> evidence])
    reverse_body := reindex(graph_pair_reverse,[P -> evidence])

    check forward_body : R_right in Gamma,y,r_left:R_left
    check reverse_body : R_left in Gamma,y,r_right:R_right
    validate structural compilation certificate
    intern and publish CompiledTransform
~~~

GraphPairTemplate retains the two diagrams, their parameter context, the common y parameter, the fresh proof slot P, distinct input slots, domain/codomain, and generic forward/reverse bodies. This is the concrete proof-parameterized template used for higher coherence in section 45. The ordinary compiled record specializes P to the declaration evidence. P is distinct from every source parameter, even when that context already contains the source evidence as a variable.

For these generated subtemplate calls, instantiate a fixed template body by mapping its formal input to the argument reference. Do not introduce an unnecessary APP/LAM pair. This is the fixed compilation convention, independent of scheduling or cache readiness.

The generated maps are precisely

\[
F_p=d_R\circ(q\mapsto p^{-1}\cdot q)\circ c_L,\qquad
B_p=d_L\circ(q\mapsto p\cdot q)\circ c_R.
\]

Concatenation with p or its inverse is an equivalence of path spaces. Section 41 gives the other equivalences. Their composites establish the forward/reverse inverse homotopies. The evidence remains executable core data.

A proof may use ordinary functions, globals, compositions, Glue, and higher paths. Compilation retains those references rather than normalizing the proof. General recursive conversion or execution may not terminate; compilation does not decide termination or accept unfinished checking.

The runtime work theorem starts with the validated compiled registry fixed. An end-to-end cost report must separately include compilation and validation instead of claiming they cost nothing.

## 43. Invocation, exact agent wiring, and evaluator integration

All compiled transformations use one uniform agent schema. Declaration id and orientation distinguish the instances; C can use one dispatcher rather than handwritten handlers for individual identities.

~~~c
struct ApplyTransform {
    TransformId transform;
    Direction direction;   // FORWARD or REVERSE
    MapId parameters;      // map into template parameter context
};
~~~

The operation agent has a negative principal port and one positive result auxiliary. Its input is a positive-principal REF(a) descriptor. Let b be the surviving endpoint attached to the result auxiliary.

There is exactly one replacement:

~~~text
APPLY_TRANSFORM(id,dir,sigma).principal -- REF(a).principal
APPLY_TRANSFORM.result -- b

    becomes

REF(v).principal -- b

where:
    (template,slot) :=
        (forward_body,forward_argument_slot) if dir==FORWARD
        (reverse_body,reverse_argument_slot) if dir==REVERSE
    tau := sigma extended by slot -> a
    v := reindex(template,tau)
~~~

The rule performs no evaluation of a, the proof, or v. Retain v's owned data before retiring the consumed operation and descriptor shells. Parameter images and a are reused by handle. Every boundary port is accounted for; the two removed principal ports are internal to the redex.

Its typed preconditions are a validated compiled record in the current environment, a valid parameter map sigma, ambient entailment of required_face[sigma], and input a of the appropriate instantiated domain. The result has the opposite instantiated type under the same occurrence context and face.

Validate raw occurrences before execution. In a well-typed generated program these premises follow from the checked origin and substitution lemma. Do not run a potentially nonterminating conversion procedure inside the finite APPLY_TRANSFORM rule. Malformed raw inputs are validation failures, not alternative rewrite cases.

For an external net, b is the desired consumer. An EVAL(chi) consumer demands the output through the existing protocol; a storing consumer retains the reference unevaluated. Instantiation does not itself demand evaluation.

For calls inside referenced programs, add one internal instruction origin:

~~~text
TRANSFORM_CALL:
    transform id
    direction
    parameter map sigma
    argument reference a
    checked instantiated input/output type annotations
~~~

This is an additive instruction implementing the generated core expression, not an object-language datatype. Its checker validates the preconditions and infers the specified output type. Parameter-map images, argument, guards, and type annotations participate in complete typed support.

The source support invariant is S(instantiated_body) subset S(TRANSFORM_CALL). Compute the call support from all instantiated typed template dependencies, including declaration evidence through the template, required faces, and argument-type dependencies; retaining only the visible argument's support is insufficient. Projecting the parent face therefore preserves every entailment needed by its expanded body.

Reindexing by tau composes sigma with tau, reindexes a and its annotations, and preserves id and direction. Opening performs these operations on immediate fields. It never evaluates the source template before instantiation. Registry identity is part of the fixed definition environment.

Add this dispatch case:

~~~text
evaluate K whose opened origin is TRANSFORM_CALL(id,dir,sigma,a):
    consume the current owned evaluator frame
    allocate APPLY_TRANSFORM(id,dir,sigma)
    attach REF(a).principal to APPLY_TRANSFORM.principal
    allocate negative-principal CONTINUE_REFERENCE(K), with no auxiliaries
    attach APPLY_TRANSFORM.result to CONTINUE_REFERENCE.principal
    transfer ownership of K's suspended evaluation to the receiver
~~~

The receiver has one rule:

~~~text
CONTINUE_REFERENCE(K).principal -- REF(v).principal
    ->
    REQ(key(v,E[K].face), continuation FORWARD_RESULT(K))
~~~

Retire the shells after transferring ownership. The child key uses v's support and the parent entry's projected face, as for other child demands. K remains RUNNING. The continuation is linear.

Delivery to FORWARD_RESULT(K) schedules the normal parent evaluator publication frame, which emits PUB(K,result). There is no inline ready-entry shortcut. An actual demand cycle retains the existing unresolved/quiescence behavior.

Represent pending local active pairs as NET_PAIR jobs in the same outstanding-work accounting as evaluator jobs. Distinct job and pair queues may use different selection policies, but their queued/executing jobs contribute to one outstanding count. Enqueue the newly enabled application pair before finishing the creating evaluator job. After each committed replacement, enqueue its newly enabled pairs or emitted requests before finishing that NET_PAIR job. Thus an empty evaluator queue cannot report quiescence while a transformation pair is pending. Stale pair jobs are handled by the existing revalidation protocol and do not count as committed semantic interactions.

Introducing the three agents is one evaluator-frame event. APPLY_TRANSFORM and CONTINUE_REFERENCE are local rule events. Requests, deliveries, resumed frames, and publication retain the existing event classes. No hidden uncounted proof evaluation or cache-hit path exists.

In definitional conversion TRANSFORM_CALL is reducible by this template expansion. It is not a new neutral form. An unfinished demand is UNRESOLVED. Mathematical equivalence of two declarations does not alone make their call references identical.

## 44. Equivalences, annihilation, and retained residuals

The same interface accepts supplied e:X≃Y under a typed parameter context and face. Check e against the section 15 definition of Equiv and generate

\[
\operatorname{forward}(a)=(\operatorname{fst}e)(a),\qquad
\operatorname{reverse}(b)=
\operatorname{fst}\bigl(\operatorname{fst}((\operatorname{snd}e)(b))\bigr).
\]

The inner fst selects the centre of the contractible fibre, and the outer fst selects its X-coordinate. Fibre contractibility supplies the inverse guarantee; no inverse search is performed.

More generally a realization telescope may end in an explicit residual type Z instead of an output path. Use section 41 with the identity on Z as its base case. A supplied equivalence e:Equiv(Z_L,Z_R) gives the forward map

\[
d_R\circ e.\mathrm{map}\circ c_L
\]

and the reverse using the fibre-derived inverse. Extra constraints remain in Z. Arbitrary cyclic constraints require this actual residual and evidence; they must not be treated as a contractible acyclic function graph.

This does not prohibit recursive programs or infinitely unfolding values. Their finite syntax uses GLOBAL and the existing demand semantics. It prohibits contracting a cyclic solution space without evidence.

For a cut between C,D:B at a common output, define using ordinary Sigma and Path

\[
\operatorname{Cut}(C,D)=\Sigma(z:B).(C=z)\times(D=z).
\]

The fixed CUT_TO_PATH templates are

\[
(z,u,v)\mapsto u\cdot v^{-1},\qquad
h\mapsto(D,h,\operatorname{refl}(D)).
\]

They are equivalences by singleton elimination. Their certificate is this fixed derivation, not arbitrary assumed inverse functions. For cuts between graph realizations, apply their collapse maps before CUT_TO_PATH and expansion maps in its inverse. Represent the common output once.

Given p:C=D, the residual is the loop

\[
p^{-1}\cdot(u\cdot v^{-1}):D=D.
\]

The construction shells may disappear while this residual remains. Supplying p is not permission to replace every such loop by refl.

Semantic erasure requires a checked contraction. Given R:B→U and k:Pi(b:B).Contr(R(b)), generate COLLAPSE_FIBRE:

\[
\Sigma(b:B).R(b)\to B,\quad(b,r)\mapsto b,
\]

with reverse b↦(b,fst(k(b))). Its inverse homotopy is pointwise snd(k(b))(r), with the first coordinate fixed. These are fixed templates with a certificate checked from k. They use the same application agent.

Physical ERA remains an ownership operation. It neither manufactures k nor proves a mathematical quotient. Substitution/transport, cut contraction, residual retention, and contractible erasure therefore have distinct executable meanings.

## 45. Substitution, higher coherence, and interaction work

Generated programs use substitution-respecting core constructors, so

\[
(F_p(r))[\sigma]=F_{p[\sigma]}(r[\sigma])
\]

with diagrams, boundary, types, guards, and scopes reindexed together. This is the substitution law for the generated expression; it does not identify arbitrary propositionally equal proofs as one RefId.

In context the replacement is

\[
(\beta,r,c)\mapsto(\beta,F_p(r),c).
\]

Boundary handles are retained. Equal instantiated template references under equal relevant faces reach the same evaluation entry. Witnesses that affect the result remain dependencies.

The maps depend on p as an ordinary parameter. If H is a path from p_0 to p_1, then

\[
\langle i\rangle F_{H@i}(r)
\]

is the output path. Generate it with the same graph-pair template, substituting H@i into its proof slot. Repeated dimension abstraction handles higher cubes without per-dimension handlers.

The inverse homotopies for c_M,d_M and the path laws compare F_q∘F_p with F_(p·q). This is generally a higher equality, not a definitional collapse of two counted invocations to one. Coherence does not become proof irrelevance or an unaccounted cost reduction.

The new active pairs satisfy section 25: one principal port per agent, one deterministic rule for each fixed payload, and preservation of the surviving boundary. Immutable interning commutes. CONTINUE_REFERENCE transfers a uniquely owned parent frame to one request continuation.

The additional overlap cases are therefore:
- two distinct application pairs: disjoint shells, commuting interning and boundary splicing;
- an application pair and another distinct ordinary pair: preserved residual principal connection;
- a receiver pair and a distinct pair: disjoint shells, linear parent ownership, and explicit request emission;
- emitted requests against requests/publication: exactly section 27's existing overlaps.

No new rule chooses a result from waiter order, waiter count, or the first caller's identity. Use the existing pinning, locks, and boundary revalidation.

Thus the exact residual-diamond and interaction-work conclusions extend under the same hypotheses. Add APPLY_TRANSFORM and CONTINUE_REFERENCE to the local-rule event vector. Demanded execution of generated transports counts normally; a supplied proof is not a free computational oracle.

The theorem concerns executions of the same represented workload and elementary relation. Different supplied identity programs are not silently merged into nondeterministic rewrite alternatives. Any broader comparison must use its declared computation and cost semantics.

## 46. Complete associativity instance

Parameters are

\[
X:U,\quad m:X\to X\to X,\quad a,b,c:X,\quad
\alpha:m(m(a,b),c)=m(a,m(b,c)),
\]

under true face, with common output parameter y:X.

The left diagram has one node u=m(a,b) with witness s:m(a,b)=u and output m(u,c). The right has one node v=m(b,c), witness t:m(b,c)=v, and output m(a,v). Thus

\[
\begin{aligned}
R_L(y)&=\Sigma(u:X).\Sigma(s:m(a,b)=u).(m(u,c)=y),\\
R_R(y)&=\Sigma(v:X).\Sigma(t:m(b,c)=v).(m(a,v)=y).
\end{aligned}
\]

For r_L=(u,s,w), the generated collapse is exactly

\[
c_L(r_L)=\operatorname{coe}^{i}
\operatorname{Path}_{X}(m(s@(\neg i),c),y)\ w.
\]

For r_R=(v,t,w),

\[
c_R(r_R)=\operatorname{coe}^{i}
\operatorname{Path}_{X}(m(a,t@(\neg i)),y)\ w.
\]

The expansions are

\[
d_L(q)=(m(a,b),\operatorname{refl},q),\qquad
d_R(q)=(m(b,c),\operatorname{refl},q).
\]

Therefore the exact forward and reverse emitted templates are

\[
r_L\mapsto
\left(m(b,c),\operatorname{refl},
\alpha^{-1}\cdot
\operatorname{coe}^{i}\operatorname{Path}_{X}(m(s@(\neg i),c),y)\ w\right),
\]

\[
r_R\mapsto
\left(m(a,b),\operatorname{refl},
\alpha\cdot
\operatorname{coe}^{i}\operatorname{Path}_{X}(m(a,t@(\neg i)),y)\ w\right).
\]

Here s or t is fst(snd(r)), and w is snd(snd(r)). Every operation lowers by section 40. The transport expression for c_L is propositionally equal to ap_(z↦m(z,c))(s)·w in section 21. The generated program consistently uses the displayed transport form; no judgmental equality between presentations is assumed.

For invocation, sigma supplies references for X,m,a,b,c,alpha,y and r is checked at R_L[sigma]. Build TRANSFORM_CALL(associativity,FORWARD,sigma,r), or the corresponding external application pair.

Execution:
1. The pair creates a view of the fixed forward body with sigma and its argument slot mapped to r.
2. Its receiver requests that view under the parent's projected face.
3. Weak-head evaluation exposes a pair retaining m(b,c), refl, and the output-path reference. It need not evaluate that path to expose the pair.
4. Demanding the path executes alpha reversal, singleton transport, and concatenation through the ordinary cubical evaluator.
5. Publication/delivery use the standard protocol. Repeated identical demands share entries.

Boundary references remain shared. The source r stays immutable for its other consumers. The output realization is returned at the application's result boundary; other uses of r are not rewritten.

The round trip is related to r by the generated equivalence's inverse homotopies. Verification checks a typed witness or the structural certificate, not equality of endpoint RefIds.

For sharing, use one node u=f(x) and output m(u,u). Its realization contains one u and one witness s:f(x)=u. Collapse uses the family

\[
\operatorname{Path}(m(s@(\neg i),s@(\neg i)),y).
\]

Both occurrences use the same instantiated reference. Do not generate two singleton blocks or duplicate f(x)'s origins.

## 47. Compiler and integration verification

Review must locate actual emitted programs and their execution, not merely a function named compile_identity.

| Responsibility | Required implementation evidence |
| --- | --- |
| Validation | Typed telescope, canonical substitutions, checked endpoints and required face |
| Realization | One singleton block per shared node, correctly bound dependent tail |
| Map emission | Executable down/expand and forward/reverse templates |
| Invocation | Application replacement, internal call dispatch, exact receiver behavior |
| Boundary | Shared parameter/image handles and immutable source references |
| Evaluation | Generated terms use the existing cubical evaluator and cache |
| Residuals | Cuts retain path data; erasure requires checked contraction |
| Certificate | Structural derivation checked, not arbitrary inverse assertions |
| Scheduling | New rule counters participate in existing schedule comparisons |

Focused verification cases:
1. Empty diagram: collapse/expand are identity on the output path type.
2. A tail depending on its witness: emitted transport substitutes both x and e.
3. Complete associativity declaration and both invocation orientations.
4. Shared predecessor used twice: one singleton block and identical repeated image references.
5. Dimension substitution and strengthened face: reindex the complete call before rebuilding its observation key.
6. Wrong endpoints, bad node type, or unmet face: reject; unresolved checking must not publish a compiled record.
7. Higher path in the evidence parameter: generated output family has the stated endpoints.
8. Cut followed by loop conversion: retain the residual without contractibility evidence.
9. Contractible-fibre projection/section: check templates and the certificate from k.
10. Duplicate transformed-reference demands under mixed schedulers: one evaluator per key, equal complete result graphs modulo renaming, equal balanced event vectors.
11. Recursive terms without an obtainable observation: preserve nontermination/unresolved demand; never synthesize success.

Round-trip checks concern typed homotopies or validated certificates, not syntactic identity of generally homotopic expressions. Schedule comparison still uses exact graph comparison for executions of the same program.

These are requirements for actual worker validation. This document does not claim those code tests have already run.

## 48. Combined contract and incoming review

The complete specified implementation path is:

~~~text
annotated diagrams + checked identity/equivalence
    -> validated realization descriptions
    -> fixed core templates + structural certificate
    -> immutable compiled-transform record
    -> explicit oriented application agent
    -> instantiated reference
    -> existing cubical demand evaluator
    -> shared result and preserved dependent boundary
~~~

Existing runtime subsystems remain the substrate. Add the declaration/compiler records, singleton-map emission, uniform application, internal call instruction, and validation. The call instruction extends origin dispatch and checking; it does not replace existing representations.

Compiler correctness follows from singleton contraction, path concatenation equivalences, composition of equivalences, and substitution. Sharing follows from representing each source node once, retaining parameter/image handles, and using the existing cache. Interaction-work properties follow from the deterministic principal-pair rules and explicit cache protocol.

Automatic realization contraction covers finite typed singleton-definition telescopes ending in an output path or retained residual. Other supplied equivalences use the checked equivalence interface. Higher and cyclic constraints are not silently treated as contractible definitions. Recursive executable terms retain their finite GLOBAL descriptions.

For the incoming review, assess existing runtime compliance and presence of the compiler path separately. A missing compiler is an additive subsystem; it does not require discarding a correctly implemented reference, scope, cubical evaluation, sharing, or scheduling subsystem.


## Appendix A. Latest assistant reply verbatim

The following is the complete available assistant reply to “Are you sure this is 100% correct”.

**I’m confident in the face-sensitive cache correction. I cannot honestly turn that into a 100% certification of the entire machine or its implementation.** Here is the exact mathematical justification, including the implementation condition that matters.

For a reference \(t\), let \(S(t)\) contain every free dimension in its **instantiated boundary**: the term, its type, types of free variables, required faces, and retained endpoint data.

“Instantiated” matters: if a substitution replaces \(x\) with a reference depending on \(j\), then \(j\) must enter the support. Looking only at the origin’s original dimension variables would be incorrect.

For a normalized face \(\chi\), define \(\pi_S(\chi)\) by deleting literals outside \(S\) from each clause and normalizing again. Then cache evaluation using

\[
\boxed{\operatorname{EvalKey}(t,\chi)
      =\bigl(t,\pi_{S(t)}(\chi)\bigr).}
\]

The reason this is correct is the following exact property:

\[
\boxed{\chi\Rightarrow\phi
\quad\Longleftrightarrow\quad
\pi_S(\chi)\Rightarrow\phi
\qquad\text{whenever }FV(\phi)\subseteq S.}
\]

To prove it, write the normalized DNFs as collections of consistent clauses. Entailment means that every clause \(C\) of \(\chi\) contains some clause \(D\) of \(\phi\). Because \(D\) uses only dimensions in \(S\),

\[
D\subseteq C
\quad\Longleftrightarrow\quad
D\subseteq C|_S.
\]

That proves the claim. Normalize **before** deleting literals: an inconsistent clause must disappear, rather than becoming consistent after deletion.

Consequently, projection preserves every face test involving the reference’s boundary. Evaluation must use that projected face as its ambient assumption; freshly opened bound dimensions remain symbolic. This is face projection, **not** the cubical \(\forall\) operation.

Why a cache keyed only by `RefId` fails is equally definite. For a neutral path \(p\) with endpoints \(a_0,a_1\), the same reference \(p@i\) has:

\[
\begin{array}{c|c}
\text{Ambient face}&\text{Reduction}\\ \hline
\top&\text{neutral}\\
i=0&a_0\\
i=1&a_1
\end{array}
\]

A single unconditional cached answer cannot represent those three outcomes.

The implementation therefore needs these precise invariants:

- **Origins and references remain immutable.** A reduction under \(i=0\) never replaces the reference globally with its endpoint.
- **Evaluation results belong to the projected-face cache entry.** They are reusable under ambient faces with the same projected key.
- **Reindexing acts on the original reference.** It does not silently substitute into a face-specialized cached result.
- **Support includes substituted images and their typed dependencies.** It is not merely the origin’s syntactic list of dimensions.

These rules also preserve the worker’s sharing example. If \(R\) has no dependence on \(x\), then \(R[x\mapsto a]\) and \(R[x\mapsto b]\) remain the same `RefId`. If \(R\) has empty dimension support, every consistent ambient face projects to \(\top\), so those requests also share one evaluation entry.

**That correction is established by the argument above.** The worker’s central change—retaining component references and specializing them by substitution before evaluation—is consistent with it. This check establishes that particular design point; it does not establish, by itself, every reduction clause or the correctness of code being written.

## Appendix B. Worker report verbatim

The following is the complete available user message relaying the implementation worker's report.

Worker says: Yes, it's better, and it removes the cause of my band-aid rather than covering it.

**Why my version needed a band-aid.** On the λ-net, a value can't be substituted into. So my `comp` read the head at a generic point and then re-evaluated the type line at each point (`\i. component(L i)`). Re-evaluating at a point fires that point's face tests. So `Glue [⊤ ↦ (T,e)] A` collapses to `T` there, and `A` is gone. That forced the non-collapsing codes, and they in turn forced the special case for the U test.

**How your document fixes it.** Substitution is an operation on references: `VIEW(origin, σ)`, with `reindex` and `compose`. Opening the comp origin gives one fresh `j` from `(owner, slot)`, shared by the family and the tube. Each component, `A[σ_i]` or `T`, `e`, `α`, is a reference with `j` free, and using it at `r` is `reindex(·, [j ↦ r])`, which evaluates nothing. Collapse happens only if that view is later opened and evaluated, and then it is the correct collapse at that point. That is exactly CCHM.

The consequences for what I built:
- the non-collapsing Glue and U codes go away;
- the neutral-scrutinee case goes away;
- the generic point `gen` goes away;
- ∀ becomes the real `forall_dimension` on normal forms, not "read at gen";
- intervals and faces are canonical DNF with entailment, which also removes my unnormalized `i ∧ i` printing.

**On sharing.** Your §30 is the example you used against closure copying. Restriction to `FV(C)` plus interning makes `R[x↦a]` and `R[x↦b]` the same `RefId`. If evaluation results are attached to `RefId`s, `R` reduces once. That's sharing by identical instantiated boundary, which is different from the Lamping sharing graph I transcribed in `net.c`. The document's agents carry handles to references, and their duplication copies handles, not cells. So the levelled fans, brackets and croissants are no longer what carries sharing; `net.c` would be superseded, not extended.

**I checked the parts that could hide a mathematical error.** They're correct:
- the endpoint conditions on interval DNF: `(r=0)` is the meet over clauses of the join of `(a=0)`;
- negated atoms: `(¬i = ε) = (i = 1−ε)`;
- single-lookup simultaneous substitution;
- the binder identity from `(owner, slot)`, which is fresh relative to the owner's images because the owner is built first;
- dependency restriction including the types of free variables;
- `δ[σ] = ∀j(α[σ_i])` for the Glue clause.

**What it leaves open, and where that comes from.** The document covers scope only. Two things are still needed:
1. **Evaluation on these references**, meaning what is attached to a `RefId` when it reduces. Your §30 says evaluation state belongs to the reference; I'd store each reference's weak head normal form once, keyed by `RefId`.
2. **The reduction rules on head recipes.** These are the ones already in MACHINE_SPEC:
   - application;
   - projections;
   - path application, with endpoints even for neutral paths;
   - glue and unglue at entailed faces;
   - system selection by coverage;
   - `comp`: face coverage first, then the head table at the opened `j`;
   - the Π, Σ, PathP, Glue and U clauses written as global definitions, so each result is a view of one fixed origin.

Next I'll build the machine this way: your scope subsystem as written, plus that evaluator, replacing `net/`.

The report's single-`RefId` cache suggestion is superseded by sections 10–11. Its neutral-scrutinee statement applies to the artificial generic-point mechanism, not to all genuine neutral terms. The report is preserved as a quotation rather than silently edited to incorporate those corrections.
