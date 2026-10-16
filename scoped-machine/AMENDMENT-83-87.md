## 83. Runtime construction of presentations and actions

This section removes §80's restriction to host-prepared diagram pairs. The input to an identity action may itself be computed: its types, realization families, collapse/expansion maps, and inverse witnesses are ordinary values. No registry publication is required for such values to act. The existing declaration compiler remains an adapter from source diagrams to these values.

All records below abbreviate nested existing Σ types. Functions, paths, application and projection have their existing core meanings. No Nat, Bool, list, syntax-oracle, proof-search or datatype handler is added. All formulas are universe-indexed families of ordinary definitions; do not introduce U:U or silently identify distinct universe levels.

All judgments and definitions are under their complete occurrence context and required face Γ;φ. Retain that annotation and the dependency-closed field declarations in the existing scope/template representation. An ordinary record representation does not make a partial field globally available or weaken any previously required formation check.

### 83.1 Retain the inverse witnesses as terms

For X:U_a and Z:U_b define

\[
\operatorname{Maps}(X,Z)=
\Sigma(c:X\to Z).\Sigma(d:Z\to X).
  (\Pi x:X.\operatorname{Path}_X(d(c(x)),x))
  \times(\Pi z:Z.\operatorname{Path}_Z(c(d(z)),z)).
\]

Write its fields c,d,h,k. Its universe is U_max(a,b). This is the explicit inverse data used by the construction, not a new primitive equivalence type. The proof fields are retained, including higher distinctions between them. No proof irrelevance or claim that this entire record type is proposition-valued is made.

A presentation of Z with realization level a is

\[
\operatorname{Pres}_{a,b}(Z)=\Sigma(X:U_a).\operatorname{Maps}(X,Z).
\]

It is in U_max(a+1,b). Write X_P,c_P,d_P,h_P,k_P for its projections. A program can compute P:Pres(Z), pass P to another program, project X_P as a type, and apply c_P or d_P. The type checker already supports these dependent projections; there is no host type-query callback in their execution.

The constant presentation is `(Z,id,id,λz.refl(z),λz.refl(z))` at a=b. Its level is not implicitly raised. General level combinations use the displayed exact maxima and existing annotated constructors.

For maps E=(f,g,h,k):Maps(X,Y) and F=(u,v,H,K):Maps(Y,Z), their composite has

\[
\begin{aligned}
f'&=u\circ f,&g'&=g\circ v,\\
h'(x)&=\operatorname{ap}(g)(H(fx))\cdot h(x),&
k'(z)&=\operatorname{ap}(u)(k(vz))\cdot K(z).
\end{aligned}
\]

Inverse swaps f,g and h,k. Identity uses identity maps and refl. Here `ap(f,p)=⟨i⟩f(p@i)` and concatenation is exactly §40. These definitions fix both the executable maps and their proof terms.

### 83.2 The dependent singleton constructor, with both proofs

Let A:U_a, t:A and D:(x:A)→Path_A(t,x)→U_r. Define

\[
S_D=\Sigma(x:A).\Sigma(e:t=x).D(x,e),\qquad Z=D(t,\operatorname{refl}(t)).
\]

The singleton constructor is a value of Pres_max(a,r),r(Z). Its maps are exactly §41:

\[
\begin{aligned}
c(x,e,z)&=\operatorname{coe}^{j}D(e@\neg j,\langle k\rangle e@(\neg j\wedge k))\ z,\\
d(z_0)&=(t,\operatorname{refl}(t),z_0).
\end{aligned}
\]

The following two core terms supply the previously host-certified inverse witnesses. For w=(x,e,z), set

\[
B_w(j)=D(e@\neg j,\langle k\rangle e@(\neg j\wedge k)),\qquad
b_w(j)=\operatorname{fill}^{j'}B_w(j')\,[\bot]\ z\ j.
\]

Then

\[
h(w)=\langle i\rangle
 (e@i,\langle k\rangle e@(i\wedge k),b_w(\neg i))
 : d(c(w))=w.
\]

For z_0:Z, let `b₀(j)=fill^{j'} Z [⊥] z₀ j`. Then

\[
k(z_0)=\langle i\rangle b_0(\neg i):c(d(z_0))=z_0.
\]

The endpoints use fill's boundary equations and path/Σ η. They do not assert judgmental regularity for constant-family coe. D is arbitrary and may depend on both x and e. The whole family is passed and specialized together.

`review_singleton_witnesses.c` constructs all four terms with the existing APIs and checks them in the context `A:U₀,t:A,D:(x:A)→(t=x)→U₀`. Both inverse proofs pass on the current core. This is a generic dependent-family check, not just a check at a constant example.

### 83.3 Build any finite diagram by ordinary constructor applications

For B:U_b define the value type

\[
\operatorname{Diagram}_{b,r}(B)=
\Sigma(C:B).
\Sigma(R:(y:B)\to U_r).
\Pi(y:B).\operatorname{Maps}(R(y),\operatorname{Path}_B(C,y)).
\]

This type is in U_max(b,r+1). Its fields are a canonical value C, a realization family R, and its maps and witnesses. It retains the realized construction as R and its executable maps; it is not a quotient which forgets residual constraints or routes. Ordinary reference DAGs retain sharing. Source labels can remain attached as provenance without participating in semantic keys.

`zero(B,C)` has R(y)=Path_B(C,y) and the identity maps. Its realization level is b.

The dependent extension constructor takes

\[
A:U_a,\ t:A,\ Q:(x:A)\to(t=x)\to\operatorname{Diagram}_{b,r}(B).
\]

Its result has realization level max(a,r), canonical value `C₀=C_(Q(t,refl))`, and family

\[
R'(y)=\Sigma(x:A).\Sigma(e:t=x).R_{Q(x,e)}(y).
\]

For each y, instantiate §83.2 at `D(x,e)=R_(Q(x,e))(y)`. Compose that singleton presentation with the maps of `Q(t,refl)` at y using §83.1. Concretely, if s_c,s_d,s_h,s_k are the singleton maps and q_c,q_d,q_h,q_k are the centre tail's maps, then

\[
\begin{aligned}
c'&=q_c\circ s_c,&d'&=s_d\circ q_d,\\
h'(w)&=\operatorname{ap}(s_d)(q_h(s_cw))\cdot s_h(w),&
k'(z)&=\operatorname{ap}(q_c)(s_k(q_dz))\cdot q_k(z).
\end{aligned}
\]

Every field is now specified by an ordinary term. No evaluator rule dispatches on a DiagramId or allocates a new native handler.

The host array in §39 elaborates by a right fold of this constructor ending in zero. A runtime program constructs the same values by the same functions. Tail dependencies stay under ordinary binders, and shared predecessor references remain shared. The number of constructed nodes is not a compile-time parameter of the constructor. A recursively computed finite diagram is supported to the extent that its producing core program terminates; there is no assumption that every recursively defined producer terminates.

Residual descriptions use the same extension with an arbitrary terminal family Z(x,e,…) and a terminal identity presentation. Retain those constraints. Ordinary diagrams are the case whose terminal family is an output path.

These values provide runtime construction of the required semantic diagrams. They are not claimed to be a quotation datatype for every piece of C implementation syntax. Full reflection of the checker/evaluator is a distinct status item in §87.

### 83.4 Action on runtime-computed diagrams

Given runtime L:Diagram(B), R:Diagram(B), p:Path_B(C_L,C_R), y:B, define

\[
\begin{aligned}
F(L,R,p,y,r)&=d_R(y)(p^{-1}\cdot c_L(y)(r)),\\
G(L,R,p,y,s)&=d_L(y)(p\cdot c_R(y)(s)).
\end{aligned}
\]

These are the existing §42 expressions, now parameterized over the diagram values themselves. The host compiler specializes this ordinary definition; it does not own a stronger operation than the running language. L, R and p may each be computed by programs. Their fields remain lazy references.

`review_generic_identity_action.c` constructs and checks both complete functions with L, R, p, y and the realization argument universally bound. Its only free assumption is B:U₀; no specific diagram pair is imported. Both functions check with zero registered transforms on the current core.

For the middle path-space maps `f(q)=p⁻¹·q`, `g(s)=p·s`, the two inverse paths are

\[
\begin{aligned}
h(q)&=\operatorname{assoc}(p,p^{-1},q)^{-1}
 \cdot\operatorname{ap}(\lambda v.v\cdot q)(\operatorname{rinv}(p))
 \cdot\operatorname{lunit}(q),\\
k(s)&=\operatorname{assoc}(p^{-1},p,s)^{-1}
 \cdot\operatorname{ap}(\lambda v.v\cdot s)(\operatorname{linv}(p))
 \cdot\operatorname{lunit}(s).
\end{aligned}
\]

Here assoc has orientation `(p·q)·r = p·(q·r)`, rinv is `p·p⁻¹=refl`, and linv is `p⁻¹·p=refl`. Compose these maps and witnesses with L's collapse and R's expansion using §83.1. This gives the full action and both inverse proofs, not merely functions with compatible types.

For precise lowering of these groupoid witnesses, use the following finite construction, not new trusted axioms. Path induction is the ordinary term

\[
J(P,d,b,p)=\operatorname{coe}^{i}P(p@i,\langle j\rangle p@(i\wedge j))\ d.
\]

Generate each named groupoid law by path induction on its path arguments from left to right, retaining later endpoints and paths under Π in the motive. The base case has all paths refl. For any word w built from refl, inverse and concatenation at a point a, construct K(w):w=refl recursively:

* K(refl)=refl.
* K(v⁻¹)=ap(inverse,K(v)); inverse(refl) is the constant path by its definition.
* K(v·w) is `⟨k⟩(K(v)@k)·(K(w)@k)` followed by K(refl·refl).
* `K(refl·refl)@k@i = fill^j_A [(i=0)↦a,(i=1)↦a] a (¬k)`.

The equality between two base words u,v is K(u)·K(v)⁻¹. This terminates structurally and emits only the existing coe/fill/path constructors. It specifies the base evidence even where constant hcomp is not judgmentally regular. Register each resulting law as one fixed typed template per level tuple; do not repeat this generation at each invocation.

### 83.5 The other existing schemas remain ordinary values

For supplied e:Equiv(X,Y), take `c=fst(e)`. The inverse d(y) is the X-coordinate of the centre of `(snd e)(y)`. Its k(y) is the centre's path `c(d(y))=y`; h(x) is `ap(fst)` of that fibre's contraction at `(x,refl)` in the fibre over c(x). This yields Maps(X,Y) without inverse search.

A residual equivalence composes the two residual presentations with those maps. For CUT_TO_PATH retain exactly §44's maps `(z,u,v)↦u·v⁻¹` and `h↦(D,h,refl(D))`. Their inverse witnesses are obtained by the same path-induction lowering in §83.4: eliminate h for the path-space round trip; for the cut round trip eliminate v:D=z then u:C=D (reverse u first when using induction anchored at D), keeping the other dependent data in the motive. At refl bases use K for path components, Σ paths for the tuples, and the displayed centre. No loop is discarded.

For COLLAPSE_FIBRE, with k:Πb.Contr(R b), the maps are `fst` and `λb.(b,fst(k b))`. The first inverse path at `(b,r)` is `⟨i⟩(b,(snd(k b)(r))@i)`; the other is refl(b). k is an ordinary argument and may be computed at runtime.

All five previous certificate schemas therefore have ordinary typed value counterparts. Keep their host certificate/source records for provenance, import validation and specialization. Do not make those host records prerequisites for applying a value already admitted by the core typing rules.

## 84. One witness interface across supplied and produced identities

### 84.1 The uniform execution rule

A supplied proof and a proof computed by evaluation have the same type and enter the same action term. The elaborator must not dispatch on their provenance. `compile_identity` is a source adapter which produces/specializes the §83.4 term; it is not a mandatory runtime installation step.

For an explicitly passed action value, application uses existing APP, projection, substitution and cubical composition. No new native agent type is required. Existing APPLY_TRANSFORM/CONTINUE_REFERENCE may remain a specialization of this route with the same typed body and recorded cost. Do not add independent runtime handlers for the five evidence schemas.

The host source adapter should export an ordinary Diagram term and its occurrence evidence for each checked source diagram. Memoize this pure export by the complete structural diagram/boundary key. The exported term's c,d fields must compare by conversion to the current emitted collapse/expand templates. Its h,k must check at their stated types. The source diagram's extra residual constraints stay in its terminal family.

Where a runtime producer constructs the same value, §76 supplies structural sharing and §78 supplies established-reduction sharing. Source provenance can distinguish occurrences without forcing duplicate mathematical producers. Do not turn paths between values into untyped aliasing of the values.

### 84.2 Reuse along an arbitrary known identity

For a family O:B→U, p:x=y and a:O(x), the general reuse operation is

\[
\operatorname{reuse}(O,p,a)=\operatorname{coe}^{i}O(p@i)\ a:O(y).
\]

This is already an ordinary core program. §78's definitional reduction receipts are a particularly direct source of reusable facts; they are not the only admissible evidence. A propositionally established identity supplies transport, with its residual and actual cost, instead of permission to substitute one cached WHNF class for another.

Evidence is retained as a reference. Its already-completed computations are shared by the same producer mechanism. A map on evidence is a scope view where the existing substitution law applies, not a traversal replaying the derivation. Evaluating the resulting transport is still computation; reuse does not assert it is free.

A finite prefix receipt for t⇒u can be exposed once that prefix and its premises are committed, even if later work on u is pending. It is available through the same source/map/face/dependency rules as a completed prefix in §78. No fabricated proof of the unfinished suffix is published. Publishing the prefix must not mark the whole evaluation READY.

This closes the value-level compile/run distinction for these constructions. It does not replace a missing inference algorithm by the phrase “the identity is available.” Constructing a witness, passing it, applying it, and retaining its completed work are now all specified operations.

## 85. The interaction-length obligation must refer to the actual machine

The equal-length theorem in `docs/index.html` §5.13 takes a one-step diamond for a particular relation Step and a finite trace to a normal form. Its conclusion is about that relation. It does not follow from type safety, from two local rule schemas inside a larger evaluator, or from a same-key one-producer invariant alone.

V9 §78.5 expressly allows a different claim: opportunistic discovery may change the selected reuse graph and work. This is adequate as a statement of that implementation's observed behavior; it is not completion of the user's stronger equal-interaction-length requirement. Do not present its qualified schedule comparison as that theorem.

The attached finite executable model makes the distinction precise. There are independent generic and instance requests. If the instance runs first, it computes directly. If the generic result becomes ready first, the instance uses a two-step adapter. Both terminate with the same answers, but lengths are two and three and their first steps have no one-step join. The model is not alleged to reproduce a particular C timing. It shows that ready-state-sensitive recipe choice plus memoization does not imply the required diamond. One request reads readiness another request changes; disjoint principal-pair reasoning cannot simply be applied to those two transitions.

Accordingly the full interaction-length requirement remains a proof obligation on a concrete whole-machine local transition relation, including producer cells, subscriptions, structural maps, receipt propagation and cost frames. Its proof must account for reuse becoming available during evaluation. Fixing a reuse graph proves a conditional result about that graph; it does not prove that all identities have been incorporated into a uniquely forced initial graph.

Likewise, counting C instructions as new fine steps establishes a cost measure; it does not by itself prove that C work is within a constant factor of the earlier coarse interaction count. To claim that factor, exhibit the simulation from the chosen native relation, a uniform bound for each simulated step and charged administrative work. The bounded-helper implementation in §81 is necessary to this audit, not a substitute for the simulation theorem.

The worker should preserve actual counters and the selected dependency graph, finish the specified reusable core, and avoid claiming this theorem from schedule tests. Resolving the native relation and proof is specification-author work, not an invitation to choose an optimizer or a fallback search.

## 86. Declaration-to-answer is distinct from executing a supplied action

The source's §5.27 asks for more than the evaluator/compiler implemented here. It asks that posing a declaration with its identities produces a computation whose normalization yields an inhabitant or establishes absence. The currently exposed interfaces check, convert, observe or apply supplied terms. None is a specified general posing operation from a type to an answer-producing interaction object.

For a constructive complete handoff of that additional feature, the missing component must have explicit input/output types and term/agent equations. In particular it must explain how a request for Q becomes a computation yielding an a:Q without assuming such an a in its input, and how its supported obstruction outcomes are represented and justified. “Normalize Q” observes the type expression; it is not by itself a construction of an inhabitant of Q. “Take the centre of a contraction” presupposes a supplied contraction.

This distinction is already explicit in the repository's `research/PNP_GEODESIC_REDUCTION_20260916.md`, A2–A5. The fibre of a truncation is described conditional on a point of the truncation; forming a type, receiving a witness and deciding inhabitation are different judgments. The unique-fold theorem likewise takes an existing derivation as input. Its recursor reads each derivation; uniqueness of that reader does not construct a derivation from two endpoints.

The diamond theorem settles neither this posing operation nor termination. A deterministic relation `n→n+1` has the one-step diamond and no normal form. Its valid equal-length theorem does not produce a finite obstruction report. Nontermination allowed by the source and the runtime cannot silently be identified with a completed proof of absence.

If the full claim additionally requires a guaranteed finite inhabitant-or-obstruction decision for every arbitrary computably represented goal, including termination goals for this machine, that total effective claim is incompatible with unrestricted computation. For a program e, a finite halting-trace type is inhabited exactly when e halts. A total procedure returning either a witness or a sound decisive absence result would decide halting. Permitting a pending or infinite execution avoids that contradiction; it also does not meet the stated total finite-decision claim. This is a precise qualification of that claim, not a reason to discard executable identities or the uniform construction above.

No replacement inference/search algorithm is invented in this amendment. There is no faithful concrete implementation of an unspecified posing rule to give the worker. The generic arbitrary-goal completion claim therefore cannot currently be signed off. Domain-specific constructive introductions/identities can still produce answers through the fully specified ordinary programs; their actual definitions determine what they compute.

### 86.1 Recursive program typing is not a total-proof certificate

There is a second, concrete semantic distinction in the current implementation. On `3a0d7c4`, register

```text
loop : (X : U₀) → X
loop := loop
```

`check_admission` returns VALID, checking `loop` at that type returns VALID, and `observe_checked` returns W_STUCK with no result. `review_recursive_proof_boundary.c` reproduces this. The type itself is expressible using only the existing Π and universe constructors; no Empty or Nat primitive is needed.

This behavior is consistent with a type system for partial programs. It is not a total constructive inhabitant of `(X:U₀)→X`. The provisional-claim mechanism prevents some circular cache errors; it does not prove termination or guard recursion merely by checking a recursive body under its own declared signature. Requiring only WHNF would not fix the logical issue: a lambda can hide the same divergence in its body.

Consequently a compiled record must not acquire an unconditional mathematical proof/equivalence guarantee solely because its evidence has CK_VALID typing in an unrestricted recursive signature. Preserve the distinction between operationally typed code, a committed logical premise, and a total or appropriately guarded proof. Evidence imported as an explicit assumption remains a conditional assumption; it must not be mistaken for a theorem proved by a recursive definition.

The immediate precise requirement is that any unconditional proof-admission claim account for the recursive components on which the evidence and its types depend. A checked well-founded recursion or a guarded recursion rule for a declared coinductive type can discharge the corresponding obligation. Merely reaching a signature SCC fixed point cannot. The current specification has not supplied those certificate types and recursion rules; choosing them is further author-side work. Do not patch this by rejecting all executable recursive programs or by treating W_STUCK as a proof of emptiness.

The supplied recursive-boundary source is a diagnostic of the current contract, not an acceptance test demanding that the contract remain unchanged. Its observed VALID/W_STUCK combination must be cited when stating what current checks establish. The ordinary generic witnesses in §83 require no recursive globals and do not depend on this issue.

## 87. Worker instructions and completion status

### 87.1 Implementable work

Continue §§74–82 and add §§83–84. Preserve the accepted runtime and all its validation checks. Implement the fixed templates for Maps, presentation composition, the dependent singleton including h/k, diagram zero/extension, and the generic runtime identity action. Export host diagrams through this same construction. Retain the existing source certificate schemas and compare their maps against the exported ordinary terms.

Acceptance must cover:

1. The three attached existing-core witnesses pass unchanged: generic dependent down/up/h/k check; computed presentation arguments execute with zero registered transforms; and both fully parameterized identity actions check with no prepared diagram pair.
2. A core program constructs a nonempty diagram using runtime-computed tail data and applies a runtime-computed identity. It must not call a host compiler after evaluation starts.
3. Reify each existing §47 example through the ordinary presentation export; check both inverse witnesses and compare old/new maps at their expected types. Nontrivial loop residuals remain.
4. The zero/node and action constructions commute with simultaneous term/dimension substitution, including dependent types, scope metadata and required faces.
5. An identity obtained from an earlier computation is passed to the same action definition used for a supplied identity. Repeated computation and adaptation satisfy §§74–82's producer-count requirements.
6. An unavailable guard, malformed nested scope, wrong level or uncommitted premise is still rejected. A cyclic proof produces no fabricated successful action result.
7. Record actual adaptation work and retain the selected graph. Do not label a fixed-graph comparison as a proof of adaptive equal-length normalization.

The three supplied C sources are review witnesses, not production changes. Use fixed templates and existing shared environments in production; do not copy the host-building code into every call. The worker still owns implementation and integration testing of the complete constructor family and the v9 reuse changes.

### 87.2 Exact status

| Requirement | Status after this amendment |
| --- | --- |
| Accepted cubical evaluator, checker, scopes and prior compiler | Existing implementation, with the previously reviewed fixes |
| Eight measured administrative sharing boundaries | Specified in §§74–82; worker implementation still required |
| Runtime proof parameter for a prepared pair | Specified in §80 |
| Runtime construction of semantic diagram/presentation values and their actions | Derived explicitly in §§83–84; foundational generic terms checked on the existing C core |
| Same execution mechanism for supplied and produced identity values | Specified in §84; no per-proof host registration required |
| Unconditional logical proof admission in the presence of general recursive globals | Not established; §86.1 has a concrete VALID/W_STUCK reproduction and the required distinction |
| Full self-representation and execution of the checker/compiler/evaluator as object-language programs | Not supplied by these sections; semantic diagram values do not constitute a reflected implementation of the whole kernel |
| Full native interaction diamond including adaptive reuse | Not proved; §85 identifies the exact unsupported inference |
| Constant-factor refinement from that native interaction relation to C work | Not proved; bounded helpers and a simulation theorem are required |
| General declaration-to-answer posing operation | Not specified by the current executable construction; §86 gives the missing interface and the limit of the cited arguments |
| Universal finite answer-or-obstruction procedure over unrestricted computation | Cannot be promised as an effective total operation |

The prior useful construction remains useful. These statuses must not be compressed into “everything is done” or into a percentage. In particular this package closes a concrete runtime-construction boundary and records the remaining mathematical/representation gaps explicitly; it is not a full-system sign-off.
