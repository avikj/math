# A Proof-Relevant Interaction Calculus in Cubical Type Theory

**A local-first computational prototype for partial knowledge, certified transport, and compositional interaction for decentralized organisms & algorithms**

This repository defines a computational model in which data, program, execution, proof, and transport are different views of the same evolving symbolic object.

The central primitive is a partially known local state equipped with computable paths describing how that state may transform while preserving what is already valid.

Two states interact. The interaction may reveal information, derive information, exchange information, reconcile representations, execute programs, or construct new programs. The result includes a symbolic trace of the transformation itself: what was learned, what changed, which distinctions were preserved, which boundary conditions applied, and how the resulting state relates to its antecedents.

The fundamental transition is

```math
(\text{state}_A,\text{state}_B)
\;\longrightarrow\;
(\text{state}'_A,\text{state}'_B,\tau)
```

where $\tau$ is simultaneously:

- an execution trace,
- a provenance object,
- a transport witness,
- a proof object,
- a reconciliation record,
- and a potentially executable symbolic object.

The machine is an interactive symbolic computer for partial-information computation.

Its unit of accumulated value is not a scalar weight. It is a trace.

```math
\boxed{\text{weights} \Rightarrow \text{traces}}
```

---

## 1. Flow-persistent computational objects

A computational object is represented as a flow-persistent continuant:

```math
X = (\text{identity},\text{invariants},\text{modes}).
```

Its current mode may change while its relevant identity persists.

The primitive relation between two representations is therefore not restricted to syntactic equality,

```math
x \equiv y,
```

but includes structured paths

```math
p : x = y
```

whose computational content specifies how one representation becomes the other.

In Cubical Agda, paths are computational objects. Transport along paths computes. Univalence turns equivalences into paths.

Given

```math
e : A \simeq B,
```

univalence produces

```math
\mathrm{ua}(e) : A = B.
```

Transport along this path computes according to the equivalence:

```math
\mathrm{transport}(\mathrm{ua}(e)) : A \to B.
```

A proof of equivalence therefore participates directly in execution.

The transformation is not merely justified by a proof external to it.

```math
\boxed{\text{the proof is executable transport}}
```

## 2. Computable cubical transport

The primitive operation is

```math
\mathrm{transport} :
(A = B) \to A \to B.
```

Suppose two peers represent the same semantic object differently:

```math
A = \text{representation}_1
```

and

```math
B = \text{representation}_2.
```

A certified equivalence

```math
e : A \simeq B
```

induces a path between those representations.

A value crosses the representation boundary as

```math
a:A
\quad\xrightarrow{\mathrm{transport}(\mathrm{ua}(e))}
\quad b:B.
```

The stored computational object is not only $b$. It contains the transport relation:

```math
(a,e,b).
```

More generally, computation accumulates a path history

```math
a
\xrightarrow{p_1}
x_1
\xrightarrow{p_2}
x_2
\xrightarrow{p_3}
\cdots
\xrightarrow{p_n}
b.
```

That history is the trace.

A trace records semantic motion through representation space.

## 3. Weights to traces

Conventional systems repeatedly compress value into scalar quantities:

```math
\text{score},\quad
\text{probability},\quad
\text{loss},\quad
\text{price},\quad
\text{rank},\quad
\text{reward},\quad
\text{reputation}.
```

A scalar is a low-bandwidth projection of a richer process.

It may report that value changed while discarding:

- how it changed,
- through whom,
- from which antecedents,
- under which transformation,
- with which evidence,
- across which boundary,
- according to which semantics.

The machine stores the richer object.

```math
\boxed{\text{weight} = \pi(\text{trace})}
```

for some projection

```math
\pi : \mathrm{Trace} \to S
```

where $S$ may be a scalar, ranking, probability, score, price, or other summary.

The reverse map is generally not available:

```math
S \not\to \mathrm{Trace}.
```

Therefore the trace is canonical and the scalar is derived.

A score is a bandwidth-limited view.

The trace is the materialized value.

## 4. Materialized value

Value is represented by the transformation history that produced it.

For an interaction between two states,

```math
A \otimes B
\longrightarrow
(A',B',\tau),
```

the trace $\tau$ can contain:

```math
\text{provenance},
\quad
\text{causal contribution},
\quad
\text{semantic relation},
\quad
\text{proof},
\quad
\text{boundary conditions},
\quad
\text{reconstruction data}.
```

The value is no longer stored only as a number attached to a node.

It is materialized in the symbolic relation itself.

Financial value, semantic value, epistemic value, optimization value, and provenance all instantiate this pattern:

```math
\text{interaction}
\longrightarrow
\text{structured change}
\longrightarrow
\text{trace}.
```

A scalar may summarize the trace for a human or machine operating under a bandwidth constraint.

The scalar is not the ontology.

## 5. Partial information is the native state

A peer does not require complete global knowledge.

Its state is a partial observation

```math
K_A : \mathcal{U} \rightharpoonup \mathrm{Value},
```

where $\mathcal{U}$ is a universe of propositions, objects, relationships, programs, measurements, or observations.

Another peer holds

```math
K_B.
```

Neither is required to possess a complete authoritative state.

Interaction computes directly from partial knowledge:

```math
K_A \otimes K_B
\longrightarrow
(K'_A,K'_B,\tau).
```

In general,

```math
K'_A \neq K'_B.
```

Successful interaction does not require state identity.

It requires explicit compatibility where compatibility is needed, explicit divergence where divergence remains, and witnesses for the transformations that occurred.

Consensus is therefore not the universal primitive.

```math
\boxed{\text{certified interaction is the primitive}}
```

## 6. Knowledge revelation and knowledge generation

Interaction may reveal knowledge already present on one side.

Before:

```math
A:x,\qquad B:?
```

After:

```math
A:x,\qquad B:x.
```

Interaction may also generate knowledge that existed on neither side independently.

```math
K_A \otimes K_B \to K_C
```

with

```math
K_C \not\subseteq K_A,
\qquad
K_C \not\subseteq K_B.
```

The encounter itself performs computation.

The primitive is therefore an interactive knowledge revelation/generation process.

"Knowledge" here is typed broadly.

It may denote:

- mathematical knowledge,
- scientific knowledge,
- historical lineage,
- provenance,
- information,
- semantic content,
- financial value,
- optimization information,
- boundary knowledge,
- executable capability.

The common structure is a change in what can subsequently be established, reconstructed, transmitted, or done.

## 7. Zero knowledge as controlled transport

A zero-knowledge proof changes the verifier's epistemic state:

```math
K_V
\longrightarrow
K'_V
```

while preserving a boundary on what may be learned.

The verifier gains justified knowledge without receiving the prohibited witness.

The general computational form is:

```math
(\text{private state},\text{public interface})
\longrightarrow
(\text{new justified state},\tau)
```

subject to constraints on disclosure.

The interaction specifies:

```math
\text{what may cross},
```

```math
\text{what must remain hidden},
```

```math
\text{what may be derived},
```

```math
\text{what must remain reconstructible},
```

and

```math
\text{what witness certifies the resulting state}.
```

Privacy, disclosure, proof, and computation are boundary conditions on transport.

## 8. Conservative computation

A transformation is conservative when it does not silently erase previously valid distinctions.

If

```math
S \hookrightarrow S',
```

then information established in $S$ remains recoverable from $S'$ unless invalidation itself is represented.

The preservation condition is

```math
\mathrm{Valid}(S)
\subseteq
\mathrm{Recoverable}(S').
```

Conservativity applies to semantic information, not byte identity.

A representation may:

- rewrite,
- normalize,
- compress,
- specialize,
- reorganize,
- migrate,
- factor,
- inline,
- partially evaluate.

The rewrite remains conservative when the relevant prior semantics can be reconstructed or transported through a witness.

Therefore:

```math
\boxed{\text{self-rewriting} + \text{conservative}}
```

is a single design condition.

The system may transform its own representation while preserving declared invariants.

## 9. Lossless transport

Lossless does not mean unchanged.

It means that a transformation preserves the information declared invariant by its interface.

For an equivalence

```math
f:A\to B,\qquad
g:B\to A,
```

with witnesses

```math
g(f(a)) = a
```

and

```math
f(g(b)) = b,
```

transport from $A$ to $B$ is certified by its recoverability structure.

Representation preservation and information preservation are distinct:

```math
\text{representation preservation}
\neq
\text{information preservation}.
```

The machine preserves the latter.

A transformation may be radically different in representation while remaining exact in semantics.

## 10. Data, program, execution, proof, transport

Once transformations are first-class symbolic objects, conventional category boundaries become projections of one structure.

A trace is data because it can be stored.

A trace is program because it specifies a transformation.

A trace is execution because constructing it performs the transformation.

A trace is proof because its type constrains which transformations can inhabit it.

A trace is transport because it carries an object between representations or states.

These are different interfaces onto one typed symbolic object:

```math
\begin{array}{rcl}
\mathrm{store}(\tau) &:& \text{data},\\
\mathrm{execute}(\tau) &:& \text{program / execution},\\
\mathrm{type}(\tau) &:& \text{proof obligation},\\
\mathrm{apply}(\tau) &:& \text{transport}.
\end{array}
```

The claim is not that these interface types are pairwise equivalent. The same trace can be stored, executed, checked, and applied through each interface.

## 11. Metacircular execution

Traces are executable objects.

Therefore traces may transform traces.

Given

```math
\tau : A \rightsquigarrow B,
```

another transformation may act on $\tau$:

```math
\Phi(\tau) : A' \rightsquigarrow B'.
```

The transformer $\Phi$ can itself be represented as a trace.

The machine is therefore metacircular:

```math
\text{programs transform programs},
```

```math
\text{proofs transform proofs},
```

```math
\text{transports transform transports}.
```

Self-modification occurs inside the same typed substrate used for ordinary computation.

A self-rewrite is accepted when its witness inhabits the required preservation type.

```math
\boxed{\text{self rewriting becomes proof-carrying rewriting}}
```

## 12. Composition

Local transformations compose.

Given

```math
p:A=B
```

and

```math
q:B=C,
```

path composition produces

```math
p\cdot q:A=C.
```

At the trace level:

```math
\tau_{AB} \circ \tau_{BC}
=
\tau_{AC}.
```

A distributed history therefore forms a compositional structure of witnessed transformations.

Different histories may connect the same endpoints:

```math
A
\overset{p}{\longrightarrow}
B,
\qquad
A
\overset{q}{\longrightarrow}
B.
```

Those histories need not be identified.

Their difference may encode provenance, causal ordering, cost, authority, privacy, or semantic route.

A higher path may relate them:

```math
\alpha:p=q.
```

Relations among transformations therefore become first-class structure.

Cubical computation makes this higher-dimensional structure executable.

## 13. Braid fabric topology

A distributed history is not fundamentally a linear log.

Independent interactions may occur concurrently:

```math
A \xrightarrow{p} A'
```

and

```math
B \xrightarrow{q} B'.
```

Other interactions may cross their causal futures:

```math
A' \leftrightarrow B,
\qquad
B' \leftrightarrow C.
```

The resulting history is a braid of partially ordered, composable transformations.

The primary persistent structure consists of:

- objects,
- paths between objects,
- paths between paths,
- independent commuting transformations,
- dependent crossings,
- local observations of shared history.

The network is therefore represented as

```math
\boxed{\text{a fabric of composable witnessed interactions}}
```

rather than as a set of machines attached to a central state.

Machines hold local sections of the fabric.

## 14. Local-first state

Each participant owns its local state.

No operation requires an authoritative server to decide what an object is.

A node can:

1. compute locally;
2. construct traces locally;
3. verify received traces locally;
4. reveal only selected information;
5. transport data across certified interfaces;
6. merge compatible knowledge;
7. retain unresolved divergence.

If peers hold local states

```math
S_1,S_2,\ldots,S_n,
```

the system does not require a privileged stored state $S^*$.

The distributed object is reconstructed from compatible local states and their relations:

```math
\{S_i,\tau_{ij}\}.
```

Global structure is formed by gluing local knowledge through explicit transport.

## 15. Decentralized identity

A location-bound identifier has the form

```
host/path/object.
```

Its identity depends on administrative and infrastructural continuity.

The machine separates identity from location.

Conceptually,

```math
\mathrm{ID}(x)
=
H(
\text{semantic content},
\text{type},
\text{provenance},
\text{relations}
).
```

Location becomes routing information.

Identity belongs to content and its witnessed relations.

This permits the same computational object to move among personal devices, edge processors, vehicles, robots, satellites, temporary clusters, datacenters, and archival physical infrastructure.

The address may change without changing the object.

## 16. Pairwise interaction as the unit of value formation

Two states may contain information whose value is not visible independently.

Before interaction:

```math
V(A),\qquad V(B).
```

After interaction:

```math
V(A\leftrightarrow B).
```

In general,

```math
V(A\leftrightarrow B)
\neq
V(A)+V(B).
```

The interaction may reveal compatibility, contradiction, complementarity, novelty, provenance, trust, arbitrage, coordination opportunity, or new proof.

The edge generates information.

Therefore the persistent unit is

```math
(A,B,\tau_{AB}).
```

Repeated pairwise interaction produces a graph of traces.

Composition turns the graph into a braid of provenance and transformation.

The accumulated symbolic interaction history is the materialized value.

## 17. Interactive autonomy

The system combines autonomous local state with collaborative computation.

A participant does not surrender its entire internal state to join a collective process.

Its boundary determines:

```math
\text{what is revealed},
```

```math
\text{what is transported},
```

```math
\text{what is derived},
```

```math
\text{what is retained},
```

```math
\text{what is accepted}.
```

Collaboration occurs through explicit interfaces and witnessed transformations.

Autonomy resides in control of the local state and boundary.

Collective intelligence resides in the compositional interaction fabric.

```math
\boxed{
\text{interactive autonomy}
=
\text{local sovereignty}
+
\text{composable exchange}
}
```

## 18. Jain ontology as executable computational semantics

The computational ontology corresponds directly to the Jain ontology of persistence-through-transformation.

A real computational object is not static substance and not a sequence of unrelated moments.

It is a persistent continuant with real successive modes.

```math
\text{continuant}
+
\text{invariants}
+
\text{successive modes}.
```

The correspondence is:

| Jain structure | Computational semantics |
|---|---|
| *dravya* | flow-persistent computational continuant |
| *gua* | preserved invariant/interface |
| *paryya* | current computational mode |
| *utpda* | construction of a new mode |
| *vyaya* | cessation of the prior mode |
| *dhrauvya* | identity preserved through transformation |
| *aneknta* | irreducibility to one representation or projection |
| *naya* | explicit partial view/interface |
| *syt* | assertion indexed by view, context, or boundary |
| *ahis* | non-destructive transformation |
| *savara* | controlled boundary preventing invalid ingress |
| *nirjar* | removal of accumulated obstructive state |
| *moka* | complete removal of extrinsic binding without destruction of identity |

Different projections of one object may all be valid:

```math
\pi_1(X),
\pi_2(X),
\ldots,
\pi_n(X).
```

No projection is thereby promoted to the complete object:

```math
\pi_i(X) \neq X.
```

Each projection carries an explicit domain of validity.

Composition transports information between projections while retaining the witness of that transport.

Partiality resides in the view, not as an assumed defect in the underlying object.

This is the computational reading of anekānta–naya–syāt:

```math
\boxed{
\text{many-aspected object}
+
\text{partial view}
+
\text{indexed assertion}
}
```

The corresponding safety condition is ahis.

A transformation does not obtain a new state by silently destroying distinctions required to reconstruct the old one.

A rewrite may change representation, organization, location, or execution strategy while preserving the declared invariant through a computational witness.

The basic computational object is therefore:

```math
\boxed{
\text{a flow-persistent symbolic continuant whose identity is carried by computable, composable, witnessed transformation}
}
```

## 19. The Interactive Symbolic Computer

The machine state consists of:

```math
\mathcal{M}
=
(
K,
T,
B,
I
)
```

where

- $K$ is local partial knowledge,
- $T$ is the local trace fabric,
- $B$ is the interaction boundary,
- $I$ is the invariant structure governing admissible transformation.

An interaction between machines

```math
\mathcal{M}_A
\quad\text{and}\quad
\mathcal{M}_B
```

produces

```math
\mathrm{Interact}
(
\mathcal{M}_A,
\mathcal{M}_B
)
=
(
\mathcal{M}'_A,
\mathcal{M}'_B,
\tau
).
```

The trace $\tau$ is checked against both boundaries and the relevant invariants.

The transition is admitted only when the required proof objects compute.

The machine therefore performs:

```math
\text{interaction}
\to
\text{knowledge change}
\to
\text{witnessed transport}
\to
\text{new executable state}.
```

There is no separate semantic layer that must later explain what happened.

The semantic relation is carried by the trace.

## 20. Trace algebra

A trace may be represented abstractly as

```math
\tau =
(
s,
t,
p,
c,
b,
\mu
)
```

where

- $s$ is the source state,
- $t$ is the target state,
- $p$ is the transport proof,
- $c$ is causal/provenance structure,
- $b$ is boundary metadata,
- $\mu$ is semantic meaning.

The precise representation may vary.

The algebraic requirements are identity, composition, inversion where available, and higher coherence.

**Identity**

```math
\mathrm{id}_A : A \rightsquigarrow A
```

**Composition**

```math
\tau_1 : A \rightsquigarrow B,
\qquad
\tau_2 : B \rightsquigarrow C
```

produce

```math
\tau_2 \circ \tau_1 : A \rightsquigarrow C.
```

**Inversion where available**

For reversible transports,

```math
\tau^{-1} : B \rightsquigarrow A.
```

**Higher coherence**

If two composites represent the same semantic transport,

```math
\tau_1 \circ \tau_2
```

and

```math
\tau_3 \circ \tau_4,
```

their coherence is itself represented:

```math
\alpha : (\tau_1 \circ \tau_2)
=
(\tau_3 \circ \tau_4).
```

The trace fabric therefore carries both transformations and relations among transformations.

## 21. Proof-carrying state transition

A state transition has the form

```math
(S,\tau) \mapsto S'
```

where the trace inhabits a type that states the admissibility condition.

For an invariant $P$,

```math
P(S)
```

and transformation $f$,

```math
f:S\to S',
```

the transition requires a witness

```math
w :
P(S) \to P(S').
```

The system executes the transition together with the witness.

For reversible transformations, the stronger condition is an equivalence:

```math
S \simeq S'.
```

For conservative extensions, the condition may be an embedding:

```math
S \hookrightarrow S'.
```

For partial revelation, the condition may be a refinement relation.

Different interaction classes therefore use different transport structures, while preserving the same architecture:

```math
\boxed{
\text{state change}
+
\text{typed witness}
}
```

## 22. Self-rewriting machine

Because the state contains executable symbolic structure, the machine may rewrite its own programs.

Let

```math
P
```

be a program represented inside the state.

A transformation

```math
R : P \rightsquigarrow P'
```

is accepted when it carries the required preservation witness.

For semantic equivalence:

```math
R :
P \simeq P'.
```

For optimization preserving extensional behavior:

```math
\forall x,\;
P(x)=P'(x).
```

For partial refinement:

```math
\mathrm{Behavior}(P')
\subseteq
\mathrm{Allowed}(P).
```

The rewritten program becomes part of the next state.

The same mechanism applies to schemas, protocols, proofs, compilers, interpreters, optimizers, policies, interfaces, and transport rules.

The machine can therefore rewrite the machinery by which it rewrites.

That recursion remains inside the proof-carrying substrate.

## 23. Distributed execution without global state

A conventional distributed execution often seeks a single serializable history.

This machine does not require one except where an application invariant demands it.

Independent operations remain independent.

Commuting transformations form a square:

```math
\begin{array}{ccc}
A & \xrightarrow{p} & B \\
\downarrow q & & \downarrow q' \\
C & \xrightarrow{p'} & D
\end{array}
```

with a coherence witness

```math
p\cdot q' = q\cdot p'.
```

The square records that two execution orders yield compatible results.

Cubical structure makes this commuting relation explicit.

Concurrency is represented geometrically rather than erased by serialization.

Higher-dimensional cubes encode compatibility among larger families of independent transformations.

The execution history is therefore a partially ordered geometric object.

## 24. Conflict as explicit non-coherence

When two transformations do not commute, the system does not silently collapse them.

Suppose

```math
p:A\to B
```

and

```math
q:A\to C.
```

If no coherent filler exists that reconciles them under the current invariant, the divergence remains explicit.

Conflict is represented as absence of a required path or filler.

The system may retain both branches, request more information, weaken the projection, invoke a domain-specific reconciliation, construct a new common refinement, or reject one branch under a local boundary policy.

Conflict is a first-class statement about missing transport.

## 25. Provenance is executable

A provenance chain

```math
x_0
\xrightarrow{\tau_1}
x_1
\xrightarrow{\tau_2}
x_2
\cdots
\xrightarrow{\tau_n}
x_n
```

is not passive metadata.

Because each $\tau_i$ is executable and typed, provenance supports replay, verification, rollback where inverses exist, alternative projection, causal attribution, policy checking, selective disclosure, and reconstruction.

The lineage of a value is therefore part of the computational object.

Historical knowledge and executable state share one representation principle.

## 26. Cryptographic interpretation

The trace fabric admits cryptographic commitments.

A trace can be hashed, signed, selectively disclosed, zero-knowledge proven, threshold authorized, or content addressed.

A peer may verify a transformation without possessing every hidden intermediate.

Thus:

```math
\text{proof of transport}
```

need not imply

```math
\text{full revelation of transported state}.
```

Cryptographic knowledge boundaries compose with semantic transport boundaries.

The machine can therefore represent provenance whose validity is public while some contents remain private.

## 27. Scientific knowledge

Scientific knowledge fits the same structure.

An observation is not only a scalar result.

It has instrument, calibration, protocol, raw observation, transformation, and derived claim.

The scientific object is a trace:

```math
\text{world interaction}
\to
\text{measurement}
\to
\text{transformation}
\to
\text{claim}.
```

A later investigator can inspect, recompute, refine, or transport the result into another representation.

Scientific provenance is executable.

## 28. Mathematical knowledge

A theorem is represented by its construction and dependencies.

A proof object already has the form

```math
p:P.
```

When proofs compute, mathematical knowledge becomes executable structure.

A mathematical result may therefore be transported through equivalences, specialized, generalized, composed, or reused as a program.

The same object may be consumed as evidence, transformation, executable implementation, rewrite rule, or certified interface.

## 29. Historical lineage

Historical lineage is represented as a compositional provenance path.

For an artifact $x$,

```math
x_0
\xrightarrow{\tau_1}
x_1
\xrightarrow{\tau_2}
\cdots
\xrightarrow{\tau_n}
x.
```

Each edge may represent transmission, translation, copying, transformation, interpretation, attribution, or correction.

Conflicting lineages remain distinct until a witness relates them.

The system preserves historical plurality without collapsing provenance into a single label.

## 30. Financial value

Financial value is interaction-produced and trace-dependent.

A price

```math
p_t
```

is a scalar projection of a richer market history.

The underlying value process contains counterparties, orders, constraints, timing, information, causality, transfer, settlement, and provenance.

A financial scalar therefore fits the same architecture:

```math
\text{market trace}
\to
\text{price}.
```

The price is a summary.

The transaction fabric is the generative object.

## 31. Optimization

An optimization system usually reduces a trajectory to an objective:

```math
J(\tau)\in\mathbb{R}.
```

This architecture retains $\tau$.

The scalar objective becomes one projection:

```math
J : \mathrm{Trace}\to\mathbb{R}.
```

Different objectives can evaluate the same trace without reconstructing information discarded during optimization.

The system distinguishes the trajectory that obtained the score from the score itself.

Optimization therefore operates over symbolic histories rather than replacing them.

## 32. Boundaries as first-class objects

A computational boundary specifies admissible interaction.

Let

```math
B_A
```

be the boundary of participant $A$.

Then an incoming trace

```math
\tau : X\rightsquigarrow Y
```

is admitted only if

```math
B_A(\tau)
```

is inhabited.

A boundary may encode type compatibility, authorization, privacy, reversibility, provenance requirements, semantic invariants, resource constraints, rate limits, and trust policy.

The boundary is part of the type of interaction.

## 33. Ahis as a computational invariant

The computational form of ahis is non-destructive transformation.

A transformation must not silently erase a distinction whose preservation belongs to the contract.

If a participant accepts a state transition

```math
S\to S',
```

the transition either preserves the relevant structure or carries an explicit account of what was relinquished.

The strongest form is reversible:

```math
S \simeq S'.
```

A weaker conservative form preserves embedding:

```math
S \hookrightarrow S'.
```

A still weaker controlled transformation explicitly names the loss function.

Silent destruction is excluded.

The machine therefore distinguishes transformation from obliteration.

Ahis is encoded as preservation discipline.

## 34. Aneknta as representation semantics

A computational object may support many valid representations:

```math
R_1(X),
R_2(X),
\ldots,
R_n(X).
```

No single representation exhausts the object.

Each representation exposes particular structure and suppresses other structure.

The machine records the projection explicitly.

An assertion is therefore typed not only by proposition $P$ but by its valid view:

```math
P@R_i.
```

Transport between views requires a witness.

A contradiction between

```math
P@R_i
```

and

```math
\neg P@R_j
```

does not collapse the system when $R_i\neq R_j$.

The view index is part of the proposition.

This is the executable form of many-sidedness.

## 35. Sydvda as indexed computation

A proposition is not accepted as a context-free scalar bit when its truth depends on a view.

Instead:

```math
\mathrm{Assert}(P,R,t,l,m,\ldots)
```

binds the relevant index structure.

The computational analogue of syt is therefore:

```math
\boxed{\text{assert under explicit index}}
```

An interaction may refine or change the index.

Transport then determines whether the proposition survives that change.

Truth conditions become compositional objects rather than hidden assumptions.

## 36. Savara as ingress control

A distributed system receives potentially unbounded external influence.

Savara corresponds to closure of inadmissible ingress.

Given an incoming transformation

```math
\tau_{\text{in}},
```

the local boundary checks whether the transformation satisfies the required constraints.

If not, it is not incorporated into local state.

The system therefore distinguishes received from admitted.

Ingress control is semantic, not merely network-level.

## 37. Nirjar as removal of obstructive accumulated state

Historical state may remain valid yet become operationally obstructive.

Nirjar corresponds to explicit shedding of accumulated state whose continued retention is no longer required by the active invariant.

This includes garbage collection, proof-normalization, cache elimination, dead-code elimination, history compaction, and removal of superseded obligations.

The operation is admissible only when required reconstructibility is preserved or intentionally relinquished under an explicit contract.

State reduction is itself witnessed transformation.

## 38. Moka as complete extrinsic decoupling

A computational object may carry extrinsic bindings: location, owner, server, schema, implementation, authority, or transient dependency.

A fully portable object is one whose identity and semantics no longer depend on those accidental bindings.

The computational analogue of moka is therefore complete removal of extrinsic dependency without destruction of intrinsic identity.

```math
\boxed{
\text{identity}
-
\text{extrinsic binding}
=
\text{portable self-certifying object}
}
```

## 39. Temple as executable specification

A specification normally exists separately from the artifact it governs.

Here the construction can be its own certificate when correct execution necessarily produces a measurable invariant.

The ulba geometric tradition provides a physical form of this pattern.

The construction instruction and the derivation are one operation.

A cord-stretching procedure produces the geometry whose measurement verifies compliance.

The artifact is therefore an instance of an executable specification.

Formally:

```math
\text{specification}
\xrightarrow{\text{execution}}
\text{artifact}
```

with

```math
\text{verification}(\text{artifact})
=
\text{measurement of construction invariant}.
```

Anyone with the specification and measuring apparatus can reconstruct and verify it.

## 40. Physical computation and geometry

Physical infrastructure has computational geometry.

At sufficiently low latency,

```math
\text{distance}
```

is a computational variable.

Propagation delay is bounded by physical path length and medium.

Therefore physical placement determines reachable performance.

The relevant site parameters include:

```math
\text{power source and cost curve},
```

```math
\text{thermal mass and ambient conditions},
```

```math
\text{sky view and horizon geometry},
```

```math
\text{geodesic position relative to peers},
```

```math
\text{thermal, seismic, and hydrological time constants}.
```

These parameters are measurable and operational.

The site is part of the program.

The physical structure participates in computation.

## 41. Content-bound software, location-bound physics

Mobile computation separates software identity from location.

A process may move among devices and sites.

The physical plant does not.

Power, thermal mass, horizon, land, and geodesic position remain local.

This produces a two-layer architecture:

```math
\text{software identity}
\to
\text{content-bound and portable}
```

while

```math
\text{physical compute substrate}
\to
\text{site-specific}.
```

The common requirement is a public specification whose execution certifies itself and whose identity does not depend on an institution remaining alive.

## 42. Durable knowledge substrate

A durable knowledge system needs:

- public reconstruction rules,
- redundancy across independent carriers,
- local verification,
- error detection by disagreement,
- independence from a unique master copy.

The ghana-pha and related recitational permutations instantiate this structure in human memory.

Redundant transformations of the same source permit defect localization by disagreement among frames.

The computational analogue is:

```math
\text{one semantic object}
\to
\text{multiple independently checkable encodings}.
```

No single encoding is authoritative.

Consistency emerges from cross-verification.

## 43. Content-addressed physical instances

A public construction specification can define the identity of a physical artifact.

The identity then belongs to the construction rule and invariant, not to one builder.

Conceptually:

```math
\text{specification}
=
\text{content identity}
```

and

```math
\text{constructed artifact}
=
\text{physical instance}.
```

Anyone who possesses the specification can reconstruct another instance and verify it by measurement.

This is content addressing in physical form.

## 44. Interactive partial-information internet

The network architecture that follows from these primitives is not based on globally synchronized documents at fixed addresses.

It consists of autonomous peers exchanging certified symbolic transformations.

A network message is therefore not merely:

```math
\text{payload}.
```

It is:

```math
\boxed{
\text{payload}
+
\text{type}
+
\text{provenance}
+
\text{boundary}
+
\text{transport witness}
}
```

Peers may hold different representations of the same object.

They may reveal different projections.

They may execute different local programs.

Interoperability is supplied by certified transport rather than identical implementation.

The internet becomes a fabric of locally owned symbolic states connected by composable proofs of interaction.

## 45. Protocol and semantics

Transport carries semantic witnesses.

The protocol can therefore carry:

- what type of thing moved,
- under which equivalence,
- which invariants were preserved,
- which provenance relation was added,
- which boundary authorized the move.

The transport object is semantic.

## 46. Protocol evolution

Because protocols are symbolic objects, protocol changes can themselves be transported.

Suppose version $P_1$ and version $P_2$ are related by an equivalence or refinement:

```math
e:P_1\simeq P_2.
```

Peers do not require simultaneous migration.

A participant may remain on $P_1$ while another uses $P_2$, provided transport between them is certified.

Protocol evolution therefore becomes local and compositional.

The network need not stop for a global upgrade.

## 47. Schema evolution

The same mechanism applies to data schemas.

Given

```math
S_1 \simeq S_2,
```

data transports between schemas with executable proof.

A database migration becomes:

```math
\text{schema path}
+
\text{data transport}
+
\text{round-trip or refinement witness}.
```

Schema evolution is represented as ordinary computation.

## 48. Compiler interpretation

A compiler is a transport from one executable representation to another.

```math
\text{Source}
\rightsquigarrow
\text{Target}.
```

A verified compiler supplies a witness relating source semantics and target semantics.

Compilation is therefore an instance of the same primitive as schema migration, protocol translation, proof transport, distributed reconciliation, and representation conversion.

## 49. Local compilers between worlds

Each peer may possess its own representation.

The network does not require one universal internal language.

Instead it requires certified translators.

For peer $A$,

```math
L_A
```

and peer $B$,

```math
L_B,
```

an interaction requires a transport

```math
L_A \rightsquigarrow L_B
```

for the relevant shared object.

The internet is therefore a network of local compilers between semantic worlds.

## 50. Symbolic execution as communication

When a message includes an executable trace, communication itself performs computation.

A peer may receive not only a result but the transformation required to derive it.

The receiver can replay, verify, specialize, invert, compose, partially disclose, or transport onward.

A message is therefore a portable computation.

```math
\boxed{\text{communication becomes symbolic execution}}
```

## 51. Knowledge as transportable capability

Knowledge is not represented only as stored propositions.

If a trace enables a new valid transformation, then possessing the trace changes capability.

Thus:

```math
\text{knowledge}
=
\text{what transformations are now constructible}.
```

This unifies declarative and procedural knowledge.

A theorem, protocol, proof, compiler, model, and historical provenance chain can all increase the set of admissible future computations.

## 52. Value as boundary-relative capability

Value is not intrinsic to an isolated object.

It depends on what an object permits within a boundary.

For state $S$ and boundary $B$,

```math
V_B(S)
```

denotes the usable capability exposed under $B$.

Interaction changes value by changing reachable transformations:

```math
\mathrm{Reach}_B(S)
\to
\mathrm{Reach}_{B'}(S').
```

A trace is therefore a record of value creation because it records the enlargement, restriction, or redirection of reachable capability.

## 53. Proof of transport

The universal certificate is a proof that an object moved across a boundary while satisfying the declared invariant.

Abstractly:

```math
\mathrm{PoT}(A,B,I)
=
\Sigma(p:A=B).\;I(p)
```

or, for weaker relations,

```math
\mathrm{PoT}(A,B,I)
=
\Sigma(f:A\to B).\;I(f).
```

The witness contains both transformation and admissibility.

This is the computational kernel shared by data migration, program transformation, distributed state reconciliation, scientific derivation, provenance, zero-knowledge interaction, protocol evolution, and self-rewriting code.

## 54. The primitive

The complete primitive can be written:

```math
\mathrm{Interact}
:
(A,B,\mathcal{B}_A,\mathcal{B}_B)
\to
(A',B',\tau)
```

subject to

```math
\tau :
\mathrm{PoT}
(
(A,B),
(A',B'),
I
).
```

The output is not merely new state.

It is new state together with the materialized relation that makes the transition intelligible, verifiable, composable, and executable.

Everything else in the machine is a specialization of this operation.

## 55. System properties

The system is:

**local-first** because authoritative state resides locally.

**decentralized** because identity and verification do not depend on a central server.

**partial-information native** because peers compute without requiring complete shared state.

**lossless** because declared semantic invariants are preserved through witnessed transformation.

**conservative** because previously valid distinctions are not silently destroyed.

**self-rewriting** because programs and transformation rules are first-class symbolic objects.

**metacircular** because traces can transform traces.

**compositional** because local transports compose into larger transports.

**proof-carrying** because admissibility witnesses are part of state transition.

**interactive** because pairwise encounters reveal and generate knowledge.

**symbolic** because the value-generating history is retained as structured representation.

**autonomous** because participants control their state and boundaries.

**collaborative** because local states compose through certified interaction.

## 56. Final form

The machine begins with local partial knowledge.

```math
K_i
```

Peers interact.

```math
K_i \otimes K_j.
```

Interaction produces state change and a trace.

```math
(K_i,K_j)
\longrightarrow
(K'_i,K'_j,\tau_{ij}).
```

The trace carries execution, proof, provenance, and transport.

```math
\tau_{ij}
=
\text{data}
=
\text{program}
=
\text{execution}
=
\text{proof}
=
\text{transport}
```

under different projections.

Traces compose.

```math
\tau_{ij}\circ\tau_{jk}
=
\tau_{ik}.
```

Independent traces form commuting cells.

Conflicting traces remain explicit.

Higher relations connect alternative histories.

The resulting network is a braid fabric of witnessed interactions.

Value is accumulated in the fabric.

Scalars are projections of that fabric.

```math
\boxed{\text{weights} \Rightarrow \text{traces}}
```

Identity persists through change.

Partial views remain partial.

Transport preserves declared distinctions.

Programs rewrite themselves through proof-carrying transformation.

Knowledge moves by interaction.

Knowledge is generated by interaction.

The network does not require a global observer.

The object does not require a fixed address.

The proof does not sit outside the execution.

The specification does not sit outside the construction.

The history does not sit outside the value.

```math
\boxed{
\text{Interactive Symbolic Computer}
=
\text{computable cubical transport}
+
\text{partial local knowledge}
+
\text{composable symbolic traces}
}
```

The computational substrate is the fabric of paths itself.
