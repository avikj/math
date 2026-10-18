# The implementation route from witnessed interactions to the intended system

This is a source-grounded review of the mathematical destination and the current implementation contract. It accompanies a concrete new regression and an executable-prefix specification. It does not certify unseen worker changes or turn the contextual *Witnessed Computation* PDF into a mandatory application architecture.

The reviewed implementation is `scoped-machine/` at `c365d86`. The source material is the locally retained `docs/index.html`, the repository derivation/fibre modules identified below, the v13 master `HANDOFF.md` carried by V20, the subsequent V20 review, and the bounds correction package. Implementation status and mathematical consequences are distinguished throughout.

## 1. The destination is one witnessed evolving source

The intended object is a state with typed interfaces, admissible local transitions and retained evidence. A useful general presentation is

\[
\mathcal M=(S,\operatorname{Step}:S\to S\to\mathcal U,
             \{\operatorname{Obs}_i,\operatorname{Act}_i\}_i).
\]

A finite execution is a composable chain of actual steps; a continuing execution exposes such finite prefixes on demand. A program, an identity, an observation request, an agent's action and a suspended continuation can all occur inside this source. Their C module names do not make them separate computational universes.

For an observation `q:S→B`, retaining the source fibre gives

\[
S\simeq\Sigma(b:B).\operatorname{fib}_q(b),\qquad
\operatorname{fib}_q(b)=\Sigma(s:S).(q(s)=b).
\]

The forward map is `s↦(q(s),s,refl)`; the inverse returns `s`. The nontrivial round trip is the contraction of the dependent singleton. This is the same construction already used by the runtime singleton, diagram extension and action definitions. It is not a second representation theory that has to be invented for networking, accounts or agency.

Retention is a mathematical property of what is represented, not a requirement to eagerly materialize every possible event or expand every proof. Immutable DAGs, views, suspended producers and receipt DAGs are appropriate representations. Reclamation must preserve any residual still owned by a live observation, continuation, fact or retained history.

The existing useful construction is therefore at the right structural location: complete typed boundaries, simultaneous views, cubical transport, generic runtime presentations, immutable evidence and shared producers. Removing arbitrary bounds and exposing intermediate facts corrects that realization; it does not replace those primitives.

## 2. Why local replacement already gives contextual correctness

For families `X,Y,K:B→U`, gluing an interior to its surrounding component over the same boundary gives

\[
X\star_B K=\Sigma(b:B).X(b)\times K(b).
\]

A boundary-preserving equivalence `E:Πb. X(b)≃Y(b)` acts by

\[
E_K(b,x,k)=(b,E_b(x),k).
\]

Its inverse and two inverse laws are pointwise. A substitution `σ:B'→B` gives the same result whether performed before or after replacement:

\[
(b',x,k)\longmapsto(b',E_{\sigma(b')}(x),k).
\]

This proves contextual transport once, for every compatible surrounding component. There is no additional theorem to reinvent for each composition node, client, network neighbourhood or resource account. In the general open-interface representation, the joining path itself is retained and transported; one cannot replace matching over the same boundary with two independently chosen copies.

The surrounding `K` may itself contain cyclic wiring and outstanding calls. This argument does not require an acyclic surrounding network: the complete compatibility constraints are fields of the joined object. Cycles matter to its behaviour and retained fibre, but do not create a new case of the contextual replacement proof.

Implementation obligations follow directly: preserve the complete declaration-closed boundary; retain path evidence when dependent data can observe it; compose substitutions simultaneously; and keep fields lazy. The existing scope/TVIEW machinery and runtime `Maps`, singleton and action definitions implement these roles. The tests must check their substitutions and boundaries, not create one special runtime mechanism for each application.

The same rule applies to a computed identity. `E` can be a parameter, an already stored value or the result of a running computation. Its provenance does not change the action. Proof-use admission still establishes which premises support using it as a mathematical identity; operationally typed recursive code is not automatically unconditional proof.

## 3. Stokes supplies the global accounting law

Let a local event have a finite multiset of input and output port occurrences. Its port boundary is

\[
\partial e=\operatorname{out}(e)-\operatorname{in}(e).
\]

An internal wire joins the same occurrence with opposite orientations. For a finite causally closed execution region `H`, summing local boundaries cancels exactly those matched interior occurrences:

\[
\partial H=\text{external output frontier}-\text{external input frontier}.
\]

This is a local-to-global theorem by cancellation. It does not require every interior event to be visible to every observer or all agents to agree on a total chronological order.

The cubical interpretation retains higher compatibility data. With the usual orientation,

\[
\partial\sigma=\sum_k(-1)^{k-1}(d_k^1\sigma-d_k^0\sigma),
\qquad \partial^2=0.
\]

For a cochain `a`, define `(da)(σ)=a(∂σ)`. Then

\[
\langle a,\partial\sigma\rangle=\langle da,\sigma\rangle.
\]

The actual typed cells contain more than their signed chains: dependent types, source/target references, guards, paths and resource commitments. Their additive boundaries are readings of that richer object. The machine must retain the interpretation map; adding chain coefficients alone does not check an ill-typed gluing.

The concrete conservation instance is a graph incidence map `∂G`, transfer vector `J` and balances `b`:

\[
b(t)-b(s)=\partial_G J.
\]

For any region `U`, pairing with its indicator leaves incoming minus outgoing transfers. A cycle has zero net balance change while its retained computation, knowledge and commitments can change. A pending transfer is still on the cut; a suspended continuation still owns an open obligation. Neither disappears because no final answer has arrived.

This is why prefix retention, correct ownership and noncancelling suspension are foundational implementation requirements. They are the representation of an unclosed boundary, not optional accounting polish.

## 4. Sharing, authority and actual events

Three identities must remain distinguishable:

| Identity | Meaning | Consequence |
| --- | --- | --- |
| Mathematical operation key | Same pure operation, operands and applicable premises | Join its producer and reuse its facts/results. |
| Evidence reference | Same witnessed proposition or reduction prefix | Share the proof without rerunning its historical production. |
| Accepted effect occurrence | This particular state-changing event at this boundary | Replaying its receipt is not permission to perform the effect again. |

This is one typed source with different dependent fields. It does not call for three replacement runtimes.

For an actual event set, independent composition uses the union of identical event identities. If histories overlap in the same events `J`, then

\[
W(H_1\cup_J H_2)=W(H_1)+W(H_2)-W(J).
\]

Consumers remain distinct: one shared result used by two clients has one producing history and two actual request/delivery occurrences. Reusing the proof of that history has its own present lookup/adaptation work. No historical event is executed again merely because another proof DAG references it.

Specialization of symbolic work keys is Boolean direct image, not linear pushforward of signed costs. If `a` and `b` both instantiate to `z`, the image of `{a,b}` is `{z}`. Deduplicate after specialization, then apply ready cuts and compute costs. In particular, cache subtraction must occur after this identification. These are the existing §§60–63 laws; no search procedure follows from them.

For effects, consider a current acceptance boundary `h` and a proposed successor `x`. Copying the proposal or its arithmetic proof is harmless. Admitting it requires the current boundary's maintained exclusion condition. Two incompatible successors cannot both be accepted in the same permitted local history. In a local implementation, atomic head advancement can realize that condition; in a distributed implementation, the chosen receipt/authority structure must realize it. Merely signing both proposals does not.

The PDF's general receipt theorem already states the necessary premise: incompatible acceptance sets meet in a witness that cannot issue both receipts along one permitted local history. Its proof projects the alleged global history to that local history. The particular unanimous protocol is an example, not a forced runtime feature.

Replacing that witness by a subnetwork has the same short proof. Supply a trace map `π` from the subnetwork's permitted histories to the witness's histories, preserving composition and externally issued receipts. Two incompatible external receipts would project to two incompatible receipts in one witness history, contradicting its exclusion law. Composition of such trace maps proves arbitrary finite nesting. Internal steps may project to stuttering; an externally usable receipt must project to its actual issue. This is the precise mechanism by which a network inherits the local guarantee. It is already derived in the source, not a fresh distributed-consensus theorem assigned to the worker.

Consequently a mathematical identity can transport the description and proof of a live commitment, but it cannot erase its accepted occurrence or replay its authority. That commitment is part of the boundary preserved by the identity. A networking or cash integration should expose this existing distinction through one generic witnessed-effect boundary, not through privileged domain-specific constructors.

## 5. The exact relationship between identities, Stokes and geodesics

The repository supplies both random descent and the fact that execution cost does not descend to semantic equality. They fit together when applied to their actual objects.

For a fixed deterministic interaction relation with exact residual diamonds, any finite reduction to a normal form has a fixed length. With diamond-balanced weights it has a fixed weighted cost. The source's `docs/index.html` §5.28 explicitly fixes the initial posed object. A different term, an added shortcut or a changed ready boundary is not silently the same initial comparison.

Now let `ω` read the actual nonnegative work of a directed execution edge. A supplied cell `α` comparing two composable paths `γ` and `γ'` has, with orientation `∂α=γ'-γ`,

\[
\Delta_\alpha W=W(\gamma')-W(\gamma)
=\langle\omega,\partial\alpha\rangle
=\langle d\omega,\alpha\rangle.
\]

This directly gives the shifted work bound associated with an identity. For a commuting scheduling square with the same residual events and balanced weights, this difference is zero. For a shortcut replacing three charged interactions by one, it is `1−3=−2`. Higher coherence of these differences follows from `d²=0` on the relevant chain presentation, while the full typed witness retains distinctions the additive reading forgets.

That equation applies to the stated witnessed boundary, not to two final values with their machine states omitted. If two realizations leave different caches or commitments, retain their actual successor states. For a continuation `C`, the exact comparison is

\[
\operatorname{Cost}(P;C,S)-\operatorname{Cost}(Q;C,S)
=\operatorname{Cost}(P,S)-\operatorname{Cost}(Q,S)
+\operatorname{Cost}(C_P,S_P)-\operatorname{Cost}(C_Q,S_Q).
\]

A cell comparing those histories must include any connecting boundary transports; their actual execution work is not silently zero. This is the existing §63 contextual law and the reason an output-only equality cannot replace the complete state in the geodesic argument.

There is no contradiction between these cases and no need to charge a physical instruction negatively. A negative difference compares two realized histories from the same complete starting boundary. Executing the shortcut or transporting its witness still incurs its own nonnegative work.

The concrete obstruction to a stronger blanket claim is elementary. If one relation contains both

```
s -> a -> z
s ------> z
```

with all three edges charged one and `z` terminal, its normalizing paths have lengths two and one. They cannot simultaneously satisfy the equal-length conclusion. Naming the new edge an identity does not change that calculation. One must retain its nonzero cost defect, change the stated comparison, or supply a different actual rule realization. Padding the shortcut, hiding the old work or putting it in uncounted compilation is not a correction.

The repository's checked localization modules already exhibit precisely the relevant distinction: equal-meaning derivations of lengths two and four, and a reversal round trip with trivial meaning but positive length. Thus arbitrary semantic quotienting cannot erase work. This is affirmative support for retaining the cost fibre, not a reason to abandon identity execution.

For a geodesic lower bound, the exact constructive contract is a potential `V` on the compared complete states satisfying

\[
V(z)=0,\qquad V(s)\le w(e)+V(t)
\quad(e:s\to t).
\]

Telescoping proves `V(s)≤W(γ)` for every successful compared path. If the selected path has equality at each edge and reaches the goal, it attains the lower bound. Positive integer decreases or an additional well-founded rank justify termination where required. An identity shortcut preserves an existing bound precisely when it satisfies the same edge inequality; otherwise the available bound changes. This is a local rule-schema obligation that can be instantiated and reused. It is not an instruction to run Bellman search.

**Resolved conclusion:** Stokes is the common law for boundary conservation and identity cost differences. Zero-defect scheduling cells support equal-length descent. Cost-changing identities remain available as witnessed transformations with their exact defect. No theorem needs to be invented separately for every application; the worker does need the actual rule premises and a faithful execution reading.

## 6. Adaptive reuse: what has to be proved about the actual relation

When a newly available prefix permits an instance to skip work, the future execution graph can change. The prefix improvement is desirable. Whether two schedules have equal total work is then a question about the actual adoption, publication and residual rules, not just about uniqueness of the final answer.

A complete state for this comparison includes available facts, running cuts, dependency snapshots, open continuations and charged administrative state. A selected historical receipt must be immutable. This prevents a race from silently replacing the proposition, assumptions or endpoint that an adapter is using.

The next author-level proof must inspect overlapping transitions, particularly:

- publish a prefix versus specialize a source;
- advance a source versus lift its prefix through a context;
- adopt an available fact versus advance the target directly;
- change a dependency revision versus use an old fact;
- deliver a result versus release a client or reclaim storage.

Some pairs are causally ordered, some are independent squares, and some are genuine alternative transitions with a recorded cost difference. That classification is forced by the full boundary; it is not a scheduler preference. The existing ready-set/selected-graph theorem remains valid in its stated domain. A whole-machine exact diamond needs the corresponding proof for these actual rules.

`PREFIX-CONTRACT.md` closes a concrete representational absence before that proof: already completed facts are not made to depend on future termination. It does not freeze reuse, force generic work first, or insert fallback enumeration.

## 7. One execution can supply its mathematical and work readings

Let a receiver assign an action to each generating step. Its fold on a finite derivation obeys

\[
\operatorname{fold}_R(\mathrm{done})=\epsilon_R,\qquad
\operatorname{fold}_R(\mathrm{step}(e,d))=R_e(\operatorname{fold}_R(d)).
\]

For two receivers, induction gives

\[
\operatorname{fold}_{R\times T}(d)
=(\operatorname{fold}_R(d),\operatorname{fold}_T(d)).
\]

The existing initiality result supplies this theorem. Its implementation consequence is to retain one event/derivation DAG with compatible readings for operational evidence, exposed boundary, dependencies and performed work. It does not require separate rediscovery traversals for facts already supplied by the event. A derived scalar remains an observation of this source, not its replacement.

An event's result may be ready before its complete printable trace is traversed. The witness can remain a lazy DAG. Copying or serializing it costs the actual work performed. The origin/frame/receipt infrastructure is useful precisely because it can represent that sharing without eagerly copying derivations.

The kernel refinements in progress should make this common event boundary explicit. A pthread stack is an implementation of a continuation only within its representable stack resources; it is not the mathematical definition of input depth. Variable-size maps, exact arithmetic and arena growth must be traversed by persistent bounded steps. The existing native operation names can remain stable while their frames are refined.

## 8. Constant-factor C correspondence: the acceptance statement

For a fixed backend, the required claim is about every transition path through the implementation, not only successful example timings. A charged elementary transition has a fixed bound on word operations, memory accesses and bounded-size updates. Variable work is a retained sequence of those transitions. Dispatch, joins, retries, publication and reclamation are included.

For a trace with `n` such transitions, bounded expansion gives `I_C≤c n+d` for fixed backend constants. A reverse accounting bound requires that charged units also have bounded multiplicity per actual instruction sequence; counters cannot be arbitrarily inflated to manufacture it. Resource acquisition from the host must have its declared model and explicit failure/suspension boundary. This is an instruction correspondence, not a bound on operating-system latency.

This claim belongs to the fine transition relation that is actually implemented. It does not retroactively bound a macro event that opens an arbitrarily large field array. Nor does it prove every schedule has equal fine cost. An exact macro-to-fine theorem needs a bounded macro realization or a macro weight equal to its explicitly retained fine work.

The recent fixes are directed at this exact contract: unbounded helper bodies, false dependencies introduced by one global kernel gate, retry outcomes cached as mathematical failures, unreclaimed storage and arbitrary representation caps. They are concrete conformance defects. The closure point is a transition inventory with bounded bodies, retained continuations and regressions at the affected boundaries—not endless incidental sanitizer additions.

## 9. The shortest faithful implementation sequence

| Stage | Concrete closure | What remains preserved |
| --- | --- | --- |
| Current worker correction | Pass the assigned V20/bounds regressions; exact levels/costs; extensible storage; progress and retry correctness; bounded resumable kernels | Core terms, scope mathematics, templates, runtime actions and their existing tests |
| Live prefix integration | Pass the supplied regression and the contract's scope/revision/concurrency cases | Same producer keys, final-answer meanings and receipt interpretation |
| Common execution reading | Map each real committed rule to its witness, retained cut, dependencies and fine work; connect prefix and final publication through that map | Existing counters remain projections; proof DAGs remain shared |
| Foundational end-to-end witness | One finite causal execution using a runtime-produced identity, a suspended shared computation, a compatible boundary replacement and an explicit accepted effect, with the same retained source supplying result and cut accounting | No new cash/agent primitives; existing cubical action and generic boundary contracts |
| Theorem closure for the chosen native relation | Classify its actual overlaps; prove zero-defect diamonds where claimed and retain nonzero identity defects elsewhere; connect its elementary work to C | No planner and no theorem inferred from a benchmark |

The fourth row is an integration witness, not a mandate to implement a complete network stack or an arbitrary financial protocol. In a one-process test, the exclusion premise can be supplied by the same owned-boundary discipline as other state transitions. A distributed replacement must provide its own emission-preserving refinement to that boundary. The mathematical substitution theorem then carries the guarantees; it does not presume them from network connectivity.

A decisive example should return to the same balance while changing a retained fact, keep a pending transfer visible until acceptance, use one historical producer event through two consumers, and reject replay of an already consumed authority. Reassociation must preserve the actual outstanding commitments. These observations exercise the user's consilience directly; a Nat/Bool demo would not.

The general declaration-to-inhabitant operation and fully reflected checker/compiler are still separate author-side specification claims in §§85–91. This review does not silently certify them, implement a search substitute or turn them into unexplained worker TODOs. The available texts specify applying and composing supplied or computed witnesses. They do not yet provide executable posing equations that manufacture an inhabitant from an arbitrary bare type. An absence result must itself be justified; suspension is not one. This limitation concerns that exact interface, not the validity of contextual identity execution or Stokes composition.

## 10. Review evidence and source anchors

**Executed in this review:** `review_live_prefix.c` against independently built objects from `c365d86`, two modes with zero/four workers under ASan/UBSan and TSan. All eight return the correct specialized value and leave the generic source pending, but repeat one beta and therefore fail the new assertion. Evidence JSON is included. No sanitizer fault occurred. LSan was not run on this host. The runner builds fresh objects by default for the next tree.

**Previously executed bounds correction:** dynamic net scope arities and required-face depth; full signature retrieval; sparse pointer directories; full-width bound-atom coordinates; targeted ASan/TSan checks and 552 semantic suite checks. Exact numeric values, extensible/reclaiming allocator completion and all remaining kernel progress/cost corrections must be judged on the worker's new tree, not inferred from those tests.

**Source anchors read for this review:**

- `docs/index.html` §§5.4–5.28: the actual net relation, random descent and the fixed-start comparison.
- `HANDOFF.md` §§25–31, 60–66, 73–84, 85–96: cache event laws, sharing/specialization, explicit exclusion of plan search, runtime actions, prefix exposure and corrected claim scope.
- `formal/cubical/Kernel/TheLocalizationSequenceAsOneObjectMeaningDescendsAndCostDoesNot.agda`: equal-meaning histories with different lengths; the non-descent theorem.
- `formal/cubical/Kernel/TheRoundTripIsPureCostAndTrivialMeaningSoCostIsSupportedOnTheKernelOfTheGroupoidCompletion.agda`: positive execution length retained across a meaning-trivial round trip.
- `abstracts/49_the_kernel_is_initial_every_reading_is_its_unique_fold.txt` and the corresponding kernel-flat initiality module: receiver folds and their uniqueness; applied to existing derivations.
- `research/PNP_GEODESIC_REDUCTION_20260916.md`, especially A1–A5, B3–B5, D1–D3 and G1–G5: fibre retention, constructive witness premises, exact costed realization and the demonstrated native geodesic.
- *Witnessed Computation*, §§1–6, 8–13 and 20–27: the general source, interface substitution, independent agency, shared origins, incidence conservation, stateful receipts and subnetwork refinement.
- `src/eval.c`: `forward_rc`, `adapter_candidate`, `eval_entry_receipt`, `eval_entry_residual`, `resume` and publication; `src/runtime.h`: ordinary runtime presentations/actions; `src/fine.h` and `src/kcont.h`: the delivered work and continuation boundary.

These anchors fix what can be accepted now, what the worker can implement directly, and which broader theorem must be stated on the actual relation. They preserve the existing construction while preventing another handoff from confusing correct answers, retained witnesses, reusable work and geodesic claims.
