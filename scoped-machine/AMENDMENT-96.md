## 96. One computational system: checked runtime diagram extension

This section strengthens §§83–84 with an executable nonempty diagram constructor and clarifies the architecture after the b612a07 review. It preserves the implementation, R1/R2 in §§93–94, and the worker's current assignment. It introduces no plan search, new primitive type, native diagram handler, or replacement runtime.

### 96.1 The relevant boundary is computational, not a C file boundary

The source's requirement is explicit: index §5.26 places evaluation, checking and optimization in the same language. The initiality development also makes soundness, length and the evaluator integral instances of the same derivation recursor. Separate implementation files are not evidence against either requirement. Saying “checker, compiler, evaluator” names operations and their result judgments; it must not introduce a staging barrier, separate representation of mathematical values, or a privileged host-only identity action.

The operational requirement already guiding §§74–84 is:

1. Constructions, families, maps and proof terms use the existing references, substitutions, scopes and templates. Runtime-produced parameters have the same status as supplied parameters.
2. A demand uses its mathematical operation, operands, complete typed boundary and actual external dependencies as its key. Calling phase, source label and requesting client do not create a second mathematical computation. Distinct judgments remain distinct keys unless an explicit valid transformation connects them.
3. A shared computation has one producer and persistent continuation. Consumers share its results, including proofs and residuals. Checking may demand evaluation; a runtime computation may produce an identity action; using that action may demand further evaluation. These dependencies form the existing demand graph.
4. A constructed identity acts through the same ordinary maps and transports as a supplied identity. Host declaration compilation specializes those constructions and retains provenance. Registration does not confer an extra mathematical ability.
5. Work performed inside any of these operations is subject to the same bounded-step accounting. A synchronous helper is not made constant-cost by naming it one operation. The already assigned R2 lowering is the concrete implementation task here.

The three C modules therefore do not warrant three replacement implementations. Nor does shared C storage alone establish §5.26's full internal representation of the implementation's programs. The latter remains the accurately recorded author-side obligation in §§87/91; this amendment does not turn it into a new discretionary worker project or certify it from file organization.

### 96.2 Exact ordinary value signature

For A:U_a and B:U_b retain the four-field record of §83.1:

\[
\mathrm{Maps}(A,B)=\Sigma(f:A\to B).\Sigma(g:B\to A).
 (\Pi x:A.\mathrm{Path}_A(g(fx),x))
 \times(\Pi y:B.\mathrm{Path}_B(f(gy),y)).
\]

It lies in U_max(a,b); its inverse witnesses are retained as terms, with their higher distinctions intact. For B:U_b,

\[
\mathrm{Diagram}_{b,r}(B)=\Sigma(C:B).
 \Sigma(R:(y:B)\to U_r).
 \Pi y:B.\mathrm{Maps}(R(y),\mathrm{Path}_B(C,y))
 : U_{\max(b,r+1)}.
\]

The new closed function is exactly the §83.3 constructor:

\[
\begin{aligned}
\mathrm{node}_{a,b,r}:\;&(B:U_b)\to(A:U_a)\to(t:A)\to\\
 &((x:A)\to\mathrm{Path}_A(t,x)\to\mathrm{Diagram}_{b,r}(B))\to
 \mathrm{Diagram}_{b,\max(a,r)}(B).
\end{aligned}
\]

Every displayed arrow is an ordinary dependent function type. The levels are exact; there is no universe cumulativity assumption. In particular the tail's type has level max(a,b,r+1), and the output diagram has level max(b,max(a,r)+1).

Write Q for the runtime tail, Q₀=Q(t,refl(t)), C₀=C_Q₀ and s=max(a,r). At y:B set

\[
D_y(x,e)=R_{Q(x,e)}(y),\quad
S_y=\Sigma(x:A).\Sigma(e:t=x).D_y(x,e),\quad
Z_y=D_y(t,\mathrm{refl}(t)).
\]

The result is the ordinary tuple

\[
(C_0,\;\lambda y.S_y,\;\lambda y.(q_y\circ s_y)),
\]

where s_y:Maps(S_y,Z_y) is §83.2's dependent singleton construction and q_y:Maps(Z_y,Path_B(C₀,y)) is projected from Q₀. Nothing inspects a host diagram registry to determine the number of nodes, the type of a realization or the next action.

### 96.3 Both inverse proofs are part of the emitted construction

The executable witness emits the singleton's down, up, h and k exactly as §83.2 states, including the non-regular constant-family fill in k. It simultaneously substitutes x and e into D; it never substitutes into their images again. D may depend on x, e, y and all retained ambient parameters.

For E=(f,g,h,k):Maps(X,Y) and F=(u,v,H,K):Maps(Y,Z), it emits

\[
\begin{aligned}
f'(x)&=u(fx),& g'(z)&=g(vz),\\
h'(x)&=\mathrm{ap}(g)(H(fx))\cdot h(x),&
k'(z)&=\mathrm{ap}(u)(k(vz))\cdot K(z).
\end{aligned}
\]

The first composite path has endpoints g(v(u(fx))) and x: its intermediate point is g(fx). The second has endpoints u(f(g(vz))) and z: its intermediate point is u(vz). Thus the constructor's forward and reverse maps and both proofs have the required dependent types without a new inverse-selection operation or an assumed groupoid law.

The C file is a finite emitter for a closed ordinary term. Its runtime tail is universally bound in that term. The emitter is not a host callback invoked by the term's execution. For production, register the recipes once per exact level tuple using the existing fixed-template machinery, and instantiate by the existing environment/substitution operations. In particular, do not rebuild the generic definition at each invocation or replace its runtime Q parameter with a per-tail host specialization.

The right fold from §83.3 follows directly: zero supplies the terminal diagram and each node application extends it. Since the extension accepts an arbitrary tail value, a tail computed by another node application is covered by the same function. Host declarations and runtime producers use this same constructor; the host fold is an elaboration convenience. This is an inductive construction of finite diagrams, not a termination claim for every recursive program that tries to produce one.

### 96.4 Executable acceptance evidence and its scope

`review_runtime_nodes.c` checks the complete closed function above with an unknown dependent Q, including all four map fields. It then constructs

\[
Q=\lambda x\,e.\mathrm{zero}(A,x),\qquad
Q_{computed}=\mathrm{id}(Q),\qquad
D=\mathrm{node}_{0,0,0}(A,A,t,Q_{computed}).
\]

This tail is computed by ordinary application, and its centre depends on x. The example is a nonempty diagram. Its realization type is

\[
\Sigma(x:A).\Sigma(e:t=x).\mathrm{Path}_A(x,y).
\]

For an arbitrary symbolic p:Path_A(t,y), the test checks:

- D at its diagram type and C_D=t by conversion;
- the projected complete maps record at Maps(R_D(y),Path_A(t,y));
- expansion of p into a realization and collapse back into the output path type;
- the two projected inverse proofs at their full round-trip path types;
- both endpoints of each inverse proof;
- zero registered transforms throughout.

The unknown-Q check is stronger than the concrete example: it admits tails dependent on both x and e, with arbitrary realization family and supplied inverse data. The concrete case additionally exercises actual reduction of a computed tail. Separate checks use (a,b,r)=(1,0,0),(0,1,0),(0,0,1), covering each distinct source of a raised universe maximum.

The author executed this witness on b612a07 with the explicit §93 R1 alias correction, not on an unreported later worker commit. The complete runtime case passes under ASan/UBSan with actual pools 0 and 4. The complete generic constructor, including both proofs, passes TSan with pools 0 and 4. The three mixed-level checks pass under both sanitizer configurations. The C witness installs and asserts the pool itself. ASan leak detection is disabled on the author host because its process inspection is unsupported; no independent LSan result is claimed.

The fully instantiated runtime case exceeds this host's 8 GiB cgroup limit under TSan: the processes are killed and the cgroup records OOM kills. A sequential retry and a shadow-memory-limit retry do not resolve it. Its full TSan result is **resource-inconclusive**, not passing and not a sanitizer race report. An attempted variant retaining observed record references does not close the resource issue and is not included in the final witness. Keep the full assertions; run that case on an adequately provisioned host or investigate its memory use. `results.json` and the supplementary logs retain the outcomes. `--modes generic` isolates the generic proof check without pretending it ran the full example. The runner fresh-builds a supplied tree and never applies a patch implicitly.

These are executable typed proof terms checked by the current implementation. They are not a metatheorem establishing the soundness of that entire implementation. They close a concrete constructor-and-proof integration case that the earlier three runtime witnesses did not exercise together.

### 96.5 The common recursor gives a precise integration principle

For the source's derivations, a receiver R has an identity action ε_R and an action for each generating step. The fold obeys

\[
\mathrm{fold}_R(\mathrm{done})=\varepsilon_R,\qquad
\mathrm{fold}_R(\mathrm{step}(s,d))=R_s(\mathrm{fold}_R(d)).
\]

Given receivers R and S, define their product componentwise. Induction on d gives

\[
\mathrm{fold}_{R\times S}(d)=
(\mathrm{fold}_R(d),\mathrm{fold}_S(d)).
\]

The base case is the pair of identities; the step case applies the two actions to the induction hypothesis. This is the exact reason a checked transition, its evidence and its work reading can be produced together and shared, rather than independently rediscovered by three traversals. It uses the initiality result in the repository in its stated scope.

For this machine, attach the operational work reading to the actual executed microstep derivation. A cache hit contributes its actual lookup/delivery work; it does not charge the cached computation again merely because its proof is reused. Conversely, a historical receipt for that computation does not make current validation or delivery work disappear. The existing receipts, dependency records and event ledger provide the representation to retain these distinctions. The product-fold identity does not alone prove that two different adaptive schedules have the same cost; §90's actual-diamond obligation still governs that claim.

### 96.6 Worker action and completion meaning

Continue R1/R2 and the already assigned §§83–84/88 integration. Add this witness to that integration's acceptance suite and use its recipes to register the nonempty runtime node with both inverse proofs. Retain the earlier generic action and singleton witnesses, v9 sharing regressions, proof-use boundary and existing gates. No work on a replacement runtime or automatic planner is requested.

Return the production template/function mappings and the runner results against the corrected tree. Preserve lazy fields: observing a canonical value or one map does not require evaluating the other map or its proofs. Mathematical use of proof fields follows the same contextual proof-use contract regardless of whether Q or the proof was supplied or computed.

This pass adds a checked executable construction on the current machine. The scope still requiring integration is explicit; the broader author obligations are not silently reassigned to the worker. Acceptance of this library increment is distinct from claiming that the full adaptive geodesic theorem, whole-machine bounded-C refinement, reflected implementation programs and declaration-to-answer operation have all been completed. Those claims require the evidence specified in §§85–91. None of that changes the concrete result here: the nonempty runtime constructor, its dependent maps and its inverse proofs already execute in the core that has been built.
