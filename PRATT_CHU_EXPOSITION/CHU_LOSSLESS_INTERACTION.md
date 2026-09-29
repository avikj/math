# From Chu Space to the Universal Lossless Interaction Object

## The construction

A Chu space begins with an evaluation

\[
(A,X,e),\qquad e:A\times X\to K.
\]

For every map \(f:S\to V\), there is a canonical dependent decomposition

\[
S\simeq\sum_{v:V}\operatorname{fib}_f(v),
\qquad
\operatorname{fib}_f(v):=\sum_{s:S}(f(s)=v).
\]

Apply it to the defining Chu evaluation:

\[
\boxed{A\times X\simeq\sum_{k:K}\operatorname{fib}_e(k).}
\]

The ordinary Chu value \(k\) is the visible coordinate. Its canonically forced remainder is

\[
\operatorname{fib}_e(k)=\sum_{(a,x):A\times X}(e(a,x)=k).
\]

This is not chosen metadata. For any conservative factorisation over the visible result, the trace family is pointwise equivalent to the fibre family of the induced visible map. The fibre is the unique lossless residue up to equivalence.

Do not truncate that fibre. Its witnesses have witnesses,

\[
e(a,x)=k,\qquad p=q,\qquad \alpha=\beta,\qquad\ldots
\]

so the complete interaction retains whatever higher identity structure it possesses. Cubically these identities have computational cell structure: paths, higher cubes, composition, filling, and dependent transport.

By univalence,

\[
(R\simeq S)\simeq(R=_{\mathcal U}S),
\]

so equivalence of interaction types is a path in the universe and transport along that path computes.

Do not terminate the interaction at its visible value. The interactive coalgebra has the form

\[
\operatorname{react}:(q:Q(w))\to
\sum_{w':W}\sum_{o:O(w,q,w')}
\bigl(E(w,q,w',o)\times ISC(w')\bigr).
\]

One interaction returns successor, observation, proof-relevant event/residual, and continuation together. The continuation is again an interaction object.

Let transformations produced by interaction re-enter as subsequent interactions. Proof, program, data, execution, type, transport, and transformation become roles occupied by objects in one closed interaction universe.

Finally, the chosen Chu codomain \(K\) is not primitive. A general dependent interaction is a family

\[
R:A\times X\to\mathcal U,
\]

classified by the universal family

\[
\boxed{\pi:\sum_{T:\mathcal U}T\to\mathcal U.}
\]

Thus Chu evaluation, higher-dimensional/cubical structure, univalent transport, coalgebraic continuation, and metacircular execution are projections, truncations, restrictions, or presentations of one lossless dependent interaction object.

## 1. The fibre is forced

For

\[
f:S\to V,
\qquad
\operatorname{fib}_f(v)=\sum_{s:S}(f(s)=v),
\]

the map

\[
s\mapsto(f(s),s,\mathrm{refl})
\]

exhibits

\[
S\simeq\sum_{v:V}\operatorname{fib}_f(v)
\]

without injectivity or invertibility hypotheses.

The stronger repository theorem says a conservative factorisation

\[
T:B\to\mathcal U,
\qquad
A\simeq\sum_{b:B}T(b)
\]

forces

\[
\boxed{T(b)\simeq\operatorname{fib}_{\operatorname{run}}(b).}
\]

The later uniqueness theorem strengthens this globally. Define

\[
\operatorname{Lossless}(f):=
\sum_{T:B\to\mathcal U}
\sum_{\eta:A\simeq\sum_{b:B}T(b)}
(\pi_1\circ\eta\sim f).
\]

Then

\[
\boxed{\operatorname{isContr}(\operatorname{Lossless}(f)).}
\]

Losslessness is a property of the map, not additional machine structure. At machine level,

\[
\boxed{\operatorname{LawfulStep}(A)\simeq(A\to A).}
\]

For Chu, \(S=A\times X\), \(V=K\), \(f=e\). The classical matrix entry retains \(k\); the lossless interaction retains exactly the complete source distinction lying over \(k\).

## 2. Higher interaction

The homotopy fibre

\[
\operatorname{fib}_e(k)=\sum_{(a,x)}(e(a,x)=k)
\]

is retained without imposing set/propositional truncation. Cubical composition gives a constructive language for paths, higher cells, compatible boundaries, filling, and dependent transport.

Pratt's own concurrency geometry supplies the complementary process reading: true \(n\)-fold concurrency resides in an \(n\)-dimensional transition, while nondeterminism is treated through monoidal homotopy. The cubical calculus supplies executable composition/coherence for higher interaction rather than adding a separate sequential semantics.

## 3. Chu morphisms and transport

A Chu transform

\[
(A,X,e_A)\to(B,Y,e_B)
\]

consists of

\[
g:A\to B,\qquad h:Y\to X
\]

satisfying

\[
e_A(a,h(y))=e_B(g(a),y).
\]

At the lossless level, equality of visible evaluations transports the dependent fibres over those values. For universe-valued interaction

\[
R:A\times X\to\mathcal U,
\]

a structural equivalence

\[
R_A(a,h(y))\simeq R_B(g(a),y)
\]

becomes, by univalence,

\[
R_A(a,h(y))=_{\mathcal U}R_B(g(a),y),
\]

so the complete dependent interaction transports computationally.

## 4. Productive interaction

A classical evaluation terminates:

\[
(a,x)\mapsto k.
\]

The interactive symbolic computer instead returns

\[
\operatorname{react}:(q:Q(w))\to
\sum_{w':W}\sum_{o:O(w,q,w')}
(E(w,q,w',o)\times ISC(w')).
\]

The deterministic orbit is the one-query restriction:

\[
Q(w)\simeq1\Longrightarrow ISC|_Q\simeq\operatorname{Orbit}.
\]

Finite interaction composes exactly:

\[
\operatorname{Ans}_{m+n}(w)
\simeq
\sum_{a:\operatorname{Ans}_m(w)}
\operatorname{Ans}_n(\operatorname{end}_m(w,a)).
\]

## 5. Metacircular interaction

Interaction results inhabit the same typed universe as the objects being transformed. A transformation produced by one interaction can therefore become an operation in a later interaction:

\[
\mathcal M\xrightarrow{\mathrm{interact}}\delta
\xrightarrow{\mathrm{install}}\mathcal M'
\xrightarrow{\mathrm{interact}}\cdots
\]

`IntrinsicRewrite`, self-presentation/contextual installation, and `ProductiveIndraNet` provide checked source-level loci for retained transformation, reweaving, and productive continuation.

## 6. The fixed Chu alphabet is a specialization

Classical Chu fixes

\[
e:A\times X\to K.
\]

General interaction allows

\[
R:A\times X\to\mathcal U.
\]

Every such family is classified by

\[
\pi:\sum_{T:\mathcal U}T\to\mathcal U.
\]

The classifier theorem gives

\[
\boxed{\left(\sum_{E:\mathcal U}(E\to B)\right)\simeq(B\to\mathcal U).}
\]

Every family is canonically a pullback of the universal family, and finite towers of dependent families flatten to one family over the original base.

## 7. Pratt coordinates

The same construction should be read directly through Pratt's own mature vocabulary and results: propositional dynamic logic and near-optimal reasoning about action; Action Logic and interval action; pomsets/partial strings; Birkhoff schedule/automaton duality; solid higher-dimensional automata; monoidal homotopy; Gates Accept Concurrent Behavior; state/event duality; time/information duality; Rational Mechanics and residuation; Chu spaces over 2, 3, and 4; Types as Processes; transformational mathematics; dialectic lambda calculus; the Stone gamut/universal mathematics; communes/Yoneda; final-coalgebraic continuum; generalized quantum mechanics; primality certificates; LINGOL and the speech manifold; algebraic/geodesic foundations of geometry.

These are not stylistic analogies. The exposition task is to identify exact restrictions/equivalences and then transport the completed construction into those coordinates.

## 8. Time / information / phase / charge

The braid carrier has unit lookahead

\[
x\equiv_{n+1}y\Rightarrow\sigma x\equiv_n\sigma y,
\]

and a word \(w\) has modulus \(|w|\):

\[
x\equiv_{n+|w|}y\Rightarrow w(x)\equiv_nw(y).
\]

Thus

\[
\boxed{\text{depth}=\text{time},\qquad|w|=\text{causal radius}.}
\]

It also derives

\[
\rho^4=1,
\qquad
Q:R\to\mathbb Z/4,
\qquad
Z_{\mathrm{cell}}=\langle\rho\rangle\simeq\mathbb Z/4,
\]

with global charge not bounded-locally readable:

\[
\forall n\;\exists x,y:\quad x\equiv_ny\land Q(x)\neq Q(y).
\]

## 9. Observation / residual / phase

For observation \(q\), action `step`, and predictor \(P\),

\[
\delta(x)=q(\operatorname{step}x)-P(qx).
\]

A response character satisfies

\[
\boxed{\chi(\delta x)=\chi(q(\operatorname{step}x))\chi(P(qx))}
\]

and

\[
\chi(a)=\chi(b)\iff\chi(a-b)=1.
\]

The checked hostile case has injective \(\delta(x)=2x\) while every sign character maps the whole residual to the identity phase. A faithful classical residual can therefore become invisible under a quotient observation; the lossless completion specifies exactly what must remain.

## 10. Exact interaction geodesics

For the rope transformation moving cell \(n\) to the head, locality forces

\[
\ell(\gamma)\ge n
\]

for every crossing path accomplishing the observation, while an explicit path has length \(n\). Hence

\[
\boxed{d_{\mathrm{interaction}}(\text{cell }n,\text{head})=n.}
\]

This is the intrinsic optimality template relevant to Pratt's earlier near-optimal action reasoning: derive the lower bound from dependency geometry and realize its geodesic in native interaction steps.

## 11. Runtime

The cubical operations

\[
I,\operatorname{Path},\operatorname{PathP},
\operatorname{comp},\operatorname{coe},\operatorname{hcomp},
\operatorname{Glue},\operatorname{ua}
\]

meet the Bend/HVM local interaction calculus with native sharing/superposition and parallel reduction:

\[
\boxed{\text{constructive mathematical interaction}\longleftrightarrow\text{runtime interaction}.}
\]

## 12. Checked repository anchors

- `fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda`
- `fibre/src/Fibre/Visvarupa_EveryFamilyIsAPullbackOfTheUniverseAndTheTowerFlattensToOne.agda`
- `fibre/src/Fibre/Samvada_TheOrbitIsTheOneQueryCaseOfTheInteractiveCoalgebraAndTheDemandIsWhatDiffers.agda`
- `fibre/src/Fibre/Nucleus.agda`
- `formal/cubical/theorems/residue/Ekatva_LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleTypeAndTheMachinesIsUnique.agda`
- `formal/cubical/theorems/residue/VerifyIsDecide_ThereIsNoGapBetweenFindingAndCheckingBecauseBothAreProjectionsOfOneEquivalence.agda`
- `formal/cubical/theorems/residue/ActionResidualPhase.agda`
- `formal/cubical/theorems/residue/ChuAdvance.agda`
- `formal/cubical/theorems/order/ChuDefect.agda`
- `formal/cubical/theorems/logic/ObsBridge.agda`
- `LIFECYCLE.rst`
- `collab/bend2-interactive-cubical/CONVERGENCE.md`

## Compressed statement

Take Chu evaluation \(e:A\times X\to K\). Its unique conservative completion is the total space of its homotopy fibres. Retain the full identity structure and interaction is higher/cubical. Univalence makes structural equivalence executable transport. Return continuation and interaction is coinductive. Re-admit produced transformations and it is metacircular. Generalize the fixed result object \(K\) to a dependent family classified by \(\pi:\sum_TT\to\mathcal U\). The resulting object is the lossless dependent interaction object from which the classical presentations are obtained by restriction/projection/truncation.
