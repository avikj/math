# Fibre-preserving reduction, geodesics, SAT, and minimum-cost loops

Read [the subsequent source-based theoretical correction](THEORY_READING.md) alongside this checkpoint. It identifies the existing universal constructions and SAT results that the original framing underused.

Research checkpoint, 16 September 2026. Entry points: [SAT proofs](SATFibre.agda), [geodesic proof](InteractionGeodesic.agda), [colour-frame proof](ColorFrame.agda), [minimum-cost proof](../tsp_fibre/TropicalReduction.agda). These are safe Cubical Agda modules. Runtime measurements and their reproducible generators accompany them; a checked mathematical statement and an experimentally validated cost model are identified separately below.

## 1. What the foundational decomposition supplies

The central construction read in `formal/cubical/theorems/physics/photon.agda` is the decomposition of a source by an observation:

    A â‰ Î (b : B), fiber f b

The dependent pair retains the observation, the source, and evidence relating them. It makes reproduction exact. Forgetting the second component changes what can subsequently be reconstructed. This matters operationally: a Boolean verdict, a single satisfying assignment, every satisfying assignment, and the full assignment/verdict carrier are different requested outputs.

`photon` also treats a process as more than its present reading. Its orbit and nucleus constructions preserve a trajectory, and its interactive coalgebra returns evidence and a continuation. A SAT client can therefore ask for a verdict and then ask the returned continuation for the retained assignment. `SATProcess.bend` does precisely this for the four assignments of two-variable exclusive-or. Bend's `--total` gate passes; the lowered HVM program produces the four correct readings in **1,624 interactions**. The receipt records compiler, runtime, source, and imported-module hashes. This checks an executable client of the existing whole-process machinery; it does not establish a compiler correctness theorem.

`SATFibre.agda` formalizes finite Boolean reproduction, observation at each reproduced coordinate, reduction through `photon.Carrier`, retention of future behavior, and the relationship between residual functions and exact state representations. Its Boolean cube is a mathematical reference representation. Native runtime programs use labelled superpositions and duplication; no host backtracking solver selects their answers.

The mathematical reading extends beyond this one equivalence: `photon` develops phase structure, interference, projective observations, compatible differential presentations, finite-prefix completion, Cauchy completion, and operator-domain constructions. These establish distinct structures with explicit hypotheses. The analytic realization discussed in comments should not be silently promoted to an additional checked theorem. Likewise, semantic transport across equivalent presentations is not itself a theorem equating their C-runtime allocation or interaction counts.

## 2. A checked geodesic theorem

`InteractionGeodesic.agda` gives a precise version of the reduction-geodesic claim. Let `Step` be a relation on objects and assume its **one-step diamond**:

    s â’ a and s â’ b imply
    a = b, or there exists c with a â’ c and b â’ c.

A `Trace n s t` has exactly n steps. If t is normal, the module proves:

1. Any available first step from s removes exactly one step from a complete positive-length trace to t (`peel`).
2. Two complete traces from the same s to the same normal t have equal lengths (`same-normalization-length`).
3. Consequently every such trace attains the minimum length among its competitors (`normalization-is-geodesic`).

The proof is constructive induction. Compare the chosen first step with the trace's first step. Equal successors leave the existing tail; a diamond supplies a common successor and the induction hypothesis removes one step from the tail. A purported outgoing step from the normal endpoint eliminates the base-case obstruction. Iterating this argument aligns the lengths.

This is a formalization of the classical random-descent argument, not a claim to have invented it. Its value here is the explicit grade: the diamond must close in **one step on each side**. Ordinary confluence with arbitrarily long joining paths is insufficient for this equal-length conclusion.

The theorem quantifies over reductions of a fixed initial object. Two nets with the same Boolean denotation can have different initial structure and different required counts. An interaction net satisfies that hypothesis by construction: every node has one principal port, so two distinct active pairs share no node, each rule rewrites only its own pair, and firing the two pairs in either order meets in one step on each side. Erasure is interaction too. So for a fixed net and demand, the counted interactions to its collapsed normal form are the geodesic.

There are therefore several useful optimality statements with different domains: minimum states among exact residual representations; minimum tour objective; minimum complete reduction length for a fixed net; and minimum computational cost over all representations/algorithms. The first three have concrete results here. The fourth does not follow merely by changing the quantifier in one of them.

## 3. Residuals characterize the continuation a SAT representation must retain

Fix an order of n Boolean coordinates. After a prefix p of length d, define its residual `r_p(z) = f(p ++ z)`. Two prefixes are equivalent precisely when every remaining assignment gives the same verdict. Let W_d be the number of distinct residual functions at that layer.

**Exact-state lower bound.** Suppose prefixes are encoded into states and a decoder, given a state and a suffix, reconstructs the original verdict. Prefixes mapped to the same state have equal residual functions: apply the decoder to any suffix. Hence an exact representation at this layer needs at least W_d states. The Agda module proves the factorization argument. The numerical counting corollary requires the finite layer/cardinality setup.

**Attainment as a representation.** Taking the residual function itself as the state realizes precisely these equivalence classes. This is a mathematical construction, not a free runtime procedure for discovering equivalence. A representation may carry sufficient evidence to make identification local; absent that evidence, constructing the quotient has its own cost. This is the connection to canonical ordered decision diagrams; see [Bryant's original paper](https://www.cs.cmu.edu/~wklieber/15817-f08/ieeetc86.pdf).

An instructive family is equality of two k-bit words. With all x coordinates before all y coordinates, the layer after x has **2^k** distinct residuals. For distinct words a and b, the suffix a distinguishes them. Interleaving x_i,y_i leaves only the accumulated mismatch state and the current unmatched bit: maximum width is three. At k=5 the measured diagnostic widths are:

    grouped:     1,2,4,8,16,32,17,9,5,3,2
    interleaved: 1,2,2,3,2,3,2,3,2,3,2

These are exact semantic continuation widths. They are not asserted equal to HVM heap size or interactions. They identify where a presentation exposes or conceals reusable future behavior.

## 4. Observation contracts and the measurement method

The elementary SAT suite contains 27 instances and four demands each:

- `answers`: reduce the Boolean observation, without a promise to preserve branch multiplicity.
- `carrier`: expose every original coordinate paired with its verdict.
- `models`: expose every satisfying coordinate.
- `first`: request one satisfying coordinate through HVM collapse.

The host truth-table oracle validates only these small cases and computes diagnostic widths. Its exponential work is explicitly outside the claimed runtime algorithm. Larger experiments use construction-based facts or witness checking, not a host solver that supplies the answer.

`build_profile.py` copies the pinned HVM C source and instruments the existing interaction increment sites. It additionally distinguishes equal-label and different-label DUPâ“SUP events. Completed profiled cases are checked against the original runtime for identical output and total interactions. Rule totals sum to the original counter. This is instrumentation validation, not a formal semantics-preservation proof. The runtime is [HVM4](https://github.com/HigherOrderCO/HVM4); exact binary hashes appear in receipts.

Timing samples use the original binary, with three repetitions for the larger SAT and TSP cases. They include process startup and parsing. Profiled timing includes instrumentation overhead and should not be presented as runtime performance. `heap_nodes` is cumulative allocation, not resident memory. A budget exit is inconclusive, never evidence of unsatisfiability. Source construction, parsing, output serialization, and integer bit costs must be included in any end-to-end complexity claim.

Representative elementary results:

| Instance and demand | Interactions | Outputs |
|---|---:|---:|
| XOR, all models | 114 | 2 |
| XOR, first model | 84 | 1 |
| Contradiction, all models | 30 | 0 |
| Simplified false, 10 coordinates, all models | 13 | 0 |
| Simplified true, 10 coordinates, all models | 6,171 | 1,024 |
| Late contradiction, 10 coordinates, all models | 9,372 | 0 |

The full-carrier demand for a constant false predicate still produces 1,024 coordinate/verdict pairs. The empty model demand does not. Retention in the process and eager serialization of every retained coordinate are different operations.

## 5. Predicting exact interaction counts before held-out execution

Consider the presentation

    F_n = (âˆ§_{1â‰i<n} (x_i âˆ¨ Âx_i)) âˆ§ x_n âˆ§ Âx_n.

For the emitted short-circuit conjunction followed by complete model filtering, the inferred cost model is

    T_short(n) = 9Â2^n + 16n âˆ’ 4.
    T_reverse(n) = n + 30.

Reversing the clauses exposes the contradiction first. Both presentations denote false. The model was frozen before running n=13,â¦,18. Every predicted total and per-rule count matched those twelve held-out runs. At n=18 the counts are **2,359,580 versus 48**. `cost_predictions.json` and `cost_results.json` preserve predictions and observations.

The short-presentation per-rule predictions are:

| Rule | Count |
|---|---:|
| AND-ONE | 2nâˆ’1 |
| AND-SUP | n+1 |
| AND-ZER | 2 |
| APP-LAM | 2^n+n |
| APP-MAT-NUM-MAT | 2^n |
| APP-MAT-SUP, APP-SUP, DUP-LAM (each) | 2^nâˆ’1 |
| DUP-NOD | 3Â2^n+3nâˆ’2 |
| DUP-SUP-DIFF | 2^n+nâˆ’1 |
| DUP-SUP-SAME | n |
| OP2-NUM-NUM, OP2-NUM-SUP (each) | n |
| OR-ONE | 2nâˆ’1 |
| OR-SUP | 2n |
| OR-ZER | n+1 |

Summing gives the displayed total. The formulas are an experimentally validated model informed by rewrite inspection, **not yet an Agda proof for all n**. The exponential term is especially informative: an empty output does not entail constant internal reduction work. Clause presentation determines whether the emitted net reproduces many false alternatives before filtering consumes them. This does not contradict geodesicity for either fixed net; it identifies the importance of constructing the net.

## 6. Engagement with NP-complete encodings

`np_experiment.py` emits pigeonhole CNFs, permutation constraints, one-hot graph three-colouring, and planted 3-CNF instances. It compares four presentations: native short-circuit operations, reversed clauses, strict numeric Boolean operations, and a gated continuation per clause. There are 120 cases: 99 finish and 21 reach the two-million-interaction budget.

Selected first-output or complete-unsatisfiable reductions:

| Instance | Short | Reversed | Gated |
|---|---:|---:|---:|
| PHP(5,4), unsatisfiable | 136,139 | 60,440 | 74,319 |
| PHP(6,5), unsatisfiable | >2,000,000 | 855,374 | 1,451,992 |
| K4, one-hot 3-colouring, unsatisfiable | 8,151 | 8,294 | 5,703 |
| Planted 3-CNF, n=22, seed 17 | 941,406 | 1,608,640 | 552,565 |
| Planted 3-CNF, n=22, seed 41 | 1,541,238 | 952,889 | 718,884 |

Here â>â means budget termination before completion. The n=26 cases also reach the budget. PHP(6,5) reversed takes approximately 0.053 seconds in the original-runtime measurements, with the machine/startup qualifications above. These instance families demonstrate concrete nontrivial reductions; they do not characterize worst-case SAT complexity. Planted satisfiable instances are not representative evidence for arbitrary unsatisfiable 3-CNF.

## 7. A nontrivial fibre transformation: colour frames

`ColorFrame.agda` formalizes the six permutations of three colours, their inverses, and invariance of inequality. For a graph with a designated edge, its endpoint colours are distinct. Represent those two colours by a frame applied to canonical colours c0,c1; transport the other vertices into that frame. Canonicalization and restoration are inverse, and edge validity is invariant.

The formal source representation already uses a frame for the distinct endpoint pair. It does not separately prove classification of every unrestricted endpoint pair into this representation. Every measured graph has the designated edge (0,1), making exclusion of equal endpoint colours valid.

The runtime reduces canonical assignments and retains the six frames needed to reproduce raw colourings. Every decoded output is checked against the graph, and raw/framed output sets agree:

| Graph | Outputs | Raw interactions | Framed interactions |
|---|---:|---:|---:|
| Triangle | 6 | 599 | 756 |
| K4 | 0 | 965 | 156 |
| K4 plus isolated vertices, 8 vertices total | 0 | 969 | 160 |
| Triangle plus isolated vertices, 8 vertices total | 1,458 | 17,806 | 24,416 |
| Path, 6 vertices | 96 | 4,399 | 4,496 |
| Path, 8 vertices | 384 | 17,347 | 14,168 |

The result is useful precisely because it includes regressions. Factoring the invariant predicate reduces its active coordinates, but reconstructing all frames and serializing all witnesses can cost more than it saves. Fibre preservation establishes exactness; the demand determines whether preserving the fibre requires eagerly exposing it.

## 8. Travelling salesman as minimum-cost loop reduction

The implementation and derivations are in [the TSP notes](../tsp_fibre/README.md). It reproduces the finite min-plus recurrence as an explicitly shared HVM graph, retains a minimizing closed Hamiltonian route, and checks the route against independent lower-bound certificates. This is a concrete weighted continuation quotient: prefixes with the same visited set and endpoint have the same available suffixes; adding the same suffix cost preserves the ordering of prefix costs.

At n=10, the potential-weight family reaches its certified optimum **220 in 187,641 interactions**. The otherwise analogous reference-expanding presentation reaches five million interactions without completion. All sixteen shared cases exhibit exactly the predicted arithmetic-rule count. There are no DUPâ“SUP interactions in this particular TSP encoding: its measured benefit comes from explicit sharing of a min-plus graph. The SAT/colour experiments separately exercise labelled SUP/DUP.

## 9. Proof and complexity obligations exposed by the work

A second obligation concerns presentation formation. An equivalence preserving all future observations can justify a representation change without establishing a cheap uniform procedure for constructing it. A theorem about arbitrary problems must charge that construction, residual evidence, output requirements, and bit representation. Minimal residual cardinality alone is a lower bound on representation size at a fixed interface, not a lower bound on every algorithm's time.

The current repository's projection and transport theorems should be read at their declared types. For example, the reflexive `answer-is-projection` equality in `AnswerIsProjectionAtOutputSize.agda` does not quantify over SAT encodings or HVM counters. The unary arithmetic cost examples do establish costs for their chosen representations. The transport-overhead examples show why semantic equality can coexist with additional operational steps. The contribution here is to connect those distinctions to concrete measured reductions and an explicit geodesic theorem, rather than silently identifying their cost models.

The experiments support exact reproduction, continuation-sensitive factoring, strong presentation effects, and useful predictive cost models. They establish neither a polynomial bound for arbitrary SAT/TSP nor a universal minimum over all possible algorithms. Settling that stronger claim requires the missing uniform construction; no benchmark can replace that quantifier.
