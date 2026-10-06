# Continuation checkpoint: SAT fibre/runtime work

This note is for restarting the research after context loss. It records the
current state, conclusions, boundaries, and next actions. It supersedes no
existing theorem and should be read with `THEORY_READING.md`,
`CLAUSE_GEOMETRY.md`, and `REDUCTION_FOUNDATIONS.md`.

## User's governing intent

Treat SAT as witness construction for a Boolean proposition, represented as
binary geometry and reduced through shared/coinductive fibres. Do not frame
the method as a search procedure or backtracking. Preserve the global
variable identifications across clauses. Work toward exact complexity and
interaction counts for Bend2/HVM4, and distinguish semantic reduction from
runtime work. The desired claim is a cost-optimal reduction where the net,
demand, representation, and interaction currency are all specified.

## What is already established in the repository

- `photon.Fibre.lossless`, `Carrier`, `Orbit`, `Nucleus`, and `Trace` provide
  lossless observation, future transport, and retained fibres.
- `SankramanaSesa` gives dependent-fibre composition:
  `fiber (g âˆ˜ f) z â‰ Î w:fiber g z, fiber f (fst w)`.
- `Lagakriya` gives the joint/conditional-fibre equivalence for two
  observables on one source.
- `FiniteInformation` proves descent through observations, exact
  reconstruction with side data, and finite side-information cardinality
  bounds. The decoder is typed on the image.
- `MyhillNerodeMinimalMachine` identifies complete future-behaviour
  quotients and proves their universal/minimal factorization property.
- `Anvaya` and `ChhayaRig` distinguish provenance, multiplicity, and Boolean
  support; an algebraic homomorphic section does not exist, although an
  ordinary set-theoretic choice can exist.
- `DesaSanghata` proves that coarse fibre censuses do not compose as a scalar
  graded cost; which outer points carry which inner fibres matters.
- `InteractionGeodesic` proves equal complete reduction lengths under an
  exact one-step diamond, which an interaction net has by construction:
  distinct active pairs are disjoint.
- `OptimalObservation` proves outcome-cardinality minimality for an injective
  lossless observation with equal cardinality.
- `DSOCutCalibration` proves a concrete strict hierarchy: two rectangle
  modes < three deterministic rows < four raw states.
- `TropicalReduction` proves minimum witnesses and common-continuation
  dominance for finite alternatives, with exact comparison counts.

## New checked modules in this session

`SATBoundary.agda` (SHA-256
`e3fe95de4c19c6c00d07ef3cc71c9e16280d922c5456eea01940619ea7171f14`) defines
split clauses `A(left) or B(right)`, the full solution type, the residual
obligation type, and an `Iso` between them. It proves obligation dominance,
representative witness reconstruction, preservation of emptiness in both
directions, preservation of the right assignment, and
`retained-reduction : Solution â‰ Î ReducedSolution (fiber reduce-witness)`.
The selector and dominance evidence are explicit arguments.

`RepresentativeContinuation.agda` (SHA-256
`56be086cc31bd3db0f9dae0912bfd1d4f5a5398801dc173d54eeec09e10dff19`) defines
cheap XOR combinations of retained rows. A spanning certificate proves:

1. every accepted original row has an accepted retained representative no
   more expensive;
2. a retained optimum is globally optimal for every continuation;
3. every attained original optimum has a retained representative of exactly
   equal cost;
4. emptiness is preserved in both directions.

Both final Agda checks exited 0 under Agda 2.8.0.1, Cubical v0.9,
`--safe --cubical --guardedness`; the command and source hashes are in
`boundary-proof-verification.md`. These proofs do not construct a minimum
basis, prove a SAT complexity bound, or prove an Agda-to-HVM compiler.

## Exact SAT specialization currently held

For a 3-clause with three distinct variables, one forbidden local pattern
extends to an excluded cylinder of size `2^(N-3)` and geometric dimension
`N-3`. A single clause retains `7/8` of a uniform cube, contributing
`log2(8/7)` conditional bits. A fixed forbidden pattern carries three
coordinate bits; the one-bit clause verdict is a different observable.

For cylinders `e_p`, incompatible partial assignments multiply to zero and
compatible ones union their assignments. The satisfying indicator is
`Î _j (1-e_pj)`. Inclusion-exclusion over compatible clause subsets gives
`#SAT = Î_J (-1)^|J| 2^(N-|union scopes|)`. This is an exact algebraic
derivation; it is not asserted to be a generally efficient representation.

At a variable cut, a left assignment has an obligation set `U(l)` of crossing
clauses whose left side is false. Its complete right continuation is
`R_U(r) = F_R(r) âˆ§ Î _{jâˆˆU} B_j(r)`. Identical `R_U` rows may share a
deterministic state. Inclusion `UâŠW` gives a satisfiability/witness
dominance relation, but not a counting equivalence unless multiplicities are
retained.

## Runtime semantics and cost facts

Pinned HVM source: `research/biology_exact/build/toolchain/HVM4-6defdfc7dae2a3cca5dd6e74ed0612385b5646a8/src/hvm.c`, SHA-256
`3d2724d0716b5d6b1c07a3b0b3c5cb89f848487a43d364ea689658f9aeb75fe7`.
`ITRS_INC` increments once per named interaction rule. `term_clone` and
term constructors allocate heap words without incrementing this counter.

Source-derived local allocation costs:

| HVM rule case | interactions | fresh heap words in body/helpers |
|---|---:|---:|
| DUP-SUP, equal labels | 1 | 0 |
| DUP-SUP, different labels | 1 | 4 |
| DUP-LAM, used binder | 1 | 5 |
| DUP-LAM, erased binder | 1 | 3 |
| DUP-NOD, arity `a` | 1 | `2a` |
| APP-SUP | 1 | 3 |
| APP-MAT-SUP | 1 | 5 |
| AND-SUP / OR-SUP | 1 | 3 |
| numeric AND/OR | 1 | 0 |

These are local contributions, not whole-program totals. `cnf_at` means
collapsed normal form, not conjunctive normal form. Collapse queue work,
printing, parsing, dispatch, source construction, and output are separate.
`heap_nodes` in profiles is cumulative allocation, not peak memory/RSS.

`-C1` (first result) and complete collapse are different demands, with
different normal forms and different geodesics.

Aspertiâ“Mairson's theorem that implementation cost of Levy-optimal shared
beta reduction is nonelementary is relevant motivation for charging
duplication explicitly, but does not prove a lower bound for this SAT net.

## External complexity results now connected

- Mik¡aâ“Nordstrm: fixed-width unsatisfiable CNFs have linear-length
  multilinear polynomial-calculus refutations, while size/monomial and degree
  can be large. [arXiv:1505.01358](https://arxiv.org/pdf/1505.01358), especially
  Proposition 2.3 and Theorem 2.2.
- Grochowâ“Pitassi: IPS makes the algebraic-circuit/proof-complexity bridge
  explicit; superpolynomial IPS lower bounds imply VP â‰  VNP.
  [arXiv:1404.3820](https://arxiv.org/pdf/1404.3820).
- Bodlaenderâ“Cyganâ“Kratschâ“Nederlof: weighted representative sets for
  connectivity use low-rank compatibility factorizations. Their TSP
  matching factorization has inner dimension `2^(b/2-1)` for an even boundary.
  [arXiv:1211.1505](https://arxiv.org/pdf/1211.1505), Â§Â§3.6â“3.7.
- Darwicheâ“Marquis: decomposability, determinism, smoothness, and query
  support distinguish compilation languages and supported operations.
  [A Knowledge Compilation Map](https://arxiv.org/pdf/1106.1819).

## Negative results already proved or derived

- `ChhayaRig` proves that positivity from natural-number multiplicity to Boolean support has no additive homomorphic section.
- `DesaSanghata` proves that coarse fibre censuses do not compose as a scalar graded cost: the placement of inner fibres over outer points is required.
- `SankramanaShreni` proves that meaning descends through the history quotient while a cost separating meaning-equivalent histories cannot.
- `AFoolingSetForcesDistinctRectangles` proves that a sound rectangle cover must assign distinct rectangles to pairwise fooling cells; its finite covering corollary supplies the corresponding cardinal obstruction.
- The SAT boundary dominance proof preserves inhabitedness and one witness; it does not preserve the complete solution fibre unless the retained fibre is carried. This is a theorem about the two different maps.
- A semantic state count, an algebraic derivation length, an interaction count, allocation, and output work are different receivers. Equality between any pair requires a proved correspondence.

## Highest-value next work

1. Implement a nontrivial representative-family SAT instance where the
   cheap-span certificate is supplied structurally, then compare interaction
   totals against an unreduced shared presentation. It must test the new
   theorem's behavior, not merely re-run an oracle-known truth table.
2. Extend the TSP boundary representation to retain connectivity partitions,
   then apply the representative criterion and compare exact HVM rule counts
   with the existing Heldâ“Karp counts. Track output witness, #tours, and
   minimum cost as separate fibres/receivers.
