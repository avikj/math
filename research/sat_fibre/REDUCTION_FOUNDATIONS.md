# From the Boolean algebra to an interaction cost

The central distinction is between the represented object, a derivation on
that object, and the cost of executing that derivation. The repository has
formal constructions for all three. The correspondence between a particular
SAT presentation and HVM's actual rules must retain all three coordinates.

**The finite algebra underneath the clause geometry.**

Fix a field K, N variables, and X={0,1}^N. Let

    R = K[x_1,...,x_N] / (x_1²-x_1,...,x_N²-x_N).

Evaluation identifies R with the algebra K^X of functions on assignments.
This can be proved directly: reduce every exponent to at most one, then use
the indicator polynomials

    δ_a(x) = Π_(i:a_i=1) x_i � Π_(i:a_i=0) (1-x_i).

They evaluate to the coordinate basis of K^X. There are 2^N square-free
monomials spanning R, so the evaluation map is an isomorphism. The δ_a are
orthogonal idempotents: δ_a²=δ_a, δ_aδ_b=0 for a≠b, and �_a δ_a=1.

A clause's forbidden cylinder has indicator e_j, a product of at most three
coordinate factors for 3SAT. The satisfying indicator

    f = Π_j (1-e_j)

is an idempotent in R. Its support is exactly the satisfying-assignment
fibre S. Multiplication by f is a projection whose image is K^S. Thus the
rank of this multiplication operator is #SAT, as an ordinary integer
dimension even if K has positive characteristic. Summing values inside a
field of positive characteristic, by contrast, only gives the count modulo
that characteristic.

There is also an exact quotient description:

    R / (e_1,...,e_m) � K^S.

Proof: restriction from K^X to K^S is surjective. Each e_j vanishes on S,
so the generated ideal is contained in its kernel. Conversely, define

    t_j = e_j Π_(i<j)(1-e_i).

These indicate the first violated clause, are pairwise orthogonal, and
sum to 1-f by telescoping. Any g vanishing on S satisfies

    g = g(1-f) = �_j [g Π_(i<j)(1-e_i)] e_j,

so it belongs to the generated ideal. This proves equality of the kernel
and the ideal, hence the quotient claim. Unsatisfiability is equivalently
f=0, or 1 belonging to that ideal, or the quotient being the zero ring.

This is the exact algebraic content of composing excluded faces and asking
what remains. It is not an analogy with algebraic geometry. The relevant
finite coordinate algebra, ideal, projection, and quotient are explicit.
These paragraphs are mathematical derivations, not new Agda declarations.

The isomorphism has an exponentially large coordinate basis. A small
factored expression for f is another representation of the same object.
The type-level isomorphism alone does not specify the work of moving between
those representations. That is precisely the setting of the repository's
CostGeometry and its distinction between transport and cost.

**A short algebraic derivation is already a theorem of SAT proof complexity.**

Mik�a and Nordstrm, Proposition 2.3, prove that every unsatisfiable fixed-k
CNF has a multilinear polynomial-calculus refutation of linear length.
Their recurrence is P_(j+1)=P_j+e_(j+1)-e_(j+1)P_j. Length counts polynomial
lines; size counts monomials. Their Theorem 2.2 states the size-degree bound
exp(Ω((D-W)²/N)), with D the required refutation degree and W the input
width. This is a precise example where few algebraic steps coexist with
large represented intermediate objects.
[Source, §2](https://arxiv.org/pdf/1505.01358).

Sharing changes the applicable proof model. Grochow and Pitassi's Ideal
Proof System represents certificates by algebraic circuits and explicitly
includes the Boolean axioms among the equations. Their Theorem 3.1 connects
superpolynomial IPS lower bounds to VP versus VNP. A monomial-size lower
bound is therefore not automatically a lower bound for an arbitrarily
shared circuit representation.
[Source, Definition 1.1 and Theorem 3.1](https://arxiv.org/pdf/1404.3820).

There is a useful trap to avoid in executing the quotient algebra. Given a
3CNF, its factored f has linear-size construction, but deciding f=0 in R
is exactly UNSAT by the indicator identity. Treating equality in this
quotient as a unit-cost primitive has moved the original decision into the
primitive. Ordinary polynomial identity testing in the unquotiented ring
is a different operation: x²-x vanishes on the Boolean cube without being
the zero formal polynomial. A reduction implementation must specify how
the Boolean identities act on its chosen shared representation.

**What the HVM counter actually counts.**

The source inspected is
[hvm.c](../biology_exact/build/toolchain/HVM4-6defdfc7dae2a3cca5dd6e74ed0612385b5646a8/src/hvm.c),
SHA-256 `3d2724d0716b5d6b1c07a3b0b3c5cb89f848487a43d364ea689658f9aeb75fe7`.
The following are direct source-level counts for the indicated rule body,
including its allocation helpers. They exclude subsequent reductions,
initial construction, dispatch, collapse traversal, and output.

| Rule case | ITRS increment | Newly allocated term-heap words |
| --- | ---: | ---: |
| DUP-SUP, equal labels | 1 | 0 |
| DUP-SUP, different labels | 1 | 4 |
| DUP-LAM, binder used | 1 | 5 |
| DUP-LAM, binder erased | 1 | 3 |
| DUP-NOD, arity a | 1 | 2a |
| APP-SUP | 1 | 3 |
| APP-MAT-SUP | 1 | 5 |
| AND-SUP or OR-SUP | 1 | 3 |
| AND/OR with numeric left operand | 1 | 0 |

For equal labels, DUP-SUP assigns the two existing SUP children to the two
copies. For unequal labels it forms two SUP nodes and leaves two further
duplications represented by projections from existing child locations.
The distinction is structural, not a test of semantic equivalence between
arbitrary residual functions. Source label discipline is therefore part of
the correspondence with the clause assignment object.

The counter is a selected rule-event counter. `term_clone` allocates a
shared slot without itself incrementing ITRS. `cnf_at` traverses and lifts
SUPs. The collapse queue uses a binary heap with SUP-depth and INC-credit
ordering; queue operations and printing are not counted interactions. Here
CNF means *collapsed normal form*, not conjunctive normal form.

Consequently a source-derived allocation contribution for just the rule
families in the table is

    4 D_diff + 5 D_lam_used + 3 D_lam_erased
    + �_a 2a D_node_a
    + 3 A_sup + 5 A_match_sup + 3 And_sup + 3 Or_sup.

It is a contribution, not a formula for the whole program's allocation.
Remaining rules, parsing, collapse, and other allocations must be included
for a total. It is cumulative allocation, not peak live memory or RSS.
An exact ITRS prediction likewise requires counting every charged event,
not assigning a uniform price to an algebraic macrostep.

Asperti and Mairson prove that L�vy-optimal shared beta-step counts do not
give an elementary bound on their implementation cost. Their result concerns
that optimality notion; it is not by itself a lower bound for this SAT
encoding on this HVM runtime. It explains why duplication work must remain
visible in the cost receiver.
[Primary paper](https://www.cs.unibo.it/~asperti/PAPERS/p303-asperti.pdf).

**Demand is part of the object whose geodesic is measured.**

`-C1` stops after an emitted result, whereas complete collapse continues
through the remaining branches. These are two demands, two normal forms, and
two geodesics.

The repository already supplies the deeper reason cost cannot simply be
read from meaning:
[MulyaVinimaya](../../formal/cubical/Kernel/MulyaVinimaya_TheValueOfATraceIsItsPairingWithAnEvaluatorPotentialsTelescopeAndADepthEvaluatorHasNonzeroCycleIntegral.agda)
defines cost-like evaluators on histories and proves when they telescope;
[SankramanaShreni](../../formal/cubical/Kernel/SankramanaShreni_TheLocalizationSequenceAsOneObjectMeaningDescendsAndCostDoesNot.agda)
exhibits meaning-equivalent histories whose costs cannot descend to the
meaning quotient. A minimum over histories may still exist. It is a new
observation of the history family, not the assertion that all histories
have that minimum cost.

**The two formal SAT/continuation contributions.**

[SATBoundary.agda](SATBoundary.agda) constructs the full equivalence between
split-clause solutions and residual obligations, for arbitrary index and
assignment types. Its representative reduction reconstructs an actual
satisfying assignment, preserves the right assignment, and preserves
emptiness in both directions. Its `retained-reduction` applies photon's
existing universal fibre equivalence to retain everything that the
representative map forgets. The selector and its dominance evidence are
explicit inputs; this file does not silently construct or price them.

[RepresentativeContinuation.agda](RepresentativeContinuation.agda) supplies
a more powerful representative criterion. For a compatibility row r_p and
cost c(p), give a finite XOR expression for r_p using retained rows whose
costs are each at most c(p). For any continuation q accepting p, an odd
number of those rows accept q, hence at least one does. The proof returns
that representative and its cost bound. It follows that a retained optimum
is a global optimum, and every attained global optimum has a retained
representative of exactly the same cost. The expression is fixed before q
is supplied: one certificate handles all continuations.

This criterion can discard a row without identifying it with a single
other row. It preserves the optimum over the family for every continuation.
That is why deterministic state minimization alone is too restrictive for
the demanded computation. The formal result assumes span certificates; it
does not implement basis construction or prove an HVM interaction bound.

For TSP, boundary degrees must be accompanied by connectivity of partial
paths. A completion can join the same exposed degrees into either one tour
or several cycles. In each compatible degree class, weighted representatives
can preserve the cheapest completion while forgetting other partial paths.
Bodlaender, Cygan, Kratsch, and Nederlof construct such reductions through
binary matrix factorizations; their matching factorization has inner
dimension 2^(b/2-1) for a nonempty even b-vertex boundary. This is the
relevant algorithmic route beyond merely identifying equal continuation
rows.
[Source, §§3.6�3.7](https://arxiv.org/pdf/1211.1505).

The next operational object is now specified: a clause or path boundary,
a certified representative transformation, the reconstruction fibre, and
the actual rule trace implementing it. Its cost must include constructing
the transformation, executing it, and satisfying the chosen output demand.
The existing universal calculus supplies the semantics; the new concrete
instances identify which representation-level operations need a costed
implementation.
