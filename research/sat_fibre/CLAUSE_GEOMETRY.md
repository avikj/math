# Clause geometry, conditional information, and the cost of reduction

This is a mathematical derivation from the repository's existing fibre,
information, and cut results. It adds no benchmark and claims no new
kernel-checked theorem. Its purpose is to specify the SAT objects and the
quantifiers needed to apply those results to an interaction-net execution.

Subsequent work: [Reduction foundations](REDUCTION_FOUNDATIONS.md) follows
the algebra down to proof complexity and runtime costs. Its companion
`SATBoundary.agda` and `RepresentativeContinuation.agda` now check the
boundary equivalence and representative reconstruction statements; their
scope and explicit hypotheses are described there.

Let V be a finite set of N variables and X = Bool^V. A non-tautological
clause with three distinct variables has a unique falsifying partial
assignment p on its scope S. Its excluded cylinder is

    E_p = { x : X | x restricted to S = p }.

It fixes three coordinates: |E_p| = 2^(N-3). Its cubical dimension is N-3,
not N-2. Here "cube" means a Boolean assignment cube; its geometric
realization is a coordinate face. A formula F excludes the union of these
cylinders, so its satisfying assignments are X minus that union. Repeated
variables must first be identified: a clause may then have a smaller scope,
or become tautological and exclude nothing.

This identification is substantive. Literal occurrences are restrictions
of ONE assignment x, not independent local choices. Negation reads the
opposite value of that same coordinate. The joint solution type is

    Î x : X . Î  j . clause_j(x) = true.

Restriction to overlapping scopes gives the pullback compatibility
conditions. The repository's pullback coupling and dependent pushforward
theorems already apply to this object; it does not require another universal
construction.

**The exact information account is conditional.**

Write S_i for the assignments satisfying the first i clauses and
r_i = |S_(i-1) intersect E_i|. Then

    |S_i| = |S_(i-1)| - r_i.

Under the uniform distribution on the preceding survivors, conditioning on
the next clause being satisfied reduces entropy by

    Î”_i = log2(|S_(i-1)| / |S_i|),

provided S_i is nonempty. For a single fresh three-variable clause this is
log2(8/7), approximately 0.192645 bits. Fixing its forbidden pattern carries
three bits; merely retaining the one-bit verdict is a different operation.
The verdict's Shannon entropy under the uniform input is h2(1/8), also a
different quantity. A three-input Boolean gate does not by itself establish
a loss of exactly two bits: its two fibres need not have equal sizes.

For a satisfiable formula the increments telescope:

    Î_i Î”_i = N - log2(#SAT(F)).

The total is invariant under clause order, while the increments and
intermediate representations need not be. A redundant clause contributes
zero. If a clause removes every survivor, conditioning on satisfaction is
undefined; the exact object is the empty fibre, not a finite entropy value.

This is the finite counting reading of
[Lagakriya](../../formal/cubical/theorems/historical_proofs/Lagakriya_TheConditionalFibreIsWhatTheSecondCountStillCostsOnceTheFirstIsKnown.agda):
the joint fibre is the second observable's fibre INSIDE the first fibre.
[BharaGana](../../formal/cubical/theorems/cost/BharaGana_MassIsConservedPermutedAndMultipliedThePreLogarithmicSecondLaw.agda)
proves product mass for independent weights;
[GhataLekha](../../formal/cubical/theorems/cost/GhataLekha_EntropyIsTheExponentTheLogIsExactOnPowersAndAdditiveBecauseMassMultiplies.agda)
proves exact additive exponents on powers of two. Seven surviving local
assignments are not a power of two. The logarithmic formulas above are
ordinary finite-probability derivations, not assertions that GhataLekha
already formalizes real logarithms.

**The excluded geometry has a direct algebra of reproduction and reduction.**

Associate to each consistent partial assignment p its cylinder indicator
e_p : X â’ â. The empty partial assignment gives 1. Pointwise multiplication
obeys

    e_p e_q = 0             if p and q disagree on an overlap;
    e_p e_q = e_(p union q) otherwise.

Thus the satisfying indicator is exactly

    [F] = Î _j (1 - e_(p_j)).

This reproduces and composes forbidden patterns. It needs no traversal of
full assignments. Expansion followed by compatibility reduction gives

    #SAT(F) = Î_(J compatible) (-1)^|J| 2^(N-|union_(j in J) scope(p_j)|).

The empty J contributes 2^N. Compatibility means ALL shared variables have
the same prescribed value, not that scopes are disjoint. This is
inclusion-exclusion with each intersection evaluated geometrically.

One executable presentation retains integer coefficients k_i(p) of distinct
partial assignments after i clauses. Start with k_0(empty)=1. To compose
clause q, retain k_i(p), and for each compatible p subtract k_i(p) from the
coefficient of p union q. Combine equal patterns and remove zero
coefficients. The update preserves the displayed indicator identity by
distributivity. The final count is Î_p k_m(p) 2^(N-|scope(p)|).

If K_i is the number of retained nonzero patterns, this presentation performs
Î_i K_i pattern-compatibility attempts and at most that many union updates,
apart from initialization, copying, and final evaluation. Those are exact
algebra-operation counts, not HVM interaction counts. Pattern operations,
map operations, integer arithmetic, and their representation must be charged.
There are at most 3^N partial assignments and at most 2^i contributing clause
subsets at stage i, so K_i â‰ min(3^N, 2^i). This is a bound on this
presentation, not a lower bound for SAT. Intermediate coefficient bit lengths
are O(i), since their absolute values are bounded by 2^i.

Equal-pattern aggregation is also not semantic normalization: the indicators
are linearly dependent. For a variable v outside p,

    e_p = e_(p,v=0) + e_(p,v=1).

That identity enables another reduction, coalescing adjacent excluded faces.
Idempotence e_pÂ²=e_p removes duplicate exclusions. If p is contained in q,
then e_p e_q=e_q, and

    (1-e_p)(1-e_q) = 1-e_p.

A larger excluded cylinder absorbs a smaller one. These identities explain
sharing, cancellation, and factoring at the level of the geometry itself.
They do not establish that this particular expanded representation is
smallest. The representation may remain factored to avoid materializing the
expansion.

**At a cut, the useful state is a remaining obligation.**

Partition the variables into L and R. Separate wholly left clauses F_L,
wholly right clauses F_R, and c crossing clauses. Write each crossing clause
as A_j(l) or B_j(r), with its literals divided by the cut. For a left
assignment l satisfying F_L, define

    U(l) = { j | A_j(l) = false };
    R_U(r) = F_R(r) and Î _(j in U) B_j(r).

Then F(l,r) = R_(U(l))(r). A left assignment failing F_L has the zero row.
This supplies a concrete decoder from an obligation set to its complete
right-hand continuation predicate. There are at most 2^c obligation sets,
and at most 2^c+1 distinct rows including the possible dead row. Logical
equivalences among the R_U can reduce this further.

The exact deterministic quotient identifies U and W when R_U=R_W as
functions, not merely when they have the same number of satisfying
continuations. This is the SAT instance of
[MyhillNerodeMinimalMachine](../../formal/cubical/theorems/automata/MyhillNerodeMinimalMachine.agda).
[FiniteInformation](../../formal/cubical/theorems/number/FiniteInformation.agda)
gives the corresponding descent criterion and finite side-information bound:
a decoder can forget distinctions exactly when its target is constant on the
forgotten fibres. Its decoder is typed on the image, so unreachable states
do not require arbitrary answers.

There is another reduction when the demand is ONE satisfying witness.
If U is contained in W, then R_W implies R_U. If both obligation sets are
realized by left assignments, retain one left representative for each
inclusion-minimal realized obligation set. Every satisfying (l,r) can be
replaced by (l_U,r) for a minimal U contained in U(l), preserving r and
satisfaction. Conversely every retained representative is an actual left
assignment, so it introduces no spurious solution. Finite descent under
strict inclusion proves that such a minimal U exists.

This gives equisatisfiability and concrete witness reconstruction. It does
NOT preserve the entire solution fibre: dominated left assignments have
been discarded. To retain all assignments, keep their fibres; to count them,
keep their multiplicities. With

    w(U) = number of left assignments satisfying F_L with obligation U,

the exact count is

    #SAT(F) = Î_U w(U) # { r | R_U(r) }.

The same r appearing under different U denotes different complete
assignments and must be counted each time. Witness demand determines which
dominance reduction is lawful. A demanded future that later inspects the
discarded left assignment also makes that discard observable.

**Optimal factoring can be smaller than optimal deterministic sharing.**

Let M(l,r)=[F(l,r)]. A Boolean factorization through k modes is

    M(l,r) = OR_(a<k) P(l,a) AND Q(a,r).

Each mode denotes a sound rectangle. Distinct rows characterize the
deterministic quotient; the least rectangle cover characterizes this
different form of factorization. The existing
[DSOCutCalibration](../../formal/cubical/theorems/lattices/DSOCutCalibration.agda)
already certifies a strict separation: two factor modes, three distinct
rows, four raw states. Treating minimal distinct-row width as minimal width
for every SUP/factor representation would therefore contradict a result
already in the repository.

For SAT, grouping left assignments by their realized U supplies an exact
cover with at most 2^c rectangles. The general
[fooling-family theorem](../../formal/cubical/theorems/unplaced/AFoolingSetForcesDistinctRectangles.agda)
and its
[finite covering bound](../../formal/cubical/theorems/cost/NRectanglesCannotCoverSucNFoolingCellsEvenWhenTheCoveringIsOnlyAProperty.agda)
can prove matching lower bounds when the matrix has appropriate crossed
zeros. Such a lower bound concerns a specified cut and representation.
It becomes an interaction bound only after proving how interactions realize
or communicate those modes. A factored object can describe many modes
without allocating one runtime object for each mode.

An overlapping Boolean cover also cannot simply be read as a counting sum:
Boolean OR absorbs overlap, natural-number addition counts it. This is the
specific relevance of the repository's provenance-to-count-to-support
hierarchy. In established knowledge compilation terminology, decomposability
controls shared variables at products and determinism controls overlapping
alternatives at sums. The distinction between representation size and its
supported observations is developed in
[Darwiche and Marquis](https://arxiv.org/pdf/1106.1819).

**Geodesicity needs its operational coordinate.**

The information total N-log2(#SAT) has the same endpoints for every clause
order. Intermediate obligation counts, factor sizes, and interaction counts
can nevertheless differ. Consequently that endpoint scalar alone cannot
price a reduction route. This agrees with
[DesaSanghata](../../formal/cubical/theorems/cost/DesaSanghata_TheCensusComposesAndThatIsWhyCostIsNotAGradedMonoid.agda):
composition depends on which inner fibres lie over which outer points,
information absent from a coarse census. Execution length remains an
additive quantity on explicit histories; it is a different receiver.

For a fixed initial net and demanded normal form, a nonempty collection of
finite reductions has a least natural-number length. The already checked
[InteractionGeodesic](InteractionGeodesic.agda) proves more under its exact
one-step diamond hypothesis: complete reductions to the same normal form
have equal lengths. An interaction net satisfies that hypothesis by construction: every node has one principal port, so two distinct active pairs share no node, each rule rewrites only its own pair, and firing the two pairs in either order meets in one step on each side. Erasure is interaction too. Full normalization and stopping after
one emitted witness are distinct demands.

Minimum length for that net is also distinct from minimum over equivalent
presentations. Factoring the clause algebra, quotienting residuals, changing
the variable cut, or retaining fewer observations can change the starting
net. The repository's
[CostGeometry](../../formal/cubical/theorems/number/CostGeometry.agda)
already makes translation and execution costs separate coordinates of such
a comparison.

The concrete optimality target is therefore a package: a specified demand,
a representation of the coupled boundary, permitted representation changes,
an execution and cost interpretation, and an attaining reduction with a
lower bound in that same interpretation. A local interaction theorem can
settle scheduling for a net while a cut theorem settles necessary retained
distinctions. The two apply together only through a costed correspondence.

Finally, a Boolean assignment cube and the interval cube of Cubical Agda
are different objects. Kan composition requires compatible partial data in
the appropriate type; it does not make an arbitrary constraint family
inhabited. Bool has no path from false to true. The repository itself
distinguishes homogeneous composition from transport in
[Adhisthana](../../formal/cubical/theorems/physics/Adhisthana_TheFreeReversalStandsOnTheDeMorganSiteAndTheKanFloorHasTwoOperationsNotOne.agda).
The computational account of univalence is given by
[Cohen, Coquand, Huber, and Mrtberg](https://arxiv.org/abs/1611.02108).
For this SAT application, the precise connection is through typed families,
restriction maps, compatibility, and computational transport of the coupled
object. The geometric formulation is productive precisely because those
maps can be written down, composed, and priced.
