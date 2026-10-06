# Directional synthesis: the fibre calculus as a geodesic SAT machine

This note preserves the user's central direction for future work. The fibre
object is already universal. The work is to instantiate it faithfully with
the Boolean cube and clause boundaries, preserve shared coordinates, and
price the resulting reduction in the interaction net that executes it.

## The intended object

Start with one global binary object X = Bool^N. A clause is a projection
condition on a three-coordinate face. Its falsifying pattern is one local
point; pulling that point back along the coordinate projection gives the
excluded cylinder in the full cube. Every occurrence of a variable is
attached to the same global coordinate. A negated occurrence is the opposite
endpoint. The clause family is a composed boundary arrangement, not a
product of independent local cubes.

The SAT object is the surviving fibre of the composed predicate. A witness
is a point in that fibre. Counting is its cardinal reading. A Boolean verdict
is its support projection. A proof/witness carrier retains source and
evidence. These are readings of one classified object, with different
information forgotten or retained.

“The fibre equivalence alone does not search” is a precise constraint. The
equivalence transports a given object and its retained fibre. It does not
supply traversal, branch choice, or a complexity theorem for discovering a
quotient. Any selector, factorization, or normalizer must be represented as a
term and charged in the runtime cost receiver.

## Geodesic meaning

“Geodesic” has three indexed meanings. A fixed net and fixed normal-form
demand have a shortest terminating trace whenever one exists. Under an
exact one-step diamond, `InteractionGeodesic` proves every complete trace to
that normal form has the same length. A fixed boundary representation can
have a minimum exact continuation state or representative family; the
`SATFibre.Minimal`, `OptimalObservation`, and
`RepresentativeContinuation` arguments address this level. A minimum over
representations additionally includes translation, certificate construction,
execution, and output work.

The universal fibre theorem proves semantic losslessness. It does not make
these three geodesics equal. The first is `InteractionGeodesic` applied to the
net, whose one-step diamond holds by construction: distinct active pairs are
disjoint.

## Why clause overlap is the information core

For clause j, let E_j be its forbidden cylinder and S_i the survivors after
a chosen prefix. When the denominator is nonzero, the exact incremental
information is log2(|S_(i-1)| / |S_(i-1) minus E_j|). A fresh 3-clause retains
7/8 of a uniform cube and contributes log2(8/7). A redundant clause
contributes zero. A contradictory clause produces an empty fibre, a
structural zero rather than a finite entropy increment.

For a satisfiable formula, the endpoint information telescopes to
N - log2(#SAT(F)). The endpoint is order-independent; intermediate fibre
shapes are not. Those shapes determine sharing, factorization, duplication,
and runtime cost. Fixed forbidden-pattern information, clause-verdict
information, conditional survivor information, and interaction work are
different observations.

## The cut object and exact reduction

For a variable cut L|R, each crossing clause is A_j(l) or B_j(r). The left
assignment carries U(l) = {j | A_j(l) = false}, and the complete right
continuation is R_U(r) = F_R(r) and, for every j in U, B_j(r). Equal R_U
functions may share a deterministic continuation state. Different rows may
still belong to one cheaper representative span, which is the stronger
weighted continuation theorem in `RepresentativeContinuation.agda`.

For one-witness demand, U contained in W implies every completion of W is a
completion of U; a representative for U can replace a prefix with obligation
W. This preserves inhabitedness and reconstructs a witness. For #SAT it is
not lawful to discard W: its multiplicity is part of the fibre. The retained
fibre supplied by `photon.Fibre.lossless` is exactly the missing data.

## The runtime rules, read on the fibre

An end-to-end theorem should define a typed net state containing the current
boundary representation, retained obligation fibre, demand, HVM labels, and
interaction/allocation ledger. The interpretation sends a net state to the
corresponding SAT solution or residual family.

Equal-label `DUP-SUP` is branch projection in an already shared fibre.
Different-label `DUP-SUP` is commuting transport that creates shared
structures. `AND-ZER` and `OR-ONE` are erasing projections whose remaining
fibre is not demanded. `APP-SUP`, `AND-SUP`, and `OR-SUP` distribute a
continuation over a superposition and charge duplication work.

A lower bound can attach to a retained-distinction invariant: if two boundary
states have separating future continuations, a faithful demanded decoder
cannot merge them. Fooling families and factor-rank witnesses provide finite
instances of this invariant.

## TSP is the same boundary problem with a richer fibre

At a path-decomposition boundary, a partial tour is not determined by exposed
vertex degrees. Its connectivity partition is also required: the same
degrees can close into one Hamiltonian cycle or multiple disconnected cycles.
The continuation is the set of compatible completions of that partition.
Weighted representative sets preserve the cheapest completion for every
future boundary state. This is the natural next nontrivial target for the
fibre/runtime correspondence.

The existing Held–Karp experiments count paths and comparisons for a fixed
presentation. A fibre-level TSP implementation must additionally retain
connectivity, distinguish one-tour demand from all-tour counting, and charge
representative reduction itself. Only then can its HVM interaction count be
compared to the algebraic minimum.

## Permanent research rule

Every future claim should carry its object, observation, representation,
transition relation, and cost receiver in its statement. Positive and
negative results are both useful when their hypotheses are explicit. The
purpose of this note is to preserve the distinctions that let the universal
calculus become a concrete, testable geodesic machine.
