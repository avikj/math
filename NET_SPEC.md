# The net: identities compiled to interaction agents

Direction document. Collected near-verbatim from the session of 2026-10-13.
It fills the gap in `docs/index.html` §5. Definition 5.5 says "for each pair
of cell kinds a rule gives a net R". Theorems 5.27/5.28 say "pose it together
with the identities available … only the identities remain to follow". Nothing
there says how an identity becomes a rule. This document does.

## 0. The missing link

Each identity equating constructions built from binary composition nodes and
unary transformation nodes compiles to interaction agent(s). Such an identity
can also be read as the difference of the two constructions being zero.

- **Annihilation by difference** is the quotient by the symmetry.
- **Substitution by equivalence** is transport along the path.

An equivalence or identity gives two things:
- a symmetry to quotient (annihilate) by;
- a dual, reversible path to transport (substitute) along.

Each such construction is an interaction agent.

These match Lafont's two rule shapes:
- **Annihilation.** A construction meets its own difference (p against p⁻¹).
  The pair cancels, and its auxiliary ports are rewired to each other. The
  higher cancellation witness is that rewiring.
- **Commutation.** An identity agent meets a construction node and passes
  through it as `cong`:
  - i ↦ f(p i) for a unary node;
  - i ↦ m(p i, q i) for a binary node;
  - (i,j) ↦ m(p i, q j) for independent changes.

So every pair of agent kinds gets its rule from the identities. No rule is
written by hand.

## 1. The identity agent (one uniform body)

Supplied identity: `p : Π (γ:Γ). L(γ) =_{B(γ)} R(γ)`.

**Forward.** Consumes `q : L(γ) = y` and produces a path `R(γ) = y`:

    E_p(q) = <i> hcomp^j_{B(γ)} [ (i=0) ↦ R(γ), (i=1) ↦ q(j) ] ( p(γ)(¬i) )

Here j is the composition direction. The bottom face is in parentheses; the
prescribed sides are in the brackets.

| Boundary | Required value | Supplied value |
|---|---|---|
| Bottom, j=0 | reversed p(γ) | p(γ)(¬i) |
| Left, i=0 | R(γ) | constant R(γ) |
| Right, i=1 | q(j) | q(j) |
| Bottom-left corner | agreement | p(γ)(1) = R(γ) |
| Bottom-right corner | agreement | p(γ)(0) = L(γ) = q(0) |
| Result's left endpoint | R(γ) | left side at j=1 |
| Result's right endpoint | y | q(1) = y |

**Reverse.** The other orientation of the same identity:

    E_p⁻¹(r) = <i> hcomp^j_{B(γ)} [ (i=0) ↦ L(γ), (i=1) ↦ r(j) ] ( p(γ)(i) )

Graph encoding of the forward body:

    inputs:  γ : Γ ;  y : B(γ) ;  q : Path(B(γ), L(γ), y)
    shared:  A = Apply(B, γ) ;  P = Apply(p, γ) ;  R0 = Apply(R, γ)
    bound dimensions:  i, j
    n0 = Not(i)
    n1 = PathApply(P, n0)
    n2 = PathApply(q, j)
    n3 = System(Face(i = 0, R0), Face(i = 1, n2))
    n4 = HComp(type = A, direction = j, sides = n3, bottom = n1)
    n5 = PathAbstract(i, n4)
    output: Pair(γ, Pair(y, n5))

The instruction contains no test for an equivalent expression. The supplied
proof p determines the whole replacement. An identity fires only where the
construction names it, never by searching the graph for a match.

## 2. Compound constructions: wire elimination

Internal wires are dependent variables. Connecting nodes forms the dependent
sum over those wires, and singleton contraction eliminates each determined
intermediate wire.

    left patch --eliminate internal wires--> G_L --E_p--> G_R --introduce right internal wires--> right patch

The elementary elimination goes from `Σ_b (f(a)=b) × (g(b)=c)` to
`g(f(a)) = c`:
- forward: `(b,s,t) ↦ ap_g(s) · t`
- inverse: `w ↦ (f(a), refl, w)`

The compiler recurses over the actual binary/unary construction. It does not
invent a transformation for each theorem.

## 3. Sharing with retained transport: Handle

    Handle_P(x) = Σ (r:X). P(r) × (r = x)

| Field | Meaning |
|---|---|
| r | representative |
| u : P(r) | payload |
| h : r = x | path |

- Read: `read(r,u,h) = coe(i ↦ P(h(i)), 0, 1, u)`.
- Canonical handle for `u : P(x)`: `(x, u, refl)`.
- `Handle_P(x) ≃ P(x)`, by contracting `Σ_r (r = x)` and transporting the
  payload along that contraction.

Given `p : x = y` and one payload `u : P(x)`:
- the references are `h_x = (x,u,refl)` and `h_y = (x,u,p)`;
- both reference the same payload node;
- `h_y` reads as `transport_P(p,u)`;
- a further identity `s : y = z` updates it: `(x,u,p) ↦ (x,u,p·s)`.

Consequences:
- The shared payload is the identified computational content.
- Each reference's path keeps its particular presentation.
- Reading a reference runs its path.
- Opposite paths cancel, with their higher cancellation witness.
- Distinct paths stay distinguishable until an identity between them is
  supplied.

## 4. Propagation through nodes

| Situation | Propagation body |
|---|---|
| Binary m, `p : a = a'`, `q : b = b'` | `i ↦ m(p(i), q(i))` |
| Unary f | `i ↦ f(p(i))` |
| Only one input changes | the other path is constant |
| Inputs vary independently | `(i,j) ↦ m(p(i), q(j))` |
| n independent inputs | `K(i₁,…,iₙ) = C(p₁(i₁),…,pₙ(iₙ))` |

In the independent square, the four edges are the two changes taken in both
orders, and the interior supplies their compatibility. For dependent ports,
the input is a well-typed cube in the whole telescope Γ.

## 5. Port-level interaction is a homotopy pullback (deep worker)

A construction `C : Γ → X` has:
- auxiliary ports Γ, a telescope;
- principal port X;
- node constraint `Node_C(γ,z) := (C(γ) =_X z)`.

The active pair is `Active_{C,D}(γ,δ) := Σ (z:X). (C(γ)=z) × (D(δ)=z)`, and
`Active_{C,D}(γ,δ) ≃ (C(γ) = D(δ))`. Firing an active pair *is* the cut.

    cut(z,u,v)        = u · v⁻¹
    uncut(h)          = (D(δ), h, refl)
    replaceLeft(p,h)  = p⁻¹ · h          restoreLeft(p,h)  = p · h
    replaceRight(r,h) = h · r            restoreRight(r,h) = h · r⁻¹

Example. Associativity `α : (a⋆b)⋆c = a⋆(b⋆c)` compiles to
`h ↦ α⁻¹ · h : a⋆(b⋆c) = y`.

### Annihilation

    difference_p(h) = p⁻¹ · h : y = y
    restore_p(ℓ)    = p · ℓ
    (x = y) ≃ (y = y)
    Σ (h : x = y). (h = p) ≃ 1

The contraction, valid at every dimension:

    contract(h,k)(i) = ( k(¬i) , λj. k(¬i ∨ j) )

Its endpoints: `contract(h,k)(0) = (p, refl)` and
`contract(h,k)(1) = (h, k)`.

When the representative is itself input data:
`Σ_p Σ_h (h = p) ≃ T`, via `(p,h,k) ↦ p` and `p ↦ (p,p,refl)`.

### Splicing

    ((a,b) = (a',b')) ≃ (a = a') × (b = b')                    parallel
    ((a,b) = (a',b')) ≃ Σ (p : a = a'). transport_B(p,b) = b'  dependent

For a general binary m, the relation `m(a,b) = m(a',b')` stays as it is
until an applicable identity decomposes it. Matching operation names alone
supplies no equivalence.

### The rule contract

    Real(P,β) := Σ (internal wires w). Π (nodes v). NodeConstraint_v(β,w)
    Rule(P,Q) := Π β. Real(P,β) ≃ Real(Q,β)

The rule record is `forward`, `backward`, `backwardForward` and
`forwardBackward`, with the boundary β fixed. A deletion
`Σ_β R(β) → boundary` is lossless exactly when every `R(β)` is contractible.
The decoder supplies the contraction's centre.

## 6. Ports: one principal port, inputs in any order, in any grouping

A chain of cells waiting one input at a time forces an order of arrival. That
order is extra structure the math never asked for, so it is a failure. Inputs
must be accepted in any order and in any grouping, and partial application is
central.

### Port type

    Σ (T ⊆ remaining, T dependency-closed given S). Π_{k∈T} A_k

### State

The state is S ⊆ Idx, holding the partial product `Π_{k∈S} A_k`. Receiving a
block T moves the agent to S ∪ T in one step.
- The states form `{0,1}ⁿ`, the n-cube.
- Receiving one indexed input is |T| = 1, a path along an edge.
- Receiving a larger block is a diagonal across a face.

### Coherence

Every route from S to the full set is identified:
- `Π_{T⊔U} A ≃ Π_T A × Π_U A` gives the diagonals;
- the cube's squares K give the edge orders;
- pairwise commutation suffices (`abstracts/14_pairwise_commutation_gives_every_order.md`).

Currying in either order is the same equivalence:
`A×X→U ≃ A→(X→U) ≃ X→(A→U)` (`CHU_LOSSLESS_INTERACTION.md`).

### Dependency

If A_k depends on A_j and j ∉ S, then either T includes j, or T carries k's
type as a function of j. For independent inputs any subset is allowed. No
order is forced beyond what the types require.

### Overlap is a gluing condition

Inputs that are not independent meet at a face and must agree there. This is
the CRT case:
- residues glue exactly when each pair agrees mod gcd;
- coprime moduli are independent dimensions.

Source:
`formal/cubical/theorems/residue/CompatibleResiduesGlueModuloTheLeastCommonMultipleAndTheFibreInsideTheProductIsTheProductOverTheLcm.agda`.
Order-dependence where no cell is supplied shows the observed state was never
produced by any source (`abstracts/14`).

### Diamond

The agent keeps one principal port, so Lafont's disjointness proof of 5.11
applies unchanged. Simultaneous arrivals at one port are sequenced. The
sequence is whatever happens, not a fixed order, and every sequence is equal.

## 7. Lowering the primitives

Each piece is transcribed from its source, not invented.

| Piece | Source and lowering |
|---|---|
| transp / hcomp per type former (Π, Σ, Path, Glue, U) | CCHM. Each equation is a commutation rule between the transp/hcomp agent and the type former's agent; the right-hand side is R. |
| Duplication and interval substitution under binders | Lamping 1990; Gonthier–Abadi–Lévy 1992; Asperti–Guerrini, *The Optimal Implementation of Functional Programming Languages* (bracket/croissant agents). |
| Face formulas | Free De Morgan algebra on finitely many generators: a fixed small rule set of agents. Not a C primitive. |
| Cells needing several inputs (e.g. hcomp needs the type head and φ) | §6 ports. Never a fixed-order chain. |

## 8. Prohibitions (the recorded failures)

- No number primitives; elements are abstract.
- No conversion or equivalence test anywhere. Equality is always a supplied
  path.
- No per-theorem hand-written transformation. Rules come from §§1–5.
- No search for where an identity applies.
- No fixed input order (§6).
- No extension as type, no arithmetic as evaluation, no hand-copying of
  outputs between programs.
- Nothing runs before everything is written and reviewed.
