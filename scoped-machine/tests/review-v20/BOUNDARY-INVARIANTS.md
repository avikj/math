# Boundary composition is the machine invariant

This note preserves the mathematical interpretation developed with Avik alongside the implementation review. It is an organizing account of existing requirements, not a new primitive signature, protocol selection, or permission to replace the construction. The supplied *Witnessed Computation* synthesis is contextual material; its particular protocols and examples are not automatically binding implementation decisions.

The relevant source is an ongoing witnessed computation. A term, proof, identity, choice, network packet, pending result and resource commitment can all be data in that computation. Checking, constructing identities and applying identities are operations on that source, with reusable completed and unfinished work. Their C module names do not define separate mathematical worlds or a mandatory compile/run boundary.

## 1. Interior replacement and substitution

Let B be the exposed boundary type and X,Y,K : B → U families of interiors or compatible surrounding components. They connect through the SAME boundary value:

    X ⋆_B K = Σ(b:B). X(b) × K(b).

A boundary-preserving equivalence E : Π(b:B). X(b) ≃ Y(b) induces

    E_K(b,x,k) = (b,E_b(x),k).

Its inverse and inverse laws are pointwise. Therefore the same identity acts in every compatible context. For σ : B' → B,

    X[σ](b') = X(σ(b')),
    E[σ]_(b') = E_(σ(b')).

Replacing inside the context and instantiating the boundary both give

    (b',x,k) ↦ (b',E_(σ(b'))(x),k).

This is the mathematical obligation behind VIEW/TVIEW, scope capture/application, contextual signatures, and simultaneous substitution. Complete types, levels, guards and dependency-closed free declarations belong to the boundary when another component can depend on them. Images are substituted simultaneously; an image is not recursively re-substituted merely because its syntax mentions a source key.

A computed E has the same type and elimination as an initially supplied E. Runtime-derived identities must use the same action construction, context extension and substitution laws. Static registration and diagnostic names do not supply extra mathematical authority. Distinct path evidence must remain distinct wherever its dependent action can distinguish it.

Implementation consequence: preserve the existing generic runtime action and fixed templates. Do not introduce a separate type of privileged static identity, or a new C agent for each economic/application-domain concept.

## 2. Witnessed cells and Stokes

For the oriented cubical presentation, form C_n from the witnessed n-cells. The additive boundary is

    ∂_n σ = Σ_k (-1)^(k-1) (d_k^1 σ - d_k^0 σ),
    ∂_(n-1) ∂_n = 0.

For an execution edge e : s → t, ∂e = t-s. For independent residual interactions,

    ∂□ = e + (f/e) - f - (e/f).

The actual typed cell contains its ports, substitutions, dependent data and compatibility witness. Its signed chain is an additive observation of that richer object. Formal negative coefficients do not execute inverse physical work.

For an additive cochain a,

    (da)(σ) = a(∂σ),
    ⟨a,∂σ⟩ = ⟨da,σ⟩.

This is Stokes. Every matched internal interface appears with opposite signs and cancels. It is already what makes local replacement compose.

In a causal event net, one can independently express port accounting as

    port-boundary(e) = outputs(e) - inputs(e).

Summing over a finite execution cancels internal wire occurrences and leaves the external input/output frontier. A pending result, in-flight transfer or suspended continuation is an unclosed interface and remains represented. This port-incidence observation and the state/cubical boundary presentation must not be silently identified with one another; the implementation supplies their interpretation maps.

Substitution of witnessed cells respects their boundary:

    ∂(σ_* α) = σ_*(∂α).

The scope system therefore participates directly in the compositional invariant. Stokes is not postponed until an application is networked.

## 3. Cycles, quotient and the retained fibre

Three conditions carry different information:

    ∂z = 0                         a cycle closes;
    z = ∂α                         a supplied higher witness fills that cycle;
    q(s) = q(t)                    a selected observation cannot distinguish endpoints.

The abelian obstruction is H_1 = ker ∂_1 / im ∂_2. The typed source can also retain nonabelian path/transport information that H_1 forgets. For a family F : B → U, a loop p : b=b acts by transport_F(p) : F(b) ≃ F(b); this action can be nonidentity. For example, the square-root family over C\{0} sends the lift of z(t)=exp(2πit), starting at +1, to exp(πit), ending at -1.

For any observation q : S → B,

    fib_q(b) = Σ(s:S). (q(s)=b),
    S ≃ Σ(b:B). fib_q(b).

A directed execution returning the same observed b can change the retained fibre element u to u'. General computation inside the fibre need not be invertible; path transport in a family is the special equivalence case. Preserve that distinction.

A balance-returning service can change code, knowledge, evidence, commitments and future choices. Zero balance change does not authorize discarding its history or asserting that it did no work. A semantic quotient may hide those distinctions only for the stated observation; retained fibres keep them available for later refinement.

If q=p∘r refines through r:S→R and p:R→B,

    fib_q(b) ≃ Σ(ρ:R). (p(ρ)=b) × fib_r(ρ).

A richer query repartitions the retained source. It does not reconstruct lost data from a coarse endpoint.

## 4. Agency and compatible local histories

A general source can expose

    Step(s) = Σ(i:Agents). Σ(a:A_i(s)). Σ(s':S). Witness_i(s,a,s').

An agent selects an admissible action; its local transition carries the witness needed by the surrounding construction. Independent accepted events can provide commuting squares. Incompatible choices describe different possible histories and need not normalize to the same result. Schedule coherence does not select one policy for every agent.

For a deterministic input machine, equality of outputs under every future input word is a transition congruence. For nondeterministic/agent systems, the chosen behavioral quotient must preserve the required observations, action/control distinctions and continuation structure; a labelled bisimulation is one precise formulation. Present balance equality alone does not establish that congruence.

Runtime consequences: explicit dependencies determine which jobs block which other jobs. A suspended or released requester does not own the remaining progress of a shared producer. An unrelated kernel continuation is not an implicit dependency. The R1 review finding is a concrete violation of these dependency-local progress requirements.

## 5. Conserved flow and electronic cash

For the selected resource-location graph G, including pending locations,

    ∂_G[u,v] = v-u,
    b(t)-b(s) = ∂_G J(e)                    for every accepted event e:s→t.

Summing along a trace γ gives

    b(t)-b(s) = ∂_G J(γ),
    ΔB_U = ⟨1_U,∂_G J(γ)⟩ = ⟨d1_U,J(γ)⟩.

For a recursive allocation with

    a_v = f_v + h_v + c_v + Σ_w b_vw,
    ε_vw = b_vw-a_w ≥ 0,
    a_root = C,

cancellation yields

    C = Σ_v(f_v+h_v+c_v) + Σ_vw ε_vw,
    Σ_v h_v ≤ C.

The pending differences ε preserve the equation before downstream receipt. Local account data must be the checked fold of accepted history, including unreleased obligations.

For incompatible successors x #_h y, if every acceptable witness set for x meets every acceptable witness set for y in a maintained witness that cannot emit both, then in a single permitted history H,

    Cert_h(x;H) ∧ Cert_h(y;H) ⇒ ⊥.

Project H to that witness's local history to prove the result. Authentication names alone do not supply the maintained exclusion state. Together, local update correctness, exclusion, inherited boundary commitments and cancellation establish the global invariant at each finite causal cut.

This is the exact connection to electronic cash: accepted use cannot duplicate constrained authority, movement preserves the accounting boundary, and independent scopes compose without a mandatory total order. The concrete receipt/admission protocol supplies the stated premises. A successful pure-kernel test is not, by itself, evidence that an external physical protocol has implemented them.

Encode such programs using the existing typed state, witnesses, substitutions and actions. Do not select the rough PDF's particular witness policy as a new mandatory kernel policy.

## 6. Sharing, receipts, cost and geodesics

For actual event occurrences in a causal DAG D,

    W(D) = Σ_(e∈D) c(e).

If two demanded computations share the same event subgraph J,

    W(D1 ∪_J D2) = W(D1) + W(D2) - W(J).

Reading one receipt twice is not performing its certified event twice. Conversely, two events that were actually executed separately remain two events even if their outputs are equal. Sharing identifies common source work and valid reuse, not an after-the-fact erasure of execution cost.

An identity comparison Σ with ∂Σ=γ'-γ carries

    W(γ')-W(γ) = ⟨c,∂Σ⟩ = ⟨dc,Σ⟩.

For a balanced independent scheduling square, dc vanishes. Another witnessed identity may change the work required; its nonzero cost difference composes by cancellation of intermediate realizations. Higher coherence satisfies d(dc)=0. The fixed-recipe schedule theorem keeps its stated fixed ready-set/reuse-graph premises; arbitrary adapter choices are not silently covered by it.

A local optimality certificate is a potential Φ with Φ(z)=0 at targets and

    Φ(s) ≤ c(e)+Φ(t)                 for every admitted e:s→t.

With λ(e)=c(e)+Φ(t)-Φ(s)≥0, any target-reaching path satisfies

    W(γ)=Φ(s)+Σ_(e∈γ) λ(e).

A path with zero slack is globally minimal in that specified execution space. Every rule admitted into that space must be covered by the certificate premises. This is a mathematical certificate, not an instruction to introduce branch-and-bound, an incumbent/frontier, or a universal agent policy.

The C refinement concerns actual fine work, including implementation administration:

    k_- W_fine ≤ I_C-I_init ≤ k_+ W_fine

under the explicit machine/accounting model and its fixed constants. Count shared events once, and charge the actual work of discovering/using them. R3 identifies concrete operations still hidden inside supposed fine atoms; counting a whole variable-sized region after it finishes does not make budget-one service bounded.

## 7. Valuation and continuing execution

An agent's continuation valuation can be

    V_i(s)=sup_(γ∈T_i(s)) v_i(γ),
    v_i(γ)=Σ_(e∈γ) r_i(e).

A value-preserving embedding T_i(s)→T_i(t) proves V_i(t)≥V_i(s). V_i need not factor through the resource balance. Hence equal balance can accompany increased or decreased future value. Guaranteed value under independently controlled actions uses the corresponding policy quantifiers, e.g. sup over one's policy and inf over the other permitted policies; a common utility is not imposed.

An exact state potential has zero change on a closed full-state cycle. A reward cochain can have a nonzero period. A useful continuing service generally closes only a selected resource observation while the full source accumulates results and changes its available continuations.

Implementation consequences: unfinished work remains available to future requesters; UNRESOLVED describes a checking attempt rather than a negative theorem; changing the permitted budget can advance/retry it without poisoning semantic caches (R2). Conversely, explicitly retired, unreferenced storage must be reusable (R4). Keeping live evidence and losing ownership of dead buffers are different cases, distinguished by the actual dependency/ownership graph.

These equations belong in the interpretation and acceptance criteria of the current machine. They do not require a separate 'Stokes subsystem'. The implementation demonstrates them through its typed boundary substitutions, witnessed local actions, causal reuse, correct publication, progress, accounting and lifecycle behavior.
