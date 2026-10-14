# Evaluation cache rule (owner, verbatim)

The worker has identified the right change: retain the construction and substitute into its references. That removes the reason for the non-collapsing Glue/U codes. The evaluator can now use the stated cubical rules directly.

There is one concrete correction to the proposed evaluator: a reference’s WHNF can depend on the ambient face. Do not store one unconditional WHNF per RefId. Here is the exact cache representation, including the sharing-preserving reduction of that context.

For a reference t, let S(t) contain its free dimension identities, including dependencies through its free term variables’ types, required faces, and other declared boundary data.

Define

\pi_S(\chi)

by taking the already normalized face DNF of \chi, removing literals whose dimension is outside S from each clause, then normalizing again.

Use

EvaluationKey:
    reference: RefId
    face: FaceId = project_face(ambient_face, support(reference))

and attach a table of these entries to each reference:

EvaluationEntry:
    state: UNEVALUATED | RUNNING | READY
    result: present only when READY
    waiters: demands awaiting this same entry

This projection is justified directly. For every face formula \phi using only dimensions in S,

\chi\Rightarrow\phi
\quad\Longleftrightarrow\quad
\pi_S(\chi)\Rightarrow\phi.

In normalized DNF, entailment asks whether each clause of \chi contains a clause of \phi. Removing literals outside S cannot change that containment.

For a closed R, S(R)=\varnothing, so every consistent ambient face projects to \top. Thus the two applications in

(\lambda f.(f\,a,f\,b))(\lambda x.R)

still reach one reference and one evaluation entry. This does not reintroduce duplicated evaluation merely because the callers have different irrelevant face assumptions.

The empty face remains empty under projection. Evaluation there returns an empty-face result; it must not export an arbitrarily chosen constructor to a nonempty context.

The reason an unconditional cache is wrong is elementary. For a neutral path p:a_0=a_1,

p@i

is neutral under \top, reduces to a_0 under (i=0), and reduces to a_1 under (i=1). Those are different valid observations of the same reference.

The corresponding evaluator contract is:

whnf(reference, ambient_face):
    chi = normalize(ambient_face)
    if chi == false:
        return EMPTY_FACE
    eta = project_face(chi, support(reference))
    key = (reference, eta)
    if entry[key] is READY:
        return entry[key].result
    if entry[key] is RUNNING:
        attach this demand to entry[key].waiters
        suspend this demand
    otherwise:
        mark entry[key] RUNNING
        evaluate the reference under eta
        publish the result as READY
        resume its waiters

RUNNING is not a neutral value. It records a shared computation in progress.

Keep the immutable reference intact when publishing the result. A result obtained under \eta belongs to that evaluation entry. It must not overwrite the origin or install an unconditional forwarding pointer on the RefId.

In particular:

reindex(t, sigma)

always acts on the immutable reference t, not on a head previously obtained under a face that may cease to hold after substitution. This prevents the original Glue-collapse bug from returning through the cache.

The remaining evaluator behavior agrees with the worker’s plan:

Operation	Required action
Application	Demand the function head; apply its retained term-binder handle.
Projection	Demand the pair head; select its existing component reference.
Path application	Check entailed endpoints first; otherwise demand the path head and apply its dimension binder when available.
Glue introduction/type	Collapse to the glued component only under an ambient face entailing its Glue face.
Unglue	Use the equivalence map on the Glue face; otherwise use introduction–elimination or retain a neutral elimination.
System	Use a covering branch when one covers the context; otherwise retain/distribute over the covering system.
Composition	Check tube-face coverage first; otherwise demand the family head at its fresh symbolic dimension and dispatch to the stated structural clause.
Global definition	Unfold to a view of its fixed body origin.

For composition, obtain component references once from that symbolic head. Instantiate those references by reindexing. Do not reconstruct a component by evaluating the entire type line again at an endpoint.

The partial components retain their guards:

* A is the base-family reference.
* T and e remain available under \alpha.
* \delta=\forall i\,\alpha supplies their availability throughout the composition line.
* At the endpoint, \alpha_1 supplies the endpoint availability used by fibre extension.

Two terminology points keep the implementation precise:

* The artificial gen sentinel disappears. The fresh symbolic dimension shared by the family and tube remains.
* The special neutral case introduced to accommodate that sentinel can disappear. Genuine neutral terms remain: composition over a genuinely neutral type family must retain its family, tube, face, and cap.

And yes: the levelled lambda-net machinery is superseded as the mechanism carrying sharing in this representation. References identify instantiated cells; evaluation entries share their face-sensitive computations; duplicating a descriptor retains those references. Useful allocation or scheduling infrastructure can remain, but there is no need to maintain a second Lamping representation of the same dependency structure.

With that cache rule, the worker’s proposed implementation follows the scope representation without losing the point-dependent cubical reductions that motivated it.
