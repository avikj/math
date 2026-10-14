# Scope subsystem (owner, verbatim)

The scope subsystem below has a concrete representation, terminating algorithms, and a replacement table covering every constructor in the cubical core. Binder application composes substitutions on existing cell references. It does not instantiate an independent copy of a body.

The representation conventions are:

* Variables have unique internal identities; printed names have no operational significance.
* A cell origin is an immutable construction record.
* An instantiated cell is an origin together with a substitution restricted to that origin’s dependencies.
* An occurrence additionally records the context in which that instantiated cell is being used.
* Binder descriptors retain their owning cell reference, so successive reindexings compose through that owner.

These conventions make scope handling explicit without introducing new object-language types.

1. Identities, contexts, and references

Use distinct handle types:

typedef uint64_t TermVarId;
typedef uint64_t DimVarId;
typedef uint64_t ContextId;
typedef uint64_t OriginId;
typedef uint64_t RefId;
typedef uint64_t MapId;
typedef uint64_t IntervalId;
typedef uint64_t FaceId;
typedef uint64_t SymbolId;
typedef uint32_t BinderSlot;
typedef uint32_t FieldIndex;

A handle denotes an entry in an arena. Handle equality is identity of that entry. Interning checks complete structural equality after a hash match; a hash collision never identifies different records.

Term-variable declarations contain their types. Dimension-variable declarations identify interval variables. A context is an ordered telescope of those declarations together with a face assumption:

Context:
    declarations:
        DIM(dimension_variable)
        TERM(term_variable, type_reference)
    assumption: FaceId

A term variable’s type can depend only on declarations available at its declaration.

A cell reference has one of two forms:

VAR(variable)
VIEW(origin, substitution)

A VAR reference denotes the identified variable.

A VIEW denotes the specified origin under a simultaneous substitution. It retains the origin rather than constructing a separate syntax tree for the substituted expression.

An occurrence is:

Occurrence:
    reference: RefId
    context: ContextId

The occurrence context is not part of reference identity. The same closed cell can occur in several contexts without becoming several different cells.

An occurrence is valid when its context supplies its free variables, their required types, and its required face assumption.

2. Sparse simultaneous substitutions

A raw substitution is two finite maps:

RawMap:
    term_images: sorted [(TermVarId, RefId)]
    dimension_images: sorted [(DimVarId, IntervalId)]

An omitted variable maps to itself:

\begin{aligned}
\operatorname{termImage}(\sigma,x)
&=
\begin{cases}
t,&(x,t)\in\sigma,\\
\operatorname{VAR}(x),&\text{otherwise},
\end{cases}\\[2mm]
\operatorname{dimImage}(\sigma,i)
&=
\begin{cases}
r,&(i,r)\in\sigma,\\
i,&\text{otherwise}.
\end{cases}
\end{aligned}

Remove identity entries:

x\mapsto\operatorname{VAR}(x),
\qquad
i\mapsto i.

The empty map is identity.

A typed scope map packages this finite operation with its source and target contexts:

TypedMap:
    source_context: ContextId
    target_context: ContextId
    raw_map: MapId

For

\sigma:\Delta\to\Gamma,

the images of the variables declared in \Gamma are terms or interval expressions available in \Delta, with the appropriate substituted types. Its face condition is

\chi_\Delta\Rightarrow\chi_\Gamma[\sigma].

The raw-map operations below compute substitution. The context fields state where that substitution is valid. Changing an occurrence to a stronger face context does not require manufacturing a new term reference.

Simultaneous substitution performs one lookup at a variable. If

\sigma=[x\mapsto y,\ y\mapsto z],

then x[\sigma]=y, not z. The replacement returned by a lookup is not recursively subjected to the same substitution.

That convention applies equally to dimension images.

3. Cell-origin records

An origin records one construction and its immediate fields:

Origin:
    tag
    immutable_scalar_payload
    fields[]
    binders[]
    free_term_variables[]
    free_dimension_variables[]
    required_face
    typing_annotation

A binder declaration records:

BinderDeclaration:
    sort: TERM | DIMENSION
    formal_variable
    domain_type       // TERM binders only

A field records its kind and any binder or face under which it is interpreted:

Field:
    kind:
        TERM
        INTERVAL
        FACE
        TERM_BODY
        DIMENSION_BODY
        PARTIAL_TERM
        PARTIAL_DIMENSION_BODY
    value
    binder_slot       // body fields only
    guard             // partial fields only

The same binder slot can govern several fields. This is essential for a composition cell: its family and tube use the same composition dimension.

The dependency arrays are the free boundary of the origin. They include dependencies appearing in its fields, required face, and typing information. Bound variables are removed at their binding construction.

For example:

\begin{aligned}
FV(\lambda x.t)
&=FV(A)\cup(FV(t)\setminus\{x\}),\\
FV(\operatorname{comp}^{i}A[\phi\mapsto u]a)
&=
(FV(A)\cup FV(u))\setminus\{i\}\\
&\quad{}\cup FV(\phi)\cup FV(a).
\end{aligned}

Here A in the lambda equation is the declared domain type.

Dependencies required by the types of free term variables are included transitively. This prevents removing a dimension merely because it appears in the type of a retained variable rather than in the variable’s printed term.

4. Canonical instantiated-cell references

A view stores only the action on its origin’s declared dependencies:

\operatorname{VIEW}(C,\sigma)
=
\operatorname{VIEW}
\left(
C,\sigma|_{FV(C)}
\right).

Entries outside that boundary are discarded. Identity entries are discarded.

The resulting pair is interned:

make_view(origin, map):
    restricted = restrict_to_origin_dependencies(origin, map)
    normalized = remove_identity_entries(restricted)
    return intern_reference(VIEW(origin, normalized))

This restriction is operationally consequential.

If a body contains a closed cell R, then applying the enclosing function at arguments a and b gives

R[x\mapsto a]=R=R[x\mapsto b].

Both return the same reference because x\notin FV(R). They do not allocate two independent instances of R.

If a cell actually depends on x, its instances at a and b retain those different substitutions. Their common origin remains explicit.

A reference is therefore more specific than a code address: its identity includes the instantiated dependency boundary.

5. The complete reference-substitution algorithm

Let reindex(t, σ) denote substitution of raw map \sigma into reference t.

reindex(reference, sigma):
    if sigma is identity:
        return reference
    match reference:
        VAR(x):
            return term_image(sigma, x)
        VIEW(origin, tau):
            term_entries = []
            dimension_entries = []
            for x in origin.free_term_variables:
                old_image = term_image(tau, x)
                new_image = reindex(old_image, sigma)
                if new_image != VAR(x):
                    append (x, new_image) to term_entries
            for i in origin.free_dimension_variables:
                old_image = dimension_image(tau, i)
                new_image = substitute_interval(old_image, sigma)
                if new_image != interval_variable(i):
                    append (i, new_image) to dimension_entries
            rho = intern_map(term_entries, dimension_entries)
            return make_view(origin, rho)

This algorithm does not descend through the origin’s body.

It descends only through finite substitution data already attached to a reference. An ordinary recursive definition is represented by a symbol reference, not by a cyclic raw substitution record.

Consequently, scope substitution does not attempt to normalize a recursive program.

Memoize the pair

(reference, sigma)

if desired; the result is a pure function of that pair. Memoization changes neither the result nor its identity.

6. Composition of scope maps

Use the notation

\sigma;\tau

for “apply \sigma, then apply \tau”:

t[\sigma;\tau]=(t[\sigma])[\tau].

If

\sigma:\Delta\to\Gamma,
\qquad
\tau:\Theta\to\Delta,

then

\sigma;\tau:\Theta\to\Gamma.

The finite algorithm is:

compose(sigma, tau):
    term_keys =
        sorted_union(keys(sigma.term_images),
                     keys(tau.term_images))
    dimension_keys =
        sorted_union(keys(sigma.dimension_images),
                     keys(tau.dimension_images))
    term_entries = []
    dimension_entries = []
    for x in term_keys:
        image = reindex(term_image(sigma, x), tau)
        if image != VAR(x):
            append (x, image) to term_entries
    for i in dimension_keys:
        image =
            substitute_interval(dimension_image(sigma, i), tau)
        if image != interval_variable(i):
            append (i, image) to dimension_entries
    return intern_map(term_entries, dimension_entries)

Including keys present only in \tau is necessary. A variable omitted by \sigma is unchanged by the first substitution and can still be changed by the second.

When forming a cell view, restrict this composite to the origin’s dependencies afterward.

The identities are

\operatorname{id};\sigma=\sigma,
\qquad
\sigma;\operatorname{id}=\sigma,

and

(t[\sigma])[\tau]=t[\sigma;\tau].

Associativity follows by checking each variable image and the recursive reference action. No equality search between arbitrary terms is performed.

7. Interval substitution

An interval expression is a normalized finite antichain of clauses of signed dimension variables.

A clause denotes a meet; the collection denotes a join.

IntervalForm = set of Clause
Clause       = set of SignedDimension
SignedDimension = (DimVarId, POSITIVE | NEGATIVE)

The representations are:

0 = {}
1 = { {} }

Normalize by removing duplicate clauses and any clause that strictly contains another clause.

A clause containing both i and \neg i remains present. The interval algebra does not identify i\wedge\neg i with zero.

Operations:

interval_join(a, b):
    return normalize(a ∪ b)
interval_meet(a, b):
    return normalize({
        clause_a ∪ clause_b
        for clause_a in a
        for clause_b in b
    })

Negation uses De Morgan distribution:

interval_not(a):
    result = 1
    for clause in a:
        negated_clause = 0
        for signed_atom in clause:
            negated_clause =
                interval_join(
                    negated_clause,
                    singleton_clause(flip_sign(signed_atom))
                )
        result = interval_meet(result, negated_clause)
    return result

Substitution is:

substitute_interval(expression, sigma):
    result = 0
    for clause in expression:
        substituted_clause = 1
        for (i, sign) in clause:
            image = dimension_image(sigma, i)
            if sign == NEGATIVE:
                image = interval_not(image)
            substituted_clause =
                interval_meet(substituted_clause, image)
        result = interval_join(result, substituted_clause)
    return result

The retrieved dimension image is inserted once. Its variables are not recursively looked up again in \sigma.

8. Face substitution and decisions

A face formula is a normalized DNF of endpoint literals:

EndpointLiteral = (DimVarId, ZERO | ONE)
FaceClause      = set of EndpointLiteral
FaceForm        = set of FaceClause

Normalization:

1. Discard a clause containing both (i=0) and (i=1).
2. Remove duplicates.
3. Remove clauses strictly containing another clause.

Again,

false = {}
true  = { {} }

Conjunction and disjunction use the same DNF product and union operations, with the face-specific contradiction rule.

For an interval DNF r, compute endpoint faces directly:

(r=1)
=
\bigvee_{C\in r}
\bigwedge_{a\in C}(a=1),

(r=0)
=
\bigwedge_{C\in r}
\bigvee_{a\in C}(a=0).

For a positive atom i,

(i=\epsilon)

is its endpoint literal. For a negative atom,

(\neg i=\epsilon)=(i=1-\epsilon).

Thus:

substitute_face(phi, sigma):
    result = false
    for clause in phi:
        substituted_clause = true
        for (i, endpoint) in clause:
            interval_image = dimension_image(sigma, i)
            endpoint_face = endpoint_condition(interval_image, endpoint)
            substituted_clause =
                face_and(substituted_clause, endpoint_face)
        result = face_or(result, substituted_clause)
    return result

Entailment is:

entails(chi, phi):
    for clause_chi in chi:
        if no clause_phi in phi satisfies clause_phi ⊆ clause_chi:
            return false
    return true

Universal restriction along dimension i is:

forall_dimension(i, phi):
    return {
        clause in phi
        where clause contains no endpoint literal for i
    }

The result is already normalized if phi was normalized.

No rule introduces

(i=0)\vee(i=1)=\top.

9. Weakening and face restriction

With unique variable identities, weakening does not rename old variables.

For an inclusion of contexts

\Gamma\hookrightarrow\Delta

that retains the existing declarations and possibly adds declarations or strengthens the face assumption, its raw substitution is identity.

The occurrence changes context:

weaken_occurrence(Occurrence(ref, Gamma), Delta):
    return Occurrence(ref, Delta)

The reference is unchanged.

For a typed map

\sigma:\Delta\to\Gamma

and a face \phi over \Gamma, its restriction is

\sigma|_\phi:
(\Delta,\phi[\sigma])
\to
(\Gamma,\phi).

The raw substitution is again unchanged:

restrict_typed_map(sigma, phi):
    mapped_phi = substitute_face(phi, sigma.raw_map)
    return TypedMap(
        source_context =
            restrict_context(sigma.source_context, mapped_phi),
        target_context =
            restrict_context(sigma.target_context, phi),
        raw_map = sigma.raw_map
    )

This operation does not clone the partial term.

A reference’s availability under a stronger face is an occurrence judgment. The underlying reference remains shared.

10. Binder identities are instantiated from the owning reference

Each origin binder has a formal identity. Opening a particular cell view assigns that binder an instantiated identity:

instantiated_binder(owner_reference, binder_slot, sort)

Intern this triple. It returns a unique term-variable or dimension-variable identity.

The identity is distinct from all previously existing unrelated identities. Reopening the same owner returns the same instantiated binder.

This operation is name generation, not a semantic equality decision.

An instantiated binder’s declaration records its type when it is a term binder. That type is the binder domain reindexed by the owner’s substitution.

A fresh instantiated binder cannot already occur in the owner’s substitution images: the owner reference is constructed before its instantiated binder is created. The representation does not permit forging future binder identities or constructing cyclic substitution records.

This provides capture avoidance without scanning or renaming entire bodies.

11. Lifting under a term binder

Suppose the origin has a binder

x:A,

and the owner is viewed under \sigma.

Let

x'=\operatorname{instantiatedBinder}(\text{owner},s,\mathrm{TERM})

for its binder slot s.

Define

\sigma^{x\mapsto x'}
=
(\sigma\setminus x)\cup[x\mapsto x'].

The corresponding domain type is

A'=A[\sigma].

The body action is

t\longmapsto t[\sigma^{x\mapsto x'}].

Executable form:

lift_term_binder(owner, binder_slot):
    origin = origin_of(owner)
    sigma = substitution_of(owner)
    binder = origin.binders[binder_slot]
    require binder.sort == TERM
    x  = binder.formal_variable
    x2 = instantiated_binder(owner, binder_slot, TERM)
    domain2 = reindex(binder.domain_type, sigma)
    lifted = remove_term_entry(sigma, x)
    lifted = set_term_entry(lifted, x, VAR(x2))
    return:
        variable = x2
        domain = domain2
        substitution = lifted

The typed scope action is

(\Delta,x':A[\sigma])
\longrightarrow
(\Gamma,x:A).

All old variable images are retained. The new formal variable maps to the new bound variable.

12. Lifting under a dimension binder

For a formal dimension i, let

i'=\operatorname{instantiatedBinder}(\text{owner},s,\mathrm{DIMENSION}).

Define

\sigma^{i\mapsto i'}
=
(\sigma\setminus i)\cup[i\mapsto i'].

Executable form:

lift_dimension_binder(owner, binder_slot):
    origin = origin_of(owner)
    sigma = substitution_of(owner)
    binder = origin.binders[binder_slot]
    require binder.sort == DIMENSION
    i  = binder.formal_variable
    i2 = instantiated_binder(owner, binder_slot, DIMENSION)
    lifted = remove_dimension_entry(sigma, i)
    lifted =
        set_dimension_entry(lifted, i, interval_variable(i2))
    return:
        dimension = i2
        substitution = lifted

Every field governed by this binder slot uses this same lifted substitution.

For a composition origin, the family and the tube therefore receive the same i'. Generating separate fresh dimensions for those two fields would be incorrect.

13. Binder handles

A binder value records its provenance:

BinderHandle:
    owner: RefId
    binder_slot: BinderSlot
    body_field: FieldIndex

The handle does not contain a copied body.

Resolving it means:

1. Read the owner’s origin and substitution.
2. Obtain the instantiated binder for the indicated slot.
3. Reindex the indicated body field using the lifted substitution.
4. Return the bound variable, domain type when applicable, guard when applicable, and body reference.

The origin field determines whether this is a term binder, dimension binder, or partial dimension binder.

Reindexing a binder handle is particularly simple:

reindex_binder(handle, sigma):
    return BinderHandle(
        owner = reindex(handle.owner, sigma),
        binder_slot = handle.binder_slot,
        body_field = handle.body_field
    )

This is why the owner reference is retained. Reindexing does not reconstruct a new anonymous binder from a previously opened body.

Successive reindexings satisfy

(h[\sigma])[\tau]=h[\sigma;\tau]

because they satisfy that equation on the owner reference.

14. Applying a term binder

Resolve the handle to

(x',A',t').

For an argument a:A', application is

t'[x'\mapsto a].

apply_term_binder(handle, argument):
    info = resolve_term_binder(handle)
    substitution =
        singleton_term_map(info.variable, argument)
    return reindex(info.body, substitution)

There is no recursive body copy in this operation.

For example, opening a view of

\lambda x.t

under \sigma gives the body

t[\sigma^{x\mapsto x'}].

Applying it to a returns

t[\sigma^{x\mapsto x'};[x'\mapsto a]],

which is the original body with the external substitution retained and the bound input connected to a.

Any body cell not depending on x discards that entry when its view is formed.

15. Applying a dimension binder

Resolve the handle to

(i',t').

For an interval expression r, return

t'[i'\mapsto r].

apply_dimension_binder(handle, interval):
    info = resolve_dimension_binder(handle)
    substitution =
        singleton_dimension_map(info.dimension, interval)
    return reindex(info.body, substitution)

For a partial dimension binder, return both the substituted guard and the substituted body:

apply_partial_dimension_binder(handle, interval):
    info = resolve_partial_dimension_binder(handle)
    substitution =
        singleton_dimension_map(info.dimension, interval)
    return Partial(
        guard = substitute_face(info.guard, substitution),
        body = reindex(info.body, substitution)
    )

In a composition tube the guard is independent of the composition dimension, so this substitution leaves that guard unchanged. The general operation is nevertheless defined correctly when a partial binder’s guard does mention its bound dimension.

16. The complete constructor signature

The origin tags are:

UNIVERSE
PI
SIGMA
LAM
APP
PAIR
FST
SND
PATH
PLAM
PAPP
GLUE_TYPE
GLUE_INTRO
UNGLUE
COMP
SYSTEM
GLOBAL

Variables use VAR references and do not require an origin tag.

The fields are:

Tag	Origin fields and binders
UNIVERSE	Scalar universe level \ell
PI	A; term binder x:A; body B
SIGMA	A; term binder x:A; body B
LAM	A; term binder x:A; body t
APP	f,a
PAIR	a,b
FST	p
SND	p
PATH	Dimension binder i; family B; endpoints l,r
PLAM	Dimension binder i; body t
PAPP	Dimension binder i for family B; endpoints l,r; path p; interval s
GLUE_TYPE	A,\phi,T,e, with T,e under \phi
GLUE_INTRO	A,\phi,T,e,t,a, with T,e,t under \phi
UNGLUE	A,\phi,T,e,v, with T,e under \phi
COMP	One dimension binder i; family A; face \phi; tube u under \phi; cap a_0
SYSTEM	Ordered finite branches (\phi_k,t_k)
GLOBAL	Symbol identity and its declared parameter boundary

The explicit Glue descriptor fields prevent scope handling from requiring a separate operation to reconstruct a value’s Glue type.

The path-application fields retain the family and endpoints needed for endpoint reduction even when the path is neutral.

There are no additional NAPP, NFST, or NCOMP syntactic forms. A blocked application remains an APP cell; a blocked composition remains a COMP cell. Blockedness belongs to evaluation state.

17. Opening one cell

open(reference) exposes one constructor and its reindexed immediate fields. It performs no beta reduction and no recursive unfolding.

Its result is a finite head recipe:

HeadRecipe:
    owner: RefId
    head_tag
    scalar_payload
    fields[]

The owner is retained in the recipe.

For a variable:

open(VAR(x)):
    return HEAD_VAR(owner = VAR(x), variable = x)

For a view:

open(VIEW(origin, sigma)):
    return the constructor-specific recipe below

All ordinary term fields use reindex(field, sigma).

All interval fields use substitute_interval(field, sigma).

All face fields use substitute_face(field, sigma).

All binder fields become BinderHandle(owner, slot, field_index).

Partial ordinary fields become

Partial(
    guard = substitute_face(original_guard, sigma),
    body = reindex(original_body, sigma)
)

These cases are exhaustive for the field kinds in the origin record.

18. Every constructor-opening replacement

Write \rho=\operatorname{VIEW}(C,\sigma). A superscript \sigma below means the appropriate reference, interval, or face substitution.

The returned head fields are as follows.

Origin	Opened head
\mathcal U_\ell	HEAD_UNIVERSE(ℓ)
\Pi(x:A).B	HEAD_PI(Aσ, binder(ρ,x,B))
\Sigma(x:A).B	HEAD_SIGMA(Aσ, binder(ρ,x,B))
\lambda(x:A).t	HEAD_LAM(Aσ, binder(ρ,x,t))
f\,a	HEAD_APP(fσ, aσ)
(a,b)	HEAD_PAIR(aσ, bσ)
\operatorname{fst}(p)	HEAD_FST(pσ)
\operatorname{snd}(p)	HEAD_SND(pσ)
\operatorname{PathP}^{i}B\,l\,r	HEAD_PATH(binder(ρ,i,B), lσ, rσ)
\langle i\rangle t	HEAD_PLAM(binder(ρ,i,t))
p@s, carrying B,l,r	HEAD_PAPP(binder(ρ,i,B), lσ, rσ, pσ, sσ)
\operatorname{Glue}[\phi\mapsto(T,e)]A	HEAD_GLUE_TYPE(Aσ, φσ, partial(φσ,Tσ), partial(φσ,eσ))
\operatorname{glue}[\phi\mapsto t]a, carrying its descriptor	HEAD_GLUE_INTRO(Aσ, φσ, partial(φσ,Tσ), partial(φσ,eσ), partial(φσ,tσ), aσ)
\operatorname{unglue}(v), carrying its descriptor	HEAD_UNGLUE(Aσ, φσ, partial(φσ,Tσ), partial(φσ,eσ), vσ)
\operatorname{comp}^{i}A[\phi\mapsto u]a_0	HEAD_COMP(binder(ρ,i,A), φσ, partial_binder(ρ,i,u), a₀σ)
[\phi_k\mapsto t_k]_k	HEAD_SYSTEM([(φkσ, tkσ)]k)
Global symbol g	HEAD_GLOBAL(g, owner=ρ)

Every head recipe carries owner=ρ, including rows where it is omitted from the displayed field list.

For COMP, both binder handles use the same binder slot. Resolving either handle returns the same instantiated dimension.

For PAPP, its stored family binder is reindexed independently of the path-application interval. Applying the family at the interval is a subsequent binder application.

19. Global references

A global definition has a finite declared parameter context and a body reference in that context:

Definition:
    symbol
    parameter_context
    body_reference

A GLOBAL origin declares that parameter boundary.

Reindexing a global reference changes its view substitution. It does not unfold the body.

Unfolding is:

unfold_global(reference):
    require reference is VIEW(global_origin, sigma)
    definition = definitions[global_origin.symbol]
    return reindex(definition.body_reference, sigma)

A recursive definition can produce another reference to the same symbol. This does not make reindex recursive through the definition. Only an explicit subsequent unfolding step follows it.

The distinction ensures that scope normalization terminates even when the represented computation does not.

20. Derived operations introduce no new scope cases

The following are expanded through the constructor signature above:

\operatorname{hcomp}^{i}_A[\phi\mapsto u]a
=
\operatorname{comp}^{i}(\lambda i.A)[\phi\mapsto u]a,

\operatorname{coe}^{0\to1}_{i\mapsto A_i}(a)
=
\operatorname{comp}^{i}A_i[]a,

and

\operatorname{fill}^{i}A[\phi\mapsto u]a(r)
=
\operatorname{comp}^{j}
A(r\wedge j)
[
\phi\mapsto u(r\wedge j),
(r=0)\mapsto a
]a.

The notation \lambda i.A here denotes a dimension-bound family, represented by a dimension binder.

Likewise,

\operatorname{fib}_f(y)=\sum_x(f(x)=y),

\operatorname{isContr}(X)=\sum_{c:X}\prod_{x:X}(c=x),

and

\operatorname{Equiv}(X,Y)
=
\sum_{f:X\to Y}
\prod_{y:Y}\operatorname{isContr}(\operatorname{fib}_f(y)).

They use \Pi,\Sigma,\operatorname{PathP}, applications, and binders already covered.

LineEquiv, fibre extension, identity transport, and the earlier identity compiler likewise expand into these constructors. They therefore receive scope handling from the table, without additional type-specific scope operations.

21. Concrete scope-agent signatures

Use positive nullary data agents:

REF(reference)
MAP(typed_map)
INTERVAL(interval)
FACE(face)
TERM_BINDER(handle)
DIM_BINDER(handle)
PARTIAL(guard, reference)
PARTIAL_DIM_BINDER(handle)
CONTEXT(context)
HEAD_RECIPE(recipe)

Each has:

principal: +
auxiliaries: none

The payload is an immutable arena handle or finite tuple of handles. Copying the data agent copies those handles, not the referenced construction.

Operation agents have:

principal: -
auxiliary 0: result +

Their operation parameters are explicit immutable payload fields. For example:

REINDEX_TERM(sigma)
COMPOSE_MAP(first_map)
APPLY_TERM_BINDER(argument)

The principal port receives the operation’s remaining input. The result auxiliary points toward the consumer of its output.

For a pair

OP.principal ↔ DATA.principal

let r denote the outside endpoint formerly connected to OP.result.

A one-result replacement means:

1. Read the two immutable payloads.
2. Compute the specified finite operation.
3. Allocate the indicated positive result agent.
4. Connect its principal to r.
5. Retire the two input agents.

Thus every row below specifies the full wiring of its replacement: there is exactly one new boundary connection.

22. Exhaustive scope-operation active pairs

Operation agent	Input data agent	Replacement result
REINDEX_TERM(σ)	REF(t)	REF(reindex(t,σ))
REINDEX_INTERVAL(σ)	INTERVAL(r)	INTERVAL(substitute_interval(r,σ))
REINDEX_FACE(σ)	FACE(φ)	FACE(substitute_face(φ,σ))
COMPOSE_MAP(σ)	MAP(τ)	MAP(σ;τ)
RESTRICT_MAP(φ)	MAP(σ)	MAP(restrict_typed_map(σ,φ))
OPEN	REF(t)	HEAD_RECIPE(open(t))
UNFOLD_GLOBAL	REF(gσ)	REF(unfold_global(gσ))
REINDEX_TERM_BINDER(σ)	TERM_BINDER(h)	TERM_BINDER(reindex_binder(h,σ))
REINDEX_DIM_BINDER(σ)	DIM_BINDER(h)	DIM_BINDER(reindex_binder(h,σ))
REINDEX_PARTIAL_DIM_BINDER(σ)	PARTIAL_DIM_BINDER(h)	PARTIAL_DIM_BINDER(reindex_binder(h,σ))
REINDEX_PARTIAL(σ)	PARTIAL(φ,t)	PARTIAL(φ[σ],reindex(t,σ))
APPLY_TERM_BINDER(a)	TERM_BINDER(h)	REF(apply_term_binder(h,a))
APPLY_DIM_BINDER(r)	DIM_BINDER(h)	REF(apply_dimension_binder(h,r))
APPLY_PARTIAL_DIM_BINDER(r)	PARTIAL_DIM_BINDER(h)	PARTIAL(apply_partial_dimension_binder(h,r))
FORALL_DIMENSION(i)	FACE(φ)	FACE(forall_dimension(i,φ))
FACE_COVERAGE(χ)	FACE(φ)	COVERED if \chi\Rightarrow\phi, otherwise NOT_COVERED
REINDEX_HEAD(σ)	HEAD_RECIPE(h)	HEAD_RECIPE(open(reindex(h.owner,σ)))

COVERED and NOT_COVERED are nullary protocol results. They do not add an object-language Boolean type.

COMPOSE_MAP also checks that the typed-map contexts compose. The result’s source is the second map’s source; its target is the first map’s target.

UNFOLD_GLOBAL accepts only a global reference. Other operation/data mismatches are malformed interfaces, not additional reductions.

The operations’ finite loops are the algorithms stated above. They are executable payload computations, not unnamed semantic handlers.

23. Explicit lift-operation pairs

When a consumer needs the lifted map itself rather than a binder handle, use:

LIFT_TERM(owner, binder_slot)
LIFT_DIMENSION(owner, binder_slot)

These consume a map value representing the owner’s external substitution.

The replacements are:

\operatorname{LIFT\_TERM}(\rho,s)
\bowtie
\operatorname{MAP}(\sigma)

\longrightarrow
\operatorname{MAP}
\left(
(\sigma\setminus x)
[x\mapsto\operatorname{VAR}(x')]
\right),

where

x'=\operatorname{instantiatedBinder}(\rho,s,\mathrm{TERM}).

Its source context is extended by

x':A[\sigma],

and its target context by x:A.

Similarly,

\operatorname{LIFT\_DIMENSION}(\rho,s)
\bowtie
\operatorname{MAP}(\sigma)

\longrightarrow
\operatorname{MAP}
\left(
(\sigma\setminus i)[i\mapsto i']
\right),

where

i'=\operatorname{instantiatedBinder}(\rho,s,\mathrm{DIMENSION}).

The output wiring is the same single-result wiring as in the preceding table.

A rule that needs the same lifted dimension for two fields requests the same (owner, binder_slot). It does not allocate a second unrelated binder identity.

24. Turning a head recipe into port agents

A head recipe can be materialized as a constructor agent with one auxiliary per field.

For a recipe

HEAD_K(owner, scalar_payload, [field0, ..., fieldNminus1])

allocate:

* One positive HEAD_K agent.
* One positive data agent for each field.

Give HEAD_K:

principal: +
auxiliary j: -

Connect:

HEAD_K.principal ↔ outside_result
HEAD_K.auxiliary[0] ↔ field_agent[0].principal
...
HEAD_K.auxiliary[N-1] ↔ field_agent[N-1].principal

Its payload retains the owner reference and scalar payload.

Each field agent is selected by the field kind:

Recipe field	Field agent
Term reference	REF
Interval expression	INTERVAL
Face formula	FACE
Term binder handle	TERM_BINDER
Dimension binder handle	DIM_BINDER
Partial term	PARTIAL
Partial dimension binder	PARTIAL_DIM_BINDER

A SYSTEM recipe’s branch sequence is represented by a finite list of branch descriptors. The list constructors are:

BRANCH_NIL:
    principal +
BRANCH_CONS:
    principal +
    branch -
    tail -
BRANCH:
    principal +
    face -
    term -

For each branch, the face field connects to FACE(φkσ) and the term field connects to REF(tkσ).

HEAD_SYSTEM has one negative auxiliary connected to this branch list.

This fixes its port signature independently of the number of branches.

25. Reindexing a materialized head

A materialized head retains owner.

Reindexing it uses

\operatorname{open}(\operatorname{reindex}(\text{owner},\sigma)).

It does not rebuild an unrelated origin from its currently displayed fields.

If the materialized head is exclusively owned by the reindex operation, its old descriptor agents can be reclaimed after their payload references are released. If other occurrences share the underlying cell, those occurrences retain their reference to the same owner.

This owner-preserving rule is necessary for exact composition of views. It also prevents fresh binder names from accumulating according to the accidental sequence in which a head was opened.

For example,

\operatorname{open}((t[\sigma])[\tau])
=
\operatorname{open}(t[\sigma;\tau])

uses the same final owner reference and therefore the same instantiated binder identities.

26. Copying and erasing scope data agents

For any positive nullary scope-data agent D(v), copying is:

\operatorname{DUP}_\kappa(u_0,u_1)
\bowtie D(v)

\longrightarrow
D(v).p\leftrightarrow u_0,
\qquad
D(v).p\leftrightarrow u_1,

using two newly allocated descriptor agents carrying the same payload handle v.

The referenced cell, map, binder owner, interval form, or face form is not copied.

Erasure is:

\operatorname{ERA}^{-}\bowtie D(v)\longrightarrow\varnothing,

with the descriptor’s ownership reference released.

Releasing one descriptor does not reclaim a payload still referenced elsewhere. Arena reclamation follows the actual reference graph, including handles stored inside maps, origins, binder handles, and recipes.

For a materialized head with n fields, use the ordinary constructor-copy rule:

* Two new head shells.
* One duplicator at each old field boundary.
* Both new shells retain the same owner reference.
* The field duplicators ultimately copy their immutable descriptor handles.

The general polarity rule handles distribution when a negative scope operation meets a sup. Its result auxiliary has positive polarity, so the result routing uses a sup as already specified by that rule.

Scope handling introduces no additional fan-label comparison.

27. Agent replacement for binder application

The one-result rules above can also be used directly by the ordinary application inspector.

After the function head exposes

HEAD_LAM(
    owner,
    domain = A,
    body = TERM_BINDER(h)
)

with argument reference a, its result is

REF(apply_term_binder(h, a))

The lambda’s body origin is retained.

For a path abstraction exposing

HEAD_PLAM(
    owner,
    body = DIM_BINDER(h)
)

application at interval r produces

REF(apply_dimension_binder(h, r))

For a family binder used by composition, application at 0, 1, a fresh dimension, or an interval expression such as r\wedge j uses that same dimension-binder application operation.

There is no distinct “instantiate a dependent family” primitive. It is a dimension-binder application to the explicitly supplied interval expression.

28. Replacement for face-restricted fields

A partial descriptor is

PARTIAL(phi, term_reference)

It records a term available under \phi.

Reindexing maps both fields:

(\phi,t)[\sigma]=(\phi[\sigma],t[\sigma]).

Using it under an ambient face \chi requires

\chi\Rightarrow\phi.

A USE_PARTIAL(χ) operation therefore has the active pair:

\operatorname{USE\_PARTIAL}(\chi)
\bowtie
\operatorname{PARTIAL}(\phi,t).

If entails(χ,φ) holds, replace it by REF(t).

If it does not hold, the descriptor remains partial; the operation reports NOT_COVERED to its requesting control state. It does not invent a value outside the face.

For a system, coverage is checked against the union of branch faces. It is not implemented by arbitrarily choosing one branch whose face fails to cover the whole ambient context.

Scope reindexing preserves every branch and its guard. Branch selection or distribution is the consuming operation’s already specified system rule.

29. Worked capture-avoidance example

Consider a cell for

\lambda x.\lambda y.x.

Let its formal variable identities be x_0,y_0. Suppose it is applied to a free variable printed as y, whose identity is y_f.

The identities y_0 and y_f are different.

Opening the outer lambda produces an instantiated binder x_1 and a body view with

x_0\mapsto x_1.

Applying it to \operatorname{VAR}(y_f) composes:

x_0\mapsto x_1
\quad;\quad
x_1\mapsto y_f.

The inner lambda is now viewed under

x_0\mapsto y_f.

Opening it generates its instantiated binder y_1, giving the body substitution

[x_0\mapsto y_f,\ y_0\mapsto y_1].

Its body is \operatorname{VAR}(y_f), not \operatorname{VAR}(y_1).

The result is the intended

\lambda y_1.y_f.

No printed-name comparison, body-wide renaming pass, or informal freshness convention occurs.

30. Worked sharing example

Consider

(\lambda f.(f\,a,f\,b))(\lambda x.R),

where R has no dependency on x.

The lambda-body origin for R has no x entry in its declared boundary.

Both applications reach:

reindex(R, { x_instance -> a })
reindex(R, { x_instance -> b })

Restriction to FV(R) removes those entries in both cases.

Both results are the same RefId.

Any live evaluation state associated with that instantiated cell is therefore associated with that same reference. An application does not create a new body instance before discovering that the parameter is unused.

For a body cell C(x) that does depend on x, the references are instead

VIEW(C, { x -> a })
VIEW(C, { x -> b })

and the different dependency assignments remain explicit.

This is the exact difference between retaining a common dependency and merely sharing a code pointer while duplicating its instantiated computation.

31. Worked cubical composition example

Let

t=
\operatorname{comp}^{i}
A_i[\phi\mapsto u_i]a_0

be represented by one origin with dimension-binder slot s.

Under substitution \sigma, let

j=\operatorname{instantiatedBinder}(\operatorname{VIEW}(t,\sigma),s).

Define

\sigma_i=(\sigma\setminus i)[i\mapsto j].

Opening gives:

A_i[\sigma_i],
\qquad
\phi[\sigma],
\qquad
u_i[\sigma_i],
\qquad
a_0[\sigma].

The family and tube share j.

Applying the family at 1 composes

\sigma_i;[j\mapsto1].

Applying the tube at 1 composes the same substitution.

Thus their endpoints agree in the same instantiated scope. No separate reindexing policy is needed for the cap, tube, family, or their boundary equations.

For Glue’s

\delta=\forall i\,\alpha,

the corresponding operation is

\delta[\sigma]
=
\forall j\bigl(\alpha[\sigma_i]\bigr).

The fresh j does not occur in the external images of \sigma, so the face-normal-form algorithm gives the required naturality.

32. Termination and preservation properties of this subsystem

The scope operations have the following direct invariants.

Finite representation. Origins, raw maps, references, interval forms, and face forms are finite records. Recursive programs recur through explicit symbol unfolding, not through cyclic substitution records.

Capture avoidance. An opened binder receives an identity determined by its owner and binder slot, fresh relative to the owner’s external substitution images. Applying the binder replaces that identity through a simultaneous substitution.

Composition.

(t[\sigma])[\tau]=t[\sigma;\tau].

For binder handles, this is inherited through their retained owner.

Restriction. Strengthening a face context changes occurrence validity and typed-map context fields; it does not clone the referenced term.

Common-boundary preservation. Reindexing retains the origin and explicitly transforms its boundary assignment. Unused substitution entries are removed. Identical instantiated boundaries produce identical references.

Dependent consistency. A binder slot is instantiated once per owner. Every governed field uses that same instantiated variable or dimension.

Scope-operation termination. Reference reindexing traverses finite substitution records; interval and face operations traverse finite normalized forms. They do not evaluate arbitrary lambda bodies or unfold recursive definitions.

No implicit identification of proofs. Interning compares the explicit finite representation. A supplied path or higher cell remains represented as such; it is not replaced by a hash-based claim of semantic equality.

These are properties of the specified operations, not additional procedures the implementer must invent.

33. The implementation boundary is now explicit

For this subsystem, the executable entry points are:

make_view
reindex
compose
substitute_interval
substitute_face
entails
forall_dimension
weaken_occurrence
restrict_typed_map
instantiated_binder
lift_term_binder
lift_dimension_binder
resolve_term_binder
resolve_dimension_binder
resolve_partial_dimension_binder
reindex_binder
apply_term_binder
apply_dimension_binder
apply_partial_dimension_binder
open
unfold_global
materialize_head

resolve_*_binder consists exactly of the owner lookup, indicated lift, field lookup, and reindexing specified above. materialize_head consists exactly of the allocation and wiring in clause 24.

The operation/data active-pair table specifies the scope-agent replacements. The constructor table specifies every case of open. The origin signature specifies every field’s binding and restriction behavior.

This completes the requested scope-map representation and its corresponding agent replacements for the stated cubical signature. There is no remaining placeholder here for “handle scope,” “lift appropriately,” “instantiate the body,” or “reindex the dependent fields”: each is the explicit operation above.
