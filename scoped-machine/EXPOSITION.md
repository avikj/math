# The scoped cubical interaction machine — mathematical exposition from zero

This document states the whole construction: the computational principle (index §5), the
fibre-theoretic facts it rests on (the Agda sources), the object language and its
representation, the face algebra, observation and its memo protocol, the cubical computation
rules, contextual templates, checking and conversion, the interaction net and its
equal-length theorem, realizations and the identity compiler, runtime construction of
identities, the demand and cost semantics, reuse, the evidence boundary, the cost-granularity
requirement, and the one-source integration of semantic, boundary and work readings. Every
formula below is the one in the specification (HANDOFF.md §§1–96, the witnessed-source
contract of 17 October, index.html §5, and the four Agda modules); proofs are given where the
specification gives them. The last part records what the reverted tree contains.

Notation. `≡` is definitional equality (conversion), `=` or `Path` is a path type,
`p@r` is path application at interval expression `r`, `⟨i⟩t` is path abstraction,
`p·q` is path concatenation, `p⁻¹` is reversal, `[φ ↦ u]` is a partial element on face `φ`.

---------------------------------------------------------------------------------------------

## Part I. The computational principle (index §5)

### I.1 One operation

The propositions-as-types correspondence reads `A ⇒ B` as `A → B`, `A ∧ B` as `A × B`,
`A ∨ B` as `A ⊎ B`, falsehood as `⊥`, `∀x.P x` as `(x:A) → P x`, `∃x.P x` as `Σ(x:A).P x`,
modus ponens as application, and checking a proof as normalizing its term. A computation is a
term of a value type; a decision is a term of `Dec P = P ⊎ ¬P`; an answer is a term of the type
the question asks for; the answer to a question is the normal form of that term. Proving,
deciding, computing and answering therefore differ only in the type inhabited: each is
"build the term, normalize it" (Proposition 5.3).

### I.2 Nets and steps

A *cell* has one principal port and finitely many auxiliary ports. A *net* is a finite set of
cells with a partial matching of ports by wires. An *active pair* is two cells whose principal
ports are wired together. For each pair of cell kinds a rule gives a net `R` on exactly the
auxiliary wires of the two cells:

```
   (c1,c2) active pair of N      (c1,c2) ⟶ R
   ─────────────────────────────────────────────
            N ⟶ N[(c1,c2) := R]
```

Every other cell and wire is unchanged. `Step s t` is one such step. Traces are indexed by
length:

```
data Trace : ℕ → S → S → Type where
  done      : Trace zero s s
  stepTrace : Step s u → Trace n u t → Trace (suc n) s t
Normal t = (u : S) → Step t u → ⊥
```

### I.3 The one-step diamond and its consequences

**Lemma 5.11 (diamond).** If `Step s a` and `Step s b`, then `a ≡ b`, or there is `c` with
`Step a c` and `Step b c`.

Proof: two distinct active pairs share no cell, because each cell has one principal port and a
principal port is wired to one partner. A step changes only its own pair and that pair's
auxiliary wires, so after either step the other pair is still present and unchanged; firing it
gives the same net from both sides.

```
              s
            ╱   ╲
     pair 1╱     ╲pair 2
          ╱       ╲
         a         b
          ╲       ╱
     pair 2╲     ╱pair 1
            ╲   ╱
              c
```

β-reduction lacks this property: two overlapping β-redexes may need several steps each to
reconverge, so the following length results are false for β-reduction and true for nets.

**Lemma 5.12 (peel).** `Step s u → Trace (suc n) s t → Normal t → Trace n u t`.
By induction on `n`: compare the given step with the trace's first step. If they coincide, the
tail is the required trace. Otherwise the diamond gives `z` with `first : s→a`, `a→z`,
`u→z`; peel the step `a→z` through the tail `a →ⁿ t` to get `z →ⁿ⁻¹ t`, and prepend `u→z`.
In the base case `n = 0`, a distinct step would leave a redex in the normal form `t`,
contradiction.

**Theorem 5.13 (equal length).** `Trace n s t → Trace m s t → Normal t → n ≡ m`, by induction
on the first trace, peeling its first step through the second. The Agda term
`RandomDescent` (index §5.4) proves this generically in `(S, Step, diamond)` under `--safe`.

**Corollary 5.14 (geodesic).** Every reduction to the normal form has the same length, so each
is minimal; the step count is fixed by the endpoints, not by the strategy.

**Theorem 5.15 (Bellman).** With edge costs `c(u→v)`, a potential `Φ` satisfies
`Φ(normal form) = 0` and `Φ(u) ≤ c(u→v) + Φ(v)` on every edge. Summing the inequality along any
finishing path gives `Φ(u) ≤ cost(path)`. The geodesic distance is a potential satisfying
`Φ(u) = min_v [c(u→v) + Φ(v)]`; by 5.14 every reduction attains it.

**Theorem 5.16 (unit lookahead).** One step changes the net only where its two cells sat; the
cells it places carry only what those two held. After `k` steps an output position depends only
on input within wire distance `k`. Equivalently, if `x ≡_{n+k} y` (agreement to observational
depth `n+k`) then `w(x) ≡_n w(y)` for every `k`-step `w`.

**Theorem 5.18 (unique normal form).** Tiling the diamond reconverges any two reductions; if
both end in normal forms those forms are equal.

**Remark 5.24 (sharing).** A shared subterm is held by a duplicator cell wired like any other
cell; duplicator interactions are ordinary steps. An active pair is never duplicated, so no
step repeats work. The diamond uses only disjointness of active pairs.

**Remark 5.26 (no outer layer).** Evaluator, type checker and optimizer are terms of the same
language; a question about them is another term reduced by the same normalizer.

**Theorem 5.27 (complete inference)** as stated: pose a declaration with its available
identities and normalize; either (a) the normal form is an inhabitant, reached in the length
fixed by 5.13, minimal by 5.14, with no repeated work by 5.24; or (b) §4 establishes that no
inhabitant exists. **Remark 5.28**: the minimum is over orders of applying the identities from
the posed term, not over choices of starting term.

---------------------------------------------------------------------------------------------

## Part II. Fibres, the carrier, and initiality (the Agda modules)

### II.1 Every map factors through a lossless middle

For `f : A → B` the *carrier* (motive) `Carrier f` is the graph of `f`. The Agda module
`TheCarrierIsTheMotiveAndEachReadingIsARealization` defines

```
to-motive : A → motive          -- descend f;  isEquiv to-motive   (unconditional)
realize   : motive → B          -- the target projection
f-factors-through-the-motive : (a : A) → realize (to-motive a) ≡ f a      -- by refl
```

All loss lives in `realize`. Its residual over `b : B` is the fibre `fib_f(b)`; `realize` is an
equivalence exactly when every fibre is contractible (both directions are terms). Concretely
(HANDOFF §21):

```
A ≃ Σ(b:B). Σ(a:A). (f a = b)
forward  a ↦ (f a, a, refl)
reverse  (b, a, p) ↦ a
homotopy (b,a,p):  i ↦ (p@i, a, ⟨j⟩ p@(i∧j))
```

At `i=0` the homotopy is `(f a, a, refl)`, the round trip; at `i=1` it is `(b,a,p)`.
Projecting `Σ(b:B).R(b) → B` is an equivalence precisely when every `R(b)` is contractible.
Erasing a residual therefore needs a contraction; physical reclamation of an unreferenced
handle is not such a contraction.

**Middle-out mediation.** For `f : A → B` and `g : A → C`, if every fibre of `f` is contractible
then `through-the-middle = g ∘ f⁻¹ : B → C`, and `through-the-middle (f a) = g a`. No direct
`B → C` translation is written; the shared source mediates.

### II.2 Every family is a pullback of the universe; towers flatten

`Σ A B ≃ Σ(a:A). fiber π (B a)` where `π` is the projection from the universal family; the
classifier `(Σ(E:Type). E → A) ≃ (A → Type)`. A tower of dependent families

```
Fam A 0       = Unit
Fam A (suc n) = Σ(B : A → Type). Fam (Σ A B) n
flatten (suc n) (B,F) a = Σ(b : B a). flatten n F (a,b)
flatten-correct : Tot n F ≃ Σ A (flatten n F)
```

is one family over `A`, by refl in the computed example. Iterating the fibre construction never
leaves the universe at a finite height: n layers are one dependent family, not n semantic
universes.

### II.3 Initiality: one fold, many readings

A receiver `R` for derivations has an identity action `ε_R` and an action `R_e` for each
generating step. Its fold is unique:

```
fold_R(done)      = ε_R
fold_R(step(e,h)) = R_e(fold_R(h))
```

For two receivers the product receiver acts componentwise, and induction on `h` gives

```
fold_{R×T}(h) = (fold_R(h), fold_T(h)).
```

So a checked transition, its evidence and its work reading are produced together by one
traversal. Initiality does not supply an action for a generator nobody wrote, and a fold over a
shared history must not count a shared producer twice (Part XVIII gives the shared-history
extension).

### II.4 A rule is one object carrying its history

In `Kernel.GenerativeKernel`, a `Branch seed` holds an operation, its applicability control,
the computed `target`, and `history : Derivation seed target`. The example has
`seed = add var (suc zero)`, `target₀ = suc var`, a direct derivation (two steps) and a detour
derivation (a step, its reverse, then the direct derivation). Both are installed as operations;
`run-targets ≡ target₀ ∷ target₀ ∷ []` by refl, and the two proof-relevant histories remain
distinct fields. `install : Derivation → NativeOperation` turns a proof into a move; the
forward pass `advance` preserves the number of branches.

---------------------------------------------------------------------------------------------

## Part III. The object language

The language has universes `U_ℓ` with exact predicative levels (`U_ℓ : U_{ℓ+1}`, no
cumulativity), dependent functions `Π`, dependent pairs `Σ`, dependent paths `PathP`, `Glue`,
face systems, and composition `comp`. Natural numbers, booleans and other datatypes get no
primitive runtime handler. Host tags used by the implementation are not object-language types.

Formation: `Π(x:A).B` and `Σ(x:A).B` lie in `U_max(i,j)` for `A:U_i`, `B:U_j`; a path family in
`U_ℓ` forms a path type in `U_ℓ`; Glue has base and partial fibre in the same `U_ℓ` with an
equivalence between them. Univalence constructs paths in a universe; it does not change
universe conversion.

Recursive definitions are `GLOBAL` symbols with registered bodies; unfolding is the registered
body. Typing a recursive body against its own declaration makes it a well-typed partial
program, not a total proof (Part XVI).

---------------------------------------------------------------------------------------------

## Part IV. Representation: origins, references, simultaneous substitution

### IV.1 The central invariant

```
reference      = VIEW(origin, substitution)
specialization = reindex(reference, substitution)
observation    = whnf(reference, ambient face)
```

Substitution changes a reference; it never evaluates. Observation is made under a face and
recorded for that face; an immutable reference is never overwritten with a result valid on one
face only.

Why this matters (the Glue failure that motivated it): a composition rule must open its type
family at a fresh symbolic dimension, keep the exposed component references, and specialize
them. Re-evaluating the whole family at an endpoint to rediscover a component can collapse a
Glue type to its fibre and lose the base family the rule needs.

### IV.2 Records

```
Context    : ordered declarations DIM(i) | TERM(x, type_ref), and an assumption face
Reference  : VAR(x) | VIEW(origin, map) | TVIEW(template_node, template_environment)
Occurrence : (reference, context)
Origin     : tag, scalar payload, fields[], binders[], free term boundary,
             free dimension boundary, required face, typing annotation
```

Origins, maps, references and global bodies are immutable and interned by structural
equality; a hash match is checked by comparing records. Printed names are presentation only.
The occurrence context is not part of a reference's identity: a closed reference weakened into
another context is the same reference. An occurrence is valid when its context supplies every
variable of the reference's boundary with compatible types and entails its required face.

The *boundary* of an origin is the dependency-closed set of free variables appearing in its
fields, field types, required faces, retained path endpoints, and the types of its free
variables, minus variables bound locally. It is a finite structural computation, not
normalization.

### IV.3 Simultaneous substitution

A map `σ : Δ → Γ` supplies, for each variable of `Γ`, a value in `Δ`; a missing entry means
identity. Its validity requires each image `σ(x)` to have type `A[σ]` under the source face,
processed in declaration order, and `ψ ⇒ χ[σ]` (source assumption entails substituted target
assumption).

```
make_view(C,σ) = intern VIEW(C, σ restricted to C's complete typed boundary, identities removed)

reindex(t,σ):
    σ identity        → t
    t = VAR(x)        → σ(x)
    t = TVIEW(Q,E)    → TVIEW(Q, E[σ])                         (Part IX)
    t = VIEW(C,τ)     → make_view(C, ρ) where
                         ρ(x) = reindex(τ(x), σ)   for x in C's term boundary
                         ρ(i) = τ(i)[σ]           for i in C's dimension boundary
```

`reindex` visits image records, never the body of `C`; it performs no β-step, Glue collapse,
unfolding or face test. It is simultaneous: `x[x↦y, y↦z] = y`, while `(x[x↦y])[y↦z] = z`.
Composition, written `σ;τ` (first `σ`, then `τ`), satisfies `t[σ;τ] = t[σ][τ]` and is computed
on the union of keys of both maps, since `σ` acts as identity on keys only `τ` mentions.

**Sharing by boundary.** If `x` is absent from the complete typed boundary of `R`, then
`R[x↦a]` and `R[x↦b]` intern to the same reference. This is the sharing the construction rests
on: identical instantiated boundary gives identical reference.

### IV.4 Support after instantiation

The support `S(t)` is the set of free dimensions of the *instantiated* typed boundary: for
`VIEW(C,σ)`, the dimensions of every `σ(i)` for `i` in the dimension boundary of `C`, and the
supports of every `σ(x)` for `x` in its term boundary, where `support(VAR x)` includes the
dimensions of the declared type and required face of `x`, transitively. If `σ(x)` depends on
`j`, then `j ∈ S(t)` though no `j` occurs in the origin. A superset is sound (it only creates
extra memo entries); a subset is unsound. Support is computed from immutable records and never
changes after interning.

### IV.5 Binders

The instantiated identity of a binder is interned from `(owner reference, binder slot, sort)`.
The owner and its images exist before the identity is minted, so the identity is fresh with
respect to the owner's boundary; reopening the same owner and slot gives the same identity.

```
resolve term binder x:A of owner VIEW(C,σ):
    x' = binder(owner, slot, TERM);   A' = reindex(A,σ)
    body = reindex(C.field, σ with x ↦ VAR(x'))
apply_term_binder(h, a) = reindex(body, [x' ↦ a])
apply_dim_binder(h, r)  = reindex(body, [j ↦ r])
reindex_binder((owner,slot,field), σ) = (reindex(owner,σ), slot, field)
```

All fields governed by one slot share one opening: a composition's family and tube use the same
fresh dimension `j`. A partial value `(φ, t)` is used as total under `χ` only when `χ ⇒ φ`;
otherwise the result is a control status that keeps the partial value.

### IV.6 Opening

`open` exposes one constructor and its immediate fields, without evaluating, and keeps the
owner so later reindexing restarts from the original construction.

| Tag | Opened fields |
|---|---|
| UNIVERSE | level |
| PI, SIGMA | domain; term binder for codomain |
| LAM | domain; term binder for body |
| APP | function; argument |
| PAIR | two fields |
| FST, SND | scrutinee |
| PATH | dimension binder for family; two endpoints |
| PLAM | dimension binder for body |
| PAPP | family binder; two endpoints; path; interval |
| GLUE_TYPE | base; face; partial fibre and equivalence |
| GLUE_INTRO | same type data; partial fibre term; base term |
| UNGLUE | same type data; value |
| COMP | family binder; face; partial tube binder; cap |
| SYSTEM | ordered list of (face, reference) branches |
| GLOBAL | symbol; owner with instantiated parameter boundary |

There are no tags for neutral terms: neutrality is a result of observation.

---------------------------------------------------------------------------------------------

## Part V. Intervals and faces

### V.1 Intervals: the free De Morgan algebra

An interval is an antichain of clauses; a clause is a finite set of signed atoms `+i`, `−i`
denoting their meet; the antichain denotes the join of its clauses.

```
0 = []      1 = [[]]      i = [[+i]]      ¬i = [[−i]]
join(r,s) = normalize(r ++ s)
meet(r,s) = normalize([C ∪ D | C ∈ r, D ∈ s])
¬r        = ⋀_{C ∈ r} ⋁_{a ∈ C} flip(a)
normalize : sort, deduplicate, delete every clause strictly containing another
```

The representation is canonical. A clause containing both `+i` and `−i` is **kept**: the algebra
is not Boolean, `i ∧ ¬i ≠ 0` and `i ∨ ¬i ≠ 1`. Substitution inserts the image of each atom once
(the negation of the image for a negative atom) and renormalizes.

### V.2 Faces

A face literal is `(i=0)` or `(i=1)`; a face is a DNF antichain of literal sets with the same
normalization plus one rule: **a clause containing both `(i=0)` and `(i=1)` is deleted**.
`false = []`, `true = [[]]`. Note `(i=0) ∨ (i=1) ≠ true`: a symbolic dimension has an interior.

```
        j
        1 ┌───────────────┐
          │               │      (i=0) ∨ (i=1) is the left and right edges only;
   (i=0)  │   interior    │ (i=1)   the interior of the square is not covered.
          │               │
        0 └───────────────┘
          0               1  i
```

Endpoint faces of an interval `r`:

```
(r=1) = ⋁_{C ∈ r} ⋀_{a ∈ C} (a=1)
(r=0) = ⋀_{C ∈ r} ⋁_{a ∈ C} (a=0)
(¬i = ε) = (i = 1−ε)
```

(`r = 1` when some clause is all 1; `r = 0` when every clause has an atom at 0.)
Face substitution replaces each literal `(i=ε)` by `(σ(i) = ε)` and renormalizes.

**Entailment** of normalized faces: `χ ⇒ φ` iff every clause `C` of `χ` contains some clause
`D` of `φ`.

### V.3 Universal quantification versus projection

```
∀i. φ      : keep exactly the clauses of φ that mention no literal on i
π_S(χ)     : normalize χ, delete from each clause the literals outside S, normalize again
```

`∀i.φ` is the largest `i`-independent face entailing `φ`. `π_S χ` is the strongest consequence
of `χ` expressible over `S`.

```
 ∀i((i=0) ∨ (j=0)) = (j=0)

        j
        1 ┌───────────────┐
          █               │     █ = (i=0) ∨ (j=0): left edge and bottom edge.
          █               │     The only part that holds along the whole i-line
          █               │     is the bottom edge (j=0).
        0 █████████████████
          0               1  i

 π_{j}((i=0) ∧ (j=0)) = (j=0)        ∀i((i=0) ∧ (j=0)) = false
```

**Theorem (projection preserves entailment).** If the dimensions of `φ` lie in `S`, then
`χ ⇒ φ  ⟺  π_S(χ) ⇒ φ`.

*Proof.* `χ ⇒ φ` iff every clause `C` of `χ` contains a clause `D` of `φ`. Since `D` mentions only
dimensions in `S`, `D ⊆ C` iff `D ⊆ C|_S`. Absorption does not change the represented face.
Contradictory clauses must be removed *before* deleting literals: projecting the unnormalized
`(i=0) ∧ (i=1)` to empty support would give `true` instead of `false`. ∎

Consequences: `χ ⇒ π_S χ`; `π_S π_S χ = π_S χ`; `π_∅ χ = true` for consistent `χ`;
`π_S false = false`; `T ⊆ S ⇒ π_T π_S χ = π_T χ`.

---------------------------------------------------------------------------------------------

## Part VI. Observation and the face-sensitive memo

### VI.1 The key

```
K(t, χ) = (t, π_{S(t)}(χ))
```

Observation (weak-head evaluation) of `t` under ambient face `χ` runs under the projected face.
Entries have three states:

```
U        unevaluated
R(W)     running, with multiset W of waiting continuations
D(v)     ready, with immutable result v       (INTRODUCTION | NEUTRAL | SYSTEM)
```

`D(v)` means weak-head observation is complete under the entry's face, not that the term has a
normal form. On `χ = false` no observation is made; a control result `NO_OBSERVATION` is
delivered.

### VI.2 Why the key is sufficient

The projection theorem preserves every entailment test on faces built from the reference's
typed boundary. Fields depend only on that boundary and its images; opening binders introduces
fresh dimensions carrying no ambient constraint; restriction adds explicit local guards, and
each child request projects again for the child. An evaluator using only these operations
cannot distinguish two ambient faces with the same projection; induction on a finite evaluation
derivation gives the same observation, up to binder identities.

### VI.3 Why a memo keyed by the reference alone fails

For a neutral path `p : a₀ = a₁`, the same reference `p@i` is

```
     a₀ ●━━━━━━━━━━━━━━━━━● a₁          ambient face     observation of p@i
        i=0       p@i      i=1          true             neutral
                                         i=0              a₀
                                         i=1              a₁
```

One unconditional entry cannot hold three different observations.

### VI.4 Reindexing rebuilds the key

After `t' = reindex(t,σ)`, compute `S(t')` and the key from `t'` and the actual target face.
Never substitute into an old projected face. Example: `t = p@i`, endpoints independent of
`i,k`, ambient `(k=0)`. `S(t) = {i}`, so the projected face is `true`. Reindex by `[i ↦ k]`:
`p@k` under `(k=0)` must observe the left endpoint; substituting into the old projected face
`true` would lose it.

### VI.5 Dispatch

| Head | Action |
|---|---|
| VAR | neutral variable |
| UNIVERSE, PI, SIGMA, LAM, PAIR, PATH, PLAM | introduction head, fields not evaluated |
| GLOBAL | unfold to the registered body under its parameter map; demand it |
| APP(f,a) | demand `f`; lambda → apply its binder to `a`, demand; system → distribute; else neutral application |
| FST/SND(p) | demand `p`; pair → field; system → distribute; else neutral |
| PAPP(B,l,r,p,s) | first test `(s=0)`, `(s=1)`: if entailed demand that endpoint; else demand `p`, apply a path binder, distribute over a system, or keep the complete neutral application |
| GLUE_TYPE(A,α,T,e) | if `χ ⇒ α` demand `T`; else Glue head with all components retained |
| GLUE_INTRO(…,t,a) | if `α` entailed demand `t`; else keep |
| UNGLUE(…,v) | on `α`: `e.map(v)`; else demand `v`, glue → base component; system → distribute; else neutral |
| SYSTEM | select a branch whose guard is entailed; else keep the covered system |
| COMP | test tube coverage first; if covered, the tube at 1; else open the family at one fresh `j` and use the clause for its head (Part VII) |

Endpoint tests come before demanding a path even when the path is neutral; tube coverage comes
before demanding a family head.

**Systems.** A system `[(φ_k, t_k)]` is valid where `χ` entails `⋁ φ_k`; branches agree on
overlaps (a typing premise). Inconsistent branches are dropped; a single covering branch is
selected; otherwise the result is a system, and eliminators act branchwise under `χ ∧ φ_k`. For a
type-family system exposed at a fresh `j`, a composition branch must hold along the whole
`j`-line: its outer guard is `∀j.φ_k`. Endpoint-only branches do not cover a symbolic interval.

**Demand and divergence.** A request for a running key appends a waiter; it never produces a
neutral result. An idle queue containing only suspended cyclic demands is not normalization.

---------------------------------------------------------------------------------------------

## Part VII. Composition and the cubical computation rules

### VII.1 Composition

```
comp^i A_i [φ ↦ u_i] a₀ : A_1
```

`φ` is independent of `i`; the tube `u_i : A_i` on `φ`; the cap `a₀ : A_0` with `u_0 = a₀` on `φ`.
The picture for a one-dimensional tube (φ = (j=0) ∨ (j=1)):

```
   i=1   ●···············●      the lid (dashed) is the result, of type A_1
         ┃               ┃
   u_i   ┃ on (j=0)      ┃ u_i on (j=1)       sides: the tube
         ┃               ┃
   i=0   ●━━━━━━━━━━━━━━━●      the cap a₀ along j, of type A_0
        j=0             j=1
```

Opening a composition gives one fresh `j` shared by family and tube; the family is observed at
`j` under the outer face; its head's component references `C` (with `j` free) are kept, and
`C` at `r` is `reindex(C,[j↦r])`, which evaluates nothing. Never recover a component as
"component of whnf(family at r)": at an endpoint the family may no longer be Glue at all.

### VII.2 Derived operations (fixed library definitions)

```
fill^i A_i [φ ↦ u_i] a₀ (r) = comp^j A_{r∧j} [φ ↦ u_{r∧j}, (r=0) ↦ a₀] a₀      (j fresh)
hcomp                       = comp in a constant family
coe^i A_i a₀                = comp^i A_i [] a₀     (empty tube)
line from r to s            : ℓ(j) = (r ∧ ¬j) ∨ (s ∧ j)
```

`fill` at `r=0` is `a₀` (the face `(r=0)` is entailed) and at `r=1` is the composition. No rule
makes composition in a constant family equal to its cap, and no rule makes transport along an
equal-endpoint line the identity, unless the calculus states that regularity; it does not.

### VII.3 The structural clauses

**Π.** `A_i = Π(x:D_i).E_i(x)`, cap `f₀`, tube `u_i`:

```
λx₁. comp^i E_i(v(i)) [φ ↦ u_i(v(i))] (f₀(v(0)))
v(r) = fill^j D_{¬j} [] x₁ (¬r)        (one shared backward filler; v(1) = x₁)
```

**Σ.** `A_i = Σ(x:D_i).E_i(x)`, cap `z₀`:

```
a(r) = fill^i D_i [φ ↦ fst u_i] (fst z₀) (r)
b₁   = comp^i E_i(a(i)) [φ ↦ snd u_i] (snd z₀)
result (a(1), b₁)          (one first-component filler, used by both components)
```

**PathP.** `A_i = PathP^j B(i,j) l_i r_i`, cap `p₀`:

```
⟨j⟩ comp^i B(i,j) [φ ↦ u_i@j, (j=0) ↦ l_i, (j=1) ↦ r_i] (p₀@j)

   i=1   ●···············●       lid = result path at j
         ┃l_i         r_i┃       the two endpoint lines are added to the tube
   i=0   ●━━━━━━━━━━━━━━━●       cap p₀@j
        j=0             j=1
```

The three tube branches agree on overlaps by the path endpoint conditions.

### VII.4 Equivalences and contractible extension

```
Contr(X)    = Σ(c:X). Π(x:X). Path_X(c,x)
fib(f,y)    = Σ(x:X). Path_Y(f x, y)
Equiv(X,Y)  = Σ(f : X→Y). Π(y:Y). Contr(fib(f,y))
```

Identity-fibre contraction: centre `(y,refl)`, and for `(x,p)` with `p : x=y`,
`⟨i⟩(p@¬i, ⟨j⟩ p@(¬i ∨ j))`, from `(y,refl)` at `i=0` to `(x,p)` at `i=1`.

```
ExtendContr(c,k; θ, v) = hcomp^j_X [θ ↦ k(v)@j] c
```

extends a partial `v` on `θ`: on `θ` the composition returns `k(v)@1 = v`.

### VII.5 Glue

`G = Glue[α ↦ (T,e)] A`. On `α`: `G` reduces to `T`, `glue t a` to `t`, `unglue v` to
`e.map(v)`. Everywhere: `unglue(glue t a) = a`; Glue η identifies `glue[α ↦ v](unglue v)` with `v`.

Composition in `G_i = Glue[α_i ↦ (T_i,e_i)] A_i`, face `ψ`, tube `u_i`, cap `u₀`, `f_i = e_i.map`,
with `A_i, T_i, e_i, α_i` the references kept from opening the family at a fresh `i`:

```
a₀    = unglue u₀
a(r)  = fill^i A_i [ψ ↦ unglue u_i] a₀ (r),         a₁ = a(1)
δ     = ∀i. α_i                                      (fibre available along the whole line)
on δ:   t(r) = fill^i T_i [ψ ↦ u_i] u₀ (r),           t'₁ = t(1)
        ω(q) = comp^i A_i [ψ ↦ a(i), (q=0) ↦ f_i(t(i)), (q=1) ↦ a(i)] a₀ ,   ω : f₁(t'₁) = a₁
on α₁:  extend the partial fibre element
          [δ ↦ (t'₁, ω),  ψ ↦ (u₁, refl)]   in fib(f₁, a₁)
        using the contraction supplied by e₁ (ExtendContr); call it (t₁, p),  p : f₁(t₁) = a₁
a'₁   = hcomp^q_{A₁} [α₁ ↦ p@¬q, ψ ↦ a₁] a₁
result  glue[α₁ ↦ t₁] a'₁
```

The base family is used everywhere; `T`, `e` only under their guards; `δ` authorizes whole-line
fibre use; `α₁` authorizes extension at the endpoint. Quantification commutes with reindexing:
`δ[σ] = ∀j.(α[σ↑])` with the lifted fresh dimension.

### VII.6 Universe and univalence

```
LineEquiv(X_j) = coe^{0→1}_{j ↦ Equiv(X₀, X_j)} (IdEquiv(X₀))           : Equiv(X₀, X₁)
comp^i U_ℓ [φ ↦ U_i] A₀  ⟶  Glue[φ ↦ (U₁, LineEquiv(j ↦ U_{¬j}))] A₀
ua(e) = ⟨i⟩ Glue[(i=0) ↦ (X,e), (i=1) ↦ (Y, id)] Y
```

On `φ`, `U₀` agrees with `A₀`, so `LineEquiv` of the reversed line has target `A₀`. No
non-collapsing universe or Glue codes are used. Transport along `ua(e)` yields, through the
Glue clause, explicit paths relating its result to `e.map(x)`; these are paths, not syntactic
identities.

### VII.7 Paths and naturality

Reflexivity `⟨i⟩a`; reversal `⟨i⟩p@¬i`; `ap f p = ⟨i⟩ f(p@i)`;

```
p·q = ⟨i⟩ hcomp^j_A [(i=0) ↦ x, (i=1) ↦ q@j] (p@i)          p : x=y, q : y=z

   j=1   x ●···············● z      lid: (p·q)@i
           ┃               ┃
 (i=0) ↦ x ┃               ┃ (i=1) ↦ q@j
           ┃               ┃
   j=0   x ●━━━━━━━━━━━━━━━● y      cap: p@i
          i=0             i=1
```

Singleton contraction from `(a,refl)` to `(b,p)`: `i ↦ (p@i, ⟨j⟩ p@(i∧j))`.

Every structural clause is built from substitution-respecting constructors, hence

```
(comp^i A [φ ↦ u] a₀)[σ] = comp^j A[σ↑] [φ[σ] ↦ u[σ↑]] a₀[σ]
```

with the fresh dimension lifted; no clause needs its own reindexing rule.

---------------------------------------------------------------------------------------------

## Part VIII. Contextual templates: one fixed origin per construction

### VIII.1 The problem and the law

Library constructions (`Refl`, `Fill`, the composition clauses) take arguments that are open
families (`D : [i] U`, `E : [i, x:D⟨i⟩] U`), not closed terms. Building fresh syntax per call
would give a fresh origin per call, so specializing a generic instance and constructing the
specialized instance directly would yield different references and two evaluations. The
encoding is: **contextual parameters plus fixed template origins**.

```
Reference = VAR(x) | VIEW(raw_origin, map) | TVIEW(template_node, environment)
reindex(TVIEW(Q,E), σ) = TVIEW(Q, E[σ])                  (same interned record)
```

A template node's identity is `(definition environment, template id, static node index)`; its
tag, field program, binder table and dependency signature are fixed. Actual arguments live in
the environment, restricted to the node's syntactic dependency closure.

### VIII.2 Scopes

```
Scope: local declarations (DIM | TERM(type, required face)), result sort (REFERENCE |
       INTERVAL | FACE), result type, availability guard, body
```

Local occurrences are `(sort, depth, slot)`: depth 0 is the innermost enclosing scope. Values:
`FREE_TERM(x)`, `BOUND_TERM(d,s)`, `RAW_VIEW(origin, scoped boundary images)`,
`TEMPLATE_VIEW(node, scoped environment)`; intervals and faces are canonical DNFs over free and
bound atoms with the same normalization rules (`i ∧ ¬i` kept, `(i=0)∧(i=1)` deleted).

* **capture**(Δ, body, type, guard): replace free identities equal to `Δ.slot[k]` by
  `BOUND(depth, k)`, recurse into views/environments/DNFs, enter nested scopes at `depth+1`;
  intern. Renaming the concrete locals before capture gives the same record.
* **reindex_scope**(S,σ): substitute free identities only; bound occurrences stay bound; an
  inserted image is not substituted again. An image mentioning a former printed name stays free,
  because bound slots and free identities carry different tags. `S[σ][τ] = S[σ;τ]`.
* **apply_scope**(S, args), at nesting depth `d` below S's body: bound depth `< d` kept (inner
  scope), depth `= d` replaced by `args[slot]` (not substituted again), depth `> d` decremented.
  The result for a reference scope is `TYPED_PARTIAL(body, type, guard)`, kept even when the
  guard is false; using its body requires ambient entailment of the guard. Scope application is
  not path application and creates no APP, PAPP or β-step.
* **forall_scope**(S) for a unary dimension face scope drops every clause containing a literal on
  `BOUND_DIM(0,0)` — exactly `∀`.

Laws (exact record equality; proofs by structural induction over images and DNF operations,
where the nested depth cases are what make the induction capture-avoiding):

```
apply(S, a⃗)[σ]          = apply(S[σ], a⃗[σ])
capture_{Δ'}(t[σ↑])      = capture_Δ(t)[σ]
(∀i.α)[σ]                = ∀j.(α[σ↑])
```

### VIII.3 Template programs

A template definition has ordered parameters of sorts REFERENCE, INTERVAL, FACE, SCOPE,
UNIVERSE_LEVEL; an acyclic expression DAG; a fixed constructor-node table. Instructions:

| Instruction | Meaning |
|---|---|
| `PARAM(k)`, `LOCAL(k)` | read a parameter / an opened local |
| `CONST_LEVEL`, `LEVEL_SUCC`, `LEVEL_MAX` | exact level arithmetic (overflow is a host failure) |
| `NODE(Q, slots)` | `TVIEW(Q, slots)`; does not execute Q's fields |
| `CALL(F, slots)` | evaluate fixed helper F's root expression |
| `SCOPE(Δ, body, type, guard)` | capture, via bridge variables minted from the build key |
| `SCOPE_APPLY(S, args)` | apply; keep body, type and guard |
| `PARTIAL_BODY/TYPE/GUARD` | inert selection of a typed partial's field |
| `SUBREF(t, map)` | reindex |
| interval and face operations | canonical De Morgan / face operations; `FORALL_SCOPE` |
| `LET` | DAG alias: all uses share one handle |

There is no weak-head evaluation, no inspection of an unknown constructor, no host callback.
`open(TVIEW(Q,E))` executes Q's finite field expressions and returns Q's core tag, fields and
binders `(owner, slot, field)`; child `NODE`s return views, so opening never materializes a body.

**Library** (each constructor occurrence is one fixed node; `S⟨args⟩` is scope application):

```
PathConst(A,l,r)     = PathP(j. A, l, r)
Refl(A,a)            = PLam(j. a)
Reverse(A,l,r,p)     = PLam(i. PApp(A,l,r,p, ¬i))
Concat(A,x,y,z,p,q)  = PLam(i. Comp(j, A, (i=0)∨(i=1),
                         System[(i=0) ↦ x, (i=1) ↦ PApp(A,y,z,q,j)], PApp(A,x,y,p,i)))
Fun, Contr, Fib, Equiv, IdFun, EquivMap = Fst(e), EquivContr(e,y) = App(Snd e, y)
IdEquiv(X)           = (IdFun X, λy. ((y, Refl y), λw. PLam(i. (PApp(p,¬i), PLam(j. PApp(p, ¬i ∨ j))))))
Fill(A,φ,u,cap,r)    = Comp(j, A⟨r∧j⟩, φ ∨ (r=0), System[φ ↦ u⟨r∧j⟩, (r=0) ↦ cap], cap)
HComp(X,φ,u,cap)     = Comp(j, X, φ, u⟨j⟩, cap)
Coe(A,cap)           = Comp(i, A⟨i⟩, false, System[], cap)
ExtendContr(X,c,k,θ,v) = HComp(X, θ, [j]. PApp(X,c,v,App(k,v),j), c)
LineEquiv(X)         = Coe([i]. Equiv(X⟨0⟩, X⟨i⟩), IdEquiv(X⟨0⟩))
Ua(X,Y,e)            = PLam(i. GlueType(Y, (i=0)∨(i=1), System[(i=0)↦X,(i=1)↦Y],
                                         System[(i=0)↦e,(i=1)↦IdEquiv Y]))
```

The five composition clauses of Part VII (Π, Σ, PathP, Glue, universe) are fixed programs over
this library (`PiComp`, `SigmaComp`, `PathComp`, `GlueComp`, `UniverseComp`). In `GlueComp`,
`under δ` and `under α₁` set availability annotations and checking guards; they do not branch.
Names introduced there are kept as partial references; a false `δ` leaves well-scoped unused
data and never demands fibre data.

**Capture at composition dispatch.** At the opened `j`:

| Head | Scoped parameters |
|---|---|
| Π, Σ | `D = capture([j], domain)`; resolve the binder once to `(x, D_j, codomain)`; `E = capture([j, x:D_j], codomain)` |
| PathP | resolve the family binder once to `(k,B)`; `B` over `[j,k]`; endpoints over `[j]` |
| Glue | A, T, e over `[j]`; the face as a total face scope over `[j]`; T, e with their guarded availability |
| U_ℓ | keep ℓ; capture the tube over `[j]` |

The emitted clause instance is annotated with the producer entry's face `η` (the face under
which the head was observed), never with a requester's face.

**Levels.** Every type position stores `TypeAt(ref, level)` (judgment `ref : U_level`), every
type scope `TypeScopeAt(scope, level)`. Levels are unchanged by substitution:
`(A,ℓ)[σ] = (A[σ],ℓ)`. A Π/Σ head supplies domain level `m` and codomain level `n` separately (the
maximum alone cannot recover them); a universe head with payload `ℓ` invokes the universe clause
at `ℓ` while the enclosing family has level `ℓ+1`.

**Sharing proof.** (1) each library constructor occurrence is one fixed node Q; (2) reindexing
changes only Q's environment; (3) capture closes local names into depth/slot records, so a
lifted local's allocated name does not affect the record; (4) canonical simultaneous
substitution yields the same environment for two paths to the same instantiated boundary,
including type and required-face annotations; (5) interning gives the same TVIEW reference;
(6) equal relevant faces give the same memo key and one producer. Hence, for `B:U₀, b:B`,
`reindex(Refl(0,A,x), [A↦B, x↦b]) = Refl(0,B,b)` as reference identity.

The denotation of `TVIEW(Q,E)` is the core construction obtained by interpreting Q's field
recipes with E; type preservation is the constructor rule at each node plus the contextual
substitution lemma; opening exposes that constructor, so the evaluator's rule table is unchanged.

---------------------------------------------------------------------------------------------

## Part IX. Checking, conversion, admission

### IX.1 Judgments and outcomes

```
Γ;χ ⊢ A : U_ℓ        Γ;χ ⊢ t : A        Γ;χ ⊢ t ≡ u : A        σ : (Δ;ψ) → (Γ;χ)
```

relative to the declared immutable global signature. Outcomes: `VALID | INVALID(reason) |
UNRESOLVED(reason)`; for conversion `EQUAL | UNEQUAL | UNRESOLVED`. An interrupted or cyclic
normalization never establishes inequality and is never accepted as typing.

**Context and map validation.** Identities unique; each declaration's type and required face
use only its prefix (the final assumption projected onto the prefix's dimensions); an
occurrence finds its whole typed boundary with matching declarations and entails its required
face; for `σ`, each dimension image is an interval over `Δ`, each `σ(x)` checks against `A[σ]`
under `ψ` in declaration order, and `ψ ⇒ χ[σ]`. Scope checks of every image and substituted
type happen even when `ψ = false` (only the subsequent typing obligations become vacuous).

**Partial declarations** `x : A @ φ_x`: the image obligation is
`Δ; ψ ∧ φ_x[σ] ⊢ σ(x) : A[σ]` and `ψ ∧ φ_x[σ] ⇒ required(σ(x))`; it is **not** required that
`ψ ⇒ φ_x[σ]`. Example: `φ = (i=0)`, image guard `g = (j=0)`, `ψ = (i=1) ∨ (j=0)`: `ψ ∧ φ ⇒ g`
holds, `ψ ⇒ g` fails; the guarded use is legal and the `i=1` part is not lost.

**Substitution lemma on the representation.** After validating a raw origin once against its
annotation in its own parameter context, `Γ_C ⊢ C : A_C` and `σ : Δ → Γ_C` give
`Δ ⊢ VIEW(C,σ) : A_C[σ]`; a copied body is never rechecked per occurrence.

### IX.2 Constructor rules

| Constructor | Checks → type |
|---|---|
| VAR(x) | declaration → its type |
| UNIVERSE(ℓ) | → `U_{ℓ+1}` |
| PI(A,B), SIGMA(A,B) | `A:U_i`; open `B` at fresh `x:A`, `B:U_j` → `U_max(i,j)` |
| LAM(A,h) | against `Π(x:D).B`: `A ≡ D`; body at fresh `x:D` checks at `B(x)` |
| APP(f,a) | type of `f` observes as `Π(x:A).B`; `a:A` → `B(a)` |
| PAIR(a,b) | against `Σ(x:A).B`: `a:A`, `b:B(a)`; a synthesized pair keeps its checked Σ annotation |
| FST(p), SND(p) | `p : Σ(x:A).B` → `A`, resp. `B(fst p)` |
| PATH(h,l,r) | family `B(j):U_ℓ` at fresh `j`; `l:B(0)`, `r:B(1)` → `U_ℓ` |
| PLAM(h) | against `PathP(j.B,l,r)`: body at fresh `j` in `B(j)`; its endpoints `≡ l`, `≡ r` |
| PAPP(B,l,r,p,s) | path type data checked; `p` at it; `s` in scope → `B(s)` |
| GLUE_TYPE(A,α,T,e) | `A:U_ℓ`; under `χ∧α`: `T:U_ℓ`, `e:Equiv(T,A)` → `U_ℓ` |
| GLUE_INTRO(A,α,T,e,t,a) | data valid; `a:A`; under `χ∧α`: `t:T`, `e.map(t) ≡ a` → the Glue type |
| UNGLUE(…,v) | data valid; `v` at the Glue type → `A` |
| COMP(hA,φ,hu,a₀) | `A(j):U_ℓ` at fresh `j`; `φ` independent of `j`; `a₀:A(0)`; under `χ∧φ`: `u(j):A(j)`, `u(0) ≡ a₀` → `A(1)` |
| SYSTEM | against `A`: `χ ⇒ ⋁φ_k`; each branch under `χ∧φ_k`; overlaps convertible |
| GLOBAL(s,σ) | declared symbol; checked parameter map → declared type `[σ]` |

Glue introductions and eliminations are checked with their explicitly retained Glue data,
never by recovering them from a type already collapsed on an entailed face. Under a false face,
obligations are vacuous once the finite syntax is in scope.

### IX.3 Conversion

Type-directed, using the computation rules, their congruence, the interval/face algebra, and
function, pair, path and Glue η. A supplied path `p : A = B` is used through transport and never
becomes a conversion rule.

* **Face clauses.** Normalize `χ`; convert under each consistent clause `C`. Intervals under `C`:
  substitute the endpoints fixed by `C`, compare canonical DNFs; faces: compare `C ∧ φ` with
  `C ∧ ψ`. A covered system always has a branch available under a single clause.
* **Types.** Observe both; equal references are equal; universes compare levels; Π/Σ compare
  domains, then both codomains at one common fresh variable; paths compare families at one fresh
  dimension and endpoints; Glue compares guards, bases, and on the common guard fibres and
  equivalences; neutral types by spine. Different irreducible tags are `UNEQUAL`; a pending
  computation is not an irreducible tag. Fresh comparison identities are keyed by the comparison
  request and slot, in their own namespace.
* **Terms.**
  `Eq_{Π}(f,g) ⟺ Eq_{B(x)}(f x, g x)`;
  `Eq_{Σ}(p,q) ⟺ Eq_A(fst p, fst q) ∧ Eq_{B(fst p)}(snd p, snd q)`;
  `Eq_{PathP}(p,q) ⟺ Eq_{B(j)}(p@j, q@j)`;
  at a non-collapsed Glue type: `unglue u ≡ unglue v : A` under `C` and `u ≡ v : T` under `C∧α`.
* **Neutral spines** compare head and elimination spine structurally (no η re-expansion of the
  head, which would loop comparing `f x, g x` back through `f, g`): same variable; applications
  with arguments at the domain; same projection tag; path applications with intervals modulo
  `C`; unglue with guards/base/fibre data; blocked compositions aligned at one fresh dimension
  with families, faces, caps and tubes compared; opaque constants by symbol and parameters.
* **Requests** are memoized by mode, ordered inputs, expected type, typed boundary and projected
  face, through the same request/publication/delivery protocol as observation. Encountering a
  running request is not permission to assume equality. A real unresolved cycle is reported at
  quiescence; a budget interruption is `UNRESOLVED` and is not stored as inequality.

### IX.4 Admission of a definition environment

One immutable definition environment; one whole-environment admission transaction: freeze all
declarations and bodies; validate declarations in dependency order; check every body against
its declaration, typing recursive occurrences from the formed declaration (never treating a
running body check as a body certificate); commit `ENV_VALID` only if every obligation is
`VALID`. One `INVALID` rejects; an unresolved obligation leaves the environment unadmitted.
Public checked observation and compiler publication pass through this gate. Example that must be
rejected: `bad : A = (λx:A.(x,x)) dependent`, `dependent : A = bad`.

---------------------------------------------------------------------------------------------

## Part X. The interaction net and the equal-length theorem for the machine

### X.1 Agents

A data *descriptor* has a positive principal port and an immutable payload: `REF`, `MAP`,
`INTERVAL`, `FACE`, `TERM_BINDER`, `DIM_BINDER`, `PARTIAL`, `PARTIAL_DIM_BINDER`, `CONTEXT`,
`HEAD_RECIPE`, `DIMSET`, `EVAL_RESULT`, and for templates `SCOPE`, `TEMPLATE_ENV`,
`TYPED_PARTIAL`. A one-result *operation agent* has a negative principal port, a positive result
port and immutable parameters. When `OP` meets `DATA`, with `r` the endpoint attached to
`OP.result`:

```
compute the finite operation;  allocate result descriptor D;  connect D.principal to r;
retire OP and the consumed descriptor
```

| Operation with input | Result |
|---|---|
| REINDEX_TERM(σ) / REF(t) | REF(reindex(t,σ)) |
| REINDEX_INTERVAL(σ), REINDEX_FACE(σ) | substituted interval / face |
| COMPOSE_MAP(σ) / MAP(τ) | MAP(compose(σ,τ)) |
| RESTRICT_MAP(φ) / MAP(σ) | source face strengthened by φ[σ], target by φ |
| LIFT_TERM, LIFT_DIMENSION(owner,slot) / MAP(σ) | lifted map of IV.5 |
| OPEN / REF(t) | HEAD_RECIPE(open t) |
| UNFOLD_GLOBAL / REF(t) | REF(unfold_global t) |
| REINDEX_*_BINDER(σ) | binder with reindexed owner |
| APPLY_TERM_BINDER(a), APPLY_DIM_BINDER(r) | REF of the applied body |
| FORALL_DIMENSION(i), PROJECT_FACE(S) | FACE(∀i.φ), FACE(π_S χ) |
| FACE_COVERAGE(χ), USE_PARTIAL(χ) | COVERED / NOT_COVERED; REF(t) when covered |
| GET_SUPPORT / REF(t) | DIMSET(S(t)) |
| CAPTURE_*_SCOPE, REINDEX_SCOPE, APPLY_SCOPE, FORALL_SCOPE, REINDEX_TEMPLATE_ENV, INSTANTIATE_TEMPLATE(Q), REINDEX/USE_TYPED_PARTIAL | the corresponding Part VIII operation |

*Materialize a head:* an `n`-field recipe of tag `K` becomes a positive-principal `HEAD_K` with
`n` negative auxiliaries attached to field descriptors; a system's branch list is
`BRANCH_NIL`/`BRANCH_CONS`. *Duplicator* meeting `D(v)`: two descriptors `D(v)` with the same
payload handle (nothing copied). *Eraser*: retire the descriptor, release ownership. *Evaluation
agent* `EVAL(χ)` meeting `REF(t)`: register the result endpoint as a continuation of the key
`(t, π_{S(t)}χ)`.

**Replacement discipline.** Each rule lists every surviving boundary connection and fresh port
once; connect opposite polarities only; for multi-node replacements compose the old boundary
matching with the replacement matching through temporary connectors. Concurrently: pin, lock all
affected owners (including surviving endpoint owners) in one total order, revalidate, install,
publish, retire, then enqueue new active pairs.

### X.2 The exact residual diamond

An interaction net with one principal port per agent and one deterministic rule per active pair
(including its payload) has, for distinct active pairs `a ≠ b`,

```
N ──a──▶ N_a ──b/a──▶ P
N ──b──▶ N_b ──a/b──▶ P          (exactly one residual step on each side)
```

The memo is shared state, so its transitions are made explicit. Jobs: `REQ(K,c)`,
`EVAL(K,frame)`, `PUB(K,v)`, `DELIVER(c,v)`; continuations are unique and consumed once.

```
REQ(K,c) + U      → R({c}) + EVAL(K, initial frame)
REQ(K,c) + R(W)   → R(W ⊎ {c})
REQ(K,c) + D(v)   → D(v) + DELIVER(c,v)
PUB(K,v) + R(W)   → D(v) + {DELIVER(c,v) : c ∈ W}
DELIVER(c,v)      → the resumed frame or root sink of c
```

Only the unique evaluator task of `K` publishes. Delivery is an event in the ready case and in
the waiting case alike. The evaluation input is determined by `K` alone.

**Overlaps, exhaustively.** Two requests to the same `U` key: both orders take two request
events, create one evaluator task, reach `R({a,b})`. Two requests to a running key: both orders
reach `R(W ⊎ {a,b})`. Two requests to a ready key: both deliver both. Request and publication on
`R(W)`:

```
request first:      R(W) → R(W∪{a}) → D(v) + deliveries for W∪{a}
publication first:  R(W) → D(v) + deliveries for W → D(v) + deliveries for W + DELIVER(a,v)
```

one request and one publication on each side, same job multiset. Request and an evaluator step
on a running key commute (the request changes only the waiter multiset; the step reads only its
own frame). Two publications for one key cannot exist; two deliveries of one continuation cannot
exist; a join is enabled only after its children deliver (causal sequence, not overlap).
Distinct keys, immutable arena extension and canonical interning commute. Hence the combined
scope, observation, memo and delivery relation has exact residual diamonds, modulo graph
isomorphism and canonical immutable data. The projected key is essential: if two requests sharing
a key could produce different heads because of their original faces, the request/request square
would fail.

### X.3 Random descent, fixed work, geodesic

**Random descent.** If `N →ⁿ Z` with `Z` normal, then every `N → M` has `M →ⁿ⁻¹ Z`. (Induction
on `n`: same event — the tail; distinct — the diamond gives a common state one step from each;
the induction hypothesis on the chosen successor gives `n−2` from there; prepend the residual
step from `M`. For `n = 1` a surviving distinct event would contradict normality.) Hence
`d(N)` = length of any complete reduction is well defined, `N → M ⇒ d(N) = 1 + d(M)`, and
`min |ρ| = max |ρ| = d(N)`.

**Geodesic in the reversible graph.** Allow each elementary edge backward. A zigzag `γ` from `N`
to `Z` with `f` forward and `b` backward traversals has `f − b = d(N)`, so
`|γ| = d(N) + 2b ≥ d(N)`, attained by any forward reduction: `d(N) = dist(N, Z)`.

```
 rank d:   3      2      1      0
           N ───▶ ● ───▶ ● ───▶ Z          forward: each edge lowers d by 1
           │      ▲
           └─────▶●  (a backward edge raises d by 1 and must be paid back)
```

**Weights.** If each diamond preserves the sum of its edge weights (the memo diamonds preserve
the event multiset; local diamonds preserve rule instances), fixed nonnegative weights give a
potential `D(N) = w(e) + D(M)` and `W(γ) = D(N) + 2 Σ_{backward} w(e) ≥ D(N)`. `REQUEST` is one
class whatever the entry state; separate running-hit/ready-hit counters are not schedule
invariant (a request can cross a publication).

**Requested observation.** For one root: fixed quiescent initial memo; stored references are
inert; every child demand is a required dependency of a retained parent; a parent publishes after
all its launched children deliver; no semantic job is cancelled. Then no unfinished evaluator
task remains in a completed root's demand network, and the completed observation is a normal
form of its demand computation. Neutral and system results are legitimate terminal observations;
a suspended demand cycle is not.

**Consequence.** For every normalizing initial configuration of this abstract machine, every
complete reduction has the same interaction-work vector, and every forward reduction is a
minimum-cost path in the reversible graph of the same elementary interactions, for every
nonnegative diamond-balanced weighting. No search for a reduction order is needed. Elapsed time,
memory and raw instruction counts are other observables (Part XVII).

### X.4 Workers, ownership, comparison

Workers: one or many run the same event protocol; `outstanding = queued + executing`; a job
enqueues its children before finishing; `outstanding = 0` at a closed workload is quiescence; a
completed root gives `W_OK`, an unresolved cycle `W_STUCK`. Joins fill slots in original branch
order. Ownership: ready entries keep results for the whole workload (evicting and rerunning a
key would break at-most-once production); continuations are consumed once; teardown stops
workers, detaches suspended waiter cycles, then destroys memo and arenas in lifetime order.
Comparison of runs: exact matching of reachable result graphs preserving sharing, anchored input
identities, generated identities renamed with owner/slot provenance preserved, exact backtracking
where refinement leaves ambiguity; hashes never decide equality.

---------------------------------------------------------------------------------------------

## Part XI. Realizations, identities as replacements, and the identity compiler

### XI.1 Realizations and contextual replacement

For a construction diagram `P` with boundary `β`, its realization is the dependent telescope of
internal witnesses and constraints, `Real(P,β) = Σ_w Constraints_P(β,w)` (dependent and higher
data included). A local replacement is evidence `e_β : Real(P,β) ≃ Real(Q,β)`; inside a context
it acts by

```
(β, p, c) ↦ (β, e_β(p), c)
```

Boundary and surrounding context stay shared; the inverse and inverse laws act pointwise, and
reindexing the boundary commutes with the action.

**Graphs of operations.** `N_f(a,b) = (f a = b)`, `N_m(a,b,c) = (m(a,b) = c)`. Wire composition:

```
Σb. (f a = b) × (g b = c)  ≃  (g(f a) = c)
(b, s, t) ↦ ap_g(s) · t          w ↦ (f a, refl, w)
```

For a finite acyclic expression `C` these contractions give `c_C : Real(C,γ,y) ≃ (C(γ) = y)`
(unary step: `ap_f(c_A(r)) · s`; binary: `ap2_m(c_A(r_A), c_B(r_B)) · s`). A shared intermediate
occurs once in the telescope. An identity `p : C_L(γ) = C_R(γ)` then determines its action

```
F_p = c_R⁻¹ ∘ (q ↦ p⁻¹ · q) ∘ c_L          inverse  c_L⁻¹ ∘ (q ↦ p · q) ∘ c_R
```

**Associativity.** `α : (a*b)*c = a*(b*c)`.

```
      left diagram                 right diagram
          *  ── y                      *  ── y
         ╱ ╲                          ╱ ╲
     u= *   c                        a   * =v
       ╱ ╲                              ╱ ╲
      a   b                            b   c

left realization  (u, s : a*b = u, t : u*c = y)
right realization (v, s : b*c = v, t : a*v = y)
forward (u,s,t) = (b*c, refl, α⁻¹ · ap_(z ↦ z*c)(s) · t)
reverse (v,s,t) = (a*b, refl, α  · ap_(z ↦ a*z)(s) · t)
```

**Cuts and residual loops.** `Σz. (C=z) × (D=z) ≃ (C=D)` by `(z,u,v) ↦ u·v⁻¹`, inverse
`h ↦ (D, h, refl)`. Given `p : C = D`, the residual is the loop `p⁻¹ · (u·v⁻¹) : D = D`; supplying
`p` does not make that loop `refl`. A fixed `p : x=y` identifies `Path(x,y)` with the loop space at
`y` by `h ↦ p⁻¹·h`; it does not trivialize loops. A binary operation on independent paths gives
the square `m(p@i, q@j)`; its diagonal is one path through it.

**Erasure.** `Σ(b:B).R(b) → B` with a contraction `k : Π b. Contr(R b)`: projection `(b,r) ↦ b`,
section `b ↦ (b, fst(k b))`, homotopy pointwise `snd(k b)(r)`. Without `k`, nothing is erased;
the physical eraser agent is an ownership operation, not a quotient.

### XI.2 Diagram declarations

```
IdentityDecl: parameters Γ, required face φ, result type B, left and right diagrams,
              evidence p : Path_B(C_left, C_right)
Diagram: nodes k = 0..n−1 with value variable x_k, witness variable e_k, type A_k,
         defining term t_k : A_k (checked after all earlier x, e); output o : B
```

After node `k` the context gains `x_k : A_k`, `e_k : Path_{A_k}(t_k, x_k)`. A shared node occurs
once; `m(m(a,b),c)` has one node `u = m(a,b)` and output `m(u,c)`. Every type input passes
formation in a universe (`x : A` is not evidence that `x : U_ℓ`).

```
R_n = Path_B(o, y)
R_k = Σ(x_k : A_k). Σ(e_k : Path_{A_k}(t_k, x_k)). R_{k+1}           Real(C,Γ,y) = R_0
canonical substitution: ν := id_Γ;  for k: a_k := t_k[ν];  ν := ν, x_k ↦ a_k, e_k ↦ refl(a_k)
C := o[ν]
```

Images are references; reusing an image reuses its handle, so a shared DAG is not expanded into a
tree. The evidence is checked at `Path_B(C_left, C_right)` under `φ`.

### XI.3 Removing one singleton block

Given `t : A`, `x : A`, `e : Path_A(t,x)`, `z : D(x,e)`:

```
x_i = e@(¬i)
e_i = ⟨j⟩ e@(¬i ∧ j)
down(A,t,D,x,e,z) = coe^i D(x_i, e_i) z        : D(t, refl t)
up(z₀)            = (t, refl t, z₀)
```

At `i = 0`: `x_0 = e@1 = x`, `e_0 = ⟨j⟩e@j = e` (path η), family `D(x,e)`. At `i = 1`:
`x_1 = e@0 = t`, `e_1 = ⟨j⟩ e@0 = refl t`, family `D(t, refl t)`. The family substitutes `x` and `e`
simultaneously; images are not substituted again. `D` may depend on the witness `e`, and the
whole dependent tail `R_{k+1}` (later types, values, witnesses) is transported, not only values.

Correctness: the singleton `S = Σ(x:A). Path_A(t,x)` is contractible with centre `(t, refl)` and

```
H((x,e), i) = (e@i, ⟨j⟩ e@(i ∧ j))

    i=0: (t, refl t)  ●━━━━━━━━━━━━━━━━━━━● (x, e) : i=1
                         e@i moves t → x along e;
                         the witness ⟨j⟩e@(i∧j) is the initial segment of e up to i
```

so including the centre fibre `D(t,refl)` into `Σ(s:S).D(s)` is an equivalence; `down` is transport
along `H` reversed. (This is singleton path induction, valid when `D` depends on `e`.)

```
emit_collapse(k, prefix, r):                       emit_expand(k, prefix, q):
  k = n → r                                          k = n → q
  A := A_k[prefix]; t := t_k[prefix]                 t := t_k[prefix]
  D := R_{k+1}[prefix]   (x_k, e_k free)             z₀ := emit_expand(k+1, prefix + (x_k↦t, e_k↦refl t), q)
  x := fst r; e := fst(snd r); z := snd(snd r)       → pair(t, pair(refl t, z₀))
  z₀ := down(A,t,D,x,e,z)
  → emit_collapse(k+1, prefix + (x_k↦t, e_k↦refl t), z₀)

c_C : Real(C,γ,y) → (C(γ) = y)          d_C : (C(γ) = y) → Real(C,γ,y)
```

These emit syntax; they evaluate nothing. Composing the per-block equivalences (base case: the
identity on the output path type) proves `c_C`, `d_C` inverse up to paths. Round trips are paths,
not equal references; constant-family `coe` is not simplified.

### XI.4 compile_identity

```
validate Γ, φ, B; validate both diagrams; build R_L, R_R, C_L, C_R
check evidence : Path_B(C_L, C_R)
generate c_L, d_L, c_R, d_R
fresh P : Path_B(C_L, C_R); common parameter y : B; distinct formal r_L : R_L, r_R : R_R
graph_pair_forward = d_R(concat(inverse P, c_L(r_L)))
graph_pair_reverse = d_L(concat(P, c_R(r_R)))
forward_body = graph_pair_forward[P ↦ evidence];   reverse_body likewise
check bodies at R_R, R_L; validate the structural certificate; intern and publish
```

so `F_p = d_R ∘ (q ↦ p⁻¹·q) ∘ c_L`, `B_p = d_L ∘ (q ↦ p·q) ∘ c_R`. Concatenation with `p` is an
equivalence of path spaces; composites give the inverse homotopies. The proof `p` is kept as a
reference; it is not normalized.

**Lowering.** `refl(a) = ⟨i⟩a`; `inverse(p) = ⟨i⟩ p@¬i`; `coe(i.A, a) = COMP` with false tube;
`concat(p,q) = ⟨i⟩ hcomp^j_A [(i=0) ↦ x, (i=1) ↦ q@j] (p@i)`; substitution is reindex.

**Certificates** (tags): IDENTITY (declaration + diagrams), EQUIVALENCE (`e : Equiv(X,Y)`;
forward `fst e`, reverse `b ↦ fst(fst((snd e)(b)))` — the X-coordinate of the fibre centre),
RESIDUAL_EQUIVALENCE (two singleton-prefix descriptions ending in terminal types `Z_L, Z_R` and
`e : Equiv(Z_L,Z_R)`; forward `d_R ∘ e.map ∘ c_L`), CUT (`(z,u,v) ↦ u·v⁻¹`, `h ↦ (D,h,refl)`),
CONTRACTIBLE_FIBRE (`k`). Verification re-emits the prescribed templates and checks exact
structural equality; arbitrary user-supplied inverse functions require an actual equivalence.
Arbitrary cyclic constraints stay in the residual type and are never contracted without evidence.

### XI.5 Invocation

```
APPLY_TRANSFORM(id, dir, σ).principal — REF(a).principal ;  APPLY_TRANSFORM.result — b
   becomes
REF(v).principal — b,    v = reindex(body_dir, σ, slot_dir ↦ a)
```

One replacement; no evaluation of `a`, the proof or `v`. Preconditions (validated record,
valid `σ`, `χ ⇒ φ[σ]`, `a` at the instantiated domain) are checked before execution, not by a
conversion run inside the rule. Inside programs, the instruction `TRANSFORM_CALL(id, dir, σ, a,
annotations)` has support containing that of its instantiated body (including evidence through
the template, required faces and argument-type dependencies). Its dispatch:

```
evaluate K whose origin is TRANSFORM_CALL(id,dir,σ,a):
   allocate APPLY_TRANSFORM(id,dir,σ) attached to REF(a);
   attach its result to CONTINUE_REFERENCE(K);  transfer K's suspended evaluation to it
CONTINUE_REFERENCE(K) — REF(v)  →  REQ(key(v, E[K].face), FORWARD_RESULT(K))
```

Delivery to `FORWARD_RESULT(K)` schedules K's normal publication frame. Pending net pairs count
in the same outstanding total as evaluator jobs. **One call origin per record and orientation:**

```
generic_call[id,dir] = TRANSFORM_CALL(id, dir, identity images of Γ, VAR(slot[id,dir]), types, face)
mk_transform_call(id,dir,σ,a) = reindex(generic_call[id,dir], σ|Γ, slot ↦ a)
reindex(call(id,d,σ,a), τ) = call(id, d, σ;τ, a[τ])          (reference equality)
```

so two observations at the same projected face have one call producer, one `APPLY_TRANSFORM`
and one `CONTINUE_REFERENCE`.

**Substitution and higher coherence.** `(F_p(r))[σ] = F_{p[σ]}(r[σ])`. For `H : p₀ = p₁`,
`⟨i⟩ F_{H@i}(r)` is the output path, produced by substituting `H@i` into the template's proof
slot; repeated abstraction handles higher cubes. `F_q ∘ F_p` versus `F_{p·q}` is a higher
equality, not a collapse of two counted invocations into one.

**Sharing example.** Node `u = f(x)`, output `m(u,u)`: one block, one witness `s`, collapse family
`Path(m(s@¬i, s@¬i), y)` with both occurrences the same reference.

---------------------------------------------------------------------------------------------

## Part XII. Identities as ordinary values: runtime construction

### XII.1 Maps and presentations

```
Maps(X,Z) = Σ(c : X→Z). Σ(d : Z→X). (Π x. Path_X(d(c x), x)) × (Π z. Path_Z(c(d z), z))
                                                                 : U_max(a,b)
Pres_{a,b}(Z) = Σ(X : U_a). Maps(X, Z)                           : U_max(a+1,b)
```

Inverse witnesses are kept as terms with their higher distinctions; no proof irrelevance.
Composition of `E = (f,g,h,k) : Maps(X,Y)` and `F = (u,v,H,K) : Maps(Y,Z)`:

```
f' = u ∘ f        g' = g ∘ v
h'(x) = ap(g)(H(f x)) · h(x)      : g(v(u(f x))) = g(f x) = x
k'(z) = ap(u)(k(v z)) · K(z)      : u(f(g(v z))) = u(v z) = z
```

(the intermediate points are `g(f x)` and `u(v z)`). Inverse swaps `f,g` and `h,k`; identity uses
identity maps and `refl`.

### XII.2 The dependent singleton, with both proofs

`A : U_a`, `t : A`, `D : (x:A) → Path_A(t,x) → U_r`; `S_D = Σ x. Σ(e : t = x). D(x,e)`,
`Z = D(t, refl t)`:

```
c(x,e,z)  = coe^j D(e@¬j, ⟨k⟩ e@(¬j ∧ k)) z
d(z₀)     = (t, refl t, z₀)
B_w(j)    = D(e@¬j, ⟨k⟩ e@(¬j ∧ k)),     b_w(j) = fill^{j'} B_w(j') [⊥] z (j)       w = (x,e,z)
h(w)      = ⟨i⟩ (e@i, ⟨k⟩ e@(i ∧ k), b_w(¬i))       : d(c w) = w
b₀(j)     = fill^{j'} Z [⊥] z₀ (j)
k(z₀)     = ⟨i⟩ b₀(¬i)                              : c(d z₀) = z₀
```

Endpoints: `h` at `i=0` is `(t, refl, b_w(1)) = (t, refl, c w) = d(c w)`; at `i=1` it is
`(x, e, b_w(0)) = (x,e,z)`. `k` at `i=0` is `b₀(1) = coe Z z₀ = c(d z₀)`; at `i=1` it is `z₀`. These
use fill's boundary equations and path/Σ η only; constant-family `coe` is not assumed regular.

### XII.3 Diagrams as values

```
Diagram_{b,r}(B) = Σ(C : B). Σ(R : (y:B) → U_r). Π(y:B). Maps(R y, Path_B(C, y))   : U_max(b,r+1)
zero(B,C)        = (C, λy. Path_B(C,y), identity maps)
node_{a,b,r} : (B:U_b) → (A:U_a) → (t:A) → ((x:A) → Path_A(t,x) → Diagram_{b,r}(B))
               → Diagram_{b,max(a,r)}(B)
node(B,A,t,Q) = (C₀, λy. S_y, λy. q_y ∘ s_y)
   Q₀ = Q(t, refl t), C₀ = C_{Q₀}, D_y(x,e) = R_{Q(x,e)}(y),
   S_y = Σ x. Σ(e : t = x). D_y(x,e),  s_y : Maps(S_y, D_y(t,refl)) the singleton of XII.2,
   q_y : Maps(D_y(t,refl), Path_B(C₀,y)) projected from Q₀
```

A finite diagram is a right fold of `node` ending in `zero`; the tail `Q` is an ordinary argument
and may be computed by a program. Nothing inspects a host registry to find the number of nodes,
a realization type, or the next action. Residual descriptions use the same extension with an
arbitrary terminal family.

### XII.4 The action on runtime diagrams

```
F(L,R,p,y,r) = d_R(y)(p⁻¹ · c_L(y)(r))        G(L,R,p,y,s) = d_L(y)(p · c_R(y)(s))
```

with `L, R : Diagram(B)`, `p : Path_B(C_L, C_R)` all arguments. The middle maps `q ↦ p⁻¹·q`,
`s ↦ p·s` have inverse paths

```
h(q) = assoc(p, p⁻¹, q)⁻¹ · ap(λv. v·q)(rinv p) · lunit(q)
k(s) = assoc(p⁻¹, p, s)⁻¹ · ap(λv. v·s)(linv p) · lunit(s)
```

(`assoc : (p·q)·r = p·(q·r)`, `rinv : p·p⁻¹ = refl`, `linv : p⁻¹·p = refl`), composed with L's
collapse and R's expansion by XII.1. The groupoid laws are generated, not assumed:
`J(P,d,b,p) = coe^i P(p@i, ⟨j⟩ p@(i∧j)) d`; each law by path induction on its path arguments
left to right; for a word `w` in refl, inverse and concatenation at a point `a`, `K(w) : w = refl`
with `K(refl) = refl`, `K(v⁻¹) = ap(inverse)(K v)`, `K(v·w) = ⟨k⟩(K(v)@k)·(K(w)@k)` followed by
`K(refl·refl)`, and `K(refl·refl)@k@i = fill^j_A [(i=0)↦a, (i=1)↦a] a (¬k)`; equality of two base
words `u,v` is `K(u)·K(v)⁻¹`.

The five certificate schemas have ordinary value counterparts: for `e : Equiv(X,Y)`, `c = fst e`,
`d(y)` = X-coordinate of the centre of `(snd e)(y)`, `k(y)` = the centre's path, `h(x)` = `ap(fst)`
of the fibre contraction at `(x, refl)`; CUT by path induction keeping the loop; COLLAPSE_FIBRE with
`⟨i⟩(b, (snd(k b)(r))@i)` and `refl`.

### XII.5 One witness interface

A supplied proof and a computed proof have the same type and enter the same action term; no
dispatch on provenance. General reuse along a known identity is the ordinary program

```
reuse(O, p, a) = coe^i O(p@i) a : O(y)            for O : B → U, p : x = y, a : O(x)
```

It transfers already computed evidence; evaluating the transport is computation with its cost;
it does not create a missing inhabitant of `O(x)`.

**Measured fact (18 October, this session).** The witness programs for XII.1–XII.4
(`review_singleton_witnesses`, `review_generic_identity_action`, `review_runtime_presentations`,
`review_runtime_nodes`) compile against the unmodified source of commit 24b2bfb and pass under
ASan/UBSan, with zero registered transforms. These constructions are terms checked and evaluated
by the existing core; no additional runtime subsystem is involved.

---------------------------------------------------------------------------------------------

## Part XIII. Demand, sharing and cost

### XIII.1 Three identities

A *producer key* identifies a deterministic computation with its complete instantiated typed
boundary (the observation key is the first example). A *consumer occurrence* is one request
with its continuation. A *primitive work occurrence* is one counted step. Two requests of one
key give two REQUESTs, two DELIVERs, one producer's EVAL frames and one PUB.

### XIII.2 Demand closure with ready cuts

For a finite acyclic producer graph `P`, root keys `R`, ready keys `K`, `dep_P(v)` the keys `v`
requests:

```
D_P(R,K) = μX. (R \ K) ∪ ⋃_{v ∈ X} (dep_P(v) \ K)
```

A ready key cuts its whole prerequisite cone: if root `r` is ready, `D_P({r},{r}) = ∅` even when
its child `a` is absent; subtracting `K` from the cold node set would wrongly charge `a`.
If `K` is closed under prerequisites, `D_P(R,K) = D_P(R,∅) \ K` (a root-to-uncached path cannot pass
a cached vertex, whose prerequisites would then be cached). Roots share by union:
`D_P(R₁ ∪ R₂, K) = D_P(R₁,K) ∪ D_P(R₂,K)`.

Work extracted: one REQUEST and DELIVER per occurrence in `O_R ∪ ⋃_{v∈D} Use_P(v)`, one PUB and
the actual EVAL/local steps per producer in `D`. **Minimum-work theorem:** if every occurrence is a
required premise of its recipe, every successful execution runs every producer in `D_P(R,K)`, and
running each once in dependency order suffices; the one-producer protocol attains it. Doing less
requires a different valid recipe, an extra initially available result, or a demonstrated
redundant premise.

### XIII.3 Alternatives: the positive antichain algebra

For finite families of required-work sets, with `N` removing duplicates and strict supersets:

```
𝒜 ⊕ ℬ = N(𝒜 ∪ ℬ)        𝒜 ⊗ ℬ = N{A ∪ B : A ∈ 𝒜, B ∈ ℬ}       0 = ∅, 1 = {∅}
𝒜 ⊗ (ℬ ⊕ 𝒞) = (𝒜⊗ℬ) ⊕ (𝒜⊗𝒞)       𝒜 ⊕ (𝒜 ⊗ ℬ) = 𝒜
```

(commutative, associative, idempotent; the positive-DNF laws). Scalar pruning is not
compositional: `a` costs 5, `b` costs 6; one obligation allows either, another needs `b`;
`{{a},{b}} ⊗ {{b}} = {{b}}`, cost 6, whereas choosing the locally cheaper `a` costs 11.

**Contextual dominance (positive weights).** With `f_𝒜(K) = min_{A∈𝒜} Σ_{e∈A\K} c(e)`:

```
[∀K. f_𝒜(K) ≤ f_ℬ(K)]  ⟺  [∀B ∈ ℬ. ∃A ∈ 𝒜. A ⊆ B]
```

(⇐: a minimizing `B` and its subset `A` give `A\K ⊆ B\K`. ⇒: take `K = B`; then `f_ℬ(K) = 0`, so
some `A` has zero residual, and positivity forces `A ⊆ B`.) Two antichains with identical profiles
are equal: the antichain is a complete representation of contextual resource behaviour.

### XIII.4 Specialization merges work identities

The image of a work set under a (possibly non-injective) key map `s` is the Boolean direct image
`s_!(A) = {s(e) : e ∈ A}`; `s_!(A∪B) = s_!A ∪ s_!B`, `(t∘s)_! = t_! ∘ s_!`, and absorption commutes:
`N{s_!A : A ∈ N(𝒜)} = N{s_!A : A ∈ 𝒜}`. Subtraction does not: `A = {a}`, `K = {b}`,
`s(a) = s(b) = z` gives `s_!(A\K) = {z}` but `s_!A \ s_!K = ∅`. Signed incidence vectors cannot be
pushed forward linearly (`e_a + e_b − e_c` maps to `e_z` though the specialized sets agree). Order:
reindex recipes and guards → validate premises → intern specialized keys → resolve demand and cut
at ready keys → extract shared work → compare costs.

### XIII.5 Cost differences carried by identities

`Cost(P;Q, S) = Cost(P,S) + Cost(Q_P, S_P)` (trace concatenation; `S_P` keeps the memo). For an
identity `α` relating realizations `P, Q`, `ε_α(S) = Cost(P,S) − Cost(Q,S)`, with
`ε_{β∘α} = ε_α + ε_β`, `ε_{α⁻¹} = −ε_α`, and for a continuation

```
ε_{α;C}(S) = ε_α(S) + Cost(C_P, S_P) − Cost(C_Q, S_Q)
```

With fixed supports `a, b, c` (incidence vectors) and completed context `k`:
`(a∨c) − (b∨c) = (1−c)(a−b)` and the remaining difference is `Σ_e c(e)(1−k_e)(1−c_e)(a_e − b_e)`.
Around any cycle of realizations the differences sum to zero (telescoping). A negative difference
is a saving between alternatives, never a negative-cost instruction.

### XIII.6 Shortcuts, certificates, transfer

Adding one edge `u→v` of cost `c` to a graph with distances `D₀`:
`D₁(x) = min{D₀(x), d₀(x,u) + c + D₀(v)}`; old distances survive exactly when
`D₀(u) ≤ c + D₀(v)` for every added edge. A **lower-bound certificate** is `V` with `V = 0` at
successful terminals and `V(s) ≤ c(e) + V(s')` on every admitted edge; then every successful path
from `s` costs at least `V(s)`; a policy with `V(s) = c(e) + V(s')` and a progress rank attains it.
**Transfer lemma:** if every concrete implementation `p` has an admitted abstract realization with
`Cost_A ≤ a·Instr(p) + b`, the selected optimal `π*` has `Instr(emit π*) ≤ c·Cost_A(π*) + d`, then
`Instr(emit π*) ≤ c(a·I_best + b) + d`. The whole cost is
`I_select + I_emit + I_execute`; instance-dependent selection is not free by calling it compilation.

### XIII.7 Resource formulas (kept as annotations, no search)

`F(PLAN(p,A)) = ⋀_{e∈A} e`, `F(ALT) = ∨`, `F(JOIN(E,G,g)) = F(E) ∧ F(G) ∧ ⋀_{e∈W(g)} e`.
A set satisfies `F` iff it contains the work of a represented realization, so
`min_p Σ_{W(p)} w = min_{S ⊨ F} Σ_S w`. Mandatory work: `Must(AND) = ∪`, `Must(OR) = ∩`;
`opt(F) = Σ_{Must F} w + opt(F[Must:=1])`; disjoint supports add. `(a∨b)∧b = b`;
`(a∨b)∧(b∨c) = b ∨ (a∧c)`, cost `min(w_b, w_a + w_c)`. Section 73 of the specification excludes the
automatic cofactor solver and the branch-and-bound frontier: these formulas are annotations and
checked derivations over actual or supplied realizations, not a planner.

---------------------------------------------------------------------------------------------

## Part XIV. Reuse of completed computation (§§74–82)

**Records.** Occurrence (reference, context, face, validation, provenance); Computation
(immutable operation and operands, one persistent producer cell); Answer (result plus the
dependency evidence needed for reuse; for evaluation also residual and receipt); Delivery (a
consumer's view at its own boundary). The U/R/D protocol applies to every pure request family;
a handle refers to the shared producer, so stepping two handles never runs two copies.

**Structural identity.** `shape(t, ρ)` is the interned alpha/view normal form of the opened
construction: bound identities as depth/slot, free identities anchored, all fields, levels, faces,
scope metadata and proof terms kept; GLOBAL by symbol and parameter images (body not expanded);
no evaluation. Required: alpha-renamed binders, nested versus composed views, generic-then-
specialized versus directly constructed, raw node versus equal template view — same shape.
**Action key** of a compiled identity excludes the source declaration label: two labels, one
action, one call producer.

**Projected judgments.** A checking/conversion request is keyed by the dependency-closed
restriction of its context (in telescope order, closed under declaration types and faces).
Weakening by an unused declaration reuses the producer; a changed relevant declaration does not.

**Receipts.** An evaluation answer keeps a residual `u` and a receipt `d : Γ;φ ⊢ t ⇒* u` built from
the actual rule sites (reflexive, unfold with body version, β with congruence, projection, endpoint
with its face, Glue/unglue collapse, covered system, covered comp, comp by family head with the
exact clause instantiation, TCALL body). **Specialization rule:** for valid `σ : (Δ;ψ) → (Γ;φ)`,
`d[σ]` lets a request for `t[σ]` continue as a request for `u[σ]` under `ψ`, without replaying `d`;
the specialized residual is then observed normally (a neutral path may reach an endpoint, a
variable may become a redex). A reflexive receipt whose residual is the same request gives no
progress and installs no self-wait. Restriction to a stronger face is the identity substitution
with an entailment premise.

**Revisions.** Each symbol slot has a stable identity and revision; reading an opaque declaration
records its revision with absent body. An answer is reusable when every recorded dependency
revision agrees with the current environment snapshot; unrelated declarations do not invalidate
answers with empty dependency sets.

**Alias boundary invariant (§93).** An alias answer must be scoped at its own entry's boundary.
Counterexample to copying the source result: `source = ((λw:A.f) z) a` has residual `f a`;
returning `source` (which mentions `z`) as the answer for `f a` in a context without `z` is
ill-scoped; and with `p : f = g`, observing `(p@i) a` under `i=0` and `i=1` and aliasing both
residuals to the same original reference made `convert(f a, g a)` flip from `UNEQUAL` to `EQUAL`.
The alias result is a new descriptor of the residual with a reflexive receipt.

**Property of this design (§85, §90).** Here which recipe runs depends on what is already ready
in the memo, so traces of one request differ in length (2 against 3 in the §85 model). That is a
consequence of keeping results in a table outside the net; Part XVIII.

---------------------------------------------------------------------------------------------

## Part XV. Program typing versus established evidence (§88)

Counterexample: in `A:U₀, a:A, b:A`, `f = λx.a`, `k : Π y. Contr(fib f y)` registered with body
`k`, `e = (f,k) : Equiv(A,A)`. Typing, compilation and certificate re-emission all succeed; the
forward call at `b` returns `a`; the reverse call stays stuck. Reading `A` as a two-point type,
`f` is not invertible. Hence a separate proof-use judgment for `(Γ, φ, e, E, dependencies)`:

| Status | Meaning |
|---|---|
| CORE | checks succeed and the dependency closure of context, type and evidence expands into the acyclic core |
| ASSUMED | same, with explicit reachable opaque declarations retained as hypotheses |
| PENDING | the closure reaches a cyclic declaration component |
| INVALID | a structural, formation or typing check rejects |
| UNRESOLVED | a check was interrupted or unresolved |

Algorithm: run admission and `check e : E`; collect symbols from context declarations, `E` and `e`
by a finite walk of stored syntax (variables with their types, every field and image of raw views,
template environments, scope declarations/bodies/types, transform-call bodies); build the symbol
graph from declarations, parameter types and bodies; Tarjan components; any cyclic component
(≥ 2 vertices or a self-edge) gives PENDING, else opaque symbols give ASSUMED, else CORE. Soundness
of CORE is topological expansion of nonrecursive bodies into the core. Runtime-produced proofs are
audited by the same operation: `(λz:P. refl a) loop` is PENDING as source and its finite residual
`refl a` is CORE; `λx. loop` remains PENDING despite its lambda head. Mathematical reuse of an
identity is authorized by CORE, or ASSUMED with hypotheses kept; execution of well-typed code is
never prohibited. **Measured fact:** the 140-line reference module and its 11 cases pass on the
24b2bfb core unchanged.

---------------------------------------------------------------------------------------------

## Part XVI. Instruction cost and the unit of a step (§89)

On the core, a system whose first branch is total and whose other branches have false faces:

| branches | fields opened | REQUEST | EVAL | PUB | DELIVER |
|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 2 | 4 | 2 | 2 |
| 64 | 128 | 2 | 4 | 2 | 2 |
| 1,024 | 2,048 | 2 | 4 | 2 | 2 |

`open_ref` builds the whole field array before a branch is selected, so constant event counts hide
growing work (reproduced on 24b2bfb this session). The transfer theorem needs a small-step machine
`(pc, fixed registers, owned cursors, store)` whose transitions each do a bounded number of word
operations: every scan, hash, comparison, DNF product, interning probe, waiter traversal, copy and
release is a sequence of such steps, and then
`C_steps(run) ≤ c · microsteps(run) + c₀ · boundary work`. The two legitimate repairs for
`open_ref`: count the growing work, or open fields on demand. A bounded-step API must suspend inside
such loops, not count them afterwards.

---------------------------------------------------------------------------------------------

## Part XVII. One witnessed source and its readings (contract of 17 October)

### XVII.1 The source

A context Γ has states `S_Γ` and admissible directed steps `Step_Γ(s,t)` with proof premises;
derivations are generated by identity and composition; higher cells compare derivations with
boundary witnesses. Its readings are: semantic evidence, operational state change, exposed
boundary (owned occurrences available, reserved, waiting, closed), dependency evidence, actual
work, and the observation a consumer reads. *One source* means these readings are attached to the
same admitted rule occurrence and its compositions (by the product fold of II.3); it does not
mean one untyped identifier serves as proof, memo key and effect occurrence. For any observation
`q : S → B`, `S ≃ Σ(b:B). fib_q(b)`: a quotient erases distinctions in its own observation while
witnesses, costs and commitments stay in the retained fibre.

A directed relation `R : S → S → U` already lives in the type theory: a term of `R(s,t)` need not
give one of `R(t,s)`, while paths stay reversible. No directed interval primitive is added.

### XVII.2 Four keys

1. pure operation key: family, canonical operands, relevant premises/revisions;
2. mathematical evidence key: the typed construction and boundary;
3. live occurrence identity: owner/namespace and fresh occurrence/version;
4. comparison key: domain, both recipes, witness, boundary correspondence.

Run history never enters a pure key; equal pure payloads never merge two accepted effect
occurrences. Reindexing an accepted receipt transports its description and keeps its anchor.

### XVII.3 Rule admission and commit

A rule supplies its parameter telescope and guards, read premises, live input versions, result
and successor-boundary recipes, evidence constructor, operational realization, and substitution
compatibility. *Preparation* computes these (suspendable, counted, possibly lost in a race);
*commit* checks the small ownership/version conditions and installs prepared handles atomically.
A live version is linear: consumed at most once, succeeded or closed. Before an observable
transition is published its event identity and immutable descriptor exist; readers never see a
new version without its event.

### XVII.4 Shared histories and inclusion–exclusion

Events `E` are ordered by causality; a finite history `H` has finite support; logical cycles
unfold into new occurrences, so the history is acyclic. A wait on a pending job is a live
obligation, not a causal edge to a nonexistent result. With weights `w ≥ 0`:

```
W(H) = Σ_{e ∈ support(H)} w(e)          W(H₁ ∪ H₂) = W(H₁) + W(H₂) − W(H₁ ∩ H₂)
```

Summing at every pointer visit is wrong; a sequential composition edge of evidence is not an
instruction to pay the referenced producer again. A query of a history is new work indexed by an
immutable prefix captured before the query. A consistent cut: capture a published prefix root per
owner stream and close over retained causal predecessors.

### XVII.5 The algebra

```
C₁ = ℤ^(E),   C₀ = ℤ^(O),   ∂[e] = [outputs(e)] − [inputs(e)]
χ(A) = Σ_{e∈A} [e],          χ(A ∪ B) = χ(A) + χ(B) − χ(A ∩ B),        W = w ∘ χ
```

`χ` is not a monoid map from union to addition (group-completing union would make everything
vanish); Boolean support, linear chains and valuation are connected by this equation. An additive
`v : C₀ → M` is conserved by every admitted generator iff `v∂ = 0`, iff it factors uniquely through
`H₀ = C₀ / im ∂`. Integer coefficients allow comparing histories; they do not allow negative
balances or performed reverse execution. Cycles are `ker ∂`; admitted comparisons give
`∂₂ : C₂ → C₁` with image in `ker ∂`; `H₁ = ker ∂ / im ∂₂`. For work `w : C₁ → M` the obstruction to
descending through supplied 2-cells is

```
w ∂₂ = dw
```

A shortcut `e` compared with a path `γ` has boundary `[e] − [γ]` and work defect `w(e) − w(γ)`;
admitting the identity does not assert the defect is zero; `(dw)∂₃ = w(∂₂∂₃) = 0`.

### XVII.6 Three cost questions

Historical `W(H)`; incremental from an available history `H₀`: `W(P | H₀) = W(support P \ support H₀)`
(cached prefix is sunk); counterfactual: needs that recipe's cost certificate or a separate run.

### XVII.7 Cubical chains

Cube maps assign interval expressions to coordinates; endpoint restrictions compose canonically:
for `i < j`, `d_i^ε d_j^η = d_{j−1}^η d_i^ε`. Hence on presented `n`-cells

```
∂x = Σ_i (−1)^{i−1} (d_i^1 x − d_i^0 x),        ∂² = 0
```

```
 square x:          d_2^1 x
             ●━━━━━━━━━━━━━━━━●
       d_1^0 x                d_1^1 x        ∂x = (d_1^1x − d_1^0x) − (d_2^1x − d_2^0x)
             ●━━━━━━━━━━━━━━━━●              each corner appears twice with opposite signs,
                    d_2^0 x                   so ∂∂x = 0
```

Cochains: `da = a∘∂`, `⟨a, ∂c⟩ = ⟨da, c⟩`, `d² = 0`; products `∂(x×y) = ∂x×y + (−1)^{deg x} x×∂y`.
A state valuation is degree 0 (conservation: `dv(e) = 0`); a work reading is degree 1 (equal work
along a supplied comparison `h`: `dω(h) = 0`). For a comparison witness `α` with
`∂α = [Q;κ_Q] − [P;κ_P]` (connectors included), the exact defect is

```
Δ_α W = ⟨ω, ∂α⟩ = ⟨dω, α⟩          (Stokes)
```

and with a continuation `C`:
`Cost(P;C,S) − Cost(Q;C,S) = Cost(P,S) − Cost(Q,S) + Cost(C_P,T_P) − Cost(C_Q,T_Q)`.
A pair of competing enabled rules is not automatically a cell; absence of a filler is absence of
that witness.

### XVII.8 Live adoption

```
Cut C: owner/slot, source s₀, guard ψ, resume recipe K, WAITING | RESUMING | CLOSED,
       generation g, residual u, q : s₀ ⇒* u, dependencies, ticket ownership, version
Ticket T: C, captured g, requested residual/key, receipt from s₀, one delivery obligation
PreparedAdoption A: C, captured (g,u,ψ), pinned fact P, map σ, ψ ⊢ φ[σ],
       connector χ : u ⇒* s[σ] if needed, q' = q;χ;ρ[σ], residual v = r[σ],
       union dependency certificate, snapshot, preallocated replacement ticket/event/launch
```

Installation under the cut lock requires WAITING, matching `g` and a valid snapshot; it consumes
the cut version and installs `g', v, q'`. Delivery consumes its ticket once; if the cut is no longer
WAITING or the generation differs it releases ownership without resuming; otherwise it claims
WAITING→RESUMING and transfers `K` to one resume. The naturality proof supplies the instantiated
evidence; generation, guard, snapshot and ownership make it applicable at a live boundary.

### XVII.9 Overlaps, effects, frames, cost, calibration

Overlap classes: disjoint transitions commute semantically (equal fine work needs equal native
weights); face restriction in two orders is the composed coordinate map; publication versus
subscription partitions delivery into catch-up or notification exactly once; publication versus
specialization may change which reuse edge is selected (keep it); adoption versus delivery is
decided by exclusive version consumption; revision updates keep historical premises; delivery
versus release keeps ownership; two consumes of one port: one acceptance.

Port incidence: `B₀(S)` = exposed resource occurrences at cut `S`;
`∂_res B₁(e) = B₀(target e) − B₀(source e)`; summing gives the cut theorem and conservation
`⟨v, ∂_res B₁(e)⟩ = 0` for all composites. Effects use prepared proposals, unique ports, ordered
reservations, one terminal commit, lazy finalization; copying a descriptor creates no acceptance
right; a refund competes for the same consumption boundary as receipt.

Continuations: a frame has family/pc, operands, owned temporaries, awaited ticket, return
destination, dependency certificate, cleanup cursor; STEP consumes a version, WAIT registers its
progress owner, RESUME consumes a matching ticket once, DROP releases one owned field per step and
never runs the unfinished program to completion.

Native cost: every primitive kind has a fixed word-operation bound and
`Instr_C(h) ≤ c · N(h) + d`. Calibration: `V(z) = 0` at targets, `V(s) ≤ ω(e) + V(t)`;
`slack(e) = ω(e) + dV(e) ≥ 0`, so `W(γ) − V(s) = Σ_{e∈γ} slack(e) ≥ 0`, equality along the selected
path proving attainment.


---------------------------------------------------------------------------------------------

## Part XVIII. The step bound and what it makes incorrect in the tree

### XVIII.1 The step bound is the definition of a step

A rule replaces an active pair by a fixed finite net on its auxiliary wires (5.5); the rule table
is finite; cells have bounded arity. One step reads the two cell kinds, indexes the rule table,
allocates a bounded number of cells and writes a bounded number of links, and the new active
pairs lie on the wires it created. Hence

```
Instr_C(run) ≤ c · steps(run) + d
```

with `c` the largest per-rule cost. This is the correctness condition of the implementation: a
primitive operation whose work depends on the size of a term, map, face, field list or waiter
list is not one step and must be expressed as several steps of the same machine, each counted.

The representation of Parts IV–X is compatible with this: a view is an explicit substitution
held as data (reindex never touches the body); interning a node whose fields are already interned
handles is bounded work per node; a memo entry is the shared producer of one key, with consumers
attached to it, so it realizes sharing (5.24) for equal keys. What violates the bound is the
granularity at which 24b2bfb performs these operations.

### XVIII.2 Operations in 24b2bfb that are not bounded steps

| Operation | Where | Unbounded part | Bounded form |
|---|---|---|---|
| Opening a reference | `open_ref` (`term.c:570`), §89 measurement | builds all `n` fields before one is used | open one field per step, on demand |
| Interning a map | `mapb_finish` (sort, dedup, intern a vector) | key is the whole image vector | maps as interned bounded nodes (one image per node) |
| `reindex`, `compose`, `make_view`, support | `term.c` | traverse a whole boundary or map in one call | one image per step over the node representation |
| Interval and face operations | `dnf.c`, `face.c`, `interval.c` | meet is a clause product, normalization compares all clause pairs, all in one call | clause and atom cells, one comparison or union per step |
| Publication | `eval.c:340–343` | delivers to every waiter in one event | one delivery per step |
| Head materialization | `net.c:319` | `n`-port head, arity narrowed to `uint8_t` | bounded-arity field sequence |
| Checking, conversion, compilation, template interpretation | `check.c`, `compiler.c`, `template.c` | recursive C inside one evaluator frame | their rules as steps of the same machine |

Each row is a granularity defect of an operation whose mathematics (Parts IV–IX) is kept. The
step counter then counts the actual steps, and the coarse event vector is a projection of it.
