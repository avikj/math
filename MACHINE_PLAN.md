# Machine plan: what is built, exactly, and where I would violate the spec

Sources: `docs/index.html` (§§0–9), `NET_SPEC.md`, `MACHINE_SPEC.md` with its
correction, and the owner's emission / binding / inspection specification.
Each **CATCH** marks a place where I have violated the spec before, or would
here, and states what is done instead.

## 0. The two layers

1. **The host** (`hcm/host.c`). It holds an agent store and wires,
   selects active pairs on demand from the root, interprets rule
   descriptors, and reads results back. It knows the descriptor format and
   the generic rule families of §4, nothing else.
2. **Definitions** (`hcm/core.ctt` and the user's files). Data
   declarations, defining clauses, postulates and identities.

Each definition is reduced, with its inputs open, into agents and rule
descriptors. Compilation and run time are one process: a part that waits for
an input waits as an agent.

> **CATCH 1.** No rule for a mathematical object appears in the host: not
> comp, Pi, Sigma, PathP, Glue, U, the interval, faces, Nat or Bool. The host
> never switches on what a tag means. It switches only on a tag's structural
> class (constructor, closure, neutral, demand) and on the descriptor table.

> **CATCH 2.** The host has no type checker, no conversion test and no
> equality test on terms. Its only comparison is the order of two name
> labels (§2.3), which is the binder identity the spec admits as literal
> metadata (MACHINE_SPEC §26).

## 1. The descriptor format

A rule for the active pair `A ⋈ B` is:

    left_tag, right_tag
    fresh: [(local_id, tag, label_template)]
        label_template ∈ { none, copy_left, copy_right, fresh }
    connections: [(endpoint, endpoint)]
        endpoint ∈ { left_aux(i), right_aux(j), new_principal(k), new_aux(k, i) }

- Every endpoint occurs exactly once. The host checks this when it builds
  each descriptor, and refuses one that fails.
- The principal wire between A and B is consumed.
- Applying a rule: save the old auxiliary ends, allocate the fresh nodes,
  install the connections, free A and B.

> **CATCH 3.** No callback runs when a descriptor is applied. The only
> computation at that moment is copying or allocating labels. The one other
> literal operation, comparing two labels, selects which descriptor applies
> (§2.3). It is never code run inside a replacement.

## 2. Agents

### 2.1 Structural classes

| Class | Principal port | Auxiliary ports | Label |
|---|---|---|---|
| Constructor `K` | its value | its fields | — |
| Closure `Lt` | the function | its captures, in a fixed order | — |
| Neutral `ATOM` | the atom | none | a name |
| Neutral `NE_F` | the stuck value | the inputs of the stuck demand F | — |
| Name `NAME` | the name | none | a label |
| Thunk `DEF d` | itself | none | — |

- A closure is a binder in source, so `λ` and `<i>` both become closures.
  Each closure tag also records whether it binds a term or a dimension.
  Read-back needs that flag to choose what to plug in.
- `NE_F` is the record of demand F meeting a neutral or an unmatched value.
  Its first field is the value that stopped F; the rest are F's other
  inputs. It is a value.
- `DEF d` is a definition not yet forced.

Demands:

| Demand | Principal port | Auxiliary ports | Label |
|---|---|---|---|
| `APP` | the function | result, argument | — |
| Inspection state `S` (§3) | the inspected slot | result, then the other slots | — |
| `CMP1` | first name | result, second name | — |
| `CMP2` | second name | result | the first label |
| `REIDX` | the term | result, name, interval | — |
| `DUP` | its input | two outputs | — |
| `ERA` | its input | none | — |
| `EVAL` | its input | result | — |

Every demand but `DUP` and `ERA` has its result at auxiliary 0, so a
record `NE_F` has F's arity: auxiliary 0 holds the value that stopped F and
auxiliary i ≥ 1 holds F's auxiliary i. `EVAL` is read-back's demand: it
forces a `DEF` and hands any other value through.

### 2.2 How ports are classed

A port is *out* where the agent produces a value: a demand's result, or a
`DUP` output. Every other port is *in*. Demand-driven reduction follows out
ports back to their principal ports. That is the only use the host makes of
the classing.

### 2.3 Basis contract: the host's only literal operations

1. **Fresh labels.** A descriptor slot marked `fresh` gets a label never
   used before. This is how a binder is fresh: it is a new identity, so no
   counter is exposed to terms.
2. **Label order.** `CMP2(a) ⋈ NAME(b)` gives one of the constructors
   `lt`, `eq`, `gt` (declared in `core.ctt` as `data Ord`). The host finds
   them by name when it loads.

> **CATCH 4.** This is the whole literal interface. The free De Morgan
> algebra, faces, `∀`, entailment and substitution are list programs in
> `core.ctt` (MACHINE_SPEC §4: "finite constructions over lists"), built on
> label order. The earlier versions computed interval forms in C; that is
> gone.

## 3. Emission: from a definition to descriptors

### 3.1 Terms after elaboration

- `Var x`
- `Lam(x, body, flag)`, where the flag marks term or dimension
- `App(f, a)`
- `Con(K, args)`, fully applied (partial application is η-expanded)
- `Call(f, args)` for a definition with patterns, fully applied
  (η-expanded otherwise)
- `Ref d` for a definition without patterns
- `Atom p` for a postulate
- `FreshName`
- `Reidx(n, r, t)`

`let x = t in u` is `App(Lam(x, u), t)`.

### 3.2 Emitting ⟦t⟧ at a result endpoint, inside one replacement

1. Collect variable occurrences in traversal order. The environment maps
   each variable to the endpoint carrying it: an old auxiliary end, or a
   port of a node created in this replacement.
2. Split each variable by its use count k:
   - k = 0: connect it to a fresh `ERA`;
   - k = 1: connect it directly;
   - k ≥ 2: build a right-leaning `DUP` tree of k − 1 fans, its leaves taken
     in traversal order.
3. Emit by term:
   - `Con`: a constructor node, each field emitted into its auxiliary port;
   - `Lam`: a closure node whose capture ports take the free variables, in
     the closure tag's order;
   - `App`: an `APP` node, the function emitted into its principal port,
     result and argument on its auxiliary ports;
   - `Call`: the initial-state node of f, arguments emitted into its slots
     (principal at the inspected slot), result last;
   - `Ref d`: a `DEF d` node;
   - `Atom`: an `ATOM` node, carrying the postulate's name label;
   - `FreshName`: a `NAME` node with label template `fresh`;
   - `Reidx`: a `REIDX` node.

> **CATCH 5.** A rule's right-hand side is emitted into that rule's
> descriptor. It is never reached through a reference applied to arguments.
> `hcm` did that; it added an unfolding and n β steps to every firing.

> **CATCH 6.** Variable splitting is counted per replacement, in the
> replacement itself, not once per definition.

### 3.3 Closures

Every `Lam` occurrence gets its own tag `Lt` with captures `c1 … ck`, the
free variables of its body. The closure rule is

    Lt(c1 … ck) ⋈ APP(r, a) → ⟦body⟧_r,  with x ↦ a and cj ↦ the j-th old capture end.

Renaming, shadowing and capture are settled when the tag is made. A shared
path used at 0 and at 1 gives two separate `APP`s. Nothing global is
rewritten.

> **CATCH 7.** No SUP and no labelled fans. A `DUP` meeting a closure copies
> its capture fields. A body runs once per application: active pairs are
> never copied, but work inside a body is redone for each copy that is
> applied. That satisfies 5.24 as written; it does not claim optimal
> reduction.

### 3.4 Definitions with patterns: inspection states

A definition has clauses `f p1 … pn = t` and a fixed arity n. Clauses have
priority in source order, because the spec says a definition's stated
priority is part of it.

A state holds:

- a frontier of slots, each a path into the arguments;
- the candidate clauses, in order;
- the constructors seen so far, at their paths.

Building the states:

1. The initial state's frontier is the n argument positions, and every
   clause is a candidate.
2. A state is **final** when the first candidate has a variable, or nothing,
   at every slot in the frontier. It then fires that clause:
   `⟦t⟧_r`, each pattern variable taken from its slot, or rebuilt as the
   constructor seen at its path when another clause took it apart.
3. Otherwise the inspected slot is the first slot where the first candidate
   has a constructor pattern. The state's principal port is that slot.
4. For each constructor c appearing at that path in some candidate, there is
   a transition. Its frontier has c's fields spliced in place of the slot.
   Its candidates are those with a variable, or c, at that path.

At run time:

- a constructor with a transition moves to the next state, or fires;
- any other value (an unmatched constructor, a closure, an atom, a name, an
  `NE`) gives `NE_S`, keeping the slots.

> **CATCH 8.** Clauses are inspected in a fixed left-to-right, first-match
> order, which is the definition's own stated priority. Nothing is chosen at
> run time. A neutral value at the inspected slot suspends the definition,
> even when a later clause has a variable there. The definition gave
> priority to the earlier clause, so the machine doesn't skip it.

## 4. Generic rule families

These are generated from structural class alone, the first time a pair is
seen. Each is a descriptor.

1. **Copy** (owner spec §5): `DUP ⋈ V`, for V a constructor, closure,
   `NE_F`, `NAME` or `ATOM`. Two copies of V, one fan per field, labels
   copied.
2. **Erase**: `ERA ⋈ V`. One `ERA` per field.
3. **Force** (owner spec §3): `D ⋈ DEF d`, for any demand D. The body ⟦d⟧ is
   emitted with its result on D's principal port. For a `DUP`, `DUP ⋈ DEF d`
   gives two `DEF d`; for an `ERA`, nothing.
4. **Neutral elimination** (MACHINE_SPEC §31; a neutral suspends its
   eliminator): demand F meets an `ATOM`, an `NE_G`, a `NAME` it doesn't
   inspect, or a value no rule matches. The result is the value `NE_F`,
   holding that value and F's other inputs.
5. **Branchwise elimination** (MACHINE_SPEC §6): demand F meets `sys`/`nosys`
   (core constructors) where F has no transition for them.
   - `F ⋈ sys(φ, e, rest)` gives `sys(φ, F(e, …), F(rest, …))`, with F's
     other inputs fanned.
   - `F ⋈ nosys` gives `nosys`, F's other inputs erased.
6. **Reindexing** (MACHINE_SPEC §3 and correction §11): `REIDX(n, r) ⋈ V`.
   - V an interval-form constructor (`inil`/`icons`): becomes the call
     `isubst n r V`. A face-form constructor (`fnil`/`fcons`): `fsubst n r V`.
     Both are `core.ctt` list programs.
   - Another constructor, or a closure: the same node, with `REIDX` on each
     field (n and r fanned).
   - `NE_F`, F an `APP` or `CMP`: rebuilds F with `REIDX` on every input,
     so the elimination is attempted again.
   - `NE_S`, S a state of definition f: rebuilds f's arguments from the
     record's slots and the constructors S had seen, puts `REIDX` on each,
     and feeds them to f's *initial* state. Every test f makes runs again,
     the face test of `compH` first (the owner's reactivation rule). A face
     that the substitution makes true can now fire.
   - `ATOM`, `NAME`: unchanged.

> **CATCH 9.** These families are generic over tags. Branchwise elimination
> and reindexing are fixed by the spec's §6 and §3 for every eliminator and
> every construction. The host knows `inil`/`icons`/`fnil`/`fcons` and
> `sys`/`nosys` only to say which core programs carry the interval and face
> algebra, and which constructors are systems. That is the representation
> contract.

## 5. `core.ctt`: the basis written as definitions

### 5.1 Data

    Ord: lt eq gt
    Lit: pos n | neg n                 interval literal over a NAME
    FLit: at0 n | at1 n                face literal
    Clause: cnil | ccons l c           interval clause, sorted
    IForm: inil | icons c f            interval form, an antichain
    FForm: fnil | fcons c f            face form, an antichain of Clauses of FLit
    Bool: true false                   only to return tests
    Sys: sys φ e rest | nosys          a partial element
    Pi D C | Sigma D C | PathP A a b | GlueT α A S | U
    pair a b

### 5.2 Interval and face programs (De Morgan, §4–5)

- **Order:** `litcmp` orders literals by name label, then sign.
- **Clauses:** `cins` (sorted insert, removing duplicates), `cunion` (merge),
  `csub` (sorted subset, giving a Bool).
- **Forms:**
  - `fmadd c f` adds a clause to an antichain: it drops c if some clause of
    f is a subset of c, otherwise drops every clause of f that c is a subset
    of, then adds c.
  - `ijoin` folds `fmadd`. `imeet` takes pairwise unions, then `fmadd`.
  - `ineg` is De Morgan, clause by clause.
- **Faces:** the same, plus `fcontra`, which drops a clause holding both
  `at0 n` and `at1 n`. Then:
  - `feq1 r` maps `pos n` to `at1 n` and `neg n` to `at0 n`, and normalizes;
  - `feq0 r = feq1 (ineg r)`;
  - `fall n φ` keeps the clauses that don't mention n;
  - `isubst` and `fsubst` substitute r for n, literal by literal, and
    normalize.

The top form is `icons cnil inil` (or `fcons cnil fnil`), and the bottom
form is `inil` (or `fnil`). These are ordinary constructor patterns.
`i ∧ ¬i` is never reduced to 0. `(i=0) ∧ (i=1)` is ⊥.

### 5.3 Partial elements

`sel s` takes the first branch whose face is top:

- `sel (sys (fcons fcnil fnil) e rest) = sel e`, so a nested system is
  selected again;
- `sel (sys φ e rest) = sel rest` otherwise;
- `sel nosys` has no clause, so it suspends.

Selecting from a total value: `sel` has a default clause `sel v = v`,
placed after the `sys` clauses.

### 5.4 Composition, the single primitive (revised against the owner's cubical layer)

    comp L φ u a0 = let n = freshname in compH (L @ (ivar n)) n L φ u a0
    compH h n L (fcons cnil fnil) u a0 = sel (u @ 1)              face test first (clause 1)
    compH (Pi D C) n L φ u f0       = clause 5, with D, C reabstracted: <i> reidx n i D
    compH (Sigma D C) n L φ u z0    = clause 6, the same reabstraction
    compH (PathP B l r) n L φ u p0  = clause 7
    compH (GlueT α A S) n L ψ u u0  = compGlue (<i> reidx n i A) (<i> reidx n i α) (<i> reidx n i S) ψ u u0
    compH U n L φ u A0              = Glue A0 [ φ → (sel (u @ 1) , lineEquiv (<j> sel (u @ (~ j)))) ]
    compH (sys α A rest) n L φ u a0 = sys (fall n α) (comp (<i> reidx n i A) φ u a0) (compH rest n L φ u a0)
    compH nosys n L φ u a0          = nosys

How this is evaluated:

- Clause 1 inspects φ before the head, so the face test is the first thing
  done.
- When a head is neutral, `NE_compH` keeps every operand. Reindexing
  re-invokes `compH`, so both the face test and the head inspection run
  again. This is the owner's reactivation rule for `NComp`.
- The head `L @ ν` is demanded only if the face test fails.
- The face context χ is realized as substitution. A restricted occurrence
  carries `REIDX` of the face's endpoint literals, so "χ ⇒ φ" is "φ[σ] is
  the top form". At top level χ is ⊤.
- `coeRS L r s a = comp (<j> L @ ((r ∧ ~j) ∨ (s ∧ j))) bot (<_> nosys) a`.
  `coe` is the 0 → 1 case.

> **CATCH 13.** The system head `sys α A rest` is a case of `compH` (owner
> clause 2 and 11), with `θ_k = ∀i α_k`. Without it, a family presented as a
> total system would suspend.

### 5.4a The earlier draft of this section, superseded

    comp L φ u a0  = compF φ L u a0
    compF (fcons fcnil fnil) L u a0 = sel (u @ 1)            full face
    compF φ L u a0 = let n = freshname in compH (L @ (ivar n)) n L φ u a0
    compH (Pi D C)     n L φ u f0 = …  §10, with fill backwards
    compH (Sigma D C)  n L φ u c  = …  §11
    compH (PathP A a b) n L φ u p0 = … §12
    compH (GlueT α A S) n L ψ u u0 = compGlue (<i> reidx n i A) (<i> reidx n i α) (<i> reidx n i S) ψ u u0
    compH U            n L φ u A0 = Glue A0 [ φ → (sel (u @ 1) , PathEquiv (<j> sel (u @ (~ j)))) ]

A head with no clause is an unmatched value, so composition suspends there
(family 4).

- `fill`, `hcomp`, `coe`, `Contr`, `fib`, `Equiv`, `IdEquiv`, `PathEquiv`,
  `ExtendContr`, `EquivExtend`, `Ua`, `reverse`, `compose`, `transport`,
  `contractSingleton`, `cut`, `uncut`, `difference` and the handles are
  exactly as MACHINE_SPEC §§9–25 state them.
- `compGlue` follows the six stages of §§17–20.
- `Glue` is a definition, `Glue (fcons fcnil fnil) A S = (sel S) .1`, else
  `GlueT α A S`.
- `glue` and `unglue` are definitions with face clauses, and `unglue` keeps
  the glue data (§16).

> **CATCH 10.** Kan structure for a user type is a clause the user adds to
> `compH` (clauses for one definition may come from several files). Nothing
> is built in, and there is no `rule p` special form.

### 5.5 Reflection

A postulate whose declared type is literally Π, Σ or PathP is emitted as
`reflect T (ATOM p)`, where `reflect` is a core definition:

    reflect (Pi D C) n = \ x → reflect (C x) (n x)
    reflect (PathP A a b) n = <i> reflect (A @ i) (npapp n i a b)
    reflect (Sigma D C) n = (reflect D (fst n) , reflect (C (fst n)) (snd n))
    reflect T n = n

`npapp n inil a b = a`, `npapp n (icons cnil inil) a b = b`. Any other
interval leaves `npapp` suspended.

`reflect` at a neutral type is itself suspended (CATCH 8: a neutral at the
inspected slot suspends, whatever later clauses say). That is exact: the
type may become Π under a substitution, and then the record re-invokes
`reflect`.

## 6. Read-back

1. Demand the root.
2. A constructor prints its name and fields. An `NE_F` prints as F applied to
   its fields; a stuck state prints as f applied to its arguments rebuilt
   from the slots and the constructors seen.
3. A closure is applied to a fresh atom and its result is read: a term
   closure gets an `ATOM`, a dimension closure gets the interval
   `icons (ccons (pos NAME) cnil) inil`. The closure value at that point is
   unshared: copies are separate values (CATCH 7), so applying it changes
   nothing else.
4. A system branch with face φ is read under each clause of φ, each literal
   applied as `REIDX` (MACHINE_SPEC §6: surviving terms are restricted to
   their faces).

> **CATCH 11.** Printing is structural. Forms print as their constructors.
> The host has no pretty-printer that knows what they mean.

## 7. The identity agent

`agent p` with `p : (γ : Γ) → Path B L R` generates, as source definitions,
`p-realL`, `p-realR`, `p-forward` and `p-backward`:

- `Real`, `c` and `c⁻¹` are built recursively over the construction trees L
  and R (§24, owner spec §6), using the core's `ap`, `compose` and
  `reverse`.
- The type of each internal node comes from the signatures of the heads.

This is a transformation of syntax into definitions, which are then emitted
like any other. Concretely, for a node `h(t1 … tn)` with `h : A1 → … → An → C`:

    Real(h(t…), y) = Σ x1:A1. Σ r1:Real(t1,x1). … Σ xn:An. Σ rn:Real(tn,xn). Path C (h x…) y
    Real(leaf t, y) = Path T t y
    c(u)   = compose C (<i> h (c(r1) i) … (c(rn) i)) q
    c⁻¹(q) = (t1, (c⁻¹(refl t1), … (tn, (c⁻¹(refl tn), q))))

A head whose signature is dependent would need these paths over lines of
types; the pass refuses such a head as a node and treats the subterm as a
leaf, which is exact (a leaf's Real is the singleton `Path T t y`).

## 8. Cost and strategy

- One interaction is one step. A DEF forcing is a step, and so is every
  generated interaction.
- Reduction is demanded from the root: an in-port whose partner is an
  out-port waits on the node that owns it, down to an active pair, which
  fires. A value that nothing demands (an erased branch, the head of a
  composition whose face test succeeds) is never reduced.

## 9. Examples (`book.ctt`)

The examples use abstract postulated types, paths, Σ and Π transports, `Ua`,
composition in U, singleton contraction, the fibre round trip, handles, the
square, and an identity agent. Bool appears only as a data type with `if`
defined by clauses.

> **CATCH 12.** No number as a tally. No `natrec` arithmetic. A number is
> posed only as §6 poses it, and the book contains none until that is done
> properly.

## 10. Process

- Write all of it. Verify by inspection against this plan and the spec.
- Compile and run nothing until the owner permits.
- Commit on the designated branch.
- Any violation found while writing is fixed where it is found.
