# Hyperactive

Source: `docs/index.html`, read as one derivation. Section numbers refer to it.

## 1. The element

There is one element: **an identification**, meaning "these two are the same point" (§0). It has two faces in the implementation, and they are one thing:

- **A wire.** Two ports joined by a wire are one value. A wire *is* `refl` / `x = y`: it holds the same thing at both ends and adds nothing.
- **A labelled node.** A node has a principal port, two auxiliary ports, and a label. The label is a *name*. A node is an identification that has not yet been folded: one point, seen along the name, with its two faces on the auxiliary ports.

There is one interaction, which applies when two nodes meet principal to principal:

| labels | what happens | in §0–§2 terms |
|---|---|---|
| equal | **fold.** Wire aux₁ to aux₁ and aux₂ to aux₂; both nodes disappear. | Two identifications along the same name are one. The singleton contracts, `Σ y. x = y` becomes `(x, refl)`, and J / transport happens. |
| different | **commute.** Each node passes through the other: two copies of each, cross-wired. | A map applied to a path: `f x = f y` is `i ↦ f (p i)`, definitional (§0, §2). |

That is the whole runtime. The rest of this document says what these pieces already are.

**Where this comes from.** This is the labelled interaction combinator: one binary node, one rule decided by label equality. Lafont proved that system universal. CONVERGENCE Part IV already reads its two cases as the corpus's two fibres: equal labels annihilate (the contractible fibre, folded), different labels commute (the independent dimensions, kept).

The nullary case of the node (no auxiliary ports) is erasure. It is the only place information is destroyed, and it is where the effect cost is charged (§3, §5).

## 2. What everything already is

Nothing below is a new cell or a new rule. Each item is a wiring pattern of the element.

- **Function and application.** Both are the node at one label: `λx.b` and `f a` meeting fold, which wires `x` to `a` and the body to the result. That is β, which is substitution, which is J (§0).
- **Using a value twice.** A value used twice is a node at a fresh label. It meets the value and commutes through it. This is also "sharing every isomorphic subterm" (§5): the shared thing is one cell, and a copy exists only where a face is actually taken.
- **Names, paths, faces.** A label is a name. A path along name `i` is a node at label `i` whose auxiliary ports are its two faces. Taking a face is meeting a node at the same label: fold. Faces along different names commute (`δᵢδⱼ = δⱼδᵢ`).
- **`f a` keeping its fibre (§1).** The input port stays wired. Nothing that was not asked for is erased, so `(f a, (a, refl))` is the net as it stands.
- **Univalence (§2).** An isomorphism is a path. Transporting along it is the fold rule applied along that path's name.
- **Numbers.** A number is a finite set up to identification: n points, all their relabellings folded. `+` is placing two nets side by side (disjoint union), `×` is pairing (product), and divisibility and logic are the same lattice.
- **Lists and multisets.** A list is n values on n ports. A multiset is the same with the relabellings folded (the construction of ℕ, with labels).
- **Order and comparison.** A comparison is an identification: `a ≤ b` is a map, i.e. a wiring. An implied comparison is already folded, because transitivity is composition of wirings. It costs no interaction.
- **Types.** Types are nets of the same element. There is no separate type layer; the type checker is a net (§5, no outer layer).

## 3. Implementation

**Memory.** One array of nodes. A node is four words:

| word | contents |
|---|---|
| 0 | label, or the erasure tag |
| 1 | peer of the principal port |
| 2 | peer of aux₁ |
| 3 | peer of aux₂ |

A port address is `node·4 + slot`. The peer word is the wire, and there is no other wire structure.

**Link.** `link(p, q)` writes each port into the other's peer word. If both are principal ports, it pushes the pair onto the redex list.

**Interact(a, b).**
- Both erasers: free both.
- One eraser: link an eraser to each auxiliary port of the other node, free both, and count one erasure (the effect axis).
- Equal labels: `link(a.aux1, b.aux1)`, `link(a.aux2, b.aux2)`, free both.
- Different labels: allocate copies a′, a″ of `a` and b′, b″ of `b`. Link them in the 2×2 square: principal ports to the old auxiliary peers, auxiliary ports crossed. Free `a` and `b`.

Each call is one step, and the step count is incremented once per call.

**Run.** Pop any redex and interact, until the list is empty.
- **Order.** There is no scheduler. By the diamond (§5), every order gives the same result and the same count.
- **Parallelism.** Redexes are disjoint, so they can run concurrently with no locks beyond the pop.

**Reading in.** A term becomes a net by a direct translation, with no evaluation:
- λ, application and pairs become nodes at the base label;
- each variable used k times becomes k−1 sharing nodes at fresh labels;
- each name `i` becomes the label `i`;
- a free input is a port left open for the world.

**Reading out.** The normal form is read by walking the net from the root port. This is a fold that copies the net and fires no interactions (§5, "adding no step").

**Interaction with the world.** An open port is a question. The world answers by linking a value to it, which is one more `link`. A run is its answer stream.

**Cost report.**
- **Length:** the number of interact calls. By §5 it is fixed by the answer.
- **Effect:** the number of erasures, the bits destroyed. It is zero when every fibre is kept.

**Size.** The rule, link, the run loop, reading in and reading out come to a few hundred lines of C. Nothing else exists.

## 4. `sort`, in this runtime

```
sort : (x : Fin n → V) → Σ (y : Fin n → V). (ms y = ms x) × ((i j : Fin n) → y i > y j → i > j)
```

- **The equalities are wires.** `ms y = ms x` is `ms y` wired to `ms x`. The order condition is a wiring of comparisons.
- **y is determined.** The fibre of `ms` over `ms x` is the relabellings of `x`. The order wiring cuts it to one point, so the net's open port `y` has one normal form: `x` transported along the order-isomorphism (§2).
- **Cost.** There are n! relabellings, one bit per comparison, so ⌈log₂ n!⌉ comparisons are needed. A comparison already implied by earlier ones is already folded, so it takes no interaction, and the run meets the bound.

## 5. The language

A file is definitions: `name = term;`. The text is read directly into the element's wiring:

| term | reads as |
|---|---|
| `\x t` | a node at label 0: the value is the principal port, face 1 is `x`, face 2 is `t` |
| `(f a b …)` | one node at label 0 per argument: the principal meets `f`, face 1 takes the argument, face 2 is the result |
| `{a b}#i` | a node at label `i`: the value is the principal port, the faces are `a` and `b` |
| `let {x y}#i = t; u` | a node at label `i`: its principal meets `t`, and its faces are `x` and `y` |
| `let x = t; u` | `x` names `t` |
| `*` | erasure |
| `name` | a bound variable, otherwise a definition placed where it is used, otherwise a free port (a question to the world) |

A variable used k times is shared by k−1 nodes at fresh labels. A variable used zero times is erased.

The runtime is `hyper/hyper.c`, about 300 lines. Nothing else exists.
- Usage: `hyper FILE [NAME]`. It prints the normal form of `NAME` (default `main`), then the number of steps and the number of erasures.
- Reading the result back walks the net. A path that enters a node through a face, and later meets a node of the same label at its principal port, leaves through that same face, because the two are one identification. A principal port with no entered face of its label is a superposition.

## 6. Worked through, by hand and then run

| example | term | worked by hand | run | steps |
|---|---|---|---|---|
| β | `((\x x) (\x x))` | the λ and the application both have label 0, so they fold. Face 1 wires the argument to `x`; `x` is wired to the body; the body is wired to the result. So the result is the argument. | `\x x` | 1 |
| fold along a name | `let {a b}#i = {true false}#i; {b a}#k` | same label, so the faces are identified: `a = true`, `b = false` | `{false true}#k` | 1 |
| commute | `let {a b}#i = {true false}#j; {a b}#k` | different labels, so the `i`-node passes through the `j`-node. Each face is `{true false}#j` | `{{true false}#j {true false}#j}#k` | 9 (2 erasures, the unused faces of the copies) |
| sharing | `(two two)`, where `two = \f \x (f (f x))` | Church four | `\f \x (f (f (f (f x))))` | 14 |

Popping redexes in the opposite order (a throwaway build, not part of the runtime) gives the same normal forms and the same counts. That is what the diamond predicts.

## 7. Next

`sort` as its type, in this language: finite sets, the multiset projection, and order written as the element's wiring. It gets the same treatment: work it by hand, then run it, and compare its count with ⌈log₂ n!⌉.
