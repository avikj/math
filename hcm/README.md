# hcm: the hypercubical interaction machine

This implements `MACHINE_SPEC.md`.

| File | Contents |
|---|---|
| `hcm.c` | The net, every interaction, the one primitive COMP with its dispatch, the identity-agent compiler, and read-back |
| `core.ctt` | The defined programs: fill, hcomp, coe, composition at Π/Σ/PathP/Glue/U, Equiv, IdEquiv, PathEquiv, EquivExtend, Ua, reverse, compose, transport, contraction, cut, difference, handles |
| `book.ctt` | The constructions of the spec, posed for the machine |

    make && ./hcm book.ctt <name>

## Syntax

| Category | Forms |
|---|---|
| Interval | `0 1 ~ && \|\|` (also `∧ ∨`) |
| Faces | `(r = 0) (r = 1) top bot /\ \/` |
| Paths | `<i> t`, `p @ r`, `Path A a b`, `PathP L a b` |
| Systems | `[ φ → t ; ψ → u ]` |
| Composition | `comp L (<i> [ … ]) a0`, whose φ is the join of the faces; `compF L φ u a0` |
| Glue | `Glue A [ φ → (T , e) ]`, `glue [ φ → t ] a`, `unglue G v` |
| Constructions with rules | `rule p` for `p : (γ : Γ) → Path B (f t1 … tn) R`, where the `ti` are patterns (variables of γ, each used once, or postulated constructions applied to patterns): `f` becomes the head of a matching automaton, every construction in the patterns becomes a constructor agent, and the match fires `R`. `rule p` for `p : (φ u c) → Path T (compF (<_> T) φ u c) R` gives a postulated type `T` its composition. No datatype is built in. |
| Identity agents | `agent p` for `p : (γ : Γ) → Path B L R` generates `p-realL`, `p-realR`, `p-forward` and `p-backward` |

A name declared with a type and no definition is a postulate. If its type
is a Π or path type, it is reflected at that type, so a postulated path
exposes its declared ends.

## Reindexing and Glue

A composition at a Glue family receives the family's components as lines.
Each component is the head at a fresh name ν, reindexed by `ν := i`.
Reindexing travels with the term: it waits for values, and passes through
any consumer that hasn't produced one yet, so a face it makes true can then
fire. The Glue family may therefore be its own T wherever its face holds.
`Glue` is formed strictly on its face: when the face holds, the type is its
T (§16).
