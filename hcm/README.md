# hcm: the hypercubical interaction machine

The specification is `../MACHINE_SPEC.md` (the owner's text, verbatim) and `../NET_SPEC.md`.

- **`host.c`**: the fixed step.
  - It holds the agent store and the wires, demands active pairs from the root, applies descriptors, and reads the result back.
  - Binders are body subnets (`LAM`: variable wire, body wire). Copying a binder uses labelled `SUP`/`DUP` fans, so a body's redexes reduce once for all copies.
  - Every rule is a descriptor generated from definitions the first time its pair meets. That covers inspection states, and the copy, erase, force, neutral, branchwise and reindexing families.
  - The literal operations are fresh labels and label order.
  - The identity-agent pass (`agent p`) is here as a transformation of syntax into definitions.
- **`core.ctt`**: the basis, written as definitions:
  - interval and face forms as list programs over names;
  - systems and `sel`;
  - `comp` with the face test first, then the head table: Pi, Sigma, PathP, GlueT, U, a system head, and `nosys`;
  - `fill`, `hcomp`, `coe`, `coeRS`;
  - `Equiv`, `idEquiv`, `lineEquiv`, `extendEquiv`;
  - Glue and the six-stage `compGlue`;
  - `ua`, path operations, handles, and reflection of postulates.
- **`book.ctt`**: examples. No number appears as a tally.

Usage: `make && ./hcm core.ctt book.ctt`.

Source syntax:

- `data T = c x y | d`
- `postulate x : T` and `name : T` (signature)
- `f p1 … pn = t` (a clause; clauses of one definition may come from several files and keep source order)
- `agent p`
- `eval t`

Terms:

- binders: `\x -> t` and `<i> t`
- application: `t u` and `t @ r`
- `let x = t in u`
- pairs and arrows: `(a , b)`, `A -> B` and `(x : A) -> B`
- interval: `0`, `1`, `~ r`, `r /\ s`, `r \/ s`
- faces: `(r = 0)` and `(r = 1)`
- primitives: `freshname`, `reidx n r t` and `cmpname a b`

Status: written and checked by inspection only. It has not been compiled or run; that waits for the owner's permission.
