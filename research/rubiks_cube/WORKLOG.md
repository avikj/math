# Rubik 3x3 fibre query work log

- Added `Cube3Optimization.bend`: the exact 3x3 action relation `(u,v,w) ↦ Path(executeWord(3,u,w),v)`, unit word cost, proof-relevant `LeastWitness3`, `MuDomainQuery3`, pairwise minimum map query, and diameter witness/result types.
- Added `Cube3FibreQuery.bend`: maps the complete `PuzzleFamilyPresentation` to the 3x3 objective and sends that map through the existing `FibreCoalgebra` in one observation.
- Removed the previous bounded candidate list, singleton-state diameter input, and hard-coded proof arrays from this new query path. The query names the complete `Word` relation; the returned `LeastWitness3`/`DiameterWitness3` are the fibre result types and retain residual obligations.
- Verified both new sources type-check with Bend. The full HVM emission also parses successfully in the existing toolchain.

The existing `Cube3ReadoutFull.bend` remains an older bounded experiment and is intentionally not used by the new query path.

# The diameter as a type, and what the native runtime does with it

## The carrier

`CubeGroup.bend` presents the group in coordinates rather than as sticker
states: `Elt` is `(cp, co, ep, eo)` — an 8-permutation with twists mod 3 and a
12-permutation with flips mod 2 — with `compose` the wreath law

    r.p[i] = g.p[h.p[i]]        r.o[i] = (h.o[i] + g.o[h.p[i]]) mod m

for `compose(g, h)` read as "g first, then h". The 18 face turns are the six
quarter turns and their squares and cubes. `inG` cuts the subgroup out of
`(Z3 wr S8) x (Z2 wr S12)` by the three invariants: corner twist sum zero mod
3, edge flip sum zero mod 2, and agreeing permutation parities.

Twelve identity checks are in the file and all return `True`: order four for
U, R, F; the half turn is the square and the inverse is the cube; opposite
faces commute on all three axes; every generator and every composite stays in
G; the superflip is in G and is an involution.

The move tables were pinned against five published facts, and the first
derivation had U and D inverted. Order-four and the three invariants are blind
to chirality, so they passed anyway; the error was caught only by requiring a
published 20-move face-turn word for the superflip to evaluate to the
superflip. The flip convention is a gauge — (F,B), (L,R) and (U,D) all work —
but the chirality is not.

## The statement

`CubeDiameter.bend` states the diameter as a type and nothing else. There is
no search in the file.

    Within(g, k)    the type of ways g lies within k face turns of the identity
    Exactly(g, k)   the same, spending every turn
    InG(g)          a sigma of three paths, not a boolean test
    DistIs(g, d)    within d, and `Within(g, d-1) -> Empty`
    Diameter(D)     some g in G at distance exactly D, and every h in G within D

`Within` recurses on the step count structurally, and that is the whole
difference from a datatype carrying a path between k and its predecessor: at a
concrete k the family REDUCES. The first version was a datatype, and a
normaliser that reduces under binders unfolds it forever, because the step
count it matches on is bound. `Reaches(identity, 0)` did not terminate either,
which is what named the defect: it was never search depth.

It is also linear in k rather than exponential, because `act(s)` is stuck for a
bound s. The eighteen branches live in the inhabitant, not in the type.

The checker now reduces `main = Diameter(twenty())` in full, to a finite,
explicit twenty-level statement: twenty nested `Σs:Gen` under the `Or`, the
accumulated `compose(...(compose(g, act(s)), ...), act(s))` at each level, and
the identity written out in coordinates at every leaf. The negative half
reduces alongside it, as a twenty-deep `∀closer: Or(...). Empty`.

`uWithinOne : Within(gU(), 1n)` is in the file and checks `[total]`:

    @inr{(@sUi, <_> identity())}

U lies one turn from the identity, by the inverse turn, and the receipt is
`refl` — because coordinates make "the same element" definitional rather than a
question. The construction is inhabitable and this is an inhabitant.

## Handing it to the evaluator

    bend CubeDiameter.bend --to-hvm4-full > CubeDiameter.hvm4
    hvm CubeDiameter.hvm4 -s

Measured, on the built toolchain:

- `@uWithinOne` normalises: `#Pair{#inr, #Pair{#Pair{#sUi, #One}, #PLm{λ_. identity}}}`.
  The inhabitant runs natively.
- `@InG(@superflip)` normalises in 22,497 interactions to
  `Sig{Path{Num,0,0}, Sig{Path{Num,0,0}, Path{Num,0,0}}}`. The runtime computed
  the superflip's three membership obligations and reduced each to a
  reflexivity: twist sum 0, flip sum 0, parities equal. Membership in G is
  decided by the evaluator.
- `@compose(@gU)(@gU)` normalises in 10,453 interactions; `@Elt`, `@Gen`,
  `@Or(#Unit)(#Unit)`, `@Within(@gU)(#Zer)` all normalise.
- `@Within(@gU)(#Suc{#Zer})` does not terminate. Bisecting it: the diverging
  term is `@compose(@gU)(q)` for a free `q`, and under that `@nth(q)(0)`.
  `@nth` at a closed list is 28 interactions and correct.

So the obstruction is not in the statement. It is in the runtime, and it is
three lines wide — `OpenTermDivergence.hvm4`:

    @loop = λxs. (λ{#Nil: 0; #Con: λh. λt. @loop(t)})(xs)
    @peel = λxs. (λ{#Nil: 0; #Con: λh. λt. h})(xs)

    @main = @loop(#Con{1,#Con{2,#Nil}})    ->  0, in 12 interactions
    @main = #Sig{#Unit, λq. @loop(q)}      ->  does not terminate
    @main = #Sig{#Unit, λq. @peel(q)}      ->  1 interaction, stays stuck, prints

HVM4 expands a recursive definition's reference eagerly, without waiting for
its match to be able to fire. It normalises closed terms and diverges on any
open term whose free variable a recursive function scrutinises. A type family
under a binder is exactly such a term: the family reaches `compose`, which
reaches `permAt`, which reaches `nth`, on the bound element. The Bend checker
reduces the same families without trouble, because its whnf is demand-driven.

The consequence for inhabitant search is sharp: the native runtime cannot be
handed a proposition with a free variable in it and asked to work under that
variable. It can run any closed instance, which is what the superposition
search below does.

## The search the runtime does have

The runtime's own choice primitive is the labelled superposition, and its own
enumeration is collapse. `emit_superposition_search.py` places one
superposition per word position — a distinct label per position, so the
choices are independent rather than correlated — composes the superposed move
into the accumulated element, and voids the branch with the nullary `&{}` when
the product is not the identity. Collapse returns the surviving words. Nothing
in it is an interpreter; the runtime chooses, filters and enumerates.

    python3 emit_superposition_search.py CubeDiameter.hvm4 1 '@gU'
    hvm search_1.hvm4 -s -C
    #Con{2,#Nil}          2 = U cubed = U inverse, the unique one-move answer

Measured interaction counts, target `@gU`, searching words of length exactly K:

    K    branches (18^K)    interactions    per branch    time
    1                  18          93,720         5,207    0.004 s
    2                 324         520,935         1,608    0.019 s
    3               5,832      17,253,988         2,959    2.621 s
    4             104,976     165,492,171         1,576   14.597 s
    5           1,889,568               -             -   killed

Depth 5 was killed by the out-of-memory killer at 13.97 GB resident after 88
seconds, with no output: the collapse builds the whole branch set in the heap
rather than streaming it.

The per-branch cost is flat at roughly 1,600-3,000 interactions, so the
measured growth is the full 18-way tree: collapse enumerates every word and
shares only what sits upstream of the first branch point. That matches the
earlier direct measurement of HVM4 superposition — distinct labels give the
whole exponential tree; same labels give correlated choice, one path per
branch, not state identification.

State identification is the thing the cube needs and the thing this encoding
does not give the runtime: two words that reach the same element are two
separate branches here, because HVM4 shares through duplication and not
through structural equality. The next object to write is one where the
branching is on the element rather than on the word, so that the coinductive
fibre's returned path is what identifies two observations as the same state.
