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

    Reaches(g, k)   a type family whose inhabitant carries the k moves
    LE(a, b)        a type
    InG(g)          a sigma of three paths, not a boolean test
    DistIs(g, d)    reachable in d, and no smaller k reaches
    Diameter(D)     some g in G at distance exactly D, and every h in G within D

`main` is `Diameter(twenty())`, and the checker accepts it, normalising to the
statement itself:

    Sg:Elt. Sinside:InG(g). Srealises:(Sr:Reaches(g,20). Ak:Nat. Aq:Reaches(g,k). LE(20,k)).
      Ah:Elt. AalsoInside:InG(h). Reaches(h,20)

## Handing it to the evaluator

    bend CubeDiameter.bend --to-hvm4-full > CubeDiameter.hvm4
    hvm CubeDiameter.hvm4 -s

Measured, on the built toolchain:

- `@twenty` normalises.
- `@InG(@superflip)` normalises in 22,497 interactions to
  `Sig{Path{Num,0,0}, Sig{Path{Num,0,0}, Path{Num,0,0}}}`. The runtime
  computed the three membership obligations of the superflip and reduced each
  to a reflexivity: twist sum 0, flip sum 0, parities equal. Membership in G
  is decided by the evaluator.
- `@Reaches`, `@LE`, `@DistIs` and `@GodsNumber` do not terminate.
  `@Reaches(@identity, 0)` does not terminate either, so this is not search
  depth. Both families recur inside a match branch on a bound variable, and
  the full-runtime normaliser reduces under binders, so it unfolds the
  declaration forever rather than reaching a decision. Normalising a recursive
  type family is not the same act as inhabiting it.

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
