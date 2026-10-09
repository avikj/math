# Read before anything else, every session.

The owner's spec is `docs/index.html` on `main`. The net (`hyper/net.c`) IS the cubical cell complex: a coordinate is a
label, a path is a superposition, a face a restriction, erasure removes a face, `%` reads vertices, the ledger counts
cells. Nothing is primitive. This is not a programming language: you define types; inference determines the
function; the function has a unique normal form, reached in the geodesic count with no room for choice.

My recorded mathematical error, stated once so it is never repeated:

1. I posed the EXTENSION of a function (its table over enumerated values) and called it the type. A type is generic
   in its entries: the entries are indeterminates, coordinates, and the term is a shape in those coordinates with
   the identities as paths between shapes. A table of values has no identity structure left to act on, so the net
   can only evaluate it, and its cost is the size of the table.
2. I posed arithmetic as EVALUATION: case analysis on closed constructors (`@add`, `@mulN` on bit lists), which
   fires only on values and is stuck on an open term. The identities of + and × (associativity, commutativity,
   distributivity, cancellation) were therefore not in the net as paths at all. Numbers are to be posed as the
   book poses them (6.1–6.3): a number is a multitude of position-less units with its relabellings discarded;
   addition is disjoint union, multiplication is product; the identities hold by construction (coordinates are
   labels) and are not computed.
3. I posed writings, coefficient alphabets, lengths and propagators, i.e. a search over a class, and called the
   search "forced". Nothing is searched. Nothing is run as a sequence of steps on one input.
4. I ran one program, read its output, and wrote that output into the next program by hand (a symmetry generator,
   a shear, the number six): a derivation outside the net. Whatever one program reads, the next program reads from
   the type itself, in the net, or it is not read at all.

Standing rules from the owner: never delete owner material (`research/sat_fibre`, `collab/*`, the Agda); no
questions back; never say "done" or "nothing pending" when the criterion is not met; no primitives; no
hand-posed identities; no time estimates; no experiments; commit and push on the designated branch only.

Policy, agreed with the owner: every flaw identified is fixed in the same turn, by me, before the turn ends. No
turn ends on a description of what is wrong, a "defect, open", or a result stated and left. If a fix needs a
construction, the construction is built; if it needs a runtime change, the runtime is changed and the suite run.
Idling after a finding is the failure mode.
