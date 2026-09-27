# Hyperactive

This is the net that Bend2's `--to-hvm4-full` emits into, plus one addition: a declaration with no body is a coordinate of its type.

Everything else is a program in the book, reduced by the same rules. That includes the cubical operations (`coe`, `hcomp`, `ua`, Glue), the fibre law, the whole process, and every domain.

```
TERM = VAR | LAM | APP | SUP L | DP0 L | DP1 L | ERA | CTR c | MAT T | REF d | NUM | OP2 | CRD T

DUP meets LAM             dupLam            both copies are lambdas; the binder becomes &L{x0,x1}
DUP meets SUP, same L     dupSupEqual       route: the two sides are the two copies
DUP meets SUP, other L    dupSupDifferent   cross: both copies superposed at the other label
DUP meets CTR/MAT         dupNode           both copies are the node, its parts duplicated
APP of LAM                beta
APP of SUP                appSup
APP of MAT to CTR         match
APP of MAT to SUP         appMatSup
APP of MAT to CRD, or DUP meets CRD   expand: in place, the coordinate becomes the superposition of its
                                      type's constructors, with fresh coordinates as their fields
collapse: the leaves of the result; the empty ones (&{}) are gone
```

Usage: `hyper FILE…` prints each leaf of `@main`, then the receipt (interactions, heap words, and a count for each rule).

- `sort.hyper` declares *sorted* as "each element is less than all following". Given A, B is determined: its first element is the meet of A's bag, and the rest is the same over what remains. Both numbers and the bag are in their digit charts, not unary (TransportDivScale: unary is the exponential chart).
  - A number is its binary digits.
  - A bag is a disjoint union of halves.
  - The meet is lossless: each node keeps the side that won, so removing the meet re-reads only that side.
  - Each side's top is read while the side is kept, never copied.
- `sat.hyper`: the assignment really is open. `@X, @Y : Bool` are coordinates, and XOR keeps its fibre over true.

| n (a permutation of 0…n−1) | sorted | comparisons | ⌈log₂ n!⌉ | interactions |
|---|---|---|---|---|
| 8 | yes | 17 | 16 | 1,618 |
| 64 | yes | 305 | 296 | 31,262 |
| 256 | yes | 1,721 | 1,684 | 190,630 |
| 1024 | yes | 8,949 | 8,769 | 1,072,890 |

The counts are the same under both schedules (`HYPER_ORDER=1`). Comparisons are log₂ n! + about 0.18n. Each comparison reads w = log₂ n digits, so the interaction count is Θ(n log n · w).

Diagnostics: `HYPER_REFS=1` prints unfoldings per definition and copies per constructor.
