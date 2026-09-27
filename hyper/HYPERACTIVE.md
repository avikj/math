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

- `sort.hyper` declares *sorted* as "each element is less than all following". Given A, nothing is open, so nothing is superposed or filtered. The bag is presented as its least element and the remainder (S ≅ (⋀S, S∖⋀S), the fibre law at `least`), and B is read off that presentation.
- `sat.hyper` has an assignment that really is open: `@X, @Y : Bool` are coordinates, and XOR keeps its fibre over true.

| input | result | interactions |
|---|---|---|
| `[]` | `[]` | 8 |
| `[2,1,1]` | `[1,1,2]` | 170 |
| `[3,1,2]` | `[1,2,3]` | 189 |
| `[4,2,3,1]` | `[1,2,3,4]` | 374 |
| permutation of 1…8 | sorted | 2,508 |
| permutation of 1…16 | sorted | 21,484 |
| permutation of 1…32 | sorted | 208,753 |
| permutation of 1…64 | sorted | 2,659,761 |
| XOR(x, y) | `(F,T)`, `(T,F)` (2 leaves) | 75 |

**The count, derived for this presentation.** `least` over k elements makes k − 1 comparisons, so all levels together make n(n−1)/2. A comparison `le a b` costs min(a, b) + 1 matches. Each comparison also duplicates the two unary values it compares, and a duplication costs one `dupNode` per constructor. The total is therefore Θ(n² · v̄), where v̄ is the average value. For a permutation of 1…n that is Θ(n³), which matches the table: `dupNode` is 2,304,771 of the 2,659,761 interactions at n = 64. No superposition rule fires.
