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

- `sort.hyper` declares what "sorted" means. `@B : List` has no body, and `@main` keeps `B` where `spec input B` holds.
- `sat.hyper` does the same with `@X, @Y : Bool` under XOR.

| input | leaves | result | interactions |
|---|---|---|---|
| `[]` | 1 | `[]` | 66 |
| `[2,1,1]` | 1 | `[1,1,2]` | 10,119 |
| `[3,1,2]` | 1 | `[1,2,3]` | 17,355 |
| `[4,2,3,1]` | 1 | `[1,2,3,4]` | 207,819 |
| XOR(x, y) | 2 | `(F,T)`, `(T,F)` | 75 |
