# Hyperactive

Constructive mathematics, implemented as `docs/index.html` states it.

## One object, one operation

- **The object is an identification.** `Σ y. (x = y)` is one point, `(x, refl)` (§0).
- **The operation is folding.** What is identified is one cell. J, transport and substitution are this one act.
- **Congruence is part of folding.** A cell built from folded parts is built from the one part. This is `f ∘ p`, the definition of applying a map to a path, not a second step.

## One store

- **A cell is its construction** `(kind, part, part)`, with the parts read through the folds. Building a construction that already exists gives that cell.
- **Folding is union.**
- **Identities apply at construction.** A construction that an identity makes equal to an existing cell is that cell from birth.

## The constructions

| cell | is |
|---|---|
| `ELEM(v)` | an element of `V`; its value is its construction |
| `EMPTY`, `ONE(x)`, `UNION(A, B)` | finite sets; `UNION` is disjoint union (Numbers: addition) |
| `MIN2(a, b)` | the meet of two elements. Order is this cell: `a ≤ b` is `MIN2(a, b)` folded into `a` |
| `LEAST(S)` | the least element of S |
| `REST(S)` | S without its least element |

## The identities

- **Unit of union:** `UNION(EMPTY, B) = B` and `UNION(A, EMPTY) = A`.
- **Singletons:** `LEAST(ONE x) = x` and `REST(ONE x) = EMPTY`.
- **Idempotence and commutativity:** `MIN2(a, a) = a`, and `MIN2(a, b) = MIN2(b, a)` is one construction.
- **Associativity of the meet:** `LEAST(UNION(A, B)) = MIN2(LEAST A, LEAST B)`.
- **Removing the least:** `REST(UNION(A, B))` is `UNION(REST A, B)` if that meet is `LEAST A`, and `UNION(A, REST B)` otherwise.
- **Transitivity is associativity:** `MIN2(a, c) = a` when `a ≤ b` and `b ≤ c` are folded. That meet is their composite, and nothing new is made.

A `MIN2` of two distinct elements, when no fold and no composite of folds identifies it, is a **new relation**. That is the one place an element's value is read, and each new relation is one part of the witness.

## `sort` is its definition

The ordered presentation of S is `LEAST(S)` followed by the ordered presentation of `REST(S)`. The set is `Fin n` labelled into `V`, and `Fin n` is built as the union of halves.

## Worked out from the construction, then run

- **Per union.** At a union of sizes p and q, the new relations number at most p + q − 1. Over the construction of `Fin n` that is at most n⌈log₂ n⌉ − n + 1, which is log₂ n! + O(n).
- **Cells.** O(n log n).
- **Composites.** None. Every meet this definition builds is between two elements not yet related.
- **`2 0 3`, by hand.** `MIN2(0,3)` folds to 0. `MIN2(2,0)` folds to 0. `MIN2(2,3)` folds to 2. That is 3 new relations.

| input | ordered | new relations | log₂ n! | n⌈log₂ n⌉−n+1 | composites | folds | cells |
|---|---|---|---|---|---|---|---|
| `2 0 3` | yes | 3 | 2.6 | 4 | 0 | 9 | 19 |
| `5 3 9 1 7 2 8 6` | yes | 17 | 15.3 | 17 | 0 | 51 | 85 |
| 100 random | yes | 536 | 524.8 | 601 | 0 | 1 608 | 2 345 |
| 1 000 random | yes | 8 721 | 8 529.4 | 9 001 | 0 | 26 163 | 36 885 |
| 10 000 random | yes | 120 405 | 118 458.1 | 130 001 | 0 | 361 215 | 501 621 |

## Scope

A definition's text is read as written. Each construction folds by the identities as it is built. The definition above has as many cells as its witness.

## Usage

`hyper FILE`, where FILE lists the elements separated by whitespace.
