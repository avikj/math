# Hyperactive

- **The element** is the identification.
- **The operation** is folding: what is identified is one cell.
- **A cell** is its construction: a name and its parts, with the parts read through the folds. Building a construction that already exists gives that cell. This is also congruence: a construction built from folded parts is the construction built from the one part.
- **Identities** are equations between constructions, written in a file. A cell is folded into what its equations make it.
- **The core knows no domain.** The one place a value is read is `min(a, b)` of two input elements. The input gives their order, and that fold is a *new relation*.

`sort.eq` is sort's definition:
- the finite set, built by disjoint union;
- its least element and the rest, where the meet over a union is the meet of the parts' meets;
- the ordered presentation: the least element, then the presentation of the rest.

Usage: `hyper sort.eq ELEMENTS`. The reader builds ELEMENTS as the finite set `input` (`one(e)` and the union of halves) and presents it.

| elements | ordered | new relations | log₂ n! | cells |
|---|---|---|---|---|
| `2 0 3` | yes | 3 | 2.6 | 45 |
| `5 3 9 1 7 2 8 6` | yes | 17 | 15.3 | 191 |
| 100 random | yes | 536 | 524.8 | 5 231 |
| 1 000 random | yes | 8 721 | 8 529.4 | 81 315 |
| 10 000 random | yes | 120 405 | 118 458.1 | 1 105 433 |
