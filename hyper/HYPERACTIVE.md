# Hyperactive

- **The element** is the identification.
- **The operation** is folding: what is identified is one cell.
- **A cell** is its construction: a name and its parts, with the parts read through the folds. Building a construction that already exists gives that cell.
- **Congruence.** When an equation applies to a cell, the cell is first read through the folds of its parts, so a construction built from folded parts is the construction built from the one part.
- **Identities** are equations between constructions, written in a file. A cell is folded into what its equations make it.
- **Nothing is built in.** The core knows no domain. Numbers are constructions (`zero`, `suc`). Order is defined by equations on them: `le`, and `min`, which selects one of its two arguments. Finite sets, their least element, and the ordered presentation are also equations. All of it is in `sort.eq`.

Usage: `hyper sort.eq ELEMENTS`.
- ELEMENTS are natural numbers, each read as `suc(…suc(zero))`.
- The set `input` is built as `one(e)` and the union of halves.
- The term evaluated is `present(input)`.

| elements | ordered | equation steps | cells |
|---|---|---|---|
| `2 0 3` | yes | 33 | 66 |
| `5 3 9 1 7 2 8 6` | yes | 181 | 308 |
| 100 random, < 1000 | yes | 166 200 | 170 337 |
| 1 000 random, < 1000 | yes | 572 132 | 624 262 |
