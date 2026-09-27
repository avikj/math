# Hyperactive

The runtime has one element, the identification, and one operation, folding. `hyper.c` does these five things and nothing else:

1. **A cell is its construction.** A cell is a symbol and its parts, with the parts read through the folds. Building a construction that already exists gives that cell.
2. **Identities are declarations.** They are written `lhs = rhs;` or `lhs = rhs when p = q, …;`. An identity is instantiated at each cell of its shape:
   - at the cell of its left side: the first identity in the files whose premises hold;
   - at a cell of a premise's left side, once that premise holds. From a premise it only folds cells that already exist.
3. **Folding.** Cells an identity makes equal are one class. Everything built on them is read again, so a construction that now coincides with another is that other.
4. **Cases.** `S in a b …;` makes S range over those constructors.
   - Each case is folded on its own.
   - A case with two different constructors in one class is empty.
   - What a case leaves of the declarations is one construction wherever it recurs, so a remainder found empty stays empty.
5. **The result** is what remains when nothing more folds.

The core knows no order, numbers, sets, sort or SAT. Those are the files:

- `order.eq`: ≤ by its identities (reflexive, transitive, antisymmetric, total). Values are `elem(n)`, with n built from `zero`/`suc`.
- `selection.eq`: selection sort as declared. For each position i, the position of the least element at positions ≥ i is swapped with i.
- `sat.eq`: `or` is associative, commutative and idempotent with unit `false`, plus `neg`.

## Usage

```
hyper order.eq selection.eq NUMBERS     # prints the result read from main, and counts
hyper sat.eq FORMULA.cnf                # DIMACS; x1…xn range over true, false; each clause is folded with true
```

Diagnostics:
- `HYPER_TRACE=1` prints every fold.
- `HYPER_DECISIONS=file` writes each `le` fold, with the line of the identity that made it.

## What comes out

**Selection sort** (`order.eq selection.eq`, random permutations):

| n | ordered | `le` between two values | decided by the values' own identity | by transitivity or antisymmetry | log₂ n! | n(n−1)/2 |
|---|---|---|---|---|---|---|
| 3 | yes | 3 | 3 | 0 | 2.6 | 3 |
| 8 | yes | 24 | 20 | 0 | 15.3 | 28 |
| 16 | yes | 73 | 62 | 0 | 44.3 | 120 |
| 32 | yes | 358 | 333 | 0 | 117.7 | 496 |
| 64 | yes | 1231 | 1177 | 0 | 296.0 | 2016 |
| 128 | yes | 4211 | 4091 | 0 | 716.2 | 8128 |

The result is correct at every size. The count grows as n².

With `HYPER_DECISIONS`, every relation between two values at n = 128 was checked against the relations folded before it. **None of the 4 091 was implied.** So the order identities had nothing to fold. What the declaration builds consists entirely of comparisons that are new, but most of them carry far less than one bit each.

**3-SAT** (`sat.eq`, random formulas with 4.26 clauses per variable):

| variables | result | cases folded | empty cases | remainders already empty |
|---|---|---|---|---|
| 20 | satisfiable (checked against every clause) | 6 | 1 | 0 |
| 50 | satisfiable (checked) | 1 769 | 870 | 11 |
| 100 | unsatisfiable | 119 778 | 59 889 | 1 |

Results are correct. The number of cases grows exponentially. Remainders almost never recur, so keeping empty ones changes little.
