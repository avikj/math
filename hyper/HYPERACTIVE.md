# Hyperactive

One store of cells, with folding as the only operation.

- **Cells.** A cell is a construction: a symbol and its parts, with the parts read through the folds. Building a construction that already exists gives that cell.
- **Declarations are cells in the same store.**
  - `l = r` is the cell `=(l, r)`.
  - `l = r when p = q, p # q` is the cell `when(=(l, r), =(p, q), #(p, q))`.
  - A variable is a cell wired to each place it occurs in its declaration.
  - A declaration's own cells are open and are never folded.
- **Every identity applies at every instance of its shape, once.**
  - A closed cell headed by an identity's left-side symbol is an instance. The identity's right side, with its variables wired to that cell's parts, is folded with it, and its premises are instances too.
  - A cell headed by a premise's left-side symbol, once the premise holds, folds the identity's left side, but only where that cell already exists.
- **Folding.** Cells made equal are one class, and everything built on them is read again.
- **Constructors.** A symbol that is no identity's left side is a constructor.
  - Two constructors with the same symbol in one class have their parts identified.
  - With different symbols, the case is empty.
- **Cases.** `S in a b …;` makes S range over those constructors.
- **Presentation.** `ac`, `idem` and `unit` say how parts are presented.
  - `R*` in a pattern is the remaining parts of a sum.
  - `p*` stands for every part: each part meets `p`, and `q*` on the right side is `q` at each part.

Files:
- `order.eq`: ≤ by its identities (reflexive, transitive, antisymmetric, total), and the values `elem(n)`.
- `sorted.eq`: a bag as the sum of singletons; *sorted* as "each element is less than all following"; `main = present(bag(input))`.
- `sat.eq`: `or` and `neg`.

```
hyper order.eq sorted.eq NUMBERS
hyper sat.eq FORMULA.cnf
```

Diagnostics:
- `HYPER_TRACE=1` prints every fold.
- `HYPER_DEBUG=1` prints every identity tried at a cell.

## What comes out

**Sorting** (random permutations). The output is ordered at every size. Every one of the n(n−1) relations `le(a, b)` between two values is folded, each exactly once.

| n | relations | first folded by: values | transitivity | antisymmetry | totality |
|---|---|---|---|---|---|
| 3 | 6 | 3 | 0 | 1 | 2 |
| 8 | 56 | 27 | 1 | 8 | 20 |
| 16 | 240 | 118 | 2 | 16 | 104 |
| 32 | 992 | 374 | 122 | 230 | 266 |

The run time grows faster than the fold count. Most of it is spent re-matching sums whose parts changed. That is a cost of this implementation, not of the network.

**3-SAT.** Results are correct. Satisfiable results are checked against every clause. Cases: 20 variables take 6, 50 take 1,769.
