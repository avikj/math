# Hyperactive

Constructive mathematics, implemented as it is stated in `docs/index.html`.

## The object and the operation

- **The object is an identification.** `Σ y. (x = y)` is one point: `(x, refl)` (§0).
- **The operation is folding.** What is identified is one cell. J, transport and substitution are this one act.
- **Congruence is not a second operation.** A path is a map out of the interval, so `f` applied to a path is `f ∘ p`. When parts fold, what is built from them is built from the one part.

## The store

- **Cells by construction.** A cell is identified by its construction, read through the folds. Building the same construction twice gives the same cell.
- **Folding is union.** A construction whose parts have folded is looked up through them, so it meets the one cell.

## Order is an identification

`a ≤ b` is `min(a, b) = a`: the lattice (`docs/divisibility.html`). Its identities fold like any other identification:

- **Idempotence:** `min(a, a) = a`.
- **Commutativity:** `min(a, b)` and `min(b, a)` are one construction.
- **Bottom:** `min(⊥, x) = ⊥` and `max(⊥, x) = x`.
- **Transitivity is associativity:**
  - Given `min(a, b) = a` and `min(b, c) = b`,
  - `min(a, c) = min(min(a, b), c) = min(a, min(b, c)) = min(a, b) = a`.
  - A relation already reachable through folded relations *is* that composite: the same cell.
- **New relations.** A relation not yet reachable is new: one fold that reads the order of two values. The new relations are the witness.

## `sort` is its definition

The elements are a finite set labelled into `V`.
- **The domain.** `Fin n` is built by disjoint union (Numbers: addition is disjoint union).
- **The union.** Let `a` and `b` be the ordered presentations of the two parts. The ordered presentation of their union is, by the lattice alone:

  ```
  c_k = min over i + j = k of max(a_i, b_j)        (a_0 = b_0 = ⊥)
  ```

- **Evaluation.** The cells of this definition are built and folded until each `c_k` is one value. Nothing in `hyper.c` names a strategy.

`hyper FILE` reads the elements from FILE, whitespace-separated, and prints:
- the ordered presentation;
- the number of new relations;
- ⌈log₂ n!⌉;
- the number of folds and cells.

## Measured

| input | ordered | new relations | ⌈log₂ n!⌉ | folds | cells |
|---|---|---|---|---|---|
| `2 0 3` | yes: `0 2 3` | 3 | 3 | 6 | 10 |
| `5 3 9 1 7 2 8 6` | yes | 17 | 16 | 56 | 65 |
| 100 random | yes | 536 | 525 | 9 900 | 10 001 |
| 1 000 random | yes | 8 721 | 8 530 | 999 000 | 1 000 001 |

**The new relations are within 2% of log₂ n! at every size.** Nothing is folded twice: a relation reachable through folded relations is never made again.

**The cells and folds are quadratic.** The definition `min over i+j=k of max(a_i, b_j)` is written out in full: |A|·|B| cells per union, each folded. The witness is n log n. The store holds the whole formula, and most of it folds to cells that already exist. For the same reason, 10 000 elements did not finish in two minutes.
