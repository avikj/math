# Hyperactive

This is the net that Bend2's `--to-hvm4-full` emits into, plus one addition: a declaration with no body is a coordinate of its type.

A coordinate is a slot and its type. Its type is a term: a data type `T`, `Σ x: A. B`, `Π x: A. B`, or `(≡ x y)`. When something asks the coordinate for its value (a match, an application, or collecting the leaves), the slot is written in place according to its type:

| type | value written |
|---|---|
| T | T's constructors, superposed, with fresh coordinates as fields |
| Σ A F | the pair (a, b), where b : F a |
| Π A F | λx. the coordinate of F x |
| x ≡ y | x and y unified |

Unification:
- Two constructors unify field by field; different constructors give `&{}`.
- A superposed side distributes over the other.
- A coordinate is bound in the branch that reached it. Its slot becomes one superposition per choice label on the way: the value on the side taken, and a fresh coordinate of its type on the other side. Copy labels (duplications of one variable) bind both copies.

This is the reference core's rule at a match (`fb8e64afd:hyper/cell.c`: `coordinate_asked`, `unify_step`, `bind_under`), translated into the net.

Usage: `hyper FILE…` prints each leaf of `@main`, then the receipt (interactions, heap words, and a count for each rule).

- **`sat.hyper`**: `@sat : Σ x: Bool. Σ y: Bool. (≡ (@xor x y) #T)`. Two leaves, 48 interactions.
- **`sort.hyper`**: the declaration and nothing else: `@sort : Π A: List. Σ B: List. (× (@Perm A B) (@Sorted B))`.
  - `Perm`: B's head is taken out of A, and B's tail is a permutation of what remains.
  - `Sorted`: each element ≤ all following.
  - `@main = (@sort @A)` prints the one point: B together with its proofs.

| n (a permutation of 0…n−1) | B | interactions |
|---|---|---|
| 3 | sorted | 5,749 |
| 4 | sorted | 30,178 |
| 5 | sorted | 204,249 |
| 6 | sorted | 1,734,870 |

The reference core took 37,159 interactions for [3,1,2]. Growth here is factorial: under this schedule, `Perm` is completed before `Sorted` is read, so every arrangement is built and then refused.

Under `HYPER_ORDER=1`, `Sorted` is read first over an unbound B, and collection does not terminate. So the count is not schedule-invariant here: collecting the leaves over an unbounded superposition is outside the one-step diamond.
