# playground

Programs written on top of the machine, to look at what it does. Nothing here is part of the
runtime (`src/`), its library (`lib/`), or its acceptance tests (`tests/`), and nothing outside this
directory depends on it.

- `sort-ordered.ctt` — the sorting declaration of `tests/sort.ctt` (Σ[B] (B a rearrangement of X) ×
  Sorted B, posed by the elimination of a finite bag X) over any type with a total order, given as a
  comparator `le : A → A → Bool` with its four laws. Run at Words (one machine comparison per `le`),
  at Words past 64 bits (the same steps), and at a three-colour type with no numeric content.

Run with `make playground`. Set `CUBICAL_TRACE=<file>` to get every interaction of each `(show ...)`
reading, one per line.
