# A superposed point of a DEPENDENT family is typed fibrewise, by label.
#
# The runtime's one decision is DUP-SUP: same label routes (the diagonal
# Δ ≃ 2, one correlated choice), different labels cross (the product 2×2,
# two independent coordinates). The checker types &l{a, b} against a goal
# by the DUP of the goal at l, so a value whose label is the label of the
# index it depends on lives in the fibre over its own branch:
#
#   &0{3n, ()} : F(&0{True, False})       F(True) = Nat, F(False) = Unit
#
# checks as 3n : Nat and () : Unit. It is the same rule the net runs, and
# the typed point of `diag` collapses (-C) to two readings, each a point of
# its own fibre — never (3n, False), which no label admits.
def F(b: Bool) -> Set:
  if b:
    Nat
  else:
    Unit

# the diagonal: one label, the index and the value move together
def diag() -> Σ b: Bool. F(b):
  (&0{True, False}, &0{3n, ()})

# nested inside a former: the DUP of the goal is pushed through Σ
def diagPair() -> Σ b: Bool. Σ n: F(b). Bool:
  (&0{True, False}, &0{(2n, True), ((), False)})

# the product: an independent label on the outside, the routed one inside
def prod() -> Σ b: Bool. F(b):
  (&0{True, False}, &1{&0{1n, ()}, &0{2n, ()}})

# through a dependent function: the argument's label dups the codomain
def proj(b: Bool, x: F(b)) -> Nat:
  if b:
    x
  else:
    0n

def main() -> Σ b: Bool. F(b):
  diag()
