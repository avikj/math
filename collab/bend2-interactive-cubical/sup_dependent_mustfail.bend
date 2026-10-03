# Must fail: a superposition whose label is NOT the index's label is an
# independent coordinate, so BOTH of its branches must inhabit BOTH fibres.
# 3n is not a point of Unit, so this is rejected: no label admits (3n, False).
def F(b: Bool) -> Set:
  if b:
    Nat
  else:
    Unit

def cross() -> Σ b: Bool. F(b):
  (&0{True, False}, &1{3n, ()})

def main() -> Nat:
  0n
