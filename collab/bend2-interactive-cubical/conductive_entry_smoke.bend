# The checked entry is emitted as the typed point (A, a) of Σ(A : Set). A:
# no imports, no generated companions, one emitter for terms and types.

def id(x: Nat) -> Nat:
  x

def main() -> Nat:
  id(2n)
