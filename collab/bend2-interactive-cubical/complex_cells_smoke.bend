# Every cell survives emission to the full runtime: an equality type keeps
# its carrier and endpoints, an enum type keeps its symbols, and ua keeps
# both coherences next to its two maps. Transport along ua runs by the map.

def refl(A: Set, a: A) -> A{a == a}:
  {==}

def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

def negLnv(x: Bool) -> Path(Bool, neg(neg(x)), x):
  if x:
    <_> True
  else:
    <_> False

def negPath() -> Path(Set, Bool, Bool):
  ua(Bool, Bool, neg, neg, negLnv, negLnv)

def main() -> Bool:
  coe(lambda i. negPath() @ i, i0, i1, True)

# (the enum comes last: after a `&{...}` body the parser does not accept
# an `A{a == b}` type in the following signature)
def Colour() -> Set:
  &{&red, &green}
