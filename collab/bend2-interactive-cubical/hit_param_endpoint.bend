# A parametric HIT whose path constructor's endpoints mention its parameters:
# the mapping cylinder of f, which deformation-retracts onto B.
#
# A constructor is written bare (@seg{a}); the checker reads the parameters
# off the goal and carries them into the term (Core.Check.elabFills), so the
# declared endpoint @bot{f(a)} computes with the actual f, in the checker and
# on the full runtime. Before that, the endpoint was an opaque placeholder in
# the normaliser and an empty superposition on the runtime, which annihilated
# the whole value under collapse.
type Cyl(A: Set, B: Set, f: A -> B):
  case @top:
    a: A
  case @bot:
    b: B
  path @seg(a: A): Path(Cyl(A, B, f), @top{a}, @bot{f(a)})

def dbl(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n + p: 1n + 1n + dbl(p)

def C() -> Set:
  Cyl(Nat, Nat, dbl)

# the retraction onto B: top ↦ f, bot ↦ id, and the segment is constant there
def collapse(x: C()) -> Nat:
  hrec(x) { @top: lambda a. dbl(a) ; @bot: lambda b. b ; @seg: lambda a. <i> dbl(a) }

# both ends of the segment at 3 collapse to dbl(3) = 6; at i1 the endpoint is
# the declared @bot{f(a)}, which must be read with f = dbl
def seg0() -> Path(Nat, collapse(@seg{3n} @ i0), 6n):
  <_> 6n

def seg1() -> Path(Nat, collapse(@seg{3n} @ i1), 6n):
  <_> 6n

def main() -> Nat:
  collapse(@seg{3n} @ i1)
