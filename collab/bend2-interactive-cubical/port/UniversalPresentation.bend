# Universal language presentation.
#
# This is not an optimizer or a second evaluator.  It names the one object:
#
#   typed point + every map out of it
#     == lossless fibre presentation
#     == continuing typed point.
#
# The full target has no runtime copy of it: a checked program using this
# module runs through the ordinary emitter, and its root is the typed point
# (A, a) of Σ(A : Set). A that the same law applies to again.

import FibreCoalgebra

type Point:
  case @point:
    A: Set
    value: A

def point(A: Set, a: A) -> Point:
  @point{A, a}

# A question/observation is literally a codomain and a map out of the current
# point. There is no finite opcode vocabulary.
type Question(A: Set):
  case @question:
    B: Set
    map: A -> B

def presentMap(A: Set, B: Set, f: A -> B, a: A) -> FibreElement(A, B, f):
  descend(A, B, f, a)

def presentPoint(A: Set, a: A) -> FibreCoalgebra(A, a):
  fibreCoalgebra(A, a)

# One observation does not target merely (B,f(a)); its new whole is the exact
# fibre presentation. This is the point/question calculus after lossless
# completion.
def react(A: Set, a: A, p: FibreCoalgebra(A, a), q: Question(A)) -> Point:
  match q:
    case @question{B, f}:
      match observe(A, a, p, B, f):
        case @fibreObservation{value, source, next}:
          @point{FibreElement(A, B, f), value}

# Ordinary evaluation is the visible projection of the richer presentation.
def visible(A: Set, B: Set, f: A -> B, a: A) -> B:
  observedValue(A, B, f, presentMap(A, B, f, a))

def visible_beta(A: Set, B: Set, f: A -> B, a: A) -> Path(B, visible(A, B, f, a), f(a)):
  <_> f(a)

# The first continuation is again the same universal process, now over the
# exact fibre coordinates.  Recovering the source is therefore an ordinary
# second observation, not replay or an external history lookup.
def recover(A: Set, B: Set, f: A -> B, a: A) -> A:
  observe_recover(A, a, B, f)

def recover_beta(A: Set, B: Set, f: A -> B, a: A) -> Path(A, recover(A, B, f, a), a):
  <_> a

def main() -> Nat:
  recover(Nat, Nat, lambda n. 1n + n, 2n)
