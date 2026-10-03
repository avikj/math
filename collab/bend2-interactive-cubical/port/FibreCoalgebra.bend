# The coinductive form of THE LAW.
#
# One interaction replaces the current typed point by the equivalent
# FibreElement presentation. The next process is therefore not an auxiliary
# service or history: it is the same universal process on the new whole.
import FibreElement

type FibreObservation(A: Set, a: A, B: Set, f: A -> B):
  case @fibreObservation:
    value: FibreElement(A, B, f)
    source: Path(A, ascend(A, B, f, value), a)
    next: FibreCoalgebra(FibreElement(A, B, f), value)

type FibreCoalgebra(A: Set, a: A):
  case @fibreCoalgebra:
    respond: all B: Set. all f: A -> B. FibreObservation(A, a, B, f)

def fibreCoalgebra(A: Set, a: A) -> FibreCoalgebra(A, a):
  @fibreCoalgebra{
    lambda B. lambda f.
      @fibreObservation{
        descend(A, B, f, a),
        <_> a,
        fibreCoalgebra(FibreElement(A, B, f), descend(A, B, f, a))
      }
  }

def observe(A: Set, a: A, p: FibreCoalgebra(A, a), B: Set, f: A -> B) -> FibreObservation(A, a, B, f):
  match p:
    case @fibreCoalgebra{respond}:
      respond(B, f)

def observedValue(A: Set, B: Set, f: A -> B, c: FibreElement(A, B, f)) -> B:
  match c:
    case @fibreCarry{base, carried, witness}:
      carried

def observationNext(A: Set, a: A, B: Set, f: A -> B, o: FibreObservation(A, a, B, f)) -> FibreCoalgebra(FibreElement(A, B, f), observationValue(A, a, B, f, o)):
  match o:
    case @fibreObservation{value, source, next}:
      next

def observationValue(A: Set, a: A, B: Set, f: A -> B, o: FibreObservation(A, a, B, f)) -> FibreElement(A, B, f):
  match o:
    case @fibreObservation{value, source, next}:
      value

def observe_visible(A: Set, a: A, B: Set, f: A -> B) -> B:
  observedValue(A, B, f, observationValue(A, a, B, f, observe(A, a, fibreCoalgebra(A, a), B, f)))

def observe_visible_beta(A: Set, a: A, B: Set, f: A -> B) -> Path(B, observe_visible(A, a, B, f), f(a)):
  <_> f(a)

# A second observation through the retained exact fibre coordinates recovers
# the source. This is the concrete two-step coinductive law used by compiler CI.
def observe_recover(A: Set, a: A, B: Set, f: A -> B) -> A:
  o = observe(A, a, fibreCoalgebra(A, a), B, f)
  v = observationValue(A, a, B, f, o)
  n = observationNext(A, a, B, f, o)
  o2 = observe(FibreElement(A, B, f), v, n, A, lambda c. ascend(A, B, f, c))
  observedValue(FibreElement(A, B, f), A, lambda c. ascend(A, B, f, c),
                observationValue(FibreElement(A, B, f), v, A, lambda c. ascend(A, B, f, c), o2))

def observe_recover_beta(A: Set, a: A, B: Set, f: A -> B) -> Path(A, observe_recover(A, a, B, f), a):
  <_> a

def main() -> Nat:
  observe_recover(Nat, 2n, Nat, lambda n. 1n + n)
