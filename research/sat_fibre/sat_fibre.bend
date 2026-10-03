# SAT as the cubical Bend fibre law -- a single run, not a research program.
#
# A CNF is a Boolean map  F : 2^n -> 2.  SAT is a question asked OF that map:
# the satisfying set is the fibre  fiber(F, True) = (x : Asg) * Path(F x, True).
# Decision SAT = that fibre is inhabited; a witness IS an element of it.  The
# machine decides satisfaction by REDUCING F at the assignment; the residual
# fibre (assignment + the proof F x = True) is carried exactly, nothing erased.
#
# Concrete instance (3 variables, 3 clauses):
#   F(a,b,c) = (a | b | c) & (~a | b | ~c) & (a | ~b | c)

def bnot(x: Bool) -> Bool:
  match x:
    case True:  False
    case False: True

def or2(x: Bool, y: Bool) -> Bool:
  match x:
    case True:  True
    case False: y

def and2(x: Bool, y: Bool) -> Bool:
  match x:
    case True:  y
    case False: False

def clause(a: Bool, b: Bool, c: Bool) -> Bool:
  or2(a, or2(b, c))

# assignment space: (a, b, c)
def Asg() -> Set:
  any a: Bool. any b: Bool. Bool

def F(x: Asg) -> Bool:
  match x:
    case (a, b, c):
      and2(clause(a, b, c),
           and2(clause(bnot(a), b, bnot(c)),
                clause(a, bnot(b), c)))

# ---- the fibre law object, instantiated on F ----
def fiber(A: Set, B: Set, f: A -> B, y: B) -> Set:
  any x: A. Path(B, f(x), y)

# Total space = every assignment sitting over its own F-value with exact residual
def Total(A: Set, B: Set, f: A -> B) -> Set:
  any b: B. fiber(A, B, f, b)
def tot(A: Set, B: Set, f: A -> B, a: A) -> Total(A, B, f):
  (f(a), a, <_> f(a))

# a concrete witness assignment
def w() -> Asg:
  (True, True, True)

# THE RUN: the machine reduces F at w.  The proof that w is satisfying is
# refl -- it holds definitionally BECAUSE F(w) computes to True.
def satWitness() -> fiber(Asg, Bool, F, True):
  (w, <_> True)

# decision, read off the same fibre: F(w) is the target value the fibre lies over
def decideAtW() -> Bool:
  F(w)

def main() -> Bool:
  decideAtW()
