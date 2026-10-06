import ../../collab/bend2-interactive-cubical/port/UniversalPresentation

# A concrete configuration constraint: exactly one of two features is enabled.
type Assignment:
  case @assignment:
    x: Bool
    y: Bool

def formula(a: Assignment) -> Bool:
  match a:
    case @assignment{x, y}:
      if x: if y: False else: True
      else: y

type Reading:
  case @reading:
    x: Bool
    y: Bool
    answer: Bool

# SAT-specific code is now only the mathematical object, its proposition, and
# the desired readout. The generic lossless/coinductive process is the language
# presentation supplied by UniversalPresentation / the full target.
def query(a: Assignment) -> Reading:
  answer = visible(Assignment, Bool, formula, a)
  source = recover(Assignment, Bool, formula, a)
  match source:
    case @assignment{x, y}:
      @reading{x, y, answer}

def main() -> Reading:
  query(@assignment{&100{False, True}, &101{False, True}})
