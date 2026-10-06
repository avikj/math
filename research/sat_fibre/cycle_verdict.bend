type Step:
  case @Fwd: w: Nat
  case @Bwd: w: Nat
type Trace:
  case @Done:
  case @Then: s: Step  rest: Trace
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n: b
    case 1n + p: 1n + add(p, b)
def stepVal(s: Step) -> Nat:
  match s:
    case @Fwd{w}: w
    case @Bwd{w}: w
def integ(t: Trace) -> Nat:
  match t:
    case @Done{}: 0n
    case @Then{s, rest}: add(stepVal(s), integ(rest))
def loop() -> Trace:
  @Then{@Fwd{0n}, @Then{@Fwd{1n}, @Then{@Fwd{1n}, @Then{@Bwd{1n}, @Then{@Bwd{0n}, @Then{@Bwd{0n}, @Done}}}}}}
def main() -> Nat:
  integ(loop())
