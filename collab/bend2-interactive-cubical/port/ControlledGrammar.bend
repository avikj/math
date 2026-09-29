# formal/cubical/Kernel/ControlledGrammar.agda, in Bend.
import RewriteCertificate

type NativeOperation:
  case @op:
    source: Tm
    target: Tm
    checked: Derivation(source, target)
    Control: Tm -> Set
    control_sound: all t: Tm. Control(t) -> Path(Tm, t, source)

def opSource(o: NativeOperation) -> Tm:
  match o: case @op{s, t, c, C, cs}: s
def opTarget(o: NativeOperation) -> Tm:
  match o: case @op{s, t, c, C, cs}: t
def opControl(o: NativeOperation, u: Tm) -> Set:
  match o: case @op{s, t, c, C, cs}: C(u)

def apply(o: NativeOperation, t: Tm, c: opControl(o, t)) -> Tm:
  opTarget(o)

# subst the checked derivation back along the control's path
def apply_checked(o: NativeOperation, t: Tm, c: opControl(o, t)) -> Derivation(t, apply(o, t, c)):
  match o:
    case @op{s, tg, chk, C, cs}:
      coe(lambda i. Derivation(cs(t, c) @ inot(i), tg), i0, i1, chk)

# installing a theorem: its native control is exactly evidence that the
# current term IS its certified source
def install(lhs: Tm, rhs: Tm, d: Derivation(lhs, rhs)) -> NativeOperation:
  @op{lhs, rhs, d, lambda t. Path(Tm, t, lhs), lambda t. lambda c. c}

type EnabledFuture(seed: Tm):
  case @enabled:
    operation: NativeOperation
    control: opControl(operation, seed)

type CheckedFuture(seed: Tm):
  case @checked:
    target: Tm
    derivation: Derivation(seed, target)

def efTarget(seed: Tm, f: EnabledFuture(seed)) -> Tm:
  match f: case @enabled{o, c}: apply(o, seed, c)
def efDerivation(seed: Tm, f: EnabledFuture(seed)) -> Derivation(seed, efTarget(seed, f)):
  match f: case @enabled{o, c}: apply_checked(o, seed, c)
def cfTarget(seed: Tm, f: CheckedFuture(seed)) -> Tm:
  match f: case @checked{t, d}: t
def cfDerivation(seed: Tm, f: CheckedFuture(seed)) -> Derivation(seed, cfTarget(seed, f)):
  match f: case @checked{t, d}: d

def execute(seed: Tm, f: EnabledFuture(seed)) -> CheckedFuture(seed):
  @checked{efTarget(seed, f), efDerivation(seed, f)}

# parallel advance: no quotient, no sort, no dedupe
def advance(seed: Tm, fs: EnabledFuture(seed)[]) -> CheckedFuture(seed)[]:
  map(EnabledFuture(seed), CheckedFuture(seed), lambda f. execute(seed, f), fs)

# exact no-premature-collapse law: branch multiplicity is invariant
def advance_preserves_branch_count(seed: Tm, fs: EnabledFuture(seed)[]) -> Path(Nat, length(CheckedFuture(seed), advance(seed, fs)), length(EnabledFuture(seed), fs)):
  match fs:
    case []: <_> 0n
    case f <> rest: <i> 1n + (advance_preserves_branch_count(seed, rest) @ i)

def main() -> Nat:
  0n
