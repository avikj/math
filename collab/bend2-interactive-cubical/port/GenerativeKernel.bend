# formal/cubical/Kernel/GenerativeKernel.agda, in Bend: two derivations, one output.
import ControlledGrammar

type Branch(seed: Tm):
  case @branch:
    operation: NativeOperation
    control: opControl(operation, seed)

def brTarget(seed: Tm, b: Branch(seed)) -> Tm:
  match b: case @branch{o, c}: apply(o, seed, c)
def brHistory(seed: Tm, b: Branch(seed)) -> Derivation(seed, brTarget(seed, b)):
  match b: case @branch{o, c}: apply_checked(o, seed, c)

def form_one(seed: Tm, f: EnabledFuture(seed)) -> Branch(seed):
  match f: case @enabled{o, c}: @branch{o, c}

def form(seed: Tm, fs: EnabledFuture(seed)[]) -> Branch(seed)[]:
  map(EnabledFuture(seed), Branch(seed), lambda f. form_one(seed, f), fs)

def form_preserves_futures(seed: Tm, fs: EnabledFuture(seed)[]) -> Path(Nat, length(Branch(seed), form(seed, fs)), length(EnabledFuture(seed), fs)):
  match fs:
    case []: <_> 0n
    case f <> rest: <i> 1n + (form_preserves_futures(seed, rest) @ i)

def seed() -> Tm:
  @add{@var, @suc{@zero}}
def target0() -> Tm:
  @suc{@var}

def direct_history() -> Derivation(seed(), target0()):
  @then{@suc{@add{@var, @zero}}, @add_suc{@var, @zero, {==}, {==}},
    @then{@suc{@var}, @suc_step{@add{@var, @zero}, @var, @add_zero{@var, {==}, {==}}, {==}, {==}},
      @done{{==}}}}

# same endpoints, different computational history: forward, back, then direct
def detour_history() -> Derivation(seed(), target0()):
  @then{@suc{@add{@var, @zero}}, @add_suc{@var, @zero, {==}, {==}},
    @then{@add{@var, @suc{@zero}}, @reverse{@add_suc{@var, @zero, {==}, {==}}},
      direct_history()}}

def direct_operation() -> NativeOperation:
  install(seed(), target0(), direct_history())
def detour_operation() -> NativeOperation:
  install(seed(), target0(), detour_history())

def direct_future() -> EnabledFuture(seed()):
  @enabled{direct_operation(), <_> seed()}
def detour_future() -> EnabledFuture(seed()):
  @enabled{detour_operation(), <_> seed()}

def run() -> Branch(seed())[]:
  form(seed(), [direct_future(), detour_future()])

# kernel execution exposes both futures and computes both targets
def run_count() -> Path(Nat, length(Branch(seed()), run()), 2n):
  <_> 2n
def run_targets() -> Path(Tm[], map(Branch(seed()), Tm, lambda b. brTarget(seed(), b), run()), [target0(), target0()]):
  <_> [target0(), target0()]

def main() -> Nat:
  length(Branch(seed()), run())
