# formal/cubical/Kernel/RewriteCertificate.agda, in Bend.
# The syntax Tm, the step relation (WITH reverse: a groupoid), proof-relevant
# derivations, one-hypothesis induction certificates, the evaluation
# standpoint, and soundness of everything against it.
import Prelude

type Tm:
  case @var:
  case @yvar:
  case @zvar:
  case @uvar:
  case @vvar:
  case @wvar:
  case @zero:
  case @suc:
    t: Tm
  case @add:
    l: Tm
    r: Tm

# Step x y, an indexed family: each constructor fixes its endpoints by equations
type Step(x: Tm, y: Tm):
  case @add_zero:
    t: Tm
    ex: Tm{x == @add{t, @zero}}
    ey: Tm{y == t}
  case @add_suc:
    l: Tm
    r: Tm
    ex: Tm{x == @add{l, @suc{r}}}
    ey: Tm{y == @suc{@add{l, r}}}
  case @suc_step:
    a: Tm
    b: Tm
    s: Step(a, b)
    ex: Tm{x == @suc{a}}
    ey: Tm{y == @suc{b}}
  case @add_left:
    a: Tm
    b: Tm
    s: Step(a, b)
    z: Tm
    ex: Tm{x == @add{a, z}}
    ey: Tm{y == @add{b, z}}
  case @add_right:
    z: Tm
    a: Tm
    b: Tm
    s: Step(a, b)
    ex: Tm{x == @add{z, a}}
    ey: Tm{y == @add{z, b}}
  case @reverse:
    s: Step(y, x)

type Derivation(x: Tm, z: Tm):
  case @done:
    e: Tm{z == x}
  case @then:
    y: Tm
    s: Step(x, y)
    d: Derivation(y, z)

def subVar(u: Tm, t: Tm) -> Tm:
  match t:
    case @var{}: u
    case @yvar{}: @yvar
    case @zvar{}: @zvar
    case @uvar{}: @uvar
    case @vvar{}: @vvar
    case @wvar{}: @wvar
    case @zero{}: @zero
    case @suc{a}: @suc{subVar(u, a)}
    case @add{l, r}: @add{subVar(u, l), subVar(u, r)}

# the executable meaning: var by an environment of six coordinates
type Env:
  case @env:
    x: Nat
    y: Nat
    z: Nat
    u: Nat
    v: Nat
    w: Nat

def eval(t: Tm, r: Env) -> Nat:
  match t:
    case @var{}: match r: case @env{x, y, z, u, v, w}: x
    case @yvar{}: match r: case @env{x, y, z, u, v, w}: y
    case @zvar{}: match r: case @env{x, y, z, u, v, w}: z
    case @uvar{}: match r: case @env{x, y, z, u, v, w}: u
    case @vvar{}: match r: case @env{x, y, z, u, v, w}: v
    case @wvar{}: match r: case @env{x, y, z, u, v, w}: w
    case @zero{}: 0n
    case @suc{a}: 1n + eval(a, r)
    case @add{l, rr}: add(eval(l, r), eval(rr, r))

# every step preserves meaning
def step_sound(a: Tm, b: Tm, s: Step(a, b), r: Env) -> Path(Nat, eval(a, r), eval(b, r)):
  match s:
    case @add_zero{t, ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          plusZero(eval(t, r))
    case @add_suc{l, rr, ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          plusSuc(eval(l, r), eval(rr, r))
    case @suc_step{a2, b2, s2, ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          <i> 1n + (step_sound(a2, b2, s2, r) @ i)
    case @add_left{a2, b2, s2, z, ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          <i> add(step_sound(a2, b2, s2, r) @ i, eval(z, r))
    case @add_right{z, a2, b2, s2, ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          <i> add(eval(z, r), step_sound(a2, b2, s2, r) @ i)
    case @reverse{s2}:
      <i> step_sound(b, a, s2, r) @ inot(i)

def derivation_sound(a: Tm, b: Tm, d: Derivation(a, b), r: Env) -> Path(Nat, eval(a, r), eval(b, r)):
  match d:
    case @done{e}:
      match e: case {==}:
        <_> eval(a, r)
    case @then{y, s, d2}:
      compPath(Nat, eval(a, r), eval(y, r), eval(b, r), step_sound(a, y, s, r), derivation_sound(y, b, d2, r))

# the accepted rule: x + 1 -> suc x
def accepted() -> Derivation(@add{@var, @suc{@zero}}, @suc{@var}):
  @then{@suc{@add{@var, @zero}}, @add_suc{@var, @zero, {==}, {==}},
    @then{@suc{@var}, @suc_step{@add{@var, @zero}, @var, @add_zero{@var, {==}, {==}}, {==}, {==}},
      @done{{==}}}}

def accepted_sound(r: Env) -> Path(Nat, eval(@add{@var, @suc{@zero}}, r), eval(@suc{@var}, r)):
  derivation_sound(@add{@var, @suc{@zero}}, @suc{@var}, accepted(), r)

def main() -> Nat:
  eval(@add{@var, @suc{@zero}}, @env{4n, 0n, 0n, 0n, 0n, 0n})

# ---- one-hypothesis induction certificates (the real inference rule)
type HypStep(ihL: Tm, ihR: Tm, x: Tm, y: Tm):
  case @lift_step:
    s: Step(x, y)
  case @hypothesis:
    ex: Tm{x == ihL}
    ey: Tm{y == ihR}
  case @reverse_hypothesis:
    ex: Tm{x == ihR}
    ey: Tm{y == ihL}
  case @hyp_suc:
    a: Tm
    b: Tm
    s: HypStep(ihL, ihR, a, b)
    ex: Tm{x == @suc{a}}
    ey: Tm{y == @suc{b}}
  case @hyp_add_left:
    a: Tm
    b: Tm
    s: HypStep(ihL, ihR, a, b)
    z: Tm
    ex: Tm{x == @add{a, z}}
    ey: Tm{y == @add{b, z}}
  case @hyp_add_right:
    z: Tm
    a: Tm
    b: Tm
    s: HypStep(ihL, ihR, a, b)
    ex: Tm{x == @add{z, a}}
    ey: Tm{y == @add{z, b}}

type HypDerivation(ihL: Tm, ihR: Tm, x: Tm, z: Tm):
  case @hyp_done:
    e: Tm{z == x}
  case @hyp_then:
    y: Tm
    s: HypStep(ihL, ihR, x, y)
    d: HypDerivation(ihL, ihR, y, z)

type InductionCertificate(lhs: Tm, rhs: Tm):
  case @cert:
    base: Derivation(subVar(@zero, lhs), subVar(@zero, rhs))
    step: HypDerivation(lhs, rhs, subVar(@suc{@var}, lhs), subVar(@suc{@var}, rhs))

def setX(n: Nat, r: Env) -> Env:
  match r:
    case @env{x, y, z, u, v, w}: @env{n, y, z, u, v, w}

def eval_subVar(t: Tm, body: Tm, r: Env) -> Path(Nat, eval(subVar(t, body), r), eval(body, setX(eval(t, r), r))):
  match body:
    case @var{}: match r: case @env{x, y, z, u, v, w}: <_> eval(t, @env{x, y, z, u, v, w})
    case @yvar{}: match r: case @env{x, y, z, u, v, w}: <_> y
    case @zvar{}: match r: case @env{x, y, z, u, v, w}: <_> z
    case @uvar{}: match r: case @env{x, y, z, u, v, w}: <_> u
    case @vvar{}: match r: case @env{x, y, z, u, v, w}: <_> v
    case @wvar{}: match r: case @env{x, y, z, u, v, w}: <_> w
    case @zero{}: <_> 0n
    case @suc{a}: <i> 1n + (eval_subVar(t, a, r) @ i)
    case @add{l, rr}: <i> add(eval_subVar(t, l, r) @ i, eval_subVar(t, rr, r) @ i)

def hyp_step_sound(ihL: Tm, ihR: Tm, a: Tm, b: Tm, s: HypStep(ihL, ihR, a, b), r: Env, ih: Path(Nat, eval(ihL, r), eval(ihR, r))) -> Path(Nat, eval(a, r), eval(b, r)):
  match s:
    case @lift_step{s2}: step_sound(a, b, s2, r)
    case @hypothesis{ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          ih
    case @reverse_hypothesis{ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          <i> ih @ inot(i)
    case @hyp_suc{a2, b2, s2, ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          <i> 1n + (hyp_step_sound(ihL, ihR, a2, b2, s2, r, ih) @ i)
    case @hyp_add_left{a2, b2, s2, z, ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          <i> add(hyp_step_sound(ihL, ihR, a2, b2, s2, r, ih) @ i, eval(z, r))
    case @hyp_add_right{z, a2, b2, s2, ex, ey}:
      match ex: case {==}:
        match ey: case {==}:
          <i> add(eval(z, r), hyp_step_sound(ihL, ihR, a2, b2, s2, r, ih) @ i)

def hyp_derivation_sound(ihL: Tm, ihR: Tm, a: Tm, b: Tm, d: HypDerivation(ihL, ihR, a, b), r: Env, ih: Path(Nat, eval(ihL, r), eval(ihR, r))) -> Path(Nat, eval(a, r), eval(b, r)):
  match d:
    case @hyp_done{e}:
      match e: case {==}:
        <_> eval(a, r)
    case @hyp_then{y, s, d2}:
      compPath(Nat, eval(a, r), eval(y, r), eval(b, r), hyp_step_sound(ihL, ihR, a, y, s, r, ih), hyp_derivation_sound(ihL, ihR, y, b, d2, r, ih))

# a checked base trace and successor trace, the hypothesis only at the
# predecessor, entail the equation at every environment: induction on x.
def induction_go(lhs: Tm, rhs: Tm, c: InductionCertificate(lhs, rhs), k: Nat, y0: Nat, z0: Nat, u0: Nat, v0: Nat, w0: Nat) -> Path(Nat, eval(lhs, @env{k, y0, z0, u0, v0, w0}), eval(rhs, @env{k, y0, z0, u0, v0, w0})):
  match c:
    case @cert{base, step}:
      match k:
        case 0n:
          compPath(Nat, eval(lhs, @env{0n, y0, z0, u0, v0, w0}), eval(subVar(@zero, lhs), @env{0n, y0, z0, u0, v0, w0}), eval(rhs, @env{0n, y0, z0, u0, v0, w0}),
            sym(Nat, eval(subVar(@zero, lhs), @env{0n, y0, z0, u0, v0, w0}), eval(lhs, @env{0n, y0, z0, u0, v0, w0}), eval_subVar(@zero, lhs, @env{0n, y0, z0, u0, v0, w0})),
            compPath(Nat, eval(subVar(@zero, lhs), @env{0n, y0, z0, u0, v0, w0}), eval(subVar(@zero, rhs), @env{0n, y0, z0, u0, v0, w0}), eval(rhs, @env{0n, y0, z0, u0, v0, w0}),
              derivation_sound(subVar(@zero, lhs), subVar(@zero, rhs), base, @env{0n, y0, z0, u0, v0, w0}),
              eval_subVar(@zero, rhs, @env{0n, y0, z0, u0, v0, w0})))
        case 1n + p:
          compPath(Nat, eval(lhs, @env{1n + p, y0, z0, u0, v0, w0}), eval(subVar(@suc{@var}, lhs), @env{p, y0, z0, u0, v0, w0}), eval(rhs, @env{1n + p, y0, z0, u0, v0, w0}),
            sym(Nat, eval(subVar(@suc{@var}, lhs), @env{p, y0, z0, u0, v0, w0}), eval(lhs, @env{1n + p, y0, z0, u0, v0, w0}), eval_subVar(@suc{@var}, lhs, @env{p, y0, z0, u0, v0, w0})),
            compPath(Nat, eval(subVar(@suc{@var}, lhs), @env{p, y0, z0, u0, v0, w0}), eval(subVar(@suc{@var}, rhs), @env{p, y0, z0, u0, v0, w0}), eval(rhs, @env{1n + p, y0, z0, u0, v0, w0}),
              hyp_derivation_sound(lhs, rhs, subVar(@suc{@var}, lhs), subVar(@suc{@var}, rhs), step, @env{p, y0, z0, u0, v0, w0}, induction_go(lhs, rhs, @cert{base, step}, p, y0, z0, u0, v0, w0)),
              eval_subVar(@suc{@var}, rhs, @env{p, y0, z0, u0, v0, w0})))

def induction_sound(lhs: Tm, rhs: Tm, c: InductionCertificate(lhs, rhs), r: Env) -> Path(Nat, eval(lhs, r), eval(rhs, r)):
  match r:
    case @env{x, y, z, u, v, w}: induction_go(lhs, rhs, c, x, y, z, u, v, w)
