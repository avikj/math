//! Native evaluator, first brick: the calculus of abstract 04
//! ("rewriting without matching"), mirroring formal/cubical/kernel/
//! RewriteCertificate.agda. The Agda kernel is the reference semantics;
//! every structure here must agree with it.
//!
//! Commitments carried from the corpus (do not regress):
//!  - Step includes `Reverse` as a CONSTRUCTOR: derivations are a groupoid,
//!    not a reduction order. No normal-form assumption anywhere in the
//!    derivation algebra.
//!  - No matcher. A rule fires at one term; applicability is a supplied
//!    identification, never a search (abstract 04).
//!  - No dedup, no quotient, no sort: the frontier is a map and branch
//!    multiplicity is conserved (abstracts 20, 23).
//!  - The trusted boundary is the constructor: `Rule` cannot be built
//!    without a derivation in hand (module privacy = unforgeable by type).
//!  - `eval` is the lossy projection, kept OFF the operational path; it is
//!    used only to test soundness.

pub mod term {
    /// Closed inductive term type: six independent registers, zero, suc,
    /// add. No binders — nothing to capture, no alpha, no freshness.
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub enum Tm {
        Var,
        YVar,
        ZVar,
        UVar,
        VVar,
        WVar,
        Zero,
        Suc(Box<Tm>),
        Add(Box<Tm>, Box<Tm>),
    }

    impl Tm {
        pub fn suc(t: Tm) -> Tm {
            Tm::Suc(Box::new(t))
        }
        pub fn add(l: Tm, r: Tm) -> Tm {
            Tm::Add(Box::new(l), Box::new(r))
        }
        /// unary n = sucⁿ zero
        pub fn unary(n: u64) -> Tm {
            let mut t = Tm::Zero;
            for _ in 0..n {
                t = Tm::suc(t);
            }
            t
        }
        /// iter_suc n t = sucⁿ t
        pub fn iter_suc(n: u64, t: Tm) -> Tm {
            let mut t = t;
            for _ in 0..n {
                t = Tm::suc(t);
            }
            t
        }
        /// Symbol size: the number of constructors.
        pub fn size(&self) -> u64 {
            match self {
                Tm::Suc(t) => 1 + t.size(),
                Tm::Add(l, r) => 1 + l.size() + r.size(),
                _ => 1,
            }
        }
    }

    /// Environment for the forgetful semantics: one value per register.
    #[derive(Clone, Copy, Debug)]
    pub struct Env {
        pub x: u64,
        pub y: u64,
        pub z: u64,
        pub u: u64,
        pub v: u64,
        pub w: u64,
    }

    /// The forgetful projection. Deliberately misaligned with the object
    /// calculus (the kernel's object addition recurses on the right; this
    /// host addition is primitive), so agreement is a genuine test, not a
    /// mirror.
    pub fn eval(t: &Tm, e: Env) -> u64 {
        match t {
            Tm::Var => e.x,
            Tm::YVar => e.y,
            Tm::ZVar => e.z,
            Tm::UVar => e.u,
            Tm::VVar => e.v,
            Tm::WVar => e.w,
            Tm::Zero => 0,
            Tm::Suc(t) => 1 + eval(t, e),
            Tm::Add(l, r) => eval(l, e) + eval(r, e),
        }
    }
}

pub mod derivation {
    use crate::term::Tm;

    /// One elementary motion. Two computation rules, three congruence
    /// rules, and a constructor for symmetry — exactly the generators of
    /// RewriteCertificate.Step.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Step {
        /// add t zero  ~>  t
        AddZero(Tm),
        /// add t (suc u)  ~>  suc (add t u)
        AddSuc(Tm, Tm),
        /// congruence under suc
        SucStep(Box<Step>),
        /// congruence in the left argument of add
        AddLeft(Box<Step>, Tm),
        /// congruence in the right argument of add
        AddRight(Tm, Box<Step>),
        /// symmetry, generative: double reversal is a syntactically
        /// distinct step. Every unit of cost in the system lives in the
        /// gap this opens (abstract 04).
        Reverse(Box<Step>),
    }

    impl Step {
        pub fn src(&self) -> Tm {
            match self {
                Step::AddZero(t) => Tm::add(t.clone(), Tm::Zero),
                Step::AddSuc(t, u) => Tm::add(t.clone(), Tm::suc(u.clone())),
                Step::SucStep(s) => Tm::suc(s.src()),
                Step::AddLeft(s, r) => Tm::add(s.src(), r.clone()),
                Step::AddRight(l, s) => Tm::add(l.clone(), s.src()),
                Step::Reverse(s) => s.tgt(),
            }
        }
        pub fn tgt(&self) -> Tm {
            match self {
                Step::AddZero(t) => t.clone(),
                Step::AddSuc(t, u) => Tm::suc(Tm::add(t.clone(), u.clone())),
                Step::SucStep(s) => Tm::suc(s.tgt()),
                Step::AddLeft(s, r) => Tm::add(s.tgt(), r.clone()),
                Step::AddRight(l, s) => Tm::add(l.clone(), s.tgt()),
                Step::Reverse(s) => s.src(),
            }
        }
    }

    /// A derivation: a composable chain of steps with matched endpoints.
    /// Concatenation is strictly associative and unital as data.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Derivation {
        src: Tm,
        tgt: Tm,
        steps: Vec<Step>,
    }

    #[derive(Debug)]
    pub enum DerivationError {
        EndpointMismatch { expected: Tm, found: Tm },
    }

    impl Derivation {
        /// The empty derivation at t (refl).
        pub fn done(t: Tm) -> Derivation {
            Derivation { src: t.clone(), tgt: t, steps: Vec::new() }
        }

        /// Extend by one step; the step's source must be the current
        /// target. An ill-composed next step fails to inhabit.
        pub fn then(mut self, s: Step) -> Result<Derivation, DerivationError> {
            if s.src() != self.tgt {
                return Err(DerivationError::EndpointMismatch {
                    expected: self.tgt.clone(),
                    found: s.src(),
                });
            }
            self.tgt = s.tgt();
            self.steps.push(s);
            Ok(self)
        }

        /// Concatenation: strictly associative, unital, as data.
        pub fn concat(mut self, other: Derivation) -> Result<Derivation, DerivationError> {
            if other.src != self.tgt {
                return Err(DerivationError::EndpointMismatch {
                    expected: self.tgt.clone(),
                    found: other.src,
                });
            }
            self.tgt = other.tgt;
            self.steps.extend(other.steps);
            Ok(self)
        }

        /// revD: reverse each step with the constructor, reverse the order.
        /// Grade-preserving: len (revD d) = len d.
        pub fn rev(&self) -> Derivation {
            Derivation {
                src: self.tgt.clone(),
                tgt: self.src.clone(),
                steps: self
                    .steps
                    .iter()
                    .rev()
                    .map(|s| Step::Reverse(Box::new(s.clone())))
                    .collect(),
            }
        }

        pub fn src(&self) -> &Tm {
            &self.src
        }
        pub fn tgt(&self) -> &Tm {
            &self.tgt
        }
        pub fn len(&self) -> u64 {
            self.steps.len() as u64
        }
        pub fn is_empty(&self) -> bool {
            self.steps.is_empty()
        }
        pub fn steps(&self) -> &[Step] {
            &self.steps
        }
    }
}

pub mod normalize {
    use crate::derivation::{Derivation, Step};
    use crate::term::Tm;

    /// Directed use of the two computation rules under congruence,
    /// returning the reached term WITH the derivation that reached it —
    /// the answer is a projection of this pair, never computed apart from
    /// its route. (Normalization is a strategy ON the groupoid, not a
    /// property of it.)
    pub fn normalize(t: &Tm) -> (Tm, Derivation) {
        let mut d = Derivation::done(t.clone());
        loop {
            match head_step(d.tgt()) {
                Some(s) => {
                    d = d.then(s).expect("head_step source matches by construction");
                }
                None => return (d.tgt().clone(), d),
            }
        }
    }

    /// Leftmost-outermost redex, lifted through congruence contexts.
    fn head_step(t: &Tm) -> Option<Step> {
        match t {
            Tm::Add(l, r) => match r.as_ref() {
                Tm::Zero => Some(Step::AddZero(l.as_ref().clone())),
                Tm::Suc(u) => Some(Step::AddSuc(l.as_ref().clone(), u.as_ref().clone())),
                _ => {
                    if let Some(s) = head_step(l) {
                        Some(Step::AddLeft(Box::new(s), r.as_ref().clone()))
                    } else {
                        head_step(r).map(|s| Step::AddRight(l.as_ref().clone(), Box::new(s)))
                    }
                }
            },
            Tm::Suc(inner) => head_step(inner).map(|s| Step::SucStep(Box::new(s))),
            _ => None,
        }
    }
}

pub mod rule {
    use crate::derivation::Derivation;
    use crate::term::Tm;

    /// An installed operation. Fields are private: a Rule cannot be
    /// constructed without a derivation in hand — the constructor is the
    /// trusted boundary, there is no second certificate language.
    #[derive(Clone, Debug)]
    pub struct Rule {
        lhs: Tm,
        rhs: Tm,
        derivation: Derivation,
    }

    #[derive(Debug)]
    pub enum RuleError {
        NotAtSource { rule_lhs: Tm, term: Tm },
    }

    /// install : Derivation lhs rhs -> Rule. The only way in.
    pub fn install(d: Derivation) -> Rule {
        Rule { lhs: d.src().clone(), rhs: d.tgt().clone(), derivation: d }
    }

    impl Rule {
        /// Fires at ONE term. The applicability condition is an
        /// identification of the input with the rule's single source —
        /// checked, not searched. No matcher exists in this system.
        pub fn apply(&self, t: &Tm) -> Result<(Tm, Derivation), RuleError> {
            if *t != self.lhs {
                return Err(RuleError::NotAtSource {
                    rule_lhs: self.lhs.clone(),
                    term: t.clone(),
                });
            }
            Ok((self.rhs.clone(), self.derivation.clone()))
        }

        pub fn lhs(&self) -> &Tm {
            &self.lhs
        }
        pub fn rhs(&self) -> &Tm {
            &self.rhs
        }
        /// The application arrives with a derivation about the
        /// application: rule, applicability, result and justification are
        /// one typed object.
        pub fn derivation(&self) -> &Derivation {
            &self.derivation
        }
    }
}

pub mod frontier {
    use crate::derivation::Derivation;

    /// Parallel exploration is a map over the frontier with no quotient,
    /// sort, or deduplication. The only invariant is multiplicity:
    /// identical-looking derivations must both survive, because no
    /// function of the meaning selects between routes.
    #[derive(Clone, Debug, Default)]
    pub struct Frontier {
        branches: Vec<Derivation>,
    }

    impl Frontier {
        pub fn new(branches: Vec<Derivation>) -> Frontier {
            Frontier { branches }
        }
        pub fn advance<F>(&self, f: F) -> Frontier
        where
            F: Fn(&Derivation) -> Vec<Derivation>,
        {
            Frontier {
                branches: self.branches.iter().flat_map(|d| f(d)).collect(),
            }
        }
        pub fn branch_count(&self) -> usize {
            self.branches.len()
        }
        pub fn branches(&self) -> &[Derivation] {
            &self.branches
        }
    }
}

#[cfg(test)]
mod tests {
    use super::derivation::{Derivation, Step};
    use super::frontier::Frontier;
    use super::normalize::normalize;
    use super::rule::install;
    use super::term::{eval, Env, Tm};

    fn envs() -> Vec<Env> {
        [0u64, 1, 2, 5, 11, 100]
            .iter()
            .map(|&x| Env { x, y: x + 1, z: 2 * x, u: 7, v: x * x, w: 3 })
            .collect()
    }

    /// Kernel demo, exactly: normalize (add var (suc zero)) reaches
    /// suc var by [AddSuc, SucStep(AddZero)] — the trace the Agda kernel
    /// prints in NATIVE_RECORDS (then-step (add-suc var zero)
    /// (then-step (suc-step (add-zero var)) (done (suc var)))).
    #[test]
    fn kernel_demo_trace() {
        let t = Tm::add(Tm::Var, Tm::suc(Tm::Zero));
        let (nf, d) = normalize(&t);
        assert_eq!(nf, Tm::suc(Tm::Var));
        assert_eq!(
            d.steps(),
            &[
                Step::AddSuc(Tm::Var, Tm::Zero),
                Step::SucStep(Box::new(Step::AddZero(Tm::Var))),
            ]
        );
    }

    /// derivation-sound: both endpoints of a route carry the same value
    /// in every environment. The forgetful projection is blind to the
    /// route — and only to the route.
    #[test]
    fn soundness_across_environments() {
        let cases = vec![
            Tm::add(Tm::Var, Tm::unary(4)),
            Tm::add(Tm::add(Tm::YVar, Tm::unary(2)), Tm::unary(3)),
            Tm::suc(Tm::add(Tm::ZVar, Tm::Zero)),
            Tm::add(Tm::UVar, Tm::add(Tm::VVar, Tm::unary(1))),
        ];
        for t in cases {
            let (nf, d) = normalize(&t);
            assert_eq!(*d.src(), t);
            assert_eq!(*d.tgt(), nf);
            for e in envs() {
                assert_eq!(eval(&t, e), eval(&nf, e));
            }
        }
    }

    /// winding-cost-is-unary-size and cost-equals-output-size:
    /// len (route for var + n) = n + 1 = size (sucⁿ var). An equation,
    /// not a bound: the route costs exactly the symbols it writes.
    #[test]
    fn cost_equals_output_size() {
        for n in 0..40u64 {
            let t = Tm::add(Tm::Var, Tm::unary(n));
            let (nf, d) = normalize(&t);
            assert_eq!(nf, Tm::iter_suc(n, Tm::Var));
            assert_eq!(d.len(), n + 1);
            assert_eq!(nf.size(), n + 1);
        }
    }

    /// revD: inversion is a constructor wrap, grade-preserving, endpoint-
    /// swapping, and sound (the reversed route's endpoints still agree
    /// under eval). No search is ever posed.
    #[test]
    fn reversal_is_free_and_sound() {
        let t = Tm::add(Tm::YVar, Tm::unary(6));
        let (nf, d) = normalize(&t);
        let r = d.rev();
        assert_eq!(r.len(), d.len());
        assert_eq!(*r.src(), nf);
        assert_eq!(*r.tgt(), t);
        for e in envs() {
            assert_eq!(eval(r.src(), e), eval(r.tgt(), e));
        }
    }

    /// Double reversal is syntactically distinct from the original: the
    /// groupoid is weak, and that gap is where cost lives. Do not
    /// "optimize" this into an identity.
    #[test]
    fn double_reversal_is_distinct() {
        let t = Tm::add(Tm::Var, Tm::unary(1));
        let (_, d) = normalize(&t);
        let rr = d.rev().rev();
        assert_eq!(rr.src(), d.src());
        assert_eq!(rr.tgt(), d.tgt());
        assert_eq!(rr.len(), d.len());
        assert_ne!(rr, d);
        for e in envs() {
            assert_eq!(eval(rr.src(), e), eval(rr.tgt(), e));
        }
    }

    /// install: a proved route becomes an operation that fires at its one
    /// source term with no matching, and arrives with its derivation.
    /// Off-source application is refused by the identification check.
    #[test]
    fn install_fires_at_one_term() {
        let t = Tm::add(Tm::Var, Tm::unary(2));
        let (nf, d) = normalize(&t);
        let op = install(d);
        let (out, cert) = op.apply(&t).expect("fires at its source");
        assert_eq!(out, nf);
        assert_eq!(*cert.src(), t);
        assert_eq!(*cert.tgt(), nf);
        assert!(op.apply(&Tm::add(Tm::Var, Tm::unary(3))).is_err());
    }

    /// Two different derivations, one output (GenerativeKernel): both
    /// survive the frontier. advance is a map — no dedup, no sort, no
    /// quotient; branch multiplicity is conserved.
    #[test]
    fn frontier_conserves_multiplicity() {
        let t = Tm::add(Tm::Var, Tm::unary(1));
        let (_, direct) = normalize(&t);
        // A detour: there and back and there again, same endpoints.
        let detour = direct
            .clone()
            .concat(direct.rev())
            .and_then(|d| d.concat(direct.clone()))
            .expect("endpoints match");
        assert_eq!(direct.tgt(), detour.tgt());
        assert_ne!(direct.len(), detour.len());
        for e in envs() {
            assert_eq!(eval(direct.tgt(), e), eval(detour.tgt(), e));
        }
        let f = Frontier::new(vec![direct.clone(), detour.clone()]);
        let advanced = f.advance(|d| vec![d.clone()]);
        assert_eq!(advanced.branch_count(), 2);
        // Even identical branches both survive.
        let twins = Frontier::new(vec![direct.clone(), direct.clone()]);
        assert_eq!(twins.advance(|d| vec![d.clone()]).branch_count(), 2);
    }

    /// Ill-composed histories fail to exist rather than being detected
    /// later: `then` and `concat` refuse an endpoint mismatch.
    #[test]
    fn ill_composed_runs_do_not_inhabit() {
        let d = Derivation::done(Tm::Var);
        assert!(d.then(Step::AddZero(Tm::YVar)).is_err());
        let a = Derivation::done(Tm::Var);
        let b = Derivation::done(Tm::YVar);
        assert!(a.concat(b).is_err());
    }
}
