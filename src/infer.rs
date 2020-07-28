use std::cmp::PartialEq;
use std::fmt::Display;
use std::hash::Hash;
use std::iter::FromIterator;

use im_rc::HashMap;
use im_rc::HashSet;

use log::{debug, error, trace, warn};

use crate::syntax::*;

/// d.1 or d.2
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Eliminator(HashMap<Variation, Side>);

impl VariationalType {
    pub fn apply(self, theta: &Subst) -> VariationalType {
        match self {
            VariationalType::Base(b) => VariationalType::Base(b),
            VariationalType::Fun(v1, v2) => VariationalType::fun(v1.apply(theta), v2.apply(theta)),
            VariationalType::Choice(d, v1, v2) => {
                VariationalType::choice(d, v1.apply(theta), v2.apply(theta))
            }
            VariationalType::Var(a) => match theta.lookup(&a) {
                None => VariationalType::Var(a),
                Some(v) => v.clone().apply(theta),
            },
        }
    }
}

impl MigrationalType {
    pub fn apply(self, theta: &Subst) -> MigrationalType {
        match self {
            MigrationalType::Dyn() => MigrationalType::Dyn(),
            MigrationalType::Base(b) => MigrationalType::Base(b),
            MigrationalType::Fun(m1, m2) => MigrationalType::fun(m1.apply(theta), m2.apply(theta)),
            MigrationalType::Choice(d, m1, m2) => {
                MigrationalType::choice(d, m1.apply(theta), m2.apply(theta))
            }
            MigrationalType::Var(a) => match theta.lookup(&a) {
                None => MigrationalType::Var(a),
                Some(v) => v.clone().apply(theta).into(),
            },
        }
    }

    pub fn eliminate(self, elim: &Eliminator) -> MigrationalType {
        match self {
            MigrationalType::Dyn() | MigrationalType::Base(_) | MigrationalType::Var(_) => self,
            MigrationalType::Fun(m1, m2) => {
                MigrationalType::fun(m1.eliminate(elim), m2.eliminate(elim))
            }
            MigrationalType::Choice(d, m1, m2) => match elim.get(&d) {
                Side::Right() => m2.eliminate(elim),
                Side::Left() => m1.eliminate(elim),
            },
        }
    }
}

impl TargetExpr {
    pub fn apply(self, theta: &Subst) -> TargetExpr {
        self.map_types(&|m: MigrationalType| m.apply(theta))
    }

    pub fn eliminate(self, elim: &Eliminator) -> TargetExpr {
        match self {
            Expr::Const(c) => Expr::Const(c),
            Expr::Var(x) => Expr::Var(x),
            Expr::Lam(x, t, e) => Expr::lam(x, t.eliminate(elim), e.eliminate(elim)),
            Expr::App(e1, e2) => Expr::app(e1.eliminate(elim), e2.eliminate(elim)),
            Expr::Ann(e, t) => Expr::ann(e.eliminate(elim), t.eliminate(elim)),
            Expr::If(e1, e2, e3) => {
                Expr::if_(e1.eliminate(elim), e2.eliminate(elim), e3.eliminate(elim))
            }
            Expr::Let(x, t, e1, e2) => {
                Expr::let_(x, t.eliminate(elim), e1.eliminate(elim), e2.eliminate(elim))
            }
            Expr::LetRec(defns, e2) => Expr::letrec(
                defns
                    .into_iter()
                    .map(|(v, t, e1)| (v, t.eliminate(elim), e1.eliminate(elim)))
                    .collect(),
                e2.eliminate(elim),
            ),
            Expr::UOp(op, e) => Expr::uop(op.eliminate(elim), e.eliminate(elim)),
            Expr::BOp(op, e1, e2) => {
                Expr::bop(op.eliminate(elim), e1.eliminate(elim), e2.eliminate(elim))
            }
        }
    }
}

impl TargetUOp {
    pub fn eliminate(self, _elim: &Eliminator) -> Self {
        self
    }
}

impl TargetBOp {
    pub fn eliminate(self, elim: &Eliminator) -> Self {
        match self {
            TargetBOp::Choice(d, op1, op2) => match elim.get(&d) {
                Side::Right() => op2.eliminate(elim),
                Side::Left() => op1.eliminate(elim),
            },
            _ => self,
        }
    }
}

/// pi
#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    Bot(),
    Top(),
    Choice(Variation, Option<Side>, Box<Pattern>, Box<Pattern>),
}

impl Pattern {
    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Pattern::Bot() => pp.text("⊥"),
            Pattern::Top() => pp.text("⊤"),
            Pattern::Choice(d, None, pat1, pat2) => pp.as_string(d).append(
                pp.intersperse(
                    vec![pat1.pretty(pp), pat2.pretty(pp).nest(1)],
                    pp.text(",").append(pp.line()),
                )
                .angles()
                .group(),
            ),
            Pattern::Choice(d, Some(Side::Left()), pat1, pat2) => pp.as_string(d).append(
                pp.intersperse(
                    vec![
                        pat1.pretty(pp).enclose(pp.text("*"), pp.nil()),
                        pat2.pretty(pp).nest(1),
                    ],
                    pp.text(",").append(pp.line()),
                )
                .angles()
                .group(),
            ),
            Pattern::Choice(d, Some(Side::Right()), pat1, pat2) => pp.as_string(d).append(
                pp.intersperse(
                    vec![
                        pat1.pretty(pp),
                        pat2.pretty(pp).enclose(pp.text("*"), pp.nil()).nest(1),
                    ],
                    pp.text(",").append(pp.line()),
                )
                .angles()
                .group(),
            ),
        }
    }

    pub fn select(self, d: Variation, side: Side) -> Pattern {
        match self {
            Pattern::Bot() => Pattern::Bot(),
            Pattern::Top() => Pattern::Top(),
            Pattern::Choice(d2, bias, pat1, pat2) => {
                if d == d2 {
                    match side {
                        Side::Left() => *pat1, // shouldn't need recursive select---each variation should appear only once (invariant maintained in Pattern::choice)
                        Side::Right() => *pat2,
                    }
                } else {
                    Pattern::Choice(
                        d2,
                        bias,
                        Box::new(pat1.select(d, side)),
                        Box::new(pat2.select(d, side)),
                    )
                }
            }
        }
    }

    pub fn choice(d: Variation, pat1: Pattern, pat2: Pattern) -> Pattern {
        Pattern::choice_(d, None, pat1, pat2)
    }

    pub fn biased_choice(d: Variation, bias: Side, pat1: Pattern, pat2: Pattern) -> Pattern {
        Pattern::choice_(d, Some(bias), pat1, pat2)
    }

    pub fn choice_(d: Variation, bias: Option<Side>, pat1: Pattern, pat2: Pattern) -> Pattern {
        if pat1 == pat2 {
            pat1
        } else {
            Pattern::Choice(
                d,
                bias,
                Box::new(pat1.select(d, Side::Left())),
                Box::new(pat2.select(d, Side::Right())),
            )
        }
    }

    pub fn meet(&self, other: Pattern) -> Pattern {
        match self {
            Pattern::Top() => other,
            Pattern::Bot() => Pattern::Bot(),
            Pattern::Choice(d1, bias1, pat11, pat12) => match other {
                Pattern::Choice(d2, bias2, pat21, pat22) if *d1 == d2 => {
                    let bias = match (bias1, bias2) {
                        (Some(_), Some(_)) | (None, None) => None,
                        (Some(bias), None) => Some(*bias),
                        (None, Some(bias)) => Some(bias),
                    };
                    Pattern::choice_(*d1, bias, pat11.meet(*pat21), pat12.meet(*pat22))
                }
                _ => Pattern::choice_(*d1, *bias1, pat11.meet(other.clone()), pat12.meet(other)),
            },
        }
    }

    pub fn valid_eliminators(self) -> HashSet<Eliminator> {
        match self {
            Pattern::Top() => HashSet::unit(Eliminator::new()),
            Pattern::Bot() => HashSet::new(),
            Pattern::Choice(d, bias, pi1, pi2) => {
                let ves1: HashSet<Eliminator> = pi1
                    .valid_eliminators()
                    .into_iter()
                    .map(|ve| ve.update(d, Side::Left()))
                    .collect();
                let ves2: HashSet<Eliminator> = pi2
                    .valid_eliminators()
                    .into_iter()
                    .map(|ve| ve.update(d, Side::Right()))
                    .collect();

                match bias {
                    Some(Side::Left()) if !ves1.is_empty() => ves1,
                    Some(Side::Right()) if !ves2.is_empty() => ves2,
                    _ => ves1.union(ves2),
                }
            }
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl From<bool> for Pattern {
    fn from(b: bool) -> Self {
        if b {
            Pattern::Top()
        } else {
            Pattern::Bot()
        }
    }
}

impl Eliminator {
    pub fn new() -> Self {
        Eliminator(HashMap::new())
    }

    pub fn get(&self, d: &Variation) -> Side {
        let side = self.0.get(d);

        match side {
            None => {
                warn!("No choice for variation {}; can't go wrong going right", d);
                return Side::default();
            }
            Some(side) => *side,
        }
    }

    pub fn update(self, d: Variation, side: Side) -> Self {
        Eliminator(self.0.update(d, side))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn expand(self, ds: &HashSet<&Variation>) -> Self {
        let mut elim = self;

        for d in ds.iter() {
            if elim.0.get(d) != Some(&Side::Left()) {
                elim = elim.update(**d, Side::Right());
            }
        }

        elim
    }

    pub fn score(&self) -> usize {
        self.0
            .iter()
            .filter(|(_d, side)| **side == Side::Right())
            .count()
    }
}

impl Display for Eliminator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, (d, side)) in self.0.iter().enumerate() {
            write!(f, "{}.{}", *d, side)?;

            if i != self.0.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "}}")
    }
}

/// C
///
/// we treat /\ and epsilon by just using vectors in `Constraints`, below
#[derive(Clone, Debug)]
pub enum Constraint {
    Consistent(Pattern, MigrationalType, MigrationalType),
    Ground(Pattern, MigrationalType, BaseType), // TODO ultimately need our own notion of ground type
    Choice(Variation, Option<Side>, Constraints, Constraints),
}

#[derive(Clone, Debug)]
pub struct Constraints(pub(super) Vec<Constraint>);

impl Constraint {
    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Constraint::Consistent(pi, m1, m2) => pp
                .intersperse(
                    vec![
                        m1.pretty(pp),
                        pp.text("≈").append(pi.pretty(pp)),
                        m2.pretty(pp),
                    ],
                    pp.line(),
                )
                .group(),
            Constraint::Ground(pi, m, b) => pp.intersperse(
                vec![
                    m.pretty(pp),
                    pp.text("=").append(pi.pretty(pp)),
                    pp.as_string(MigrationalType::Base(*b)),
                ],
                pp.line(),
            ),
            Constraint::Choice(d, None, cs1, cs2) => pp
                .as_string(d)
                .append(
                    cs1.pretty(pp)
                        .append(pp.text(","))
                        .append(pp.line())
                        .append(cs2.pretty(pp).nest(1))
                        .angles(),
                )
                .group(),
            Constraint::Choice(d, Some(Side::Left()), cs1, cs2) => pp
                .as_string(d)
                .append(
                    cs1.pretty(pp)
                        .enclose(pp.text("*"), pp.nil())
                        .append(pp.text(","))
                        .append(pp.line())
                        .append(cs2.pretty(pp).nest(1))
                        .angles(),
                )
                .group(),
            Constraint::Choice(d, Some(Side::Right()), cs1, cs2) => pp
                .as_string(d)
                .append(
                    cs1.pretty(pp)
                        .append(pp.text(","))
                        .append(pp.line())
                        .append(cs2.pretty(pp).enclose(pp.text("*"), pp.nil()).nest(1))
                        .angles(),
                )
                .group(),
        }
    }

    pub fn and(self, other: Constraint) -> Constraints {
        Constraints(vec![self, other])
    }

    pub fn apply(self, theta: &Subst) -> Constraint {
        match self {
            Constraint::Consistent(pi, m1, m2) => {
                Constraint::Consistent(pi, m1.apply(theta), m2.apply(theta))
            }
            Constraint::Ground(pi, m, b) => Constraint::Ground(pi, m.apply(theta), b),
            Constraint::Choice(d, bias, cs1, cs2) => {
                Constraint::Choice(d, bias, cs1.apply(theta), cs2.apply(theta))
            }
        }
    }
}

impl Constraints {
    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        if self.0.is_empty() {
            pp.text("ε")
        } else {
            pp.intersperse(
                self.0.iter().map(|c| c.pretty(pp)),
                pp.text("⋀").enclose(pp.space(), pp.space()),
            )
        }
    }

    pub fn epsilon() -> Constraints {
        Constraints(Vec::new())
    }

    pub fn and(&mut self, c: Constraint) {
        self.0.push(c);
    }

    pub fn and_many(&mut self, mut other: Constraints) {
        self.0.append(&mut other.0);
    }

    pub fn apply(self, theta: &Subst) -> Constraints {
        Constraints(self.0.into_iter().map(|c| c.apply(theta)).collect())
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl Display for Constraints {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl From<Constraint> for Constraints {
    fn from(c: Constraint) -> Self {
        Constraints(vec![c])
    }
}

// Gamma
#[derive(Clone, Debug)]
pub struct Ctx(HashMap<Variable, MigrationalType>);

impl Ctx {
    pub fn empty() -> Self {
        Ctx(HashMap::new())
    }

    pub fn extend(&self, x: Variable, m: MigrationalType) -> Self {
        Ctx(self.0.update(x, m))
    }

    pub fn lookup(&self, x: &Variable) -> Option<&MigrationalType> {
        self.0.get(x)
    }
}

// theta
#[derive(Clone, Debug)]
pub struct Subst(pub(super) HashMap<TypeVariable, VariationalType>);

impl Subst {
    pub fn empty() -> Self {
        Subst(HashMap::new())
    }

    pub fn extend(&self, a: TypeVariable, v: VariationalType) -> Self {
        Subst(self.0.update(a, v))
    }

    pub fn lookup(&self, a: &TypeVariable) -> Option<&VariationalType> {
        self.0.get(a)
    }

    pub fn compose(self, other: Subst) -> Subst {
        let composed: HashMap<_, _> = other
            .0
            .into_iter()
            .map(|(a, v)| (a, v.apply(&self)))
            .collect();

        Subst(composed.union(self.0)) // prioritizes mappings in composed over self
    }
}

impl Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, (a, v)) in self.0.iter().enumerate() {
            write!(f, "{}↦{}", a, v)?;

            if i < self.0.len() - 1 {
                write!(f, ", ")?;
            }
        }

        write!(f, "}}")
    }
}

/// Configuration options for type inference
pub struct Options {
    /// How should conditional branches of different types be treated?
    ///
    /// Consider `if b then 5 else false`. Campora et al. would simply reject
    /// this program, but it can reasonably be typed at `?`. With `strict_ifs`
    /// set, we behave like Campora et al. Without it, the program will have
    /// type `?`.
    pub strict_ifs: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options { strict_ifs: false }
    }
}

pub struct TypeInference {
    pub options: Options,
    next_variable: usize,
    next_variation: usize,
    pattern: Pattern,
    constraints: Constraints,
}

impl TypeInference {
    pub fn new(options: Options) -> TypeInference {
        TypeInference {
            options,
            next_variable: 0,
            next_variation: 0,
            pattern: Pattern::Top(),
            constraints: Constraints::epsilon(),
        }
    }

    fn fresh_variable(&mut self) -> TypeVariable {
        let next = self.next_variable;
        self.next_variable += 1;
        TypeVariable(next)
    }

    fn fresh_variation(&mut self) -> Variation {
        let next = self.next_variation;
        self.next_variation += 1;
        Variation(next)
    }

    fn add_constraint(&mut self, c: Constraint) {
        self.constraints.and(c);
    }

    fn add_constraints(&mut self, cs: Constraints) {
        self.constraints.and_many(cs);
    }

    fn add_pattern(&mut self, p: Pattern) {
        self.pattern = self.pattern.meet(p);
    }

    fn generate_constraints(
        &mut self,
        ctx: Ctx,
        e: &SourceExpr,
    ) -> Option<(TargetExpr, MigrationalType)> {
        match e {
            Expr::Const(c) => Some((Expr::Const(c.clone()), c.into())),
            Expr::Var(x) => {
                debug!("looking up {} in {:?}", x, ctx);
                let m = ctx.lookup(x)?;
                Some((Expr::Var(x.clone()), m.clone()))
            }
            Expr::Lam(x, t, e) => {
                let m_dom = self.freshen_annotation(t);

                let (e, m_cod) =
                    self.generate_constraints(ctx.extend(x.clone(), m_dom.clone().into()), e)?;

                let m_dom: MigrationalType = m_dom.clone().into();
                Some((
                    Expr::lam(x.clone(), m_dom.clone(), e),
                    MigrationalType::fun(m_dom, m_cod),
                ))
            }
            Expr::Ann(e, t) => {
                let (e, m) = self.generate_constraints(ctx, e)?;

                let m_ann = self.freshen_annotation(t);

                self.add_constraint(Constraint::Consistent(
                    Pattern::Top(),
                    m.clone(),
                    m_ann.clone(),
                ));

                Some((Expr::ann(e, m), m_ann))
            }
            Expr::App(e_fun, e_arg) => {
                let (e_fun, m_fun) = self.generate_constraints(ctx.clone(), e_fun)?;
                let (e_arg, m_arg) = self.generate_constraints(ctx, e_arg)?;

                let (m_res, cs_res, pat_res) = self.cod(&m_fun);
                self.add_constraints(cs_res);
                self.add_pattern(pat_res);
                let (cs_arg, pat_arg) = self.dom(&m_fun, &m_arg);
                self.add_constraints(cs_arg);
                self.add_pattern(pat_arg);

                Some((Expr::app(e_fun, e_arg), m_res))
            }
            Expr::If(e_cond, e_then, e_else) => {
                // ??? MMG this rule isn't in the paper... but annotations are? :(
                let (e_cond, m_cond) = self.generate_constraints(ctx.clone(), e_cond)?;
                let (e_then, m_then) = self.generate_constraints(ctx.clone(), e_then)?;
                let (e_else, m_else) = self.generate_constraints(ctx, e_else)?;

                self.add_constraint(Constraint::Consistent(
                    Pattern::Top(),
                    m_cond,
                    MigrationalType::bool(),
                ));

                let (m_res, c_res, pi_res) = self.meet(&m_then, &m_else);
                debug!(
                    "if constraints on {} and {}: {} (pi={})",
                    m_then, m_else, c_res, pi_res
                );
                self.add_pattern(pi_res);
                self.add_constraints(c_res);

                Some((Expr::if_(e_cond, e_then, e_else), m_res))
            }
            Expr::Let(x, t, e_def, e_body) => {
                let (e_def, m_def) = self.generate_constraints(ctx.clone(), e_def)?;

                let m_def = match t {
                    Some(t) => {
                        let m = self.freshen_gradual_type(t);

                        self.add_constraint(Constraint::Consistent(
                            Pattern::Top(),
                            m.clone(),
                            m_def.clone(),
                        ));

                        m
                    }
                    None => m_def,
                };

                let (e_body, m_body) =
                    self.generate_constraints(ctx.extend(x.clone(), m_def.clone()), e_body)?;

                Some((Expr::let_(x.clone(), m_def, e_def, e_body), m_body))
            }
            Expr::LetRec(defns, e_body) => {
                // extend context, mapping each variable to either its annotation or a fresh variable
                let mut ctx = ctx.clone();
                for (x, t, _) in defns.iter() {
                    ctx = ctx.extend(x.clone(), self.freshen_annotation(t));
                }

                let mut e_defns: Vec<(Variable, MigrationalType, TargetExpr)> = Vec::new();
                e_defns.reserve(defns.len());
                for (x, _, e) in defns.iter() {
                    // generate constraints for defn
                    let (e, m) = self.generate_constraints(ctx.clone(), e)?;

                    let m_annot = ctx.lookup(x).unwrap();

                    // ensure annotation matches
                    self.add_constraint(Constraint::Consistent(Pattern::Top(), m, m_annot.clone()));

                    // use annotation in resulting term
                    e_defns.push((x.clone(), m_annot.clone(), e));
                }

                let (e_body, m_body) = self.generate_constraints(ctx, e_body)?;

                Some((Expr::letrec(e_defns, e_body), m_body))
            }
            Expr::UOp(op, e) => {
                let (e, m) = self.generate_constraints(ctx.clone(), e)?;

                let (op, m_dom, m_cod) = self.uop(op);

                self.add_constraint(Constraint::Consistent(Pattern::Top(), m, m_dom));

                Some((Expr::uop(op, e), m_cod))
            }
            Expr::BOp(SourceBOp::Equal, e1, e2) => {
                let (e1, m1) = self.generate_constraints(ctx.clone(), e1)?;
                let (e2, m2) = self.generate_constraints(ctx.clone(), e2)?;

                let (mut op, mut m_dom, mut m_cod) = (
                    TargetBOp::EqualDyn,
                    MigrationalType::Dyn(),
                    MigrationalType::bool(),
                );
                let mut cs = Constraints::epsilon();

                for (op2, b_dom2, m_cod2) in vec![
                    (
                        TargetBOp::EqualBool,
                        BaseType::Bool,
                        MigrationalType::bool(),
                    ),
                    (TargetBOp::EqualInt, BaseType::Int, MigrationalType::bool()),
                ]
                .into_iter()
                {
                    let d = self.fresh_variation();

                    op = TargetBOp::choice(d, op, op2);
                    let cs2 = Constraints(vec![
                        Constraint::Ground(Pattern::Top(), m1.clone(), b_dom2),
                        Constraint::Ground(Pattern::Top(), m2.clone(), b_dom2),
                    ]);

                    cs = Constraint::Choice(d, Some(Side::Right()), cs, cs2).into();
                    m_dom =
                        MigrationalType::choice(d, m_dom.clone(), MigrationalType::Base(b_dom2));
                    m_cod = MigrationalType::choice(d, m_cod.clone(), m_cod2);
                }

                self.add_constraints(cs);

                Some((Expr::bop(op, e1, e2), m_cod))
            }
            Expr::BOp(op, e1, e2) => {
                let (e1, m1) = self.generate_constraints(ctx.clone(), e1)?;
                let (e2, m2) = self.generate_constraints(ctx.clone(), e2)?;

                let mut ops = self.bop(op).into_iter();
                let (mut op, mut m_dom, mut m_cod) = ops
                    .next()
                    .expect("need at least one option for each binary operation");
                let mut cs = Constraints(vec![
                    Constraint::Consistent(Pattern::Top(), m_dom.clone(), m1.clone()),
                    Constraint::Consistent(Pattern::Top(), m_dom.clone(), m2.clone()),
                ]);

                for (op2, m_dom2, m_cod2) in ops {
                    let d = self.fresh_variation();

                    op = TargetBOp::choice(d, op, op2);
                    let cs2 = Constraints(vec![
                        Constraint::Consistent(Pattern::Top(), m_dom2.clone(), m1.clone()),
                        Constraint::Consistent(Pattern::Top(), m_dom2.clone(), m2.clone()),
                    ]);

                    cs = Constraint::Choice(d, Some(Side::Right()), cs, cs2).into();
                    m_dom = MigrationalType::choice(d, m_dom.clone(), m_dom2);
                    m_cod = MigrationalType::choice(d, m_cod.clone(), m_cod2);
                }

                self.add_constraints(cs);

                Some((Expr::bop(op, e1, e2), m_cod))
            }
        }
    }

    /// Returns the sole possibility for a unary operation, i.e.
    ///    [(op, dom, cod), ...]
    /// where `op` is a target operation, `dom` is the domain type, and `cod` is the return type.
    fn uop(&mut self, op: &SourceUOp) -> (TargetUOp, MigrationalType, MigrationalType) {
        match op {
            SourceUOp::Negate => (
                TargetUOp::Negate,
                MigrationalType::int(),
                MigrationalType::int(),
            ),
            SourceUOp::Not => (
                TargetUOp::Not,
                MigrationalType::bool(),
                MigrationalType::bool(),
            ),
        }
    }

    /// Returns a list of possibilities:
    ///
    ///   [(op, dom, cod), ...]
    ///
    /// where `op` is a target operation, `dom` is the domain type, and `cod` is
    /// the return type.
    ///
    /// INVARIANT: make the dynamic one first, in order to "prefer" a typed
    /// answer when there aren't any real constraints
    fn bop(&mut self, op: &SourceBOp) -> Vec<(TargetBOp, MigrationalType, MigrationalType)> {
        match op {
            SourceBOp::And => vec![(
                TargetBOp::And,
                MigrationalType::bool(),
                MigrationalType::bool(),
            )],
            SourceBOp::Or => vec![(
                TargetBOp::Or,
                MigrationalType::bool(),
                MigrationalType::bool(),
            )],
            SourceBOp::Plus => vec![(
                TargetBOp::Plus,
                MigrationalType::int(),
                MigrationalType::int(),
            )],
            SourceBOp::Minus => vec![(
                TargetBOp::Minus,
                MigrationalType::int(),
                MigrationalType::int(),
            )],
            SourceBOp::Times => vec![(
                TargetBOp::Times,
                MigrationalType::int(),
                MigrationalType::int(),
            )],
            SourceBOp::Divide => vec![(
                TargetBOp::Divide,
                MigrationalType::int(),
                MigrationalType::int(),
            )],
            SourceBOp::LessThan => vec![(
                TargetBOp::LessThan,
                MigrationalType::int(),
                MigrationalType::bool(),
            )],
            SourceBOp::LessThanEqual => vec![(
                TargetBOp::LessThanEqual,
                MigrationalType::int(),
                MigrationalType::bool(),
            )],
            SourceBOp::Equal => vec![
                (
                    TargetBOp::EqualDyn,
                    MigrationalType::Dyn(),
                    MigrationalType::bool(),
                ),
                (
                    TargetBOp::EqualBool,
                    MigrationalType::bool(),
                    MigrationalType::bool(),
                ),
                (
                    TargetBOp::EqualInt,
                    MigrationalType::int(),
                    MigrationalType::bool(),
                ),
            ],
        }
    }

    fn dyn_to_var(&mut self, m: &MigrationalType) -> MigrationalType {
        match m {
            MigrationalType::Dyn() => MigrationalType::Var(self.fresh_variable()),
            MigrationalType::Base(b) => MigrationalType::Base(b.clone()),
            MigrationalType::Var(a) => MigrationalType::Var(*a),
            MigrationalType::Choice(d, m1, m2) => {
                MigrationalType::choice(*d, self.dyn_to_var(m1), self.dyn_to_var(m2))
            }
            MigrationalType::Fun(m1, m2) => {
                MigrationalType::fun(self.dyn_to_var(m1), self.dyn_to_var(m2))
            }
        }
    }

    fn freshen_gradual_type(&mut self, g: &GradualType) -> MigrationalType {
        let m: MigrationalType = g.clone().into();

        if m.has_dyn() {
            let d = self.fresh_variation();
            let m_var = self.dyn_to_var(&m);
            MigrationalType::choice(d, m, m_var)
        } else {
            m
        }
    }

    fn freshen_annotation(&mut self, g: &Option<GradualType>) -> MigrationalType {
        match g {
            None => MigrationalType::Var(self.fresh_variable()),
            Some(g) => self.freshen_gradual_type(g),
        }
    }

    fn dom(&mut self, m_fun: &MigrationalType, m_arg: &MigrationalType) -> (Constraints, Pattern) {
        match m_fun {
            MigrationalType::Dyn() => (Constraints::epsilon(), Pattern::Top()),
            MigrationalType::Fun(m_dom, _m_cod) => (
                // ??? MMG paper just says pi here (p15)
                Constraint::Consistent(Pattern::Top(), *m_dom.clone(), m_arg.clone()).into(),
                Pattern::Top(),
            ),
            MigrationalType::Var(alpha) => {
                let k1 = self.fresh_variable();
                let k2 = self.fresh_variable();
                let real_fun =
                    MigrationalType::fun(MigrationalType::Var(k1), MigrationalType::Var(k2));
                (
                    Constraint::Consistent(Pattern::Top(), MigrationalType::Var(*alpha), real_fun)
                        .and(Constraint::Consistent(
                            Pattern::Top(),
                            MigrationalType::Var(k1),
                            m_arg.clone(), // ??? MMG paper says M2, but that's not well scoped
                        )),
                    Pattern::Top(), // ??? MMG paper just says pi here
                )
            }
            MigrationalType::Choice(d, m_fun1, m_fun2) => {
                let (cs1, pat1) = self.dom(m_fun1, m_arg);
                let (cs2, pat2) = self.dom(m_fun2, m_arg);

                (
                    Constraint::Choice(*d, None, cs1, cs2).into(),
                    Pattern::choice(*d, pat1, pat2),
                )
            }
            _ => (Constraints::epsilon(), Pattern::Bot()),
        }
    }

    fn cod(&mut self, m_fun: &MigrationalType) -> (MigrationalType, Constraints, Pattern) {
        match m_fun {
            MigrationalType::Dyn() => (
                MigrationalType::Dyn(),
                Constraints::epsilon(),
                Pattern::Top(),
            ),
            MigrationalType::Fun(_m_dom, m_cod) => {
                (*m_cod.clone(), Constraints::epsilon(), Pattern::Top())
            }
            MigrationalType::Var(alpha) => {
                let k1 = self.fresh_variable();
                let k2 = self.fresh_variable();
                let real_fun =
                    MigrationalType::fun(MigrationalType::Var(k1), MigrationalType::Var(k2));
                (
                    MigrationalType::Var(k2),
                    Constraint::Consistent(Pattern::Top(), MigrationalType::Var(*alpha), real_fun)
                        .into(),
                    Pattern::Top(), // ??? MMG paper just says pi
                )
            }
            MigrationalType::Choice(d, m_fun1, m_fun2) => {
                let (m1, cs1, pat1) = self.cod(m_fun1);
                let (m2, cs2, pat2) = self.cod(m_fun2);

                (
                    MigrationalType::choice(*d, m1, m2),
                    Constraint::Choice(*d, None, cs1, cs2).into(),
                    Pattern::choice(*d, pat1, pat2),
                )
            }
            _ => (
                MigrationalType::Var(self.fresh_variable()),
                Constraints::epsilon(),
                Pattern::Bot(),
            ),
        }
    }

    fn meet(
        &mut self,
        m1: &MigrationalType,
        m2: &MigrationalType,
    ) -> (MigrationalType, Constraints, Pattern) {
        trace!("meet({}, {})", m1, m2);
        match (m1, m2) {
            (MigrationalType::Var(a), m) | (m, MigrationalType::Var(a)) => {
                let alpha = MigrationalType::Var(*a);

                (
                    alpha.clone(),
                    Constraint::Consistent(Pattern::Top(), alpha, m.clone()).into(),
                    Pattern::Top(),
                )
            }
            (MigrationalType::Dyn(), m) | (m, MigrationalType::Dyn()) => {
                (m.clone(), Constraints::epsilon(), Pattern::Top())
            }
            (MigrationalType::Choice(d, m1, m2), m) | (m, MigrationalType::Choice(d, m1, m2)) => {
                let (m1, cs1, pat1) = self.meet(m1, m);
                let (m2, cs2, pat2) = self.meet(m2, m);

                (
                    MigrationalType::choice(*d, m1, m2),
                    Constraint::Choice(*d, None, cs1, cs2).into(),
                    Pattern::choice(*d, pat1, pat2),
                )
            }
            (MigrationalType::Fun(m11, m12), MigrationalType::Fun(m21, m22)) => {
                let (m1, mut cs1, pat1) = self.meet(m11, m21);
                let (m2, cs2, pat2) = self.meet(m12, m22);

                cs1.and_many(cs2);

                (MigrationalType::fun(m1, m2), cs1, pat1.meet(pat2))
            }
            (MigrationalType::Base(b1), MigrationalType::Base(b2)) if b1 == b2 => {
                (m1.clone(), Constraints::epsilon(), Pattern::Top())
            }
            _ => {
                if self.options.strict_ifs {
                    (
                        MigrationalType::Var(self.fresh_variable()),
                        Constraints::epsilon(),
                        Pattern::Bot(),
                    )
                } else {
                    (
                        MigrationalType::Dyn(),
                        Constraints::epsilon(),
                        Pattern::Top(),
                    )
                }
            }
        }
    }

    fn merge(&mut self, d: Variation, theta1: Subst, theta2: Subst) -> Subst {
        let dom1: HashSet<&TypeVariable> = HashSet::from_iter(theta1.0.keys());
        let dom2: HashSet<&TypeVariable> = HashSet::from_iter(theta2.0.keys());

        let mut map = HashMap::new();
        for a in dom1.union(dom2) {
            let v1 = theta1
                .lookup(a)
                .cloned()
                .unwrap_or_else(|| VariationalType::Var(self.fresh_variable()));
            let v2 = theta2
                .lookup(a)
                .cloned()
                .unwrap_or_else(|| VariationalType::Var(self.fresh_variable()));
            map = map.update(a.clone(), VariationalType::choice(d, v1, v2));
        }

        Subst(map)
    }

    fn unify(&mut self, constraints: Constraints) -> (Subst, Pattern) {
        // (g)
        let mut theta = Subst::empty();
        let mut pi = Pattern::Top();

        for c in constraints.0.into_iter() {
            // (i)
            let (theta_c, pi_c) = self.unify1(c.apply(&theta));

            theta = theta_c.compose(theta);
            pi = pi.meet(pi_c);
        }

        (theta, pi)
    }

    fn unify1(&mut self, c: Constraint) -> (Subst, Pattern) {
        trace!("unify1({})", c);

        match c {
            Constraint::Consistent(_p, MigrationalType::Dyn(), _)
            | Constraint::Consistent(_p, _, MigrationalType::Dyn()) => {
                // (a), (a*)
                (Subst::empty(), Pattern::Top())
            }
            Constraint::Consistent(_p, MigrationalType::Var(a1), MigrationalType::Var(a2)) if a1 == a2 => {
                // ??? MMG arises from recursion
                (Subst::empty(), Pattern::Top())
            } 
            Constraint::Consistent(p, MigrationalType::Var(a), m)
            | Constraint::Consistent(p, m, MigrationalType::Var(a)) => {
                // (b), (b*)
                let alpha = MigrationalType::Var(a); // can't use @ patterns, unstable

                if !m.vars().contains(&a) {
                    // occurs check!
                    if let Some(v) = m.try_variational() {
                        return (Subst::empty().extend(a, v), Pattern::Top()); // first case: direct binding
                    } else if m.is_fun() {
                        // third case: check if M is a function
                        let k1 = self.fresh_variable();
                        let k2 = self.fresh_variable();
                        let kfun = MigrationalType::fun(
                            MigrationalType::Var(k1),
                            MigrationalType::Var(k2),
                        );

                        let (theta1, pi1) = self.unify1(Constraint::Consistent(
                            Pattern::Top(),
                            alpha.clone(),
                            kfun.clone(),
                        ));
                        let (theta2, pi2) =
                            self.unify1(Constraint::Consistent(Pattern::Top(), kfun, m.clone())); // ??? MMG paper says pi2, not Top
                        return (theta2.compose(theta1), pi2.meet(pi1));
                    }
                }

                // failed occurs check! choices could let us avoid some of the branches, though...
                debug!("failed occurs check");

                match m.choices().iter().next() {
                    None => (Subst::empty(), Pattern::Bot()), // failure case
                    Some(d) => {
                        // second case: case splitting
                        self.unify1(Constraint::Consistent(
                            p.clone(),
                            MigrationalType::choice(**d, alpha.clone(), alpha.clone()),
                            m.clone(),
                        ))
                    }
                }
            }
            Constraint::Consistent(
                p,
                MigrationalType::Choice(d1, m1, m2),
                MigrationalType::Choice(d2, m3, m4),
            ) if d1 == d2 => {
                // (c)
                let (theta1, pi1) = self.unify1(Constraint::Consistent(p.clone(), *m1, *m3));
                let (theta2, pi2) = self.unify1(Constraint::Consistent(p, *m2, *m4));

                let theta = self.merge(d1, theta1, theta2);
                (theta, Pattern::choice(d1, pi1, pi2))
            }
            Constraint::Consistent(p, MigrationalType::Choice(d, m1, m2), m)
            | Constraint::Consistent(p, m, MigrationalType::Choice(d, m1, m2)) => {
                // (d), (d*)
                self.unify1(Constraint::Consistent(
                    p,
                    MigrationalType::Choice(d, m1, m2),
                    MigrationalType::choice(
                        d,
                        m.select(d, Side::Left()),
                        m.select(d, Side::Right()),
                    ),
                ))
            }
            Constraint::Consistent(
                p,
                MigrationalType::Fun(m11, m12),
                MigrationalType::Fun(m21, m22),
            ) => {
                // (e), (f)
                let (theta1, pi1) = self.unify1(Constraint::Consistent(p.clone(), *m11, *m21));
                let (theta2, pi2) = self.unify1(Constraint::Consistent(
                    p,
                    m12.apply(&theta1),
                    m22.apply(&theta1),
                ));

                (theta2.compose(theta1), pi2.meet(pi1))
            }
            Constraint::Consistent(_p, MigrationalType::Base(b1), MigrationalType::Base(b2)) => {
                // (e)
                (Subst::empty(), (b1 == b2).into())
            }
            Constraint::Consistent(_p, MigrationalType::Base(_), MigrationalType::Fun(_, _))
            | Constraint::Consistent(_p, MigrationalType::Fun(_, _), MigrationalType::Base(_)) => {
                // (e)
                (Subst::empty(), Pattern::Bot())
            }
            Constraint::Choice(d, bias, cs1, cs2) => {
                // (h)
                let (theta1, pi1) = self.unify(cs1);
                let (theta2, pi2) = self.unify(cs2);

                let theta = self.merge(d, theta1, theta2);
                (theta, Pattern::choice_(d, bias, pi1, pi2))
            }
            Constraint::Ground(_pi, MigrationalType::Dyn(), _b) => (Subst::empty(), Pattern::Bot()),
            Constraint::Ground(_pi, MigrationalType::Fun(_, _), _b) => {
                (Subst::empty(), Pattern::Bot())
            }
            Constraint::Ground(_pi, MigrationalType::Base(b1), b2) => {
                (Subst::empty(), (b1 == b2).into())
            }
            Constraint::Ground(_pi, MigrationalType::Var(a), b) => (
                Subst::empty().extend(a, VariationalType::Base(b)),
                Pattern::Top(),
            ),
            Constraint::Ground(pi, MigrationalType::Choice(d, m1, m2), b) => {
                let (theta1, pi1) = self.unify1(Constraint::Ground(pi.clone(), *m1, b));
                let (theta2, pi2) = self.unify1(Constraint::Ground(pi, *m2, b));

                let theta = self.merge(d, theta1, theta2);
                (theta, Pattern::choice(d, pi1, pi2))
            }
        }
    }

    pub fn run(
        &mut self,
        ctx: Ctx,
        e: &SourceExpr,
    ) -> Option<(TargetExpr, MigrationalType, HashSet<Eliminator>)> {
        let (e, m) = self.generate_constraints(ctx, e)?;

        debug!("Generated constraints:");
        debug!("  e = {}", e);
        debug!("  m = {}", m);
        debug!("  constraints = {}", self.constraints);
        debug!("  pi = {}", self.pattern);

        if self.pattern == Pattern::Bot() {
            error!("constraint generation produced false pattern (i.e., statically untypable");
            return None;
        }

        let (theta, mut pi) = self.unify(self.constraints.clone());
        pi = pi.meet(self.pattern.clone());
        let e = e.apply(&theta);
        let m = m.clone().apply(&theta);
        debug!("Unified constraints:");
        debug!("  e = {}", e);
        debug!("  theta = {}", theta);
        debug!("  pi = {}", pi);
        debug!("  m = {}", m);

        let ves = pi.clone().valid_eliminators();
        debug!("Valid eliminators:");
        debug!("ves = [");
        for ve in ves.iter() {
            debug!("  {}", ve);
        }
        debug!("]");

        let ds = e.choices().clone().union(m.choices());
        let ves: HashSet<Eliminator> = ves.into_iter().map(move |ve| ve.expand(&ds)).collect();

        debug!("Maximal valid eliminators:");
        debug!("ves = [");
        for ve in ves.iter() {
            debug!("  {} score: {}", ve, ve.score());
        }
        debug!("]");

        Some((e, m, ves))
    }

    pub fn infer(e: &SourceExpr) -> Option<(TargetExpr, MigrationalType, HashSet<Eliminator>)> {
        let mut ti = TypeInference::new(Options::default());

        ti.run(Ctx::empty(), e)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use im_rc::HashSet;

    fn try_infer(s: &str) -> Option<(TargetExpr, MigrationalType, HashSet<Eliminator>)> {
        TypeInference::infer(&SourceExpr::parse(s).unwrap())
    }

    fn infer(s: &str) -> (TargetExpr, MigrationalType, HashSet<Eliminator>) {
        try_infer(s).unwrap()
    }

    fn no_maximal_typing(s: &str) {
        let (_e, _m, ves) = infer(s);

        assert!(ves.is_empty());
    }

    fn infer_strict(s: &str) -> Option<(TargetExpr, MigrationalType, HashSet<Eliminator>)> {
        let mut options = Options::default();
        options.strict_ifs = true;
        let mut ti = TypeInference::new(options);

        ti.run(Ctx::empty(), &Expr::parse(s).unwrap())
    }

    fn identity() -> SourceExpr {
        let x = String::from("x");
        Expr::lam(x.clone(), None, Expr::Var(x))
    }

    fn bool_identity() -> SourceExpr {
        let x = String::from("x");
        Expr::lam(
            x.clone(),
            Some(GradualType::Base(BaseType::Bool)),
            Expr::Var(x),
        )
    }

    fn dyn_identity() -> SourceExpr {
        let x = String::from("x");
        Expr::lam(x.clone(), Some(GradualType::Dyn()), Expr::Var(x))
    }

    fn neg() -> SourceExpr {
        let b = String::from("b");
        Expr::lam(
            b.clone(),
            None,
            Expr::if_(Expr::Var(b), Expr::bool(false), Expr::bool(true)),
        )
    }

    fn dyn_neg() -> SourceExpr {
        let b = String::from("b");
        Expr::lam(
            b.clone(),
            Some(GradualType::Dyn()),
            Expr::if_(Expr::Var(b), Expr::bool(false), Expr::bool(true)),
        )
    }

    fn little_omega() -> SourceExpr {
        let x = Expr::Var(String::from("x"));
        Expr::lam(String::from("x"), None, Expr::app(x.clone(), x))
    }

    #[test]
    fn infer_identity() {
        let (_e, m, ves) = TypeInference::infer(&identity()).unwrap();
        match m {
            MigrationalType::Fun(dom, cod) => match (*dom, *cod) {
                (MigrationalType::Var(a_dom), MigrationalType::Var(a_cod)) => {
                    assert_eq!(a_dom, a_cod)
                }
                _ => panic!("expected identical variables in domain and codomain"),
            },
            _ => panic!("expected function type"),
        }
        assert_eq!(ves, HashSet::unit(Eliminator::new()));
    }

    #[test]
    fn infer_dyn_identity() {
        let (e, m, ves) = TypeInference::infer(&dyn_identity()).unwrap();

        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();

        let (d, a) = match e {
            Expr::Lam(x, MigrationalType::Choice(d, m1, m2), e) => {
                assert_eq!(*m1, MigrationalType::Dyn());
                let y = match *e {
                    Expr::Var(y) => y,
                    _ => panic!("expected variable as lambda body"),
                };

                assert_eq!(x, y);
                let a = match *m2 {
                    MigrationalType::Var(a) => a,
                    _ => panic!("expected type variable in right choice"),
                };

                (d, a)
            }
            _ => panic!("expected id function at dyn or a -> a"),
        };

        assert_eq!(ve, &Eliminator::new().update(d, Side::Right()));

        let m = m.eliminate(ve);

        // should be given the true identity type
        match m {
            MigrationalType::Fun(dom, cod) => match (*dom, *cod) {
                (MigrationalType::Var(a_dom), MigrationalType::Var(a_cod)) => {
                    assert_eq!(a_dom, a);
                    assert_eq!(a_cod, a);
                }
                _ => panic!("expected identical variables in domain and codomain"),
            },
            _ => panic!("expected function type"),
        }
    }

    #[test]
    fn infer_dyn_const() {
        let x = String::from("x");
        let y = String::from("y");
        let k = Expr::lam(
            x.clone(),
            Some(GradualType::Dyn()),
            Expr::lam(y, Some(GradualType::Dyn()), Expr::Var(x)),
        );

        let (_e, m, ves) = TypeInference::infer(&k).unwrap();

        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        // should be given the type a -> b -> a
        match m {
            MigrationalType::Fun(dom1, cod1) => match (*dom1, *cod1) {
                (MigrationalType::Var(a_dom1), MigrationalType::Fun(dom2, cod2)) => {
                    match (*dom2, *cod2) {
                        (MigrationalType::Var(a_dom2), MigrationalType::Var(a_cod)) => {
                            assert_eq!(a_dom1, a_cod);
                            assert_ne!(a_dom1, a_dom2);
                        }
                        _ => panic!("expected a -> b -> a"),
                    }
                }
                _ => panic!("expected a -> b -> a"),
            },
            _ => panic!("expected a -> b -> a"),
        }
    }

    #[test]
    fn infer_boolean_negation() {
        let (_e, m, ves) = TypeInference::infer(&neg()).unwrap();

        assert_eq!(
            m,
            MigrationalType::fun(MigrationalType::bool(), MigrationalType::bool())
        );
        assert_eq!(ves, HashSet::unit(Eliminator::new()));
    }

    #[test]
    fn infer_dyn_boolean_negation() {
        let (_e, m, ves) = TypeInference::infer(&dyn_neg()).unwrap();

        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        // assigns the static type
        assert_eq!(
            m,
            MigrationalType::fun(MigrationalType::bool(), MigrationalType::bool())
        );
    }

    #[test]
    fn infer_conditional() {
        let e = Expr::if_(Expr::bool(true), Expr::bool(false), Expr::bool(true));

        let (_e, m, ves) = TypeInference::infer(&e).unwrap();

        assert_eq!(m, MigrationalType::bool());
        assert_eq!(ves, HashSet::unit(Eliminator::new()));
    }

    #[test]
    fn infer_neg_or_id() {
        let e = Expr::if_(Expr::bool(true), dyn_neg(), dyn_identity());

        let (_e, m, ves) = TypeInference::infer(&e).unwrap();
        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        // assigns the static type (narrowing id!)
        assert_eq!(
            m,
            MigrationalType::fun(MigrationalType::bool(), MigrationalType::bool())
        );
    }

    #[test]
    fn infer_very_dynamic() {
        let x = String::from("x");
        let y = String::from("y");
        let e = Expr::lam(
            x.clone(),
            Some(GradualType::Dyn()),
            Expr::lam(
                y.clone(),
                Some(GradualType::Dyn()),
                Expr::if_(
                    Expr::Var(x.clone()),
                    Expr::app(Expr::Var(y.clone()), Expr::Var(x)),
                    Expr::app(neg(), Expr::Var(y)),
                ),
            ),
        );

        let (_e, m, ves) = TypeInference::infer(&e).unwrap();

        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(
            m,
            MigrationalType::fun(
                MigrationalType::bool(),
                MigrationalType::fun(MigrationalType::Dyn(), MigrationalType::bool())
            )
        );
    }

    #[test]
    fn infer_constants() {
        check_constant(Constant::Bool(true), BaseType::Bool);
        check_constant(Constant::Bool(false), BaseType::Bool);
        check_constant(Constant::Int(0), BaseType::Int);
        check_constant(Constant::Int(6), BaseType::Int);
        check_constant(Constant::Int(-47), BaseType::Int);
    }

    fn check_constant(c: Constant, b: BaseType) {
        let (_e, m, ves) = TypeInference::infer(&Expr::Const(c)).unwrap();

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert!(ve.is_empty());

        assert_eq!(m, MigrationalType::Base(b));
    }

    #[test]
    fn infer_little_omega() {
        let (_e, m, ves) = TypeInference::infer(&little_omega()).unwrap();

        assert!(m.is_fun());
        assert!(ves.is_empty());
    }

    #[test]
    fn infer_big_omega() {
        let big_omega = Expr::app(little_omega(), little_omega());
        let (_e, _m, ves) = TypeInference::infer(&big_omega).unwrap();

        // m will probably be a type variable, but who cares
        assert!(ves.is_empty());
    }

    #[test]
    fn infer_bool_id() {
        let (_e, m, ves) = TypeInference::infer(&bool_identity()).unwrap();

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert!(ve.is_empty());

        assert_eq!(
            m,
            MigrationalType::fun(MigrationalType::bool(), MigrationalType::bool())
        );
    }

    #[test]
    fn infer_plus() {
        let (_e, m, ve) = infer("2 + 2");

        assert_eq!(ve.len(), 1);
        assert!(ve.iter().next().unwrap().is_empty());
        assert_eq!(m, MigrationalType::int());

        no_maximal_typing("2 + false");
        no_maximal_typing("false + 2");
        no_maximal_typing("false + false");
        no_maximal_typing("false + (\\x:?. x)");
        no_maximal_typing("false + (\\x. x)");
    }

    #[test]
    fn overload_eq() {
        let (e, m, ves) = infer("0 == false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        match e.eliminate(ve) {
            Expr::BOp(TargetBOp::EqualDyn, _, _) => (),
            e => panic!("expected ==?, got {}", e),
        }

        let (e, m, ves) = infer("(\\x. \\y. x == y) true false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        let e = e.eliminate(ve);
        assert!(
            match e.clone() {
                Expr::App(e1, _) => match *e1 {
                    Expr::App(e1, _) => match *e1 {
                        Expr::Lam(_, _, e) => match *e {
                            Expr::Lam(_, _, e) => match *e {
                                Expr::BOp(TargetBOp::EqualBool, _, _) => true,
                                _ => false,
                            },
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            },
            "expected ==b, got {}",
            e
        );

        let (e, m, ves) = infer("(\\x:?. \\y. x == y) true false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        let e = e.eliminate(ve);
        assert!(
            match e.clone() {
                Expr::App(e1, _) => match *e1 {
                    Expr::App(e1, _) => match *e1 {
                        Expr::Lam(_, _, e) => match *e {
                            Expr::Lam(_, _, e) => match *e {
                                Expr::BOp(TargetBOp::EqualBool, _, _) => true,
                                _ => false,
                            },
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            },
            "expected ==b, got {}",
            e
        );

        let (e, m, ves) = infer("(\\x. \\y:?. x == y) true false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        let e = e.eliminate(ve);
        assert!(
            match e.clone() {
                Expr::App(e1, _) => match *e1 {
                    Expr::App(e1, _) => match *e1 {
                        Expr::Lam(_, _, e) => match *e {
                            Expr::Lam(_, _, e) => match *e {
                                Expr::BOp(TargetBOp::EqualBool, _, _) => true,
                                _ => false,
                            },
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            },
            "expected ==b, got {}",
            e
        );

        let (_e, m, ves) = infer("(\\x:?. \\y:?. x == y) true false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        let e = e.eliminate(ve);
        assert!(
            match e.clone() {
                Expr::App(e1, _) => match *e1 {
                    Expr::App(e1, _) => match *e1 {
                        Expr::Lam(_, _, e) => match *e {
                            Expr::Lam(_, _, e) => match *e {
                                Expr::BOp(TargetBOp::EqualBool, _, _) => true,
                                _ => false,
                            },
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            },
            "expected ==b, got {}",
            e
        );
    }

    fn infer_eq(s: &str, mx: MigrationalType, my: MigrationalType, eq: TargetBOp) {
        let (e, m, ves) = infer(s);

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        let e = e.eliminate(ve);
        assert!(
            match e.clone() {
                Expr::Let(_, _, e, _) => match *e {
                    Expr::Lam(_, mx_got, e) => {
                        assert_eq!(mx, mx_got);
                        match *e {
                            Expr::Lam(_, my_got, e) => {
                                assert_eq!(my, my_got);
                                match *e {
                                    Expr::BOp(op, _, _) => {
                                        assert_eq!(eq, op);
                                        true
                                    }
                                    _ => false,
                                }
                            }
                            _ => false,
                        }
                    }
                    _ => false,
                },
                _ => false,
            },
            "expected ==b, got {}",
            e
        );
    }

    #[test]
    fn overloaded_eq() {
        infer_eq(
            "let eq = \\x:?. \\y:?. x == y in eq 5 true && eq 0 0 && eq false false",
            MigrationalType::Dyn(),
            MigrationalType::Dyn(),
            TargetBOp::EqualDyn,
        );

        infer_eq(
            "let eq = \\x:?. \\y:?. x == y in eq false false && eq true false",
            MigrationalType::bool(),
            MigrationalType::bool(),
            TargetBOp::EqualBool,
        );

        infer_eq(
            "let eq = \\x:?. \\y:?. x == y in eq 5 true",
            MigrationalType::int(),
            MigrationalType::bool(),
            TargetBOp::EqualDyn,
        );
    }

    #[test]
    fn ill_typed_ann() {
        let (_e, _m, ves) = TypeInference::infer(&Expr::ann(
            Expr::Const(Constant::Int(5)),
            Some(GradualType::Base(BaseType::Bool)),
        ))
        .unwrap();

        assert_eq!(ves.len(), 0);
    }

    #[test]
    fn strict_if_meet_not_join() {
        assert!(infer_strict("\\x:?. if x then \\y:?. x else false").is_none());
        assert!(infer_strict("\\x:?. if x then \\y. x else false").is_none());
        assert!(infer_strict("\\x. if x then \\y:?. x else false").is_none());
        assert!(infer_strict("\\x. if x then \\y. x else false").is_none());
    }

    #[test]
    fn lax_if_meet_not_join() {
        let _ = infer("\\x:?. if x then \\y:?. x else false");
        let _ = infer("\\x:?. if x then \\y. x else false");
        let _ = infer("\\x. if x then \\y:?. x else false");
        let _ = infer("\\x. if x then \\y. x else false");
    }

    #[test]
    fn well_typed_ann() {
        let (_e, m, ves) = TypeInference::infer(&Expr::lam(
            "x".into(),
            Some(GradualType::Dyn()),
            Expr::ann(
                Expr::Var("x".into()),
                Some(GradualType::Base(BaseType::Int)),
            ),
        ))
        .unwrap();

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(
            m,
            MigrationalType::fun(MigrationalType::int(), MigrationalType::int())
        );
    }

    #[test]
    fn let_plain() {
        let (_e, m, ves) = infer("let id = \\x. x in if id true then id true else id false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(m, MigrationalType::bool());
    }

    #[test]
    fn let_dynfun() {
        let (_e, m, ves) = infer("let id = \\x:?. x in if id true then id true else id false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(m, MigrationalType::bool());
    }

    #[test]
    fn let_dyn_poly_error() {
        let (_e, _m, ves) = infer("let id = \\x. x in if id true then id 5 else id 1");

        assert_eq!(ves.len(), 0);

        let (_e, m, ves) = infer("let id = \\x:?. x in if id true then id 5 else id 1");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(m, MigrationalType::Dyn());

        let (_e, m, ves) = infer("let id:? = \\x. x in if id true then id 5 else id 1");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(m, MigrationalType::Dyn());
    }

    #[test]
    fn let_poly_eq_both() {
        let (_e, m, ves) = infer("let eq : ? = \\x. \\y. x == y in eq true true && eq 0 0");
        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);
        assert_eq!(m, MigrationalType::bool());
    }

    #[test]
    fn let_poly_eq_bool() {
        let (_e, m, ves) = infer("let eq : ? = \\x. \\y. x == y in eq true false");
        assert!(!ves.is_empty());

        for ve in ves.iter() {
            let m = m.clone().eliminate(ve);
            assert!(m == MigrationalType::bool() || m == MigrationalType::Dyn());
        }
    }

    #[test]
    fn let_poly_eq_int() {
        let (_e, m, ves) = infer("let eq : ? = \\x. \\y. x == y in eq 5 0");
        assert!(!ves.is_empty());

        for ve in ves.iter() {
            let m = m.clone().eliminate(ve);
            assert!(m == MigrationalType::bool() || m == MigrationalType::Dyn());
        }
    }

    #[test]
    fn let_poly_eq_mixed() {
        let (e, m, ves) = infer("let eq : ? = \\x. \\y. x == y in eq 5 true");
        assert!(!ves.is_empty());

        eprintln!("{} eliminators", ves.len());

        for ve in ves.iter() {
            let m = m.clone().eliminate(ve);
            eprintln!("{}\n: {}", e.clone().eliminate(ve), m);
            assert!(m == MigrationalType::bool() || m == MigrationalType::Dyn());
        }
    }

    #[test]
    fn let_polyargs_eq_mixed() {
        let (e, m, ves) = infer("let eq = \\x:?. \\y:?. x == y in eq 5 true");
        assert!(!ves.is_empty());

        eprintln!("{} eliminators", ves.len());

        for ve in ves.iter() {
            let m = m.clone().eliminate(ve);
            eprintln!("{}\n: {}", e.clone().eliminate(ve), m);
            assert!(m == MigrationalType::bool() || m == MigrationalType::Dyn());
        }
    }

    #[test]
    pub fn let_polyargs_bool_wouldbenice() {
        let (e, m, ves) = infer("let eq = \\x:?. \\y:?. x == y in eq false false && eq true false");
        assert!(!ves.is_empty());

        // currently get three options:
        //
        // x, y : bool;  == --> ==b
        // x, y : ?;     == --> ==i (?!)
        // x:?, y: bool; == --> ==b
        //
        // this kind of sucks... should really only get the first one
        //
        // simply reordering the bop cases doesn't help.

        for (i, ve) in ves.iter().enumerate() {
            let m = m.clone().eliminate(ve);
            eprintln!(
                "eliminator #{}:\n{}\n: {}",
                i + 1,
                e.clone().eliminate(ve),
                m
            );
            assert_eq!(m, MigrationalType::bool());
        }
    }

    #[test]
    fn eq_poly_broken() {
        // this is behaving buggily. depending on whichever option comes closest
        // to the EqDyn operator, one of these has one VE (closest) and one has
        // two (furthest). both should have just one VE.
        //
        // i think the real solution here is something a bit more ad hoc during
        // resolution. scan the list and filter out the obvious bad ones.
        // ideally, there should just be a choice between the typed one and the
        // dynamic typed one. then the usual stuff should work fine.
        infer("true == true");
        infer("0 == 0");
    }

    #[test]
    fn let_const() {
        let (_e, m, ves) = infer("let x = 5 in x");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(m, MigrationalType::int());
    }

    #[test]
    fn infer_bad_constraints() {
        assert!(
            TypeInference::infer(&Expr::app(
                Expr::Const(Constant::Bool(true)),
                Expr::Const(Constant::Bool(false)),
            ))
            .is_none(),
            "type inference should fail"
        );
    }

    #[test]
    fn test_letrec() {
        let (_e, m, ves) = infer("let rec f = \\x. if x then false else g x and g = \\y. if y then f y else false in f true");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert!(ve.is_empty());

        assert_eq!(m, MigrationalType::bool());

        let (_e, m, ves) = infer("let rec f = \\x:?. if x then false else g x and g = \\y:?. if y then f y else false in f true");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);
        assert_eq!(m, MigrationalType::bool());
    }

    #[test]
    fn eg_width() {
        let fixed: String = "fixed".into();
        let width_func: String = "width_func".into();

        let width: SourceExpr = Expr::lam(
            fixed.clone(),
            Some(GradualType::Dyn()),
            Expr::lam(
                width_func.clone(),
                Some(GradualType::Dyn()),
                Expr::if_(
                    Expr::Var(fixed.clone()),
                    Expr::app(Expr::Var(width_func.clone()), Expr::Var(fixed.clone())),
                    Expr::app(Expr::Var(width_func.clone()), Expr::Const(Constant::Int(5))),
                ),
            ),
        );

        let (_e, m, ves) = TypeInference::infer(&width).unwrap();
        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(
            m,
            MigrationalType::fun(
                MigrationalType::bool(),
                MigrationalType::fun(MigrationalType::Dyn(), MigrationalType::Dyn())
            )
        );
    }

    #[test]
    pub fn subst_merge() {
        let mut ti = TypeInference::new(Options::default());
        let a = ti.fresh_variable();
        let b = ti.fresh_variable();
        let c = ti.fresh_variable();
        let e = ti.fresh_variable();

        let theta1 = Subst::empty()
            .extend(a, VariationalType::Base(BaseType::Bool))
            .extend(b, VariationalType::Base(BaseType::Int));
        let theta2 = Subst::empty()
            .extend(
                a,
                VariationalType::fun(
                    VariationalType::Base(BaseType::Int),
                    VariationalType::Base(BaseType::Int),
                ),
            )
            .extend(c, VariationalType::Base(BaseType::Bool));

        let d = ti.fresh_variation();
        let theta = ti.merge(d, theta1.clone(), theta2.clone());

        assert_eq!(
            theta.lookup(&a).unwrap(),
            &VariationalType::choice(
                d,
                theta1.lookup(&a).unwrap().clone(),
                theta2.lookup(&a).unwrap().clone()
            )
        );

        match theta.lookup(&b).unwrap() {
            VariationalType::Choice(d2, v1, v2) => {
                assert_eq!(*d2, d);
                assert_eq!(**v1, theta1.lookup(&b).unwrap().clone());
                match **v2 {
                    VariationalType::Var(_) => (),
                    _ => panic!("expected type variable, got {}", v2),
                }
            }
            v => panic!("expected variational choice, got {}", v),
        }

        match theta.lookup(&c).unwrap() {
            VariationalType::Choice(d2, v1, v2) => {
                assert_eq!(*d2, d);
                match **v1 {
                    VariationalType::Var(_) => (),
                    _ => panic!("expected type variable, got {}", v2),
                }
                assert_eq!(**v2, theta2.lookup(&c).unwrap().clone());
            }
            v => panic!("expected variational choice, got {}", v),
        }

        assert_eq!(theta.lookup(&e), None);
    }
}
