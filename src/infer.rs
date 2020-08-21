use std::cmp::PartialEq;
use std::fmt::Display;
use std::hash::Hash;
use std::iter::FromIterator;

use im_rc::HashMap;
use im_rc::HashSet;

use log::{debug, error, trace, warn};

use crate::options::{Options, DEFAULT_WIDTH};
use crate::syntax::*;

/// d.1 or d.2
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Eliminator(HashMap<Variation, Side>);

impl VariationalType {
    pub fn apply(self, theta: &Subst) -> VariationalType {
        match self {
            VariationalType::Base(b) => VariationalType::Base(b),
            VariationalType::Fun(v1, v2) => VariationalType::fun(v1.apply(theta), v2.apply(theta)),
            VariationalType::List(v) => VariationalType::list(v.apply(theta)),
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
            MigrationalType::List(m) => MigrationalType::list(m.apply(theta)),
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
            MigrationalType::List(m) => MigrationalType::list(m.eliminate(elim)),
            MigrationalType::Choice(d, m1, m2) => match elim.get(&d) {
                Side::Right => m2.eliminate(elim),
                Side::Left => m1.eliminate(elim),
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
            GradualExpr::Const(c) => GradualExpr::Const(c),
            GradualExpr::Var(x) => GradualExpr::Var(x),
            GradualExpr::Lam(x, t, e) => GradualExpr::lam(x, t.eliminate(elim), e.eliminate(elim)),
            GradualExpr::App(e1, e2) => GradualExpr::app(e1.eliminate(elim), e2.eliminate(elim)),
            GradualExpr::Ann(e, t) => GradualExpr::ann(e.eliminate(elim), t.eliminate(elim)),
            GradualExpr::Hole(name, t) => GradualExpr::Hole(name, t.eliminate(elim)),
            GradualExpr::If(e1, e2, e3) => {
                GradualExpr::if_(e1.eliminate(elim), e2.eliminate(elim), e3.eliminate(elim))
            }
            GradualExpr::Let(x, t, e1, e2) => {
                GradualExpr::let_(x, t.eliminate(elim), e1.eliminate(elim), e2.eliminate(elim))
            }
            GradualExpr::LetRec(defns, e2) => GradualExpr::letrec(
                defns
                    .into_iter()
                    .map(|(v, t, e1)| (v, t.eliminate(elim), e1.eliminate(elim)))
                    .collect(),
                e2.eliminate(elim),
            ),
            GradualExpr::UOp(op, e) => GradualExpr::uop(op.eliminate(elim), e.eliminate(elim)),
            GradualExpr::BOp(op, e1, e2) => {
                GradualExpr::bop(op.eliminate(elim), e1.eliminate(elim), e2.eliminate(elim))
            }
            GradualExpr::Nil(t) => GradualExpr::Nil(t.eliminate(elim)),
            GradualExpr::Cons(e1, e2) => GradualExpr::cons(e1.eliminate(elim), e2.eliminate(elim)),
            GradualExpr::Match(e_scrutinee, e_nil, hd, tl, e_cons) => GradualExpr::match_(
                e_scrutinee.eliminate(elim),
                e_nil.eliminate(elim),
                hd,
                tl,
                e_cons.eliminate(elim),
            ),
        }
    }
}

impl ExplicitUOp {
    pub fn eliminate(self, _elim: &Eliminator) -> Self {
        self
    }
}

impl ExplicitBOp {
    pub fn eliminate(self, elim: &Eliminator) -> Self {
        match self {
            ExplicitBOp::Choice(d, op1, op2) => match elim.get(&d) {
                Side::Right => op2.eliminate(elim),
                Side::Left => op1.eliminate(elim),
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
    Choice(Variation, Box<Pattern>, Box<Pattern>),
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
            Pattern::Choice(d, pat1, pat2) => pp.as_string(d).append(
                pp.intersperse(
                    vec![pat1.pretty(pp), pat2.pretty(pp).nest(1)],
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
            Pattern::Choice(d2, pat1, pat2) => {
                if d == d2 {
                    match side {
                        Side::Left => *pat1, // shouldn't need recursive select---each variation should appear only once (invariant maintained in Pattern::choice)
                        Side::Right => *pat2,
                    }
                } else {
                    Pattern::Choice(
                        d2,
                        Box::new(pat1.select(d, side)),
                        Box::new(pat2.select(d, side)),
                    )
                }
            }
        }
    }

    pub fn choice(d: Variation, pat1: Pattern, pat2: Pattern) -> Pattern {
        if pat1 == pat2 {
            pat1
        } else {
            Pattern::Choice(
                d,
                Box::new(pat1.select(d, Side::Left)),
                Box::new(pat2.select(d, Side::Right)),
            )
        }
    }

    pub fn meet(&self, other: Pattern) -> Pattern {
        match self {
            Pattern::Top() => other,
            Pattern::Bot() => Pattern::Bot(),
            Pattern::Choice(d1, pat11, pat12) => match other {
                Pattern::Choice(d2, pat21, pat22) if *d1 == d2 => {
                    Pattern::choice(*d1, pat11.meet(*pat21), pat12.meet(*pat22))
                }
                _ => Pattern::choice(*d1, pat11.meet(other.clone()), pat12.meet(other)),
            },
        }
    }

    pub fn valid_eliminators(self) -> HashSet<Eliminator> {
        match self {
            Pattern::Top() => HashSet::unit(Eliminator::new()),
            Pattern::Bot() => HashSet::new(),
            Pattern::Choice(d, pi1, pi2) => {
                let ves1: HashSet<Eliminator> = pi1
                    .valid_eliminators()
                    .into_iter()
                    .map(|ve| ve.update(d, Side::Left))
                    .collect();
                let ves2: HashSet<Eliminator> = pi2
                    .valid_eliminators()
                    .into_iter()
                    .map(|ve| ve.update(d, Side::Right))
                    .collect();

                match d.bias() {
                    Some(Side::Left) if !ves1.is_empty() => ves1,
                    Some(Side::Right) if !ves2.is_empty() => ves2,
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
            if elim.0.get(d) != Some(&Side::Left) {
                elim = elim.update(**d, Side::Right);
            }
        }

        elim
    }

    pub fn score(&self) -> usize {
        self.0
            .iter()
            .filter(|(_d, side)| **side == Side::Right)
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
    Static {
        pi: Pattern,
        src: MigrationalType,
        tgt: VariationalType,
    },
    Choice(Variation, Constraints, Constraints),
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
            Constraint::Static { pi, src, tgt } => pp.intersperse(
                vec![
                    src.pretty(pp),
                    pp.text("=").append(pi.pretty(pp)),
                    pp.as_string(tgt),
                ],
                pp.line(),
            ),
            Constraint::Choice(d, cs1, cs2) => pp
                .as_string(d)
                .append(
                    cs1.pretty(pp)
                        .append(pp.text(","))
                        .append(pp.line())
                        .append(cs2.pretty(pp).nest(1))
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
            Constraint::Static { pi, src, tgt } => Constraint::Static {
                pi,
                src: src.apply(theta),
                tgt,
            },
            Constraint::Choice(d, cs1, cs2) => {
                Constraint::Choice(d, cs1.apply(theta), cs2.apply(theta))
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

impl SourceUOp {
    /// Returns the sole possibility for a unary operation.
    ///
    /// TODO with overloaded ones, we need UOpSignature, like below
    pub fn explicit(&self) -> ExplicitUOp {
        match self {
            SourceUOp::Negate => ExplicitUOp::Negate,
            SourceUOp::Not => ExplicitUOp::Not,
            SourceUOp::Is(g) => ExplicitUOp::Is(*g),
        }
    }
}

/// Different binary operation signatures.
pub enum BOpSignature {
    /// Used when any consistent type is okay. Only for non-overloaded operations.
    Simple(ExplicitBOp),
    Overloaded {
        dyn_op: ExplicitBOp,
        overloads: Vec<ExplicitBOp>,
    },
}

impl SourceBOp {
    pub fn explicit(&self) -> BOpSignature {
        match self {
            SourceBOp::Plus => BOpSignature::Overloaded {
                dyn_op: ExplicitBOp::PlusDyn,
                overloads: vec![ExplicitBOp::PlusInt, ExplicitBOp::PlusString],
            },
            SourceBOp::Equal => BOpSignature::Overloaded {
                dyn_op: ExplicitBOp::EqualDyn,
                overloads: vec![
                    ExplicitBOp::EqualBool,
                    ExplicitBOp::EqualInt,
                    ExplicitBOp::EqualString,
                ],
            },
            SourceBOp::And => BOpSignature::Simple(ExplicitBOp::And),
            SourceBOp::Or => BOpSignature::Simple(ExplicitBOp::Or),
            SourceBOp::Minus => BOpSignature::Simple(ExplicitBOp::Minus),
            SourceBOp::Times => BOpSignature::Simple(ExplicitBOp::Times),
            SourceBOp::Divide => BOpSignature::Simple(ExplicitBOp::Divide),
            SourceBOp::LessThan => BOpSignature::Simple(ExplicitBOp::LessThan),
            SourceBOp::LessThanEqual => BOpSignature::Simple(ExplicitBOp::LessThanEqual),
        }
    }
}

impl ExplicitUOp {
    pub fn signature(&self) -> (GradualType, GradualType) {
        match self {
            ExplicitUOp::Negate => (GradualType::int(), GradualType::int()),
            ExplicitUOp::Not => (GradualType::bool(), GradualType::bool()),
            ExplicitUOp::Is(_g) => (GradualType::Dyn(), GradualType::bool()),
        }
    }
}

impl ExplicitBOp {
    pub fn signature(&self) -> (GradualType, GradualType) {
        match self {
            ExplicitBOp::PlusInt => (GradualType::int(), GradualType::int()),
            ExplicitBOp::PlusString => (GradualType::string(), GradualType::string()),
            ExplicitBOp::PlusDyn => (GradualType::Dyn(), GradualType::Dyn()),
            ExplicitBOp::Minus => (GradualType::int(), GradualType::int()),
            ExplicitBOp::Times => (GradualType::int(), GradualType::int()),
            ExplicitBOp::Divide => (GradualType::int(), GradualType::int()),
            ExplicitBOp::And => (GradualType::bool(), GradualType::bool()),
            ExplicitBOp::Or => (GradualType::bool(), GradualType::bool()),
            ExplicitBOp::EqualBool => (GradualType::bool(), GradualType::bool()),
            ExplicitBOp::EqualInt => (GradualType::int(), GradualType::bool()),
            ExplicitBOp::EqualString => (GradualType::string(), GradualType::bool()),
            ExplicitBOp::EqualDyn => (GradualType::Dyn(), GradualType::bool()),
            ExplicitBOp::LessThan => (GradualType::int(), GradualType::bool()),
            ExplicitBOp::LessThanEqual => (GradualType::int(), GradualType::bool()),
            ExplicitBOp::Choice(_, _, _) => panic!("asked for signature of choice"),
        }
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
    pub fn new(options: Options) -> Self {
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
        Variation::new(next)
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
        ctx: Ctx, // TODO change to &Ctx
        e: &SourceExpr,
    ) -> Option<(TargetExpr, MigrationalType)> {
        match e {
            GradualExpr::Const(c) => Some((GradualExpr::Const(c.clone()), c.into())),
            GradualExpr::Var(x) => {
                debug!("looking up {} in {:?}", x, ctx);
                let m = ctx.lookup(x)?;
                Some((GradualExpr::Var(x.clone()), m.clone()))
            }
            GradualExpr::Lam(x, t, e) => {
                let m_dom = self.freshen_annotation(t);

                let (e, m_cod) =
                    self.generate_constraints(ctx.extend(x.clone(), m_dom.clone().into()), e)?;

                let m_dom: MigrationalType = m_dom.clone().into();
                Some((
                    GradualExpr::lam(x.clone(), m_dom.clone(), e),
                    MigrationalType::fun(m_dom, m_cod),
                ))
            }
            GradualExpr::Ann(e, t) => {
                let (e, m) = self.generate_constraints(ctx, e)?;

                let m_ann = self.freshen_annotation(t);

                self.add_constraint(Constraint::Consistent(
                    Pattern::Top(),
                    m.clone(),
                    m_ann.clone(),
                ));

                Some((GradualExpr::ann(e, m), m_ann))
            }
            GradualExpr::Hole(name, t) => {
                if let Some(t) = t {
                    warn!("unexpected typed hole {} : {}", name, t);
                }
                let m = self.freshen_annotation(t);

                Some((GradualExpr::Hole(name.clone(), m.clone()), m))
            }
            GradualExpr::App(e_fun, e_arg) => {
                let (e_fun, m_fun) = self.generate_constraints(ctx.clone(), e_fun)?;
                let (e_arg, m_arg) = self.generate_constraints(ctx, e_arg)?;

                let (m_res, cs_res, pat_res) = self.cod(&m_fun);
                self.add_constraints(cs_res);
                self.add_pattern(pat_res);
                let (cs_arg, pat_arg) = self.dom(&m_fun, &m_arg);
                self.add_constraints(cs_arg);
                self.add_pattern(pat_arg);

                Some((GradualExpr::app(e_fun, e_arg), m_res))
            }
            GradualExpr::If(e_cond, e_then, e_else) => {
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

                Some((
                    GradualExpr::if_(
                        e_cond,
                        GradualExpr::ann(e_then, m_res.clone()),
                        GradualExpr::ann(e_else, m_res.clone()),
                    ),
                    m_res,
                ))
            }
            GradualExpr::Let(x, t, e_def, e_body) => {
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

                Some((GradualExpr::let_(x.clone(), m_def, e_def, e_body), m_body))
            }
            GradualExpr::LetRec(defns, e_body) => {
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

                Some((GradualExpr::letrec(e_defns, e_body), m_body))
            }
            GradualExpr::UOp(op, e) => {
                let (e, m) = self.generate_constraints(ctx.clone(), e)?;

                let op = op.explicit();
                let (g_dom, g_cod) = op.signature();

                self.add_constraint(Constraint::Consistent(Pattern::Top(), m, g_dom.into()));

                Some((GradualExpr::uop(op, e), g_cod.into()))
            }
            GradualExpr::BOp(op, e1, e2) => {
                let (e1, m1) = self.generate_constraints(ctx.clone(), e1)?;
                let (e2, m2) = self.generate_constraints(ctx.clone(), e2)?;

                match op.explicit() {
                    BOpSignature::Simple(op) => {
                        let (g_dom, g_cod) = op.signature();
                        let m_dom: MigrationalType = g_dom.into();

                        self.add_constraint(Constraint::Consistent(
                            Pattern::Top(),
                            m_dom.clone(),
                            m1.clone(),
                        ));
                        self.add_constraint(Constraint::Consistent(
                            Pattern::Top(),
                            m_dom,
                            m2.clone(),
                        ));

                        Some((GradualExpr::bop(op, e1, e2), g_cod.into()))
                    }
                    BOpSignature::Overloaded { dyn_op, overloads } => {
                        let mut op = dyn_op;
                        let (g_dom, g_cod) = op.signature().into();
                        let mut m_dom: MigrationalType = g_dom.into();
                        let mut m_cod: MigrationalType = g_cod.into();

                        let mut cs = Constraints::epsilon();

                        for op2 in overloads.into_iter() {
                            let (g_dom2, g_cod2) = op2.signature();

                            let v_dom2 = g_dom2.try_variational().expect(
                                "expected variational (non-dynamic) type in operation signature",
                            );

                            let d = self.fresh_variation().biased(Side::Right);

                            op = ExplicitBOp::choice(d, op, op2);
                            let cs2 = Constraints(vec![
                                Constraint::Static {
                                    pi: Pattern::Top(),
                                    src: m1.clone(),
                                    tgt: v_dom2.clone(),
                                },
                                Constraint::Static {
                                    pi: Pattern::Top(),
                                    src: m2.clone(),
                                    tgt: v_dom2.clone(),
                                },
                            ]);
                            cs = Constraint::Choice(d, cs, cs2).into();
                            m_dom = MigrationalType::choice(d, m_dom.clone(), v_dom2.into());
                            m_cod = MigrationalType::choice(d, m_cod.clone(), g_cod2.into());
                        }

                        self.add_constraints(cs);

                        Some((GradualExpr::bop(op, e1, e2), m_cod))
                    }
                }
            }
            GradualExpr::Nil(t) => {
                let g = match t {
                    Some(g) => {
                        warn!("unexpected annotation on empty list [] ({})", g);
                        g
                    }
                    None => &GradualType::Dyn(),
                };
                let m = self.freshen_gradual_type(g);
                log::debug!("writing nil @ {}", m);

                Some((GradualExpr::Nil(m.clone()), MigrationalType::list(m)))
            }
            GradualExpr::Cons(e1, e2) => {
                let (e1, m1) = self.generate_constraints(ctx.clone(), e1)?;
                let (e2, m2) = self.generate_constraints(ctx.clone(), e2)?;

                let (m_elt, cs_elt, pat_elt) = self.elt(&m2);
                let m_list = MigrationalType::list(m_elt.clone());

                self.add_constraint(Constraint::Consistent(Pattern::Top(), m1, m_elt));
                self.add_constraints(cs_elt);
                self.add_pattern(pat_elt);

                Some((GradualExpr::cons(e1, e2), m_list))
            }
            GradualExpr::Match(e_scrutinee, e_nil, hd, tl, e_cons) => {
                let (e_scrutinee, m_scrutinee) =
                    self.generate_constraints(ctx.clone(), e_scrutinee)?;

                // make sure we're looking at a list
                let (m_elt, cs_elt, pat_elt) = self.elt(&m_scrutinee);
                let m_list = MigrationalType::list(m_elt.clone());

                self.add_constraint(Constraint::Consistent(
                    Pattern::Top(),
                    m_scrutinee,
                    m_list.clone(),
                ));
                self.add_constraints(cs_elt);
                self.add_pattern(pat_elt);

                // check the nil branch
                let (e_nil, m_nil) = self.generate_constraints(ctx.clone(), e_nil)?;

                // check the cons branch
                let (e_cons, m_cons) = self.generate_constraints(
                    ctx.extend(hd.clone(), m_elt.clone())
                        .extend(tl.clone(), m_list.clone()),
                    e_cons,
                )?;

                let (m_res, c_res, pi_res) = self.meet(&m_nil, &m_cons);
                debug!(
                    "match constraints on {} and {}: {} (pi={})",
                    m_nil, m_cons, c_res, pi_res
                );
                self.add_constraints(c_res);
                self.add_pattern(pi_res);

                Some((
                    GradualExpr::match_(
                        GradualExpr::ann(e_scrutinee, m_list.clone()),
                        GradualExpr::ann(e_nil, m_res.clone()),
                        hd.clone(),
                        tl.clone(),
                        GradualExpr::ann(e_cons, m_res.clone()),
                    ),
                    m_res,
                ))
            }
        }
    }

    fn dyn_to_var(&mut self, m: &MigrationalType) -> MigrationalType {
        match m {
            MigrationalType::Dyn() => MigrationalType::Var(self.fresh_variable()),
            MigrationalType::Base(b) => MigrationalType::Base(*b),
            MigrationalType::Var(a) => MigrationalType::Var(*a),
            MigrationalType::List(m) => MigrationalType::list(self.dyn_to_var(m)),
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
                    Constraint::Choice(*d, cs1, cs2).into(),
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
                    Constraint::Choice(*d, cs1, cs2).into(),
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

    fn elt(&mut self, m_list: &MigrationalType) -> (MigrationalType, Constraints, Pattern) {
        match m_list {
            MigrationalType::Dyn() => (
                MigrationalType::Dyn(),
                Constraints::epsilon(),
                Pattern::Top(),
            ),
            MigrationalType::List(m_elt) => {
                (*m_elt.clone(), Constraints::epsilon(), Pattern::Top())
            }
            MigrationalType::Var(alpha) => {
                let beta = MigrationalType::Var(self.fresh_variable());
                let real_list = MigrationalType::list(beta.clone());
                (
                    beta,
                    Constraint::Consistent(Pattern::Top(), MigrationalType::Var(*alpha), real_list)
                        .into(),
                    Pattern::Top(),
                )
            }
            MigrationalType::Choice(d, m_list1, m_list2) => {
                let (m1, cs1, pat1) = self.elt(m_list1);
                let (m2, cs2, pat2) = self.elt(m_list2);

                (
                    MigrationalType::choice(*d, m1, m2),
                    Constraint::Choice(*d, cs1, cs2).into(),
                    Pattern::choice(*d, pat1, pat2),
                )
            }
            MigrationalType::Fun(_, _) | MigrationalType::Base(_) => (
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
                    Constraint::Choice(*d, cs1, cs2).into(),
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
            Constraint::Consistent(_p, MigrationalType::Var(a1), MigrationalType::Var(a2))
                if a1 == a2 =>
            {
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
                    } else {
                        match m {
                            m @ MigrationalType::Fun(_, _) => {
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
                                let (theta2, pi2) = self.unify1(Constraint::Consistent(
                                    Pattern::Top(),
                                    kfun,
                                    m.clone(),
                                )); // ??? MMG paper says pi2, not Top
                                return (theta2.compose(theta1), pi2.meet(pi1));
                            }
                            m @ MigrationalType::List(_) => {
                                let k = self.fresh_variable();
                                let klist = MigrationalType::list(MigrationalType::Var(k));

                                let (theta1, pi1) = self.unify1(Constraint::Consistent(
                                    Pattern::Top(),
                                    alpha.clone(),
                                    klist.clone(),
                                ));

                                let (theta2, pi2) =
                                    self.unify1(Constraint::Consistent(Pattern::Top(), klist, m));

                                return (theta2.compose(theta1), pi2.meet(pi1));
                            }
                            _ => {
                                debug!("passed occurs check, but couldn't directly bind or use type structure");
                            }
                        }
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
                    MigrationalType::choice(d, m.select(d, Side::Left), m.select(d, Side::Right)),
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
            Constraint::Consistent(p, MigrationalType::List(m1), MigrationalType::List(m2)) => {
                self.unify1(Constraint::Consistent(p, *m1, *m2))
            }
            Constraint::Consistent(_p, MigrationalType::Base(b1), MigrationalType::Base(b2)) => {
                // (e)
                (Subst::empty(), (b1 == b2).into())
            }
            Constraint::Consistent(_p, MigrationalType::Base(_), MigrationalType::Fun(_, _))
            | Constraint::Consistent(_p, MigrationalType::Fun(_, _), MigrationalType::Base(_))
            | Constraint::Consistent(_p, MigrationalType::List(_), MigrationalType::Fun(_, _))
            | Constraint::Consistent(_p, MigrationalType::Fun(_, _), MigrationalType::List(_))
            | Constraint::Consistent(_p, MigrationalType::Base(_), MigrationalType::List(_))
            | Constraint::Consistent(_p, MigrationalType::List(_), MigrationalType::Base(_)) => {
                // (e)
                (Subst::empty(), Pattern::Bot())
            }
            Constraint::Choice(d, cs1, cs2) => {
                // (h)
                let (theta1, pi1) = self.unify(cs1);
                let (theta2, pi2) = self.unify(cs2);

                let theta = self.merge(d, theta1, theta2);
                (theta, Pattern::choice(d, pi1, pi2))
            }
            Constraint::Static {
                src: MigrationalType::Dyn(),
                ..
            } => (Subst::empty(), Pattern::Bot()),
            Constraint::Static {
                pi,
                src: MigrationalType::Fun(m1, m2),
                tgt: VariationalType::Fun(v1, v2),
            } => {
                let (theta1, pi1) = self.unify1(Constraint::Static {
                    pi: pi.clone(),
                    src: *m1,
                    tgt: *v1,
                });
                let (theta2, pi2) = self.unify1(Constraint::Static {
                    pi,
                    src: *m2,
                    tgt: *v2,
                });

                (theta1.compose(theta2), pi1.meet(pi2))
            }
            Constraint::Static {
                pi,
                src: MigrationalType::List(m),
                tgt: VariationalType::List(v),
            } => self.unify1(Constraint::Static {
                pi,
                src: *m,
                tgt: *v,
            }),
            Constraint::Static {
                src: MigrationalType::Base(b1),
                tgt: VariationalType::Base(b2),
                ..
            } => (Subst::empty(), (b1 == b2).into()),
            Constraint::Static {
                src: MigrationalType::Var(a),
                tgt,
                ..
            } => (Subst::empty().extend(a, tgt), Pattern::Top()),
            Constraint::Static {
                pi,
                src: MigrationalType::Choice(d, m1, m2),
                tgt,
            } => {
                let (theta1, pi1) = self.unify1(Constraint::Static {
                    pi: pi.clone(),
                    src: *m1,
                    tgt: tgt.clone(),
                });
                let (theta2, pi2) = self.unify1(Constraint::Static { pi, src: *m2, tgt });

                let theta = self.merge(d, theta1, theta2);
                (theta, Pattern::choice(d, pi1, pi2))
            }
            Constraint::Static {
                src: MigrationalType::Fun(_, _),
                ..
            }
            | Constraint::Static {
                src: MigrationalType::List(_),
                ..
            }
            | Constraint::Static {
                src: MigrationalType::Base(_),
                ..
            } => (Subst::empty(), Pattern::Bot()),
        }
    }

    pub fn run(
        &mut self,
        e: &SourceExpr,
    ) -> Option<(TargetExpr, MigrationalType, HashSet<Eliminator>)> {
        let (e, m) = self.generate_constraints(Ctx::empty(), e)?;

        debug!("Generated constraints:");
        debug!("  e = {}", e);
        debug!("  m = {}", m);
        debug!("  constraints = {}", self.constraints);
        debug!("  pi = {}", self.pattern);

        if self.pattern == Pattern::Bot() {
            error!("constraint generation produced false pattern (i.e., statically untypable)");
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

        ti.run(e)
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

    fn infer_unique(s: &str) -> (TargetExpr, MigrationalType) {
        let (e, m, ves) = infer(s);

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();

        (e.eliminate(ve), m.eliminate(ve))
    }

    fn no_maximal_typing(s: &str) {
        let (_e, _m, ves) = infer(s);

        assert!(ves.is_empty());
    }

    fn infer_strict(s: &str) -> Option<(TargetExpr, MigrationalType, HashSet<Eliminator>)> {
        let mut options = Options::default();
        options.strict_ifs = true;
        let mut ti = TypeInference::new(options);

        ti.run(&GradualExpr::parse(s).unwrap())
    }

    fn identity() -> SourceExpr {
        let x = String::from("x");
        GradualExpr::lam(x.clone(), None, GradualExpr::Var(x))
    }

    fn bool_identity() -> SourceExpr {
        let x = String::from("x");
        GradualExpr::lam(
            x.clone(),
            Some(GradualType::Base(BaseType::Bool)),
            GradualExpr::Var(x),
        )
    }

    fn dyn_identity() -> SourceExpr {
        let x = String::from("x");
        GradualExpr::lam(x.clone(), Some(GradualType::Dyn()), GradualExpr::Var(x))
    }

    fn neg() -> SourceExpr {
        let b = String::from("b");
        GradualExpr::lam(
            b.clone(),
            None,
            GradualExpr::if_(
                GradualExpr::Var(b),
                GradualExpr::bool(false),
                GradualExpr::bool(true),
            ),
        )
    }

    fn dyn_neg() -> SourceExpr {
        let b = String::from("b");
        GradualExpr::lam(
            b.clone(),
            Some(GradualType::Dyn()),
            GradualExpr::if_(
                GradualExpr::Var(b),
                GradualExpr::bool(false),
                GradualExpr::bool(true),
            ),
        )
    }

    fn little_omega() -> SourceExpr {
        let x = GradualExpr::Var(String::from("x"));
        GradualExpr::lam(String::from("x"), None, GradualExpr::app(x.clone(), x))
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
            GradualExpr::Lam(x, MigrationalType::Choice(d, m1, m2), e) => {
                assert_eq!(*m1, MigrationalType::Dyn());
                let y = match *e {
                    GradualExpr::Var(y) => y,
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

        assert_eq!(ve, &Eliminator::new().update(d, Side::Right));

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
        let k = GradualExpr::lam(
            x.clone(),
            Some(GradualType::Dyn()),
            GradualExpr::lam(y, Some(GradualType::Dyn()), GradualExpr::Var(x)),
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
        let e = GradualExpr::if_(
            GradualExpr::bool(true),
            GradualExpr::bool(false),
            GradualExpr::bool(true),
        );

        let (_e, m, ves) = TypeInference::infer(&e).unwrap();

        assert_eq!(m, MigrationalType::bool());
        assert_eq!(ves, HashSet::unit(Eliminator::new()));
    }

    #[test]
    fn infer_neg_or_id() {
        let e = GradualExpr::if_(GradualExpr::bool(true), dyn_neg(), dyn_identity());

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
        let e = GradualExpr::lam(
            x.clone(),
            Some(GradualType::Dyn()),
            GradualExpr::lam(
                y.clone(),
                Some(GradualType::Dyn()),
                GradualExpr::if_(
                    GradualExpr::Var(x.clone()),
                    GradualExpr::app(GradualExpr::Var(y.clone()), GradualExpr::Var(x)),
                    GradualExpr::app(neg(), GradualExpr::Var(y)),
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
        let (_e, m, ves) = TypeInference::infer(&GradualExpr::Const(c)).unwrap();

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert!(ve.is_empty());

        assert_eq!(m, b.into());
    }

    #[test]
    fn infer_little_omega() {
        let (_e, m, ves) = TypeInference::infer(&little_omega()).unwrap();

        assert!(m.is_fun());
        assert!(ves.is_empty());
    }

    #[test]
    fn infer_big_omega() {
        let big_omega = GradualExpr::app(little_omega(), little_omega());
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
    fn infer_times() {
        let (_e, m, ve) = infer("2 * 2");

        assert_eq!(ve.len(), 1);
        assert!(ve.iter().next().unwrap().is_empty());
        assert_eq!(m, MigrationalType::int());

        no_maximal_typing("2 * false");
        no_maximal_typing("false * 2");
        no_maximal_typing("false * false");
        no_maximal_typing("false * (\\x:?. x)");
        no_maximal_typing("false * (\\x. x)");
    }

    #[test]
    fn infer_strings() {
        let (_, m, ve) = infer("\\x: string. x");

        assert_eq!(ve.len(), 1);
        assert!(ve.iter().next().unwrap().is_empty());
        assert_eq!(
            m,
            MigrationalType::fun(BaseType::String.into(), BaseType::String.into())
        );

        let (_, m, ve) = infer(r#""hello""#);
        assert_eq!(ve.len(), 1);
        assert!(ve.iter().next().unwrap().is_empty());
        assert_eq!(m, BaseType::String.into());

        let (_, m, ve) = infer(r#"\x: string. "suuuup""#);

        assert_eq!(ve.len(), 1);
        assert!(ve.iter().next().unwrap().is_empty());
        assert_eq!(
            m,
            MigrationalType::fun(BaseType::String.into(), BaseType::String.into())
        );
    }

    #[test]
    fn overload_eq() {
        let (e, m, ves) = infer("0 == false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        match e.eliminate(ve) {
            GradualExpr::BOp(ExplicitBOp::EqualDyn, _, _) => (),
            e => panic!("expected ==?, got {}", e),
        }

        let (e, m, ves) = infer("0 == 0");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        match e.eliminate(ve) {
            GradualExpr::BOp(ExplicitBOp::EqualInt, _, _) => (),
            e => panic!("expected ==i, got {}", e),
        }

        let (e, m, ves) = infer(r#""hi" == "sup""#);

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        match e.eliminate(ve) {
            GradualExpr::BOp(ExplicitBOp::EqualString, _, _) => (),
            e => panic!("expected ==s, got {}", e),
        }

        let (e, m, ves) = infer("true == false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        match e.eliminate(ve) {
            GradualExpr::BOp(ExplicitBOp::EqualBool, _, _) => (),
            e => panic!("expected ==b, got {}", e),
        }

        let (e, m, ves) = infer("(\\x. \\y. x == y) true false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        let e = e.eliminate(ve);
        assert!(
            match e.clone() {
                GradualExpr::App(e1, _) => match *e1 {
                    GradualExpr::App(e1, _) => match *e1 {
                        GradualExpr::Lam(_, _, e) => match *e {
                            GradualExpr::Lam(_, _, e) => match *e {
                                GradualExpr::BOp(ExplicitBOp::EqualBool, _, _) => true,
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
                GradualExpr::App(e1, _) => match *e1 {
                    GradualExpr::App(e1, _) => match *e1 {
                        GradualExpr::Lam(_, _, e) => match *e {
                            GradualExpr::Lam(_, _, e) => match *e {
                                GradualExpr::BOp(ExplicitBOp::EqualBool, _, _) => true,
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
                GradualExpr::App(e1, _) => match *e1 {
                    GradualExpr::App(e1, _) => match *e1 {
                        GradualExpr::Lam(_, _, e) => match *e {
                            GradualExpr::Lam(_, _, e) => match *e {
                                GradualExpr::BOp(ExplicitBOp::EqualBool, _, _) => true,
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
                GradualExpr::App(e1, _) => match *e1 {
                    GradualExpr::App(e1, _) => match *e1 {
                        GradualExpr::Lam(_, _, e) => match *e {
                            GradualExpr::Lam(_, _, e) => match *e {
                                GradualExpr::BOp(ExplicitBOp::EqualBool, _, _) => true,
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

    fn infer_eq(s: &str, mx: MigrationalType, my: MigrationalType, eq: ExplicitBOp) {
        let (e, m, ves) = infer(s);

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        assert_eq!(m.eliminate(ve), MigrationalType::bool());
        let e = e.eliminate(ve);
        assert!(
            match e.clone() {
                GradualExpr::Let(_, _, e, _) => match *e {
                    GradualExpr::Lam(_, mx_got, e) => {
                        assert_eq!(mx, mx_got);
                        match *e {
                            GradualExpr::Lam(_, my_got, e) => {
                                assert_eq!(my, my_got);
                                match *e {
                                    GradualExpr::BOp(op, _, _) => {
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
            "expected term using {}, got {}",
            eq,
            e
        );
    }

    #[test]
    fn overloaded_eq() {
        infer_eq(
            "let eq = \\x:?. \\y:?. x == y in eq 5 true && eq 0 0 && eq false false",
            MigrationalType::Dyn(),
            MigrationalType::Dyn(),
            ExplicitBOp::EqualDyn,
        );

        infer_eq(
            "let eq = \\x:?. \\y:?. x == y in eq false false && eq true false",
            MigrationalType::bool(),
            MigrationalType::bool(),
            ExplicitBOp::EqualBool,
        );

        infer_eq(
            "let eq = \\x:?. \\y:?. x == y in eq 5 true",
            MigrationalType::int(),
            MigrationalType::bool(),
            ExplicitBOp::EqualDyn,
        );
    }

    #[test]
    fn overloaded_plus() {
        let (e, m) = infer_unique(r#""hi" + "bye""#);
        assert_eq!(m, MigrationalType::string());
        match e {
            GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusString),
            e => panic!("expected +s, got {}", e),
        }

        let (e, m) = infer_unique(r#"__ + "bye""#);
        assert_eq!(m, MigrationalType::string());
        match e {
            GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusString),
            e => panic!("expected +s, got {}", e),
        }

        let (e, m) = infer_unique(r#""bye" + "hi""#);
        assert_eq!(m, MigrationalType::string());
        match e {
            GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusString),
            e => panic!("expected +s, got {}", e),
        }

        let (e, m) = infer_unique(r#"__ + __ + "hi""#);
        assert_eq!(m, MigrationalType::string());
        match e {
            GradualExpr::BOp(op, e1, _) => {
                assert_eq!(op, ExplicitBOp::PlusString);
                match *e1 {
                    GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusString),
                    e => panic!("expectes +s, got {}", e),
                }
            }
            e => panic!("expected +s, got {}", e),
        }

        let (e, m) = infer_unique("1 + 1");
        assert_eq!(m, MigrationalType::int());
        match e {
            GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusInt),
            e => panic!("expected +i, got {}", e),
        }

        let (e, m) = infer_unique("1 + __");
        assert_eq!(m, MigrationalType::int());
        match e {
            GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusInt),
            e => panic!("expected +i, got {}", e),
        }

        let (e, m) = infer_unique("1 + \"hi\"");
        assert_eq!(m, MigrationalType::Dyn());
        match e {
            GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusDyn),
            e => panic!("expected +?, got {}", e),
        }

        let (e, m) = infer_unique("true + false");
        assert_eq!(m, MigrationalType::Dyn());
        match e {
            GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusDyn),
            e => panic!("expected +?, got {}", e),
        }

        let (e, m) = infer_unique("true + 1");
        assert_eq!(m, MigrationalType::Dyn());
        match e {
            GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusDyn),
            e => panic!("expected +?, got {}", e),
        }

        let (e, m) = infer_unique("\"hi\" + false");
        assert_eq!(m, MigrationalType::Dyn());
        match e {
            GradualExpr::BOp(op, _, _) => assert_eq!(op, ExplicitBOp::PlusDyn),
            e => panic!("expected +?, got {}", e),
        }
    }

    #[test]
    fn holes() {
        let (_, m) = infer_unique("__ * 1");
        assert_eq!(m, MigrationalType::int());

        let (_, m) = infer_unique("1 * __b");
        assert_eq!(m, MigrationalType::int());

        let (_, m) = infer_unique("__a * __b");
        assert_eq!(m, MigrationalType::int());

        let (_, m) = infer_unique("(\\x. x * 1) __a");
        assert_eq!(m, MigrationalType::int());

        let (_, m) = infer_unique("__ : bool");
        assert_eq!(m, MigrationalType::bool());

        let (_, m) = infer_unique("__");
        match m {
            MigrationalType::Var(_) => (),
            m => panic!("expected type variable, got {}", m),
        };
    }

    #[test]
    fn assume() {
        let (_, m) = infer_unique("assume x in x * 1");
        assert_eq!(m, MigrationalType::int());

        let (_, m) = infer_unique("assume x:? in x * 1");
        assert_eq!(m, MigrationalType::int());

        let (_, m) = infer_unique("assume x:int in x * 1");
        assert_eq!(m, MigrationalType::int());

        let (_, _m, ves) = infer("assume x:int in if x then x * 1 else 0");
        assert!(ves.is_empty());

        let (_, m) = infer_unique("assume x:? in if x then x * 1 else 0");
        assert_eq!(m, MigrationalType::int());

        let (_, m) = infer_unique("assume x:? in if x then x * 1 else true");
        assert_eq!(m, MigrationalType::Dyn());

        let (_, _m, ves) = infer("assume x in if x then x * 1 else 0");
        assert!(ves.is_empty());
    }

    #[test]
    fn ill_typed_ann() {
        let (_e, _m, ves) = TypeInference::infer(&GradualExpr::ann(
            GradualExpr::Const(Constant::Int(5)),
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
        let (_e, m, ves) = TypeInference::infer(&GradualExpr::lam(
            "x".into(),
            Some(GradualType::Dyn()),
            GradualExpr::ann(
                GradualExpr::Var("x".into()),
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
    fn list_kitchen_sink() {
        let (_, m) = infer_unique(r#"["";3;\x. x * 2; true]"#);

        assert_eq!(m, MigrationalType::list(MigrationalType::Dyn()));
    }

    #[test]
    fn match_simple() {
        let (_, m) = infer_unique("match [] with [] -> 0 | hd::tl -> 1");
        assert_eq!(m, MigrationalType::int());

        let (_, m) = infer_unique("match [] with | [] -> 0 | hd::tl -> 1");
        assert_eq!(m, MigrationalType::int());

        let (_, m) = infer_unique("match [1;2] with | [] -> 0 | hd::tl -> hd");
        assert_eq!(m, MigrationalType::int());
    }

    #[test]
    fn infer_bad_constraints() {
        assert!(
            TypeInference::infer(&GradualExpr::app(
                GradualExpr::Const(Constant::Bool(true)),
                GradualExpr::Const(Constant::Bool(false)),
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
    fn letrec_mutual_loop() {
        let (e, m, ves) = infer("let rec f x = g x and g y = f y in f true && g false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);
        assert_eq!(m, MigrationalType::bool());
        assert!(e.eliminate(ve).choices().is_empty());

        // underconstrained... will just leave a type variable, but cool
        let (e, m, ves) = infer("let rec f x = g x and g y = f y in f true");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        match m.eliminate(ve) {
            MigrationalType::Var(_) => (),
            m => panic!("expected type variable, got {}", m),
        }
        assert!(e.eliminate(ve).choices().is_empty());
    }

    #[test]
    fn type_predicates() {
        let (_e, m) = infer_unique(r#"let x = "oh, " in if string? x then x + "hi" else x + 10"#);
        assert_eq!(m, MigrationalType::string());

        let (_e, m) = infer_unique(
            r#"let x = if true then "oh, " else false in if string? x then x + "hi" else x + 10"#,
        );
        assert_eq!(m, MigrationalType::Dyn());
    }

    #[test]
    fn eg_width() {
        let fixed: String = "fixed".into();
        let width_func: String = "width_func".into();

        let width: SourceExpr = GradualExpr::lam(
            fixed.clone(),
            Some(GradualType::Dyn()),
            GradualExpr::lam(
                width_func.clone(),
                Some(GradualType::Dyn()),
                GradualExpr::if_(
                    GradualExpr::Var(fixed.clone()),
                    GradualExpr::app(
                        GradualExpr::Var(width_func.clone()),
                        GradualExpr::Var(fixed.clone()),
                    ),
                    GradualExpr::app(
                        GradualExpr::Var(width_func.clone()),
                        GradualExpr::Const(Constant::Int(5)),
                    ),
                ),
            ),
        );

        let (e, m, ves) = TypeInference::infer(&width).unwrap();
        assert_eq!(ves.len(), 2);
        for ve in ves.iter() {
            assert!(m.clone().eliminate(ve).choices().is_empty());
            assert!(e.clone().eliminate(ve).choices().is_empty())
        }
    }

    #[test]
    fn subst_merge() {
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
