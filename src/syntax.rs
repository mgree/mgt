use std::cmp::PartialEq;
use std::fmt::Display;
use std::hash::Hash;

use im_rc::HashMap;
use im_rc::HashSet;

use log::warn;

const DEFAULT_WIDTH: usize = 80;

lalrpop_mod!(parser);

/// gamma
#[derive(Clone, Debug, PartialEq)]
pub enum BaseType {
    Bool,
    Int,
}

/// alpha
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct TypeVariable(pub(super) usize);

/// T
#[derive(Clone, Debug, PartialEq)]
pub enum StaticType {
    Base(BaseType),
    Var(TypeVariable),
    Fun(Box<StaticType>, Box<StaticType>),
}

/// G
#[derive(Clone, Debug, PartialEq)]
pub enum GradualType {
    Base(BaseType),
    Var(TypeVariable),
    Fun(Box<GradualType>, Box<GradualType>),
    Dyn(),
}

/// d
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Variation(pub(super) usize);

/// .1 or .2
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Side {
    Left(),
    Right(),
}

/// d.1 or d.2
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Eliminator(HashMap<Variation, Side>);

/// V
#[derive(Clone, Debug, PartialEq)]
pub enum VariationalType {
    Base(BaseType),
    Var(TypeVariable),
    Fun(Box<VariationalType>, Box<VariationalType>),
    Choice(Variation, Box<VariationalType>, Box<VariationalType>),
}

/// M
#[derive(Clone, Debug, PartialEq)]
pub enum MigrationalType {
    Base(BaseType),
    Var(TypeVariable),
    Fun(Box<MigrationalType>, Box<MigrationalType>),
    Dyn(),
    Choice(Variation, Box<MigrationalType>, Box<MigrationalType>),
}

/// pi
#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    Bot(),
    Top(),
    Choice(Variation, Box<Pattern>, Box<Pattern>),
}

/// c
#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    Bool(bool),
    Int(isize),
}

/// x
pub type Variable = String;

/// e (ITGL)
#[derive(Clone, Debug, PartialEq)]
pub enum Expr<T> {
    Const(Constant),
    Var(Variable),
    Lam(Variable, T, Box<Expr<T>>),
    Ann(Box<Expr<T>>, T),
    App(Box<Expr<T>>, Box<Expr<T>>),
    If(Box<Expr<T>>, Box<Expr<T>>, Box<Expr<T>>),
    Let(Variable, T, Box<Expr<T>>, Box<Expr<T>>),
    // TODO operations on constants
}

pub type SourceExpr = Expr<Option<GradualType>>;
pub type TargetExpr = Expr<MigrationalType>;

impl<T> Expr<T> {
    pub fn bool(b: bool) -> Expr<T> {
        Expr::Const(Constant::Bool(b))
    }

    pub fn int(n: isize) -> Expr<T> {
        Expr::Const(Constant::Int(n))
    }

    pub fn lam(v: Variable, t: T, e: Expr<T>) -> Expr<T> {
        Expr::Lam(v, t, Box::new(e))
    }

    pub fn ann(e: Expr<T>, t: T) -> Expr<T> {
        Expr::Ann(Box::new(e), t)
    }

    pub fn app(e1: Expr<T>, e2: Expr<T>) -> Expr<T> {
        Expr::App(Box::new(e1), Box::new(e2))
    }

    pub fn if_(e1: Expr<T>, e2: Expr<T>, e3: Expr<T>) -> Expr<T> {
        Expr::If(Box::new(e1), Box::new(e2), Box::new(e3))
    }

    pub fn let_(x: Variable, t: T, e1: Expr<T>, e2: Expr<T>) -> Expr<T> {
        Expr::Let(x, t, Box::new(e1), Box::new(e2))
    }

    pub fn map_types<F, U>(self, f: &F) -> Expr<U>
    where
        F: Fn(T) -> U,
    {
        match self {
            Expr::Const(c) => Expr::Const(c),
            Expr::Var(x) => Expr::Var(x),
            Expr::Lam(x, t, e) => Expr::lam(x, f(t), e.map_types(f)),
            Expr::App(e1, e2) => Expr::app(e1.map_types(f), e2.map_types(f)),
            Expr::Ann(e, t) => Expr::ann(e.map_types(f), f(t)),
            Expr::If(e1, e2, e3) => Expr::if_(e1.map_types(f), e2.map_types(f), e3.map_types(f)),
            Expr::Let(x, t, e1, e2) => Expr::let_(x, f(t), e1.map_types(f), e2.map_types(f)),
        }
    }

    pub fn is_compound(&self) -> bool {
        match self {
            Expr::Var(_) | Expr::Const(_) => false,
            _ => true,
        }
    }

    pub fn is_app(&self) -> bool {
        match self {
            Expr::App(_, _) => true,
            _ => false,
        }
    }
}

impl SourceExpr {
    pub fn parse<'a>(s: &'a str) -> Result<Self, String> {
        parser::ExprParser::new()
            .parse(s)
            .map_err(|e| e.to_string())
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Expr::Var(x) => pp.text(x),
            Expr::Const(Constant::Bool(true)) => pp.text("true"),
            Expr::Const(Constant::Bool(false)) => pp.text("false"),
            Expr::Const(Constant::Int(n)) => pp.text(n.to_string()),
            Expr::Lam(x, None, e) => pp
                .text("\\")
                .append(pp.text(x))
                .append(pp.text("."))
                .append(pp.line())
                .append(e.pretty(pp).nest(1))
                .group(),
            Expr::Lam(x, Some(t), e) => pp
                .text("\\")
                .append(pp.text(x))
                .append(pp.space())
                .append(pp.text(":"))
                .append(pp.space())
                .append(t.pretty(pp))
                .append(pp.text("."))
                .append(pp.line())
                .append(e.pretty(pp).nest(1))
                .group(),
            Expr::Ann(e, None) => e.pretty(pp),
            Expr::Ann(e, Some(t)) => e
                .pretty(pp)
                .append(pp.space())
                .append(pp.text(":"))
                .append(pp.space())
                .append(t.pretty(pp))
                .group(),
            Expr::App(e1, e2) => {
                let mut d1 = e1.pretty(pp);
                let mut d2 = e2.pretty(pp);

                if e1.is_compound() && !e1.is_app() {
                    d1 = d1.parens();
                }

                if e2.is_compound() {
                    d2 = d2.parens();
                }

                d1.append(pp.line()).append(d2).group()
            }
            Expr::If(e1, e2, e3) => {
                let d_cond = pp
                    .text("if")
                    .append(pp.space())
                    .append(e1.pretty(pp).nest(2))
                    .append(pp.line())
                    .group();

                let d_then = pp
                    .text("then")
                    .append(pp.line())
                    .append(e2.pretty(pp).nest(2))
                    .append(pp.line())
                    .group();

                let d_else = pp
                    .text("else")
                    .append(pp.line())
                    .append(e3.pretty(pp).nest(2))
                    .group();

                pp.concat(vec![d_cond, d_then, d_else])
            }
            Expr::Let(x, t, e1, e2) => {
                let d_annot = if let Some(t) = t {
                    pp.intersperse(vec![pp.text(":"), t.pretty(pp), pp.text("=")], pp.space())
                } else {
                    pp.text("=")
                };

                let d_bind = pp
                    .intersperse(vec![pp.text("let"), pp.text(x), d_annot], pp.space())
                    .group();

                pp.intersperse(
                    vec![
                        d_bind,
                        e1.pretty(pp).nest(2).group(),
                        pp.text("in"),
                        e2.pretty(pp).group(),
                    ],
                    pp.line(),
                )
                .group()
            }
        }
    }
}

impl Display for SourceExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl TargetExpr {
    pub fn apply(self, theta: &Subst) -> TargetExpr {
        self.map_types(&|m: MigrationalType| m.apply(theta))
    }

    pub fn eliminate(self, elim: &Eliminator) -> TargetExpr {
        self.map_types(&|m: MigrationalType| m.eliminate(elim))
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Expr::Var(x) => pp.text(x),
            Expr::Const(Constant::Bool(true)) => pp.text("true"),
            Expr::Const(Constant::Bool(false)) => pp.text("false"),
            Expr::Const(Constant::Int(n)) => pp.text(n.to_string()),
            Expr::Lam(x, t, e) => pp
                .text("\\")
                .append(pp.text(x))
                .append(pp.space())
                .append(pp.text(":"))
                .append(pp.space())
                .append(t.pretty(pp))
                .append(pp.text("."))
                .append(pp.line())
                .append(e.pretty(pp).nest(1))
                .group(),
            Expr::Ann(e, t) => e
                .pretty(pp)
                .append(pp.space())
                .append(pp.text(":"))
                .append(pp.space())
                .append(t.pretty(pp))
                .group(),
            Expr::App(e1, e2) => {
                let mut d1 = e1.pretty(pp);
                let mut d2 = e2.pretty(pp);

                if e1.is_compound() && !e1.is_app() {
                    d1 = d1.parens();
                }

                if e2.is_compound() {
                    d2 = d2.parens();
                }

                d1.append(pp.line()).append(d2).group()
            }
            Expr::If(e1, e2, e3) => {
                let d_cond = pp
                    .text("if")
                    .append(pp.space())
                    .append(e1.pretty(pp).nest(2))
                    .append(pp.line())
                    .group();

                let d_then = pp
                    .text("then")
                    .append(pp.line())
                    .append(e2.pretty(pp).nest(2))
                    .append(pp.line())
                    .group();

                let d_else = pp
                    .text("else")
                    .append(pp.line())
                    .append(e3.pretty(pp).nest(2))
                    .group();

                pp.concat(vec![d_cond, d_then, d_else])
            }
            Expr::Let(x, t, e1, e2) => {
                let d_bind = pp
                    .intersperse(
                        vec![
                            pp.text("let"),
                            pp.text(x),
                            pp.text(":"),
                            t.pretty(pp),
                            pp.text("="),
                        ],
                        pp.space(),
                    )
                    .group();

                pp.intersperse(
                    vec![
                        d_bind,
                        e1.pretty(pp).nest(2).group(),
                        pp.text("in"),
                        e2.pretty(pp).group(),
                    ],
                    pp.line(),
                )
                .group()
            }
        }
    }
}

impl Display for TargetExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl StaticType {
    pub fn fun(t1: StaticType, t2: StaticType) -> StaticType {
        StaticType::Fun(Box::new(t1), Box::new(t2))
    }
}

impl GradualType {
    pub fn parse<'a>(s: &'a str) -> Result<Self, String> {
        parser::TypeParser::new()
            .parse(s)
            .map_err(|e| e.to_string())
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            GradualType::Dyn() => pp.text("?"),
            GradualType::Base(BaseType::Bool) => pp.text("bool"),
            GradualType::Base(BaseType::Int) => pp.text("int"),
            GradualType::Var(TypeVariable(n)) => pp.text(format!("a{}", n)),
            GradualType::Fun(g1, g2) if g1.is_fun() => g1
                .pretty(pp)
                .parens()
                .group()
                .append(pp.space())
                .append(pp.text("->"))
                .append(pp.line())
                .append(g2.pretty(pp).group())
                .group(),
            GradualType::Fun(g1, g2) => g1
                .pretty(pp)
                .group()
                .append(pp.space())
                .append(pp.text("->"))
                .append(pp.line())
                .append(g2.pretty(pp).group())
                .group(),
        }
    }

    pub fn fun(g1: GradualType, g2: GradualType) -> GradualType {
        GradualType::Fun(Box::new(g1), Box::new(g2))
    }

    pub fn consistent(&self, other: &GradualType) -> bool {
        match (self, other) {
            (GradualType::Dyn(), _) | (_, GradualType::Dyn()) => true,
            (GradualType::Fun(g11, g12), GradualType::Fun(g21, g22)) => {
                g11.consistent(g21) && g12.consistent(g22)
            }
            (g1, g2) => g1 == g2,
        }
    }

    pub fn dom(&self) -> Option<GradualType> {
        match self {
            GradualType::Dyn() => Some(GradualType::Dyn()),
            GradualType::Fun(g1, _) => Some(*g1.clone()),
            _ => None,
        }
    }

    pub fn cod(&self) -> Option<GradualType> {
        match self {
            GradualType::Dyn() => Some(GradualType::Dyn()),
            GradualType::Fun(_, g2) => Some(*g2.clone()),
            _ => None,
        }
    }

    /// should only be called on consistent types
    pub fn meet(&self, other: &GradualType) -> GradualType {
        match (self, other) {
            (GradualType::Dyn(), g) | (g, GradualType::Dyn()) => g.clone(),
            (GradualType::Fun(g11, g12), GradualType::Fun(g21, g22)) => {
                GradualType::fun(g11.meet(g21), g12.meet(g22))
            }
            (g1, g2) => {
                assert_eq!(g1, g2, "meet is only defined on consistent types");
                g1.clone()
            }
        }
    }

    pub fn try_meet(&self, other: &GradualType) -> Option<GradualType> {
        match (self, other) {
            (GradualType::Dyn(), g) | (g, GradualType::Dyn()) => Some(g.clone()),
            (GradualType::Fun(g11, g12), GradualType::Fun(g21, g22)) => {
                let g1 = g11.try_meet(g21)?;
                let g2 = g12.try_meet(g22)?;
                Some(GradualType::fun(g1, g2))
            }
            (g1, g2) => {
                if g1 == g2 {
                    Some(g1.clone())
                } else {
                    None
                }
            }
        }
    }

    pub fn has_dyn(&self) -> bool {
        match self {
            GradualType::Dyn() => true,
            GradualType::Fun(g1, g2) => g1.has_dyn() || g2.has_dyn(),
            GradualType::Base(_) => false,
            GradualType::Var(_) => false,
        }
    }

    pub fn is_fun(&self) -> bool {
        match self {
            GradualType::Fun(_, _) => true,
            _ => false,
        }
    }
}

impl Display for GradualType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl From<&StaticType> for GradualType {
    fn from(t: &StaticType) -> Self {
        match t {
            StaticType::Base(b) => GradualType::Base(b.clone()),
            StaticType::Var(a) => GradualType::Var(a.clone()),
            StaticType::Fun(t1, t2) => GradualType::fun(
                GradualType::from(t1.as_ref()),
                GradualType::from(t2.as_ref()),
            ),
        }
    }
}

impl VariationalType {
    pub fn fun(v1: VariationalType, v2: VariationalType) -> VariationalType {
        VariationalType::Fun(Box::new(v1), Box::new(v2))
    }

    pub fn choice(d: Variation, v1: VariationalType, v2: VariationalType) -> VariationalType {
        // reduced smart constructor, since case (b) of unification needs to generate choices with identical branches!
        // we _do_ project the inner types to the appropriate side of that variation, though
        VariationalType::Choice(
            d,
            Box::new(v1.select(d, Side::Left())),
            Box::new(v2.select(d, Side::Right())),
        )
    }

    pub fn select(&self, d: Variation, side: Side) -> VariationalType {
        match self {
            VariationalType::Base(b) => VariationalType::Base(b.clone()),
            VariationalType::Var(a) => VariationalType::Var(*a),
            VariationalType::Fun(v1, v2) => {
                VariationalType::fun(v1.select(d, side), v2.select(d, side))
            }
            VariationalType::Choice(d2, v1, v2) => {
                if d == *d2 {
                    match side {
                        Side::Left() => v1.select(d, side),
                        Side::Right() => v2.select(d, side),
                    }
                } else {
                    VariationalType::choice(*d2, v1.select(d, side), v2.select(d, side))
                }
            }
        }
    }

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
    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            MigrationalType::Dyn() => pp.text("?"),
            MigrationalType::Base(BaseType::Bool) => pp.text("bool"),
            MigrationalType::Base(BaseType::Int) => pp.text("int"),
            MigrationalType::Var(TypeVariable(n)) => pp.text(format!("a{}", n)),
            MigrationalType::Fun(m1, m2) => {
                let mut dom = m1.pretty(pp);

                if m1.is_fun() {
                    dom = dom.parens()
                }

                dom.append(pp.text(")"))
                    .append(pp.space())
                    .append(pp.text("->"))
                    .append(pp.line())
                    .append(m2.pretty(pp))
                    .group()
            }
            MigrationalType::Choice(Variation(d), m1, m2) => pp
                .text(format!("d{}", d))
                .append(
                    m1.pretty(pp)
                        .append(pp.text(","))
                        .append(m2.pretty(pp))
                        .angles(),
                )
                .group(),
        }
    }

    pub fn fun(m1: MigrationalType, m2: MigrationalType) -> MigrationalType {
        MigrationalType::Fun(Box::new(m1), Box::new(m2))
    }

    pub fn choice(d: Variation, m1: MigrationalType, m2: MigrationalType) -> MigrationalType {
        // reduced smart constructor, since case (b) of unification needs to generate choices with identical branches!
        // we _do_ project the inner types to the appropriate side of that variation, though
        MigrationalType::Choice(
            d,
            Box::new(m1.select(d, Side::Left())),
            Box::new(m2.select(d, Side::Right())),
        )
    }

    pub fn select(&self, d: Variation, side: Side) -> MigrationalType {
        match self {
            MigrationalType::Dyn() => MigrationalType::Dyn(),
            MigrationalType::Base(b) => MigrationalType::Base(b.clone()),
            MigrationalType::Var(a) => MigrationalType::Var(*a),
            MigrationalType::Fun(m1, m2) => {
                MigrationalType::fun(m1.select(d, side), m2.select(d, side))
            }
            MigrationalType::Choice(d2, m1, m2) => {
                if d == *d2 {
                    match side {
                        Side::Left() => m1.select(d, side),
                        Side::Right() => m2.select(d, side),
                    }
                } else {
                    MigrationalType::choice(*d2, m1.select(d, side), m2.select(d, side))
                }
            }
        }
    }

    pub fn eliminate(self, elim: &Eliminator) -> MigrationalType {
        match self {
            MigrationalType::Dyn() | MigrationalType::Base(_) | MigrationalType::Var(_) => self,
            MigrationalType::Fun(m1, m2) => {
                MigrationalType::fun(m1.eliminate(elim), m2.eliminate(elim))
            }
            MigrationalType::Choice(d, m1, m2) => match elim.0.get(&d) {
                Some(Side::Right()) => m2.eliminate(elim),
                Some(Side::Left()) => m1.eliminate(elim),
                None => {
                    warn!(
                        "No choice for variation {:?}; choosing {} over {}",
                        d, m1, m2
                    );
                    m1.eliminate(elim)
                }
            },
        }
    }

    pub fn is_fun(&self) -> bool {
        match self {
            MigrationalType::Fun(_, _) => true,
            _ => false,
        }
    }
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

    pub fn has_dyn(&self) -> bool {
        match self {
            MigrationalType::Dyn() => true,
            MigrationalType::Fun(m1, m2) => m1.has_dyn() || m2.has_dyn(),
            MigrationalType::Choice(_d, m1, m2) => m1.has_dyn() || m2.has_dyn(),
            MigrationalType::Base(_) => false,
            MigrationalType::Var(_) => false,
        }
    }

    pub fn vars(&self) -> HashSet<&TypeVariable> {
        match self {
            MigrationalType::Dyn() | MigrationalType::Base(_) => HashSet::new(),
            MigrationalType::Var(alpha) => HashSet::unit(alpha),
            MigrationalType::Fun(m1, m2) => m1.vars().union(m2.vars()),
            MigrationalType::Choice(_d, m1, m2) => m1.vars().union(m2.vars()),
        }
    }

    pub fn choices(&self) -> HashSet<&Variation> {
        match self {
            MigrationalType::Dyn() | MigrationalType::Base(_) | MigrationalType::Var(_) => {
                HashSet::new()
            }
            MigrationalType::Fun(m1, m2) => m1.choices().union(m2.choices()),
            MigrationalType::Choice(d, m1, m2) => m1.choices().union(m2.choices()).update(d),
        }
    }

    pub fn try_static(&self) -> Option<StaticType> {
        match self {
            MigrationalType::Dyn() | MigrationalType::Choice(_, _, _) => None,
            MigrationalType::Base(b) => Some(StaticType::Base(b.clone())),
            MigrationalType::Var(a) => Some(StaticType::Var(*a)),
            MigrationalType::Fun(m1, m2) => {
                let t1 = m1.try_static()?;
                let t2 = m2.try_static()?;

                Some(StaticType::fun(t1, t2))
            }
        }
    }

    pub fn try_variational(&self) -> Option<VariationalType> {
        match self {
            MigrationalType::Dyn() => None,
            MigrationalType::Base(b) => Some(VariationalType::Base(b.clone())),
            MigrationalType::Var(a) => Some(VariationalType::Var(*a)),
            MigrationalType::Choice(d, m1, m2) => {
                let v1 = m1.try_variational()?;
                let v2 = m2.try_variational()?;

                Some(VariationalType::choice(*d, v1, v2))
            }
            MigrationalType::Fun(m1, m2) => {
                let v1 = m1.try_variational()?;
                let v2 = m2.try_variational()?;

                Some(VariationalType::fun(v1, v2))
            }
        }
    }
}

impl Display for MigrationalType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl From<StaticType> for MigrationalType {
    fn from(t: StaticType) -> Self {
        match t {
            StaticType::Base(b) => MigrationalType::Base(b),
            StaticType::Var(a) => MigrationalType::Var(a),
            StaticType::Fun(t1, t2) => {
                MigrationalType::fun(MigrationalType::from(*t1), MigrationalType::from(*t2))
            }
        }
    }
}

impl From<GradualType> for MigrationalType {
    fn from(g: GradualType) -> Self {
        match g {
            GradualType::Base(b) => MigrationalType::Base(b),
            GradualType::Var(a) => MigrationalType::Var(a),
            GradualType::Dyn() => MigrationalType::Dyn(),
            GradualType::Fun(g1, g2) => {
                MigrationalType::fun(MigrationalType::from(*g1), MigrationalType::from(*g2))
            }
        }
    }
}

impl From<VariationalType> for MigrationalType {
    fn from(t: VariationalType) -> Self {
        match t {
            VariationalType::Base(b) => MigrationalType::Base(b),
            VariationalType::Var(a) => MigrationalType::Var(a),
            VariationalType::Choice(d, t1, t2) => {
                MigrationalType::choice(d, MigrationalType::from(*t1), MigrationalType::from(*t2))
            }
            VariationalType::Fun(t1, t2) => {
                MigrationalType::fun(MigrationalType::from(*t1), MigrationalType::from(*t2))
            }
        }
    }
}

impl From<&Constant> for MigrationalType {
    fn from(c: &Constant) -> Self {
        match c {
            Constant::Bool(_) => MigrationalType::Base(BaseType::Bool),
            Constant::Int(_) => MigrationalType::Base(BaseType::Int),
        }
    }
}

impl Pattern {
    pub fn select(self, d: Variation, side: Side) -> Pattern {
        match self {
            Pattern::Bot() => Pattern::Bot(),
            Pattern::Top() => Pattern::Top(),
            Pattern::Choice(d2, pat1, pat2) => {
                if d == d2 {
                    match side {
                        Side::Left() => *pat1, // shouldn't need recursive select---each variation should appear only once (invariant maintained in Pattern::choice)
                        Side::Right() => *pat2,
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
                Box::new(pat1.select(d, Side::Left())),
                Box::new(pat2.select(d, Side::Right())),
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
                    .map(|ve| ve.update(d, Side::Left()))
                    .collect();
                let ves2: HashSet<Eliminator> = pi2
                    .valid_eliminators()
                    .into_iter()
                    .map(|ve| ve.update(d, Side::Right()))
                    .collect();

                ves1.union(ves2)
            }
        }
    }
}

impl Eliminator {
    pub fn new() -> Self {
        Eliminator(HashMap::new())
    }

    pub fn get(&self, d: &Variation) -> Option<&Side> {
        self.0.get(d)
    }

    pub fn update(self, d: Variation, side: Side) -> Self {
        Eliminator(self.0.update(d, side))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

pub fn expand(elim: Eliminator, ds: &HashSet<&Variation>) -> Eliminator {
    let mut elim = elim;

    for d in ds.iter() {
        if elim.get(d) != Some(&Side::Left()) {
            elim = elim.update(**d, Side::Right());
        }
    }

    elim
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

/// C
///
/// we treat /\ and epsilon by just using vectors in `Constraints`, below
#[derive(Clone, Debug)]
pub enum Constraint {
    Consistent(Pattern, MigrationalType, MigrationalType),
    Choice(Variation, Constraints, Constraints),
}

#[derive(Clone, Debug)]
pub struct Constraints(pub(super) Vec<Constraint>);

impl Constraint {
    pub fn and(self, other: Constraint) -> Constraints {
        Constraints(vec![self, other])
    }

    pub fn apply(self, theta: &Subst) -> Constraint {
        match self {
            Constraint::Consistent(pi, m1, m2) => {
                Constraint::Consistent(pi, m1.apply(theta), m2.apply(theta))
            }
            Constraint::Choice(d, cs1, cs2) => {
                Constraint::Choice(d, cs1.apply(theta), cs2.apply(theta))
            }
        }
    }
}

impl Constraints {
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn expr_id() {
        assert_eq!(
            SourceExpr::parse("fun x. x").unwrap(),
            Expr::lam("x".into(), None, Expr::Var("x".into()))
        );

        assert_eq!(
            SourceExpr::parse("fun x:?. x").unwrap(),
            Expr::lam("x".into(), Some(GradualType::Dyn()), Expr::Var("x".into()))
        );

        assert_eq!(
            SourceExpr::parse("fun x:bool. x").unwrap(),
            Expr::lam(
                "x".into(),
                Some(GradualType::Base(BaseType::Bool)),
                Expr::Var("x".into())
            )
        );
    }

    #[test]
    fn expr_app() {
        assert_eq!(
            SourceExpr::parse("true false 5").unwrap(),
            Expr::app(
                Expr::app(
                    Expr::Const(Constant::Bool(true)),
                    Expr::Const(Constant::Bool(false))
                ),
                Expr::Const(Constant::Int(5))
            )
        );

        assert_eq!(
            SourceExpr::parse("true (false 5)").unwrap(),
            Expr::app(
                Expr::Const(Constant::Bool(true)),
                Expr::app(
                    Expr::Const(Constant::Bool(false)),
                    Expr::Const(Constant::Int(5))
                ),
            )
        );
    }

    #[test]
    fn expr_let() {
        assert!(SourceExpr::parse("let x = 5 in x").is_ok());
        assert!(SourceExpr::parse("let x = 5 in y").is_ok());
        assert!(SourceExpr::parse("let x = 5 in").is_err());
        assert!(SourceExpr::parse("let x = in x").is_err());

        assert!(SourceExpr::parse("let x : bool = 5 in x").is_ok());
        assert!(SourceExpr::parse("let x : int = 5 in x").is_ok());
        assert!(SourceExpr::parse("let x : = 5 in x").is_err());
    }

    #[test]
    fn expr_neg() {
        assert_eq!(
            SourceExpr::parse("fun b:bool. if b then false else true").unwrap(),
            Expr::lam(
                "b".into(),
                Some(GradualType::Base(BaseType::Bool)),
                Expr::if_(
                    Expr::Var("b".into()),
                    Expr::Const(Constant::Bool(false)),
                    Expr::Const(Constant::Bool(true))
                )
            )
        );
    }

    #[test]
    fn const_int() {
        assert!(SourceExpr::parse("22").is_ok());
        assert_eq!(
            SourceExpr::parse("47").unwrap(),
            Expr::Const(Constant::Int(47))
        );
        assert!(SourceExpr::parse("(22)").is_ok());
        assert!(SourceExpr::parse("((((22))))").is_ok());
        assert!(SourceExpr::parse("((22)").is_err());
        assert!(SourceExpr::parse("-47").is_ok());
    }

    #[test]
    fn const_bool() {
        assert_eq!(
            SourceExpr::parse("true").unwrap(),
            Expr::Const(Constant::Bool(true))
        );
        assert_eq!(
            SourceExpr::parse("false").unwrap(),
            Expr::Const(Constant::Bool(false))
        );
        assert_eq!(
            SourceExpr::parse("FALSE").unwrap(),
            Expr::Var("FALSE".to_string())
        );
    }

    #[test]
    fn types_atomic() {
        assert_eq!(
            GradualType::parse("bool").unwrap(),
            GradualType::Base(BaseType::Bool)
        );
        assert_eq!(
            GradualType::parse("int").unwrap(),
            GradualType::Base(BaseType::Int)
        );
        assert_eq!(GradualType::parse("?").unwrap(), GradualType::Dyn());
        assert_eq!(GradualType::parse("dyn").unwrap(), GradualType::Dyn());
    }

    #[test]
    fn types() {
        assert_eq!(
            GradualType::parse("bool->bool").unwrap(),
            GradualType::fun(
                GradualType::Base(BaseType::Bool),
                GradualType::Base(BaseType::Bool)
            )
        );
        assert_eq!(
            GradualType::parse("bool->bool->bool").unwrap(),
            GradualType::fun(
                GradualType::Base(BaseType::Bool),
                GradualType::fun(
                    GradualType::Base(BaseType::Bool),
                    GradualType::Base(BaseType::Bool)
                )
            )
        );

        assert_eq!(
            GradualType::parse("(bool->bool)->bool").unwrap(),
            GradualType::fun(
                GradualType::fun(
                    GradualType::Base(BaseType::Bool),
                    GradualType::Base(BaseType::Bool)
                ),
                GradualType::Base(BaseType::Bool)
            )
        );

        assert_eq!(
            GradualType::parse("(bool -> ?) -> bool").unwrap(),
            GradualType::fun(
                GradualType::fun(GradualType::Base(BaseType::Bool), GradualType::Dyn()),
                GradualType::Base(BaseType::Bool)
            )
        );
    }

    fn type_round_trip(s: &str, pp: &str) {
        let g = GradualType::parse(s).unwrap();
        let g_pp = format!("{}", g);
        assert_eq!(pp, g_pp);

        let g2 = GradualType::parse(&g_pp).unwrap();
        assert_eq!(g2, g);
        assert_eq!(format!("{}", g2), g_pp);

        let m: MigrationalType = g.into();
        let m2 = g2.into();
        assert_eq!(m, m2);
        assert_eq!(format!("{}", m), format!("{}", m2));
    }

    #[test]
    fn pretty_types() {
        type_round_trip("bool", "bool");
        type_round_trip("int", "int");
        type_round_trip("bool->bool", "bool -> bool");
        type_round_trip("bool -> bool", "bool -> bool");
        type_round_trip("\n\r\tbool\t-> bool", "bool -> bool");
        type_round_trip("(int->int)->int", "(int -> int) -> int");
        type_round_trip("(int -> bool) -> bool", "(int -> bool) -> bool");
        type_round_trip("int->int->int", "int -> int -> int");
    }

    fn se_round_trip(s: &str, pp: &str) {
        let e = SourceExpr::parse(s).unwrap();
        let e_pp = format!("{}", e);

        assert_eq!(pp, e_pp);

        let e2 = SourceExpr::parse(&e_pp).unwrap();
        // may not be equal due to empty annotations... but shouldn't come up
        assert_eq!(e, e2);
        assert_eq!(format!("{}", e2), e_pp);
    }

    #[test]
    fn pretty_sourceexpr() {
        se_round_trip("true", "true");
        se_round_trip("false", "false");
        se_round_trip("5", "5");
        se_round_trip("-20", "-20");
        se_round_trip("4747", "4747");

        se_round_trip("x", "x");
        se_round_trip("\\x. x", "\\x. x");
        se_round_trip("fun x. x", "\\x. x");
        se_round_trip("\\x:bool. x", "\\x : bool. x");

        se_round_trip(
            "if true then false else \\x. x",
            "if true then false else \\x. x",
        );

        se_round_trip("a    b \t c", "a b c");
        se_round_trip("a (b c d)", "a (b c d)");
        se_round_trip("let x = a in b", "let x = a in b");

        // durrrrr
        se_round_trip("let x = (\\x. x) (\\y. y) (\\z. z) (\\w. w) 5 in (\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) x", 
                      "let x =\n(\\x. x) (\\y. y) (\\z. z) (\\w. w) 5\nin\n(\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) (\\x. x) x");
    }
}
