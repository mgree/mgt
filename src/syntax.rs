use std::cmp::PartialEq;
use std::fmt::Display;
use std::hash::Hash;

use im_rc::HashSet;

pub const DEFAULT_WIDTH: usize = 80;

lalrpop_mod!(parser);

/// gamma
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BaseType {
    Bool,
    Int,
}

/// alpha
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct TypeVariable(pub(super) usize);

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

/// c
#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    Bool(bool),
    Int(isize),
}

/// unary operations in source expressions
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceUOp {
    Not,
    Negate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceBOp {
    Plus,
    Minus,
    Times,
    Divide,
    And,
    Or,
    Equal,
    LessThan,
    LessThanEqual,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TargetUOp {
    Not,
    Negate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TargetBOp {
    Plus,
    Minus,
    Times,
    Divide,
    And,
    Or,
    EqualBool,
    EqualInt,
    EqualDyn,
    LessThan,
    LessThanEqual,
    Choice(Variation, Box<TargetBOp>, Box<TargetBOp>),
}

/// x
pub type Variable = String;

/// e (ITGL)
#[derive(Clone, Debug, PartialEq)]
pub enum Expr<T, U, B> {
    Const(Constant),
    Var(Variable),
    Lam(Variable, T, Box<Self>),
    Ann(Box<Expr<T, U, B>>, T),
    App(Box<Expr<T, U, B>>, Box<Expr<T, U, B>>),
    If(Box<Expr<T, U, B>>, Box<Expr<T, U, B>>, Box<Expr<T, U, B>>),
    Let(Variable, T, Box<Expr<T, U, B>>, Box<Expr<T, U, B>>),
    LetRec(Vec<(Variable, T, Expr<T, U, B>)>, Box<Expr<T, U, B>>),
    UOp(U, Box<Expr<T, U, B>>),
    BOp(B, Box<Expr<T, U, B>>, Box<Expr<T, U, B>>),
}

pub type SourceExpr = Expr<Option<GradualType>, SourceUOp, SourceBOp>;
pub type TargetExpr = Expr<MigrationalType, TargetUOp, TargetBOp>;

impl<T, U, B> Expr<T, U, B> {
    pub fn bool(b: bool) -> Self {
        Expr::Const(Constant::Bool(b))
    }

    pub fn int(n: isize) -> Self {
        Expr::Const(Constant::Int(n))
    }

    pub fn lam(v: Variable, t: T, e: Self) -> Self {
        Expr::Lam(v, t, Box::new(e))
    }

    pub fn ann(e: Self, t: T) -> Self {
        Expr::Ann(Box::new(e), t)
    }

    pub fn app(e1: Self, e2: Self) -> Self {
        Expr::App(Box::new(e1), Box::new(e2))
    }

    pub fn if_(e1: Self, e2: Self, e3: Self) -> Self {
        Expr::If(Box::new(e1), Box::new(e2), Box::new(e3))
    }

    pub fn let_(x: Variable, t: T, e1: Self, e2: Self) -> Self {
        Expr::Let(x, t, Box::new(e1), Box::new(e2))
    }

    pub fn letrec(defns: Vec<(Variable, T, Self)>, e2: Self) -> Self {
        Expr::LetRec(defns, Box::new(e2))
    }

    pub fn uop(op: U, e: Self) -> Self {
        Expr::UOp(op, Box::new(e))
    }

    pub fn bop(op: B, e1: Self, e2: Self) -> Self {
        Expr::BOp(op, Box::new(e1), Box::new(e2))
    }

    pub fn map_types<F, S>(self, f: &F) -> Expr<S, U, B>
    where
        F: Fn(T) -> S,
    {
        match self {
            Expr::Const(c) => Expr::Const(c),
            Expr::Var(x) => Expr::Var(x),
            Expr::Lam(x, t, e) => Expr::lam(x, f(t), e.map_types(f)),
            Expr::App(e1, e2) => Expr::app(e1.map_types(f), e2.map_types(f)),
            Expr::Ann(e, t) => Expr::ann(e.map_types(f), f(t)),
            Expr::If(e1, e2, e3) => Expr::if_(e1.map_types(f), e2.map_types(f), e3.map_types(f)),
            Expr::Let(x, t, e1, e2) => Expr::let_(x, f(t), e1.map_types(f), e2.map_types(f)),
            Expr::LetRec(defns, e2) => Expr::letrec(
                defns
                    .into_iter()
                    .map(|(v, t, e1)| (v, f(t), e1.map_types(f)))
                    .collect(),
                e2.map_types(f),
            ),
            Expr::UOp(op, e) => Expr::uop(op, e.map_types(f)),
            Expr::BOp(op, e1, e2) => Expr::bop(op, e1.map_types(f), e2.map_types(f)),
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
                .append(e.pretty(pp).nest(2))
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
                .append(e.pretty(pp).nest(2))
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
            Expr::LetRec(defns, e2) => {
                let letrec = pp.text("let rec").append(pp.space());

                let bindings = pp.intersperse(
                    defns.into_iter().map(|(x, t, e1)| {
                        let d_annot = if let Some(t) = t {
                            pp.intersperse(
                                vec![pp.text(":"), t.pretty(pp), pp.text("=")],
                                pp.space(),
                            )
                        } else {
                            pp.text("=")
                        };

                        pp.text(x)
                            .append(pp.space())
                            .append(d_annot.group())
                            .append(pp.line())
                            .append(e1.pretty(pp).nest(2))
                    }),
                    pp.text("and").enclose(pp.hardline(), pp.hardline()),
                );

                letrec
                    .append(bindings)
                    .append(pp.hardline())
                    .append(pp.text("in"))
                    .append(pp.line())
                    .append(e2.pretty(pp))
            }
            // TODO proper pretty printing with precedence
            Expr::UOp(op, e) => pp
                .as_string(op)
                .append(pp.space())
                .append(if e.is_compound() {
                    e.pretty(pp).parens()
                } else {
                    e.pretty(pp)
                }),
            Expr::BOp(op, e1, e2) => pp.intersperse(
                vec![
                    if e1.is_compound() {
                        e1.pretty(pp).parens()
                    } else {
                        e1.pretty(pp)
                    },
                    pp.as_string(op),
                    if e2.is_compound() {
                        e2.pretty(pp).parens()
                    } else {
                        e2.pretty(pp)
                    },
                ],
                pp.space(),
            ),
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

impl TargetUOp {
    pub fn choices(&self) -> HashSet<&Variation> {
        match self {
            TargetUOp::Negate => HashSet::new(),
            TargetUOp::Not => HashSet::new(),
        }
    }
}

impl TargetBOp {
    pub fn choices(&self) -> HashSet<&Variation> {
        match self {
            TargetBOp::Choice(d, op1, op2) => op1.choices().union(op2.choices()).update(d),
            _ => HashSet::new(),
        }
    }

    pub fn choice(d: Variation, op1: Self, op2: Self) -> Self {
        TargetBOp::Choice(
            d,
            Box::new(op1.select(d, Side::Left())),
            Box::new(op2.select(d, Side::Right())),
        )
    }

    pub fn select(&self, d: Variation, side: Side) -> Self {
        match self {
            TargetBOp::Choice(d2, op1, op2) => {
                if d == *d2 {
                    match side {
                        Side::Left() => op1.select(d, side),
                        Side::Right() => op2.select(d, side),
                    }
                } else {
                    TargetBOp::choice(*d2, op1.select(d, side), op2.select(d, side))
                }
            }
            _ => self.clone(),
        }
    }
}

impl TargetExpr {
    pub fn choices(&self) -> HashSet<&Variation> {
        match self {
            Expr::Const(_) | Expr::Var(_) => HashSet::new(),
            Expr::Lam(_x, t, e) => t.choices().union(e.choices()),
            Expr::Ann(e, t) => e.choices().union(t.choices()),
            Expr::App(e1, e2) => e1.choices().union(e2.choices()),
            Expr::If(e1, e2, e3) => e1.choices().union(e2.choices()).union(e3.choices()),
            Expr::Let(_x, t, e1, e2) => t.choices().union(e1.choices()).union(e2.choices()),
            Expr::LetRec(defns, e2) => {
                let ds = defns
                    .into_iter()
                    .map(|(_x, t, e1)| t.choices().union(e1.choices()));
                HashSet::unions(ds).union(e2.choices())
            }
            Expr::UOp(op, e) => op.choices().union(e.choices()),
            Expr::BOp(op, e1, e2) => {
                HashSet::unions(vec![op.choices(), e1.choices(), e2.choices()])
            }
        }
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
                .append(e.pretty(pp).nest(2))
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

                d1.append(pp.line()).append(d2.nest(2)).group()
            }
            Expr::If(e1, e2, e3) => {
                let d_cond = pp
                    .text("if")
                    .append(pp.space())
                    .append(e1.pretty(pp).nest(2))
                    .append(pp.line());

                let d_then = pp
                    .text("then")
                    .append(pp.line())
                    .append(e2.pretty(pp).nest(2))
                    .append(pp.line());

                let d_else = pp
                    .text("else")
                    .append(pp.line())
                    .append(e3.pretty(pp).nest(2));

                pp.concat(vec![d_cond, d_then, d_else]).group()
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
                    vec![d_bind, e1.pretty(pp).nest(2), pp.text("in")],
                    pp.line(),
                )
                .append(pp.hardline())
                .append(e2.pretty(pp))
            }
            Expr::LetRec(defns, e2) => {
                let letrec = pp.text("let rec").append(pp.space());

                let bindings = pp.intersperse(
                    defns.into_iter().map(|(x, t, e1)| {
                        pp.intersperse(
                            vec![pp.text(x), pp.text(":"), t.pretty(pp), pp.text("=")],
                            pp.space(),
                        )
                        .group()
                        .append(pp.line())
                        .append(e1.pretty(pp).nest(2))
                    }),
                    pp.text("and").enclose(pp.hardline(), pp.hardline()),
                );

                letrec
                    .append(bindings)
                    .append(pp.hardline())
                    .append(pp.text("in"))
                    .append(pp.line())
                    .append(e2.pretty(pp))
            }
            // TODO proper pretty printing with precedence
            Expr::UOp(op, e) => pp
                .as_string(op)
                .append(pp.space())
                .append(if e.is_compound() {
                    e.pretty(pp).parens()
                } else {
                    e.pretty(pp)
                }),
            Expr::BOp(op, e1, e2) => pp.intersperse(
                vec![
                    if e1.is_compound() {
                        e1.pretty(pp).parens()
                    } else {
                        e1.pretty(pp)
                    },
                    pp.as_string(op),
                    if e2.is_compound() {
                        e2.pretty(pp).parens()
                    } else {
                        e2.pretty(pp)
                    },
                ],
                pp.space(),
            ),
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

impl Display for TypeVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a{}", self.0)
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
            GradualType::Var(a) => pp.as_string(a),
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

impl VariationalType {
    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            VariationalType::Base(BaseType::Bool) => pp.text("bool"),
            VariationalType::Base(BaseType::Int) => pp.text("int"),
            VariationalType::Var(a) => pp.as_string(a),
            VariationalType::Fun(v1, v2) => {
                let mut dom = v1.pretty(pp);

                if v1.is_fun() {
                    dom = dom.parens()
                }

                dom.append(pp.text(")"))
                    .append(pp.space())
                    .append(pp.text("->"))
                    .append(pp.line())
                    .append(v2.pretty(pp))
                    .group()
            }
            VariationalType::Choice(Variation(d), v1, v2) => pp
                .text(format!("d{}", d))
                .append(
                    v1.pretty(pp)
                        .append(pp.text(","))
                        .append(v2.pretty(pp))
                        .angles(),
                )
                .group(),
        }
    }

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

    pub fn is_fun(&self) -> bool {
        match self {
            VariationalType::Fun(_, _) => true,
            _ => false,
        }
    }
}

impl Display for VariationalType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl MigrationalType {
    pub fn bool() -> Self {
        MigrationalType::Base(BaseType::Bool)
    }

    pub fn int() -> Self {
        MigrationalType::Base(BaseType::Int)
    }

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
            MigrationalType::Var(a) => pp.as_string(a),
            MigrationalType::Fun(m1, m2) => {
                let mut dom = m1.pretty(pp);

                if m1.is_fun() {
                    dom = dom.parens()
                }

                dom.append(pp.space())
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

    pub fn is_fun(&self) -> bool {
        match self {
            MigrationalType::Fun(_, _) => true,
            _ => false,
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
            Constant::Bool(_) => MigrationalType::bool(),
            Constant::Int(_) => MigrationalType::int(),
        }
    }
}

impl Default for Side {
    fn default() -> Self {
        Side::Right()
    }
}

impl Display for Variation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "d{}", self.0)
    }
}

impl Display for Side {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Side::Left() => write!(f, "L"),
            Side::Right() => write!(f, "R"),
        }
    }
}

impl Display for SourceUOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            SourceUOp::Not => "!",
            SourceUOp::Negate => "-",
        };
        write!(f, "{}", s)
    }
}

impl Display for SourceBOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            SourceBOp::Plus => "+",
            SourceBOp::Minus => "-",
            SourceBOp::Times => "*",
            SourceBOp::Divide => "/",
            SourceBOp::And => "&&",
            SourceBOp::Or => "||",
            SourceBOp::Equal => "==",
            SourceBOp::LessThan => "<",
            SourceBOp::LessThanEqual => "<=",
        };
        write!(f, "{}", s)
    }
}

impl Display for TargetUOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            TargetUOp::Not => "!",
            TargetUOp::Negate => "-",
        };
        write!(f, "{}", s)
    }
}

impl Display for TargetBOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            TargetBOp::Plus => "+",
            TargetBOp::Minus => "-",
            TargetBOp::Times => "*",
            TargetBOp::Divide => "/",
            TargetBOp::And => "&&",
            TargetBOp::Or => "||",
            TargetBOp::EqualBool => "==b",
            TargetBOp::EqualInt => "==i",
            TargetBOp::EqualDyn => "==?",
            TargetBOp::LessThan => "<",
            TargetBOp::LessThanEqual => "<=",
            TargetBOp::Choice(d, op1, op2) => return write!(f, "{}<{}, {}>", d, op1, op2),
        };
        write!(f, "{}", s)
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

        se_round_trip("-x", "- x");
        se_round_trip("5-x", "5 - x");
        se_round_trip("-(m*x + b)", "- ((m * x) + b)");

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
