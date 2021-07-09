use std::cmp::PartialEq;
use std::fmt::Display;

use log::{error, info, warn};

use im_rc::OrdSet;

use crate::options::DEFAULT_WIDTH;
pub use crate::types::*;

#[allow(clippy::all)]
lalrpop_mod!(parser);

/// c
#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    Bool(bool),
    Int(isize),
    String(String),
}

/// unary operations in source expressions
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceUOp {
    Not,
    Negate,
    Is(GroundType),
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
pub enum ExplicitUOp {
    Not,
    Negate,
    Is(GroundType),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExplicitBOp {
    PlusInt,
    PlusString,
    PlusDyn,
    Minus,
    Times,
    Divide,
    And,
    Or,
    EqualBool,
    EqualInt,
    EqualString,
    EqualDyn,
    LessThan,
    LessThanEqual,
    Choice(Variation, Box<ExplicitBOp>, Box<ExplicitBOp>),
}

/// x
pub type Variable = String;

/// e (ITGL)
#[derive(Clone, Debug, PartialEq)]
pub enum GradualExpr<T, U, B> {
    Const(Constant),
    Var(Variable),
    Lam(Variable, T, Box<Self>),
    Ann(Box<GradualExpr<T, U, B>>, T),
    Hole(String, T),
    App(Box<GradualExpr<T, U, B>>, Box<GradualExpr<T, U, B>>),
    If(
        Box<GradualExpr<T, U, B>>,
        Box<GradualExpr<T, U, B>>,
        Box<GradualExpr<T, U, B>>,
    ),
    Let(
        Variable,
        T,
        Box<GradualExpr<T, U, B>>,
        Box<GradualExpr<T, U, B>>,
    ),
    LetRec(
        Vec<(Variable, T, GradualExpr<T, U, B>)>,
        Box<GradualExpr<T, U, B>>,
    ),
    UOp(U, Box<GradualExpr<T, U, B>>),
    BOp(B, Box<GradualExpr<T, U, B>>, Box<GradualExpr<T, U, B>>),
    Nil(T),
    Cons(Box<GradualExpr<T, U, B>>, Box<GradualExpr<T, U, B>>),
    /// Match(scrutinee, nil, h, t, cons (binding h and t))
    Match(
        Box<GradualExpr<T, U, B>>,
        Box<GradualExpr<T, U, B>>,
        Variable,
        Variable,
        Box<GradualExpr<T, U, B>>,
    ),
}

pub type SourceExpr = GradualExpr<Option<GradualType>, SourceUOp, SourceBOp>;
pub type TargetExpr = GradualExpr<MigrationalType, ExplicitUOp, ExplicitBOp>;

/// gamma
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GroundType {
    Base(BaseType),
    List,
    Fun,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IdType {
    Trivial,
    Safe,
    Unsafe,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Coercion {
    Id(IdType, GradualType),
    /// gamma!
    Tag(GroundType),
    /// gamma?
    Check(GroundType),
    Fun(Box<Coercion>, Box<Coercion>),
    Seq(Box<Coercion>, Box<Coercion>),
    List(Box<Coercion>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExplicitExpr {
    Const(Constant),
    Var(Variable),
    Lam(Variable, GradualType, Box<ExplicitExpr>),
    Hole(String, GradualType),
    Coerce(Box<ExplicitExpr>, Coercion),
    App(Box<ExplicitExpr>, Box<ExplicitExpr>),
    If(Box<ExplicitExpr>, Box<ExplicitExpr>, Box<ExplicitExpr>),
    Let(Variable, GradualType, Box<ExplicitExpr>, Box<ExplicitExpr>),
    LetRec(
        Vec<(Variable, GradualType, ExplicitExpr)>,
        Box<ExplicitExpr>,
    ),
    UOp(ExplicitUOp, Box<ExplicitExpr>),
    BOp(ExplicitBOp, Box<ExplicitExpr>, Box<ExplicitExpr>),
    Nil(GradualType),
    Cons(Box<ExplicitExpr>, Box<ExplicitExpr>),
    /// Match(scrutinee, nil, h, t, cons (binding h and t))
    Match(
        Box<ExplicitExpr>,
        Box<ExplicitExpr>,
        Variable,
        Variable,
        Box<ExplicitExpr>,
    ),
}

impl GradualType {
    pub fn parse(s: &str) -> Result<Self, String> {
        parser::TypeParser::new()
            .parse(s)
            .map_err(|e| e.to_string())
    }
}

impl Constant {
    pub fn ground_type(&self) -> GroundType {
        match self {
            Constant::Bool(_) => GroundType::Base(BaseType::Bool),
            Constant::Int(_) => GroundType::Base(BaseType::Int),
            Constant::String(_) => GroundType::Base(BaseType::String),
        }
    }
}

impl<T, U, B> GradualExpr<T, U, B> {
    pub fn bool(b: bool) -> Self {
        GradualExpr::Const(Constant::Bool(b))
    }

    pub fn int(n: isize) -> Self {
        GradualExpr::Const(Constant::Int(n))
    }

    pub fn lam(v: Variable, t: T, e: Self) -> Self {
        GradualExpr::Lam(v, t, Box::new(e))
    }

    pub fn lams(args: Vec<(String, T)>, e: Self) -> Self {
        args.into_iter()
            .rev()
            .fold(e, |e, (x, t)| GradualExpr::lam(x, t, e))
    }

    pub fn ann(e: Self, t: T) -> Self {
        GradualExpr::Ann(Box::new(e), t)
    }

    pub fn app(e1: Self, e2: Self) -> Self {
        GradualExpr::App(Box::new(e1), Box::new(e2))
    }

    pub fn if_(e1: Self, e2: Self, e3: Self) -> Self {
        GradualExpr::If(Box::new(e1), Box::new(e2), Box::new(e3))
    }

    pub fn let_(x: Variable, t: T, e1: Self, e2: Self) -> Self {
        GradualExpr::Let(x, t, Box::new(e1), Box::new(e2))
    }

    pub fn letrec(defns: Vec<(Variable, T, Self)>, e2: Self) -> Self {
        GradualExpr::LetRec(defns, Box::new(e2))
    }

    pub fn uop(op: U, e: Self) -> Self {
        GradualExpr::UOp(op, Box::new(e))
    }

    pub fn bop(op: B, e1: Self, e2: Self) -> Self {
        GradualExpr::BOp(op, Box::new(e1), Box::new(e2))
    }

    pub fn cons(e1: Self, e2: Self) -> Self {
        GradualExpr::Cons(Box::new(e1), Box::new(e2))
    }

    pub fn match_(
        e_scrutinee: Self,
        e_nil: Self,
        hd: Variable,
        tl: Variable,
        e_cons: Self,
    ) -> Self {
        GradualExpr::Match(
            Box::new(e_scrutinee),
            Box::new(e_nil),
            hd,
            tl,
            Box::new(e_cons),
        )
    }

    pub fn map_types<F, S>(self, f: &F) -> GradualExpr<S, U, B>
    where
        F: Fn(T) -> S,
    {
        match self {
            GradualExpr::Const(c) => GradualExpr::Const(c),
            GradualExpr::Var(x) => GradualExpr::Var(x),
            GradualExpr::Lam(x, t, e) => GradualExpr::lam(x, f(t), e.map_types(f)),
            GradualExpr::App(e1, e2) => GradualExpr::app(e1.map_types(f), e2.map_types(f)),
            GradualExpr::Ann(e, t) => GradualExpr::ann(e.map_types(f), f(t)),
            GradualExpr::Hole(name, t) => GradualExpr::Hole(name, f(t)),
            GradualExpr::If(e1, e2, e3) => {
                GradualExpr::if_(e1.map_types(f), e2.map_types(f), e3.map_types(f))
            }
            GradualExpr::Let(x, t, e1, e2) => {
                GradualExpr::let_(x, f(t), e1.map_types(f), e2.map_types(f))
            }
            GradualExpr::LetRec(defns, e2) => GradualExpr::letrec(
                defns
                    .into_iter()
                    .map(|(v, t, e1)| (v, f(t), e1.map_types(f)))
                    .collect(),
                e2.map_types(f),
            ),
            GradualExpr::UOp(op, e) => GradualExpr::uop(op, e.map_types(f)),
            GradualExpr::BOp(op, e1, e2) => GradualExpr::bop(op, e1.map_types(f), e2.map_types(f)),
            GradualExpr::Nil(t) => GradualExpr::Nil(f(t)),
            GradualExpr::Cons(e1, e2) => GradualExpr::cons(e1.map_types(f), e2.map_types(f)),
            GradualExpr::Match(e_scrutinee, e_nil, hd, tl, e_cons) => GradualExpr::match_(
                e_scrutinee.map_types(f),
                e_nil.map_types(f),
                hd,
                tl,
                e_cons.map_types(f),
            ),
        }
    }

    pub fn is_compound(&self) -> bool {
        match self {
            GradualExpr::Var(_) | GradualExpr::Const(_) | GradualExpr::Hole(_, _) => false,
            _ => true,
        }
    }

    pub fn is_app(&self) -> bool {
        match self {
            GradualExpr::App(_, _) => true,
            _ => false,
        }
    }
}

impl SourceExpr {
    pub fn list(elts: Vec<Self>) -> Self {
        elts.into_iter()
            .rev()
            .fold(GradualExpr::Nil(None), |t, h| GradualExpr::cons(h, t))
    }

    pub fn parse(s: &str) -> Result<Self, String> {
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
            GradualExpr::Var(x) => pp.text(x),
            GradualExpr::Const(c) => pp.as_string(c),
            GradualExpr::Lam(x, None, e) => pp
                .text("\\")
                .append(pp.text(x))
                .append(pp.text("."))
                .append(pp.line())
                .append(e.pretty(pp).nest(2))
                .group(),
            GradualExpr::Lam(x, Some(t), e) => pp
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
            GradualExpr::Hole(name, None) => pp.text(name),
            GradualExpr::Hole(name, Some(t)) => pp
                .text(name)
                .append(pp.space())
                .append(pp.text(":"))
                .append(pp.space())
                .append(t.pretty(pp))
                .group(),
            GradualExpr::Ann(e, None) => e.pretty(pp),
            GradualExpr::Ann(e, Some(t)) => e
                .pretty(pp)
                .append(pp.space())
                .append(pp.text(":"))
                .append(pp.space())
                .append(t.pretty(pp))
                .group(),
            GradualExpr::App(e1, e2) => {
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
            GradualExpr::If(e1, e2, e3) => {
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
            GradualExpr::Let(x, t, e1, e2) => {
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
            GradualExpr::LetRec(defns, e2) => {
                let letrec = pp.text("let rec").append(pp.space());

                let bindings = pp.intersperse(
                    defns.iter().map(|(x, t, e1)| {
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
            GradualExpr::UOp(op, e) => {
                pp.as_string(op)
                    .append(pp.space())
                    .append(if e.is_compound() {
                        e.pretty(pp).parens()
                    } else {
                        e.pretty(pp)
                    })
            }
            GradualExpr::BOp(op, e1, e2) => pp.intersperse(
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
            GradualExpr::Nil(_t) => pp.text("[]"),
            // TODO identify concrete lists and pretty print accordingly
            GradualExpr::Cons(e1, e2) => pp.intersperse(
                vec![
                    if e1.is_compound() {
                        e1.pretty(pp).parens()
                    } else {
                        e1.pretty(pp)
                    },
                    pp.text("::"),
                    if e2.is_compound() {
                        e2.pretty(pp).parens()
                    } else {
                        e2.pretty(pp)
                    },
                ],
                pp.line(),
            ),
            GradualExpr::Match(e_scrutinee, e_nil, hd, tl, e_cons) => pp.intersperse(
                vec![
                    pp.intersperse(
                        vec![pp.text("match"), e_scrutinee.pretty(pp), pp.text("with")],
                        pp.space(),
                    )
                    .group(),
                    pp.intersperse(
                        vec![
                            pp.text("|"),
                            pp.text("[]"),
                            pp.text("->"),
                            e_nil.pretty(pp).indent(2),
                        ],
                        pp.space(),
                    )
                    .group(),
                    pp.intersperse(
                        vec![
                            pp.text("|"),
                            pp.as_string(hd),
                            pp.text("::"),
                            pp.as_string(tl),
                            pp.text("->"),
                            e_cons.pretty(pp).indent(2),
                        ],
                        pp.space(),
                    )
                    .group(),
                ],
                pp.line(),
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

impl ExplicitUOp {
    pub fn choices(&self) -> OrdSet<&Variation> {
        match self {
            ExplicitUOp::Negate => OrdSet::new(),
            ExplicitUOp::Not => OrdSet::new(),
            ExplicitUOp::Is(_g) => OrdSet::new(),
        }
    }
}

impl ExplicitBOp {
    pub fn choices(&self) -> OrdSet<&Variation> {
        match self {
            ExplicitBOp::Choice(d, op1, op2) => op1.choices().union(op2.choices()).update(d),
            _ => OrdSet::new(),
        }
    }

    pub fn choice(d: Variation, op1: Self, op2: Self) -> Self {
        ExplicitBOp::Choice(
            d,
            Box::new(op1.select(d, Side::Left)),
            Box::new(op2.select(d, Side::Right)),
        )
    }

    pub fn select(&self, d: Variation, side: Side) -> Self {
        match self {
            ExplicitBOp::Choice(d2, op1, op2) => {
                if d == *d2 {
                    match side {
                        Side::Left => op1.select(d, side),
                        Side::Right => op2.select(d, side),
                    }
                } else {
                    ExplicitBOp::choice(*d2, op1.select(d, side), op2.select(d, side))
                }
            }
            _ => self.clone(),
        }
    }
}

impl TargetExpr {
    pub fn dynamize_type_variables(&mut self) {
        match self {
            GradualExpr::Const(_) | GradualExpr::Var(_) => (),
            GradualExpr::Lam(_, m, e) => {
                m.dynamize_type_variables();
                e.dynamize_type_variables();
            }
            GradualExpr::Ann(e, m) => {
                e.dynamize_type_variables();
                m.dynamize_type_variables();
            }
            GradualExpr::Hole(_, m) => m.dynamize_type_variables(),
            GradualExpr::App(e1, e2) => {
                e1.dynamize_type_variables();
                e2.dynamize_type_variables();
            }
            GradualExpr::If(e1, e2, e3) => {
                e1.dynamize_type_variables();
                e2.dynamize_type_variables();
                e3.dynamize_type_variables();
            }
            GradualExpr::Let(_, m, e1, e2) => {
                m.dynamize_type_variables();
                e1.dynamize_type_variables();
                e2.dynamize_type_variables();
            }
            GradualExpr::LetRec(defns, e2) => {
                for (_, m, e1) in defns.iter_mut() {
                    m.dynamize_type_variables();
                    e1.dynamize_type_variables();
                }
                e2.dynamize_type_variables();
            }
            GradualExpr::UOp(_, e) => {
                e.dynamize_type_variables();
            }
            GradualExpr::BOp(_, e1, e2) => {
                e1.dynamize_type_variables();
                e2.dynamize_type_variables();
            }
            GradualExpr::Nil(m) => m.dynamize_type_variables(),
            GradualExpr::Cons(e1, e2) => {
                e1.dynamize_type_variables();
                e2.dynamize_type_variables();
            }
            GradualExpr::Match(e1, e2, _, _, e3) => {
                e1.dynamize_type_variables();
                e2.dynamize_type_variables();
                e3.dynamize_type_variables();
            }
        }
    }

    pub fn choices(&self) -> OrdSet<&Variation> {
        match self {
            GradualExpr::Const(_) | GradualExpr::Var(_) => OrdSet::new(),
            GradualExpr::Lam(_, t, e) | GradualExpr::Ann(e, t) => t.choices().union(e.choices()),
            GradualExpr::Hole(_, t) | GradualExpr::Nil(t) => t.choices(),
            GradualExpr::App(e1, e2) | GradualExpr::Cons(e1, e2) => {
                e1.choices().union(e2.choices())
            }
            GradualExpr::If(e1, e2, e3) | GradualExpr::Match(e1, e2, _, _, e3) => {
                e1.choices().union(e2.choices()).union(e3.choices())
            }
            GradualExpr::Let(_x, t, e1, e2) => t.choices().union(e1.choices()).union(e2.choices()),
            GradualExpr::LetRec(defns, e2) => {
                let ds = defns
                    .iter()
                    .map(|(_x, t, e1)| t.choices().union(e1.choices()));
                OrdSet::unions(ds).union(e2.choices())
            }
            GradualExpr::UOp(op, e) => op.choices().union(e.choices()),
            GradualExpr::BOp(op, e1, e2) => {
                OrdSet::unions(vec![op.choices(), e1.choices(), e2.choices()])
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
            GradualExpr::Var(x) => pp.text(x),
            GradualExpr::Const(c) => pp.as_string(c),
            GradualExpr::Lam(x, t, e) => pp
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
            GradualExpr::Hole(name, t) => pp
                .text(name)
                .append(pp.space())
                .append(pp.text(":"))
                .append(pp.space())
                .append(t.pretty(pp))
                .group(),
            GradualExpr::Ann(e, t) => e
                .pretty(pp)
                .append(pp.space())
                .append(pp.text(":"))
                .append(pp.space())
                .append(t.pretty(pp))
                .group(),
            GradualExpr::App(e1, e2) => {
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
            GradualExpr::If(e1, e2, e3) => {
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
            GradualExpr::Let(x, t, e1, e2) => {
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
            GradualExpr::LetRec(defns, e2) => {
                let letrec = pp.text("let rec").append(pp.space());

                let bindings = pp.intersperse(
                    defns.iter().map(|(x, t, e1)| {
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
            GradualExpr::UOp(op, e) => {
                pp.as_string(op)
                    .append(pp.space())
                    .append(if e.is_compound() {
                        e.pretty(pp).parens()
                    } else {
                        e.pretty(pp)
                    })
            }
            GradualExpr::BOp(op, e1, e2) => pp.intersperse(
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
            GradualExpr::Nil(t) => {
                pp.intersperse(vec![pp.text("[]"), pp.text(":"), t.pretty(pp)], pp.space())
            }
            // TODO identify concrete lists and pretty print accordingly
            GradualExpr::Cons(e1, e2) => pp.intersperse(
                vec![
                    if e1.is_compound() {
                        e1.pretty(pp).parens()
                    } else {
                        e1.pretty(pp)
                    },
                    pp.text("::"),
                    if e2.is_compound() {
                        e2.pretty(pp).parens()
                    } else {
                        e2.pretty(pp)
                    },
                ],
                pp.line(),
            ),
            GradualExpr::Match(e_scrutinee, e_nil, hd, tl, e_cons) => pp.intersperse(
                vec![
                    pp.intersperse(
                        vec![pp.text("match"), e_scrutinee.pretty(pp), pp.text("with")],
                        pp.space(),
                    )
                    .group(),
                    pp.intersperse(
                        vec![
                            pp.text("|"),
                            pp.text("[]"),
                            pp.text("->"),
                            e_nil.pretty(pp).indent(2),
                        ],
                        pp.space(),
                    )
                    .group(),
                    pp.intersperse(
                        vec![
                            pp.text("|"),
                            pp.as_string(hd),
                            pp.text("::"),
                            pp.as_string(tl),
                            pp.text("->"),
                            e_cons.pretty(pp).indent(2),
                        ],
                        pp.space(),
                    )
                    .group(),
                ],
                pp.line(),
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

impl Display for BaseType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BaseType::Bool => write!(f, "bool"),
            BaseType::Int => write!(f, "int"),
            BaseType::String => write!(f, "string"),
        }
    }
}

impl Display for GroundType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GroundType::Base(b) => b.fmt(f),
            GroundType::List => write!(f, "list"),
            GroundType::Fun => write!(f, "fun"),
        }
    }
}

impl ExplicitExpr {
    pub fn bool(b: bool) -> Self {
        ExplicitExpr::Const(Constant::Bool(b))
    }

    pub fn int(n: isize) -> Self {
        ExplicitExpr::Const(Constant::Int(n))
    }

    pub fn lam(v: Variable, g: GradualType, e: Self) -> Self {
        ExplicitExpr::Lam(v, g, Box::new(e))
    }

    pub fn lams(args: Vec<(String, GradualType)>, e: Self) -> Self {
        args.into_iter()
            .rev()
            .fold(e, |e, (x, g)| ExplicitExpr::lam(x, g, e))
    }

    pub fn coerce(e: Self, c: Coercion) -> Self {
        match c {
            Coercion::Id(IdType::Unsafe, _) => e, // TODO flaggable?
            Coercion::Id(_, _) => e,
            c => ExplicitExpr::Coerce(Box::new(e), c),
        }
    }

    pub fn app(e1: Self, e2: Self) -> Self {
        ExplicitExpr::App(Box::new(e1), Box::new(e2))
    }

    pub fn if_(e1: Self, e2: Self, e3: Self) -> Self {
        ExplicitExpr::If(Box::new(e1), Box::new(e2), Box::new(e3))
    }

    pub fn let_(x: Variable, g: GradualType, e1: Self, e2: Self) -> Self {
        ExplicitExpr::Let(x, g, Box::new(e1), Box::new(e2))
    }

    pub fn letrec(defns: Vec<(Variable, GradualType, Self)>, e2: Self) -> Self {
        ExplicitExpr::LetRec(defns, Box::new(e2))
    }

    pub fn uop(op: ExplicitUOp, e: Self) -> Self {
        ExplicitExpr::UOp(op, Box::new(e))
    }

    pub fn bop(op: ExplicitBOp, e1: Self, e2: Self) -> Self {
        ExplicitExpr::BOp(op, Box::new(e1), Box::new(e2))
    }

    pub fn cons(e1: Self, e2: Self) -> Self {
        ExplicitExpr::Cons(Box::new(e1), Box::new(e2))
    }

    pub fn match_(
        e_scrutinee: Self,
        e_nil: Self,
        hd: Variable,
        tl: Variable,
        e_cons: Self,
    ) -> Self {
        ExplicitExpr::Match(
            Box::new(e_scrutinee),
            Box::new(e_nil),
            hd,
            tl,
            Box::new(e_cons),
        )
    }

    pub fn is_compound(&self) -> bool {
        match self {
            ExplicitExpr::Var(_) | ExplicitExpr::Const(_) | ExplicitExpr::Hole(_, _) => false,
            _ => true,
        }
    }

    pub fn is_app(&self) -> bool {
        match self {
            ExplicitExpr::App(_, _) => true,
            _ => false,
        }
    }

    pub fn coercions(self) -> Vec<Coercion> {
        match self {
            ExplicitExpr::Var(_)
            | ExplicitExpr::Const(_)
            | ExplicitExpr::Hole(_, _)
            | ExplicitExpr::Nil(_) => vec![],
            ExplicitExpr::Lam(_, _, e) | ExplicitExpr::UOp(_, e) => e.coercions(),
            ExplicitExpr::Coerce(e, c) => {
                let mut cs = e.coercions();
                cs.push(c.clone());
                cs
            }
            ExplicitExpr::App(e1, e2)
            | ExplicitExpr::Cons(e1, e2)
            | ExplicitExpr::Let(_, _, e1, e2)
            | ExplicitExpr::BOp(_, e1, e2) => {
                let mut cs = e1.coercions();
                cs.extend(e2.coercions());
                cs
            }
            ExplicitExpr::If(e1, e2, e3) | ExplicitExpr::Match(e1, e2, _, _, e3) => {
                let mut cs = e1.coercions();
                cs.extend(e2.coercions());
                cs.extend(e3.coercions());
                cs
            }
            ExplicitExpr::LetRec(defns, e2) => {
                let mut cs = e2.coercions();

                for (_, _, e1) in defns.into_iter() {
                    cs.extend(e1.coercions());
                }

                cs
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
            ExplicitExpr::Var(x) => pp.text(x),
            ExplicitExpr::Const(c) => pp.as_string(c),
            ExplicitExpr::Lam(x, t, e) => pp
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
            ExplicitExpr::Hole(name, t) => pp
                .text(name)
                .append(pp.space())
                .append(pp.text(":"))
                .append(pp.line())
                .append(t.pretty(pp))
                .group(),
            ExplicitExpr::Coerce(e, c) => c
                .pretty(pp)
                .brackets()
                .group()
                .append(pp.line())
                .append(e.pretty(pp).parens().nest(2))
                .group(),
            ExplicitExpr::App(e1, e2) => {
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
            ExplicitExpr::If(e1, e2, e3) => {
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
            ExplicitExpr::Let(x, t, e1, e2) => {
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
            ExplicitExpr::LetRec(defns, e2) => {
                let letrec = pp.text("let rec").append(pp.space());

                let bindings = pp.intersperse(
                    defns.iter().map(|(x, t, e1)| {
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
            ExplicitExpr::UOp(op, e) => {
                pp.as_string(op)
                    .append(pp.space())
                    .append(if e.is_compound() {
                        e.pretty(pp).parens()
                    } else {
                        e.pretty(pp)
                    })
            }
            ExplicitExpr::BOp(op, e1, e2) => pp.intersperse(
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
            ExplicitExpr::Nil(t) => {
                pp.intersperse(vec![pp.text("[]"), pp.text(":"), t.pretty(pp)], pp.space())
            }
            // TODO identify concrete lists and pretty print accordingly
            ExplicitExpr::Cons(e1, e2) => pp.intersperse(
                vec![
                    if e1.is_compound() {
                        e1.pretty(pp).parens()
                    } else {
                        e1.pretty(pp)
                    },
                    pp.text("::"),
                    if e2.is_compound() {
                        e2.pretty(pp).parens()
                    } else {
                        e2.pretty(pp)
                    },
                ],
                pp.line(),
            ),
            ExplicitExpr::Match(e_scrutinee, e_nil, hd, tl, e_cons) => pp.intersperse(
                vec![
                    pp.intersperse(
                        vec![pp.text("match"), e_scrutinee.pretty(pp), pp.text("with")],
                        pp.space(),
                    )
                    .group(),
                    pp.intersperse(
                        vec![
                            pp.text("|"),
                            pp.text("[]"),
                            pp.text("->"),
                            e_nil.pretty(pp).indent(2),
                        ],
                        pp.space(),
                    )
                    .group(),
                    pp.intersperse(
                        vec![
                            pp.text("|"),
                            pp.as_string(hd),
                            pp.text("::"),
                            pp.as_string(tl),
                            pp.text("->"),
                            e_cons.pretty(pp).indent(2),
                        ],
                        pp.space(),
                    )
                    .group(),
                ],
                pp.line(),
            ),
        }
    }
}

impl Display for ExplicitExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl IdType {
    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            (IdType::Trivial, t) | (t, IdType::Trivial) => t,
            (IdType::Safe, t) | (t, IdType::Safe) => t,
            (IdType::Unsafe, IdType::Unsafe) => IdType::Unsafe,
        }
    }
}

impl Coercion {
    pub fn is_safe(&self) -> bool {
        match self {
            Coercion::Id(IdType::Unsafe, _) => false,
            Coercion::Id(_, _) => true,
            Coercion::Check(_) | Coercion::Tag(_) => true,
            Coercion::Fun(c1, c2) | Coercion::Seq(c1, c2) => c1.is_safe() && c2.is_safe(),
            Coercion::List(c) => c.is_safe(),
        }
    }

    pub fn types(&self) -> Option<(GradualType, GradualType)> {
        match self {
            Coercion::Id(_, g) => Some((g.clone(), g.clone())),
            Coercion::Tag(b) => Some((GradualType::from(*b), GradualType::Dyn())),
            Coercion::Check(b) => Some((GradualType::Dyn(), GradualType::from(*b))),
            Coercion::Fun(c1, c2) => {
                let (g21, g11) = c1.types()?;
                let (g12, g22) = c2.types()?;

                Some((GradualType::fun(g11, g12), GradualType::fun(g21, g22)))
            }
            Coercion::List(c) => {
                let (g1, g2) = c.types()?;
                Some((GradualType::list(g1), GradualType::list(g2)))
            }
            Coercion::Seq(c1, c2) => {
                let (g1, g12) = c1.types()?;
                let (g21, g2) = c2.types()?;

                if g12 == g21 {
                    Some((g1, g2))
                } else {
                    error!("ill typed sequence: {} != {}", g12, g21);
                    None
                }
            }
        }
    }

    pub fn well_typed(&self) -> bool {
        self.types().is_some()
    }

    pub fn seq(c1: Self, c2: Self) -> Self {
        match (c1, c2) {
            (Coercion::Id(_, _), c) | (c, Coercion::Id(_, _)) => c,
            (Coercion::Tag(b1), Coercion::Check(b2)) => {
                if b1 == b2 {
                    Coercion::Id(IdType::Safe, b1.into())
                } else {
                    Coercion::Seq(Box::new(Coercion::Tag(b1)), Box::new(Coercion::Check(b2)))
                }
            }
            (Coercion::Check(b1), Coercion::Tag(b2)) => {
                if b1 == b2 {
                    info!(
                        "applied (unsafe) ψ optimization to skip check/tag on {}",
                        b1
                    );
                    Coercion::Id(IdType::Unsafe, b1.into())
                } else {
                    let c =
                        Coercion::Seq(Box::new(Coercion::Check(b1)), Box::new(Coercion::Tag(b2)));
                    warn!("absurd/ill-typed coercion: {}", c);
                    c
                }
            }
            (c1, c2) => Coercion::Seq(Box::new(c1), Box::new(c2)),
        }
    }

    pub(crate) fn fun(c1: Self, c2: Self) -> Self {
        match (c1, c2) {
            (Coercion::Id(t1, g1), Coercion::Id(t2, g2)) => {
                Coercion::Id(t1.join(t2), GradualType::fun(g1, g2))
            }
            (c1, c2) => Coercion::Fun(Box::new(c1), Box::new(c2)),
        }
    }

    pub(crate) fn list(c: Self) -> Self {
        match c {
            Coercion::Id(t, g) => Coercion::Id(t, GradualType::list(g)),
            c => Coercion::List(Box::new(c)),
        }
    }

    pub(crate) fn is_compound(&self) -> bool {
        match self {
            Coercion::Fun(_, _) | Coercion::Seq(_, _) | Coercion::List(_) => true,
            Coercion::Id(_, _) | Coercion::Check(_) | Coercion::Tag(_) => false,
        }
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Coercion::Id(_, g) => pp.text("ɩ").append(g.pretty(pp).brackets()),
            Coercion::Check(g) => pp.as_string(g).append(pp.text("?")),
            Coercion::Tag(g) => pp.as_string(g).append(pp.text("!")),
            Coercion::Fun(c1, c2) => {
                let d1 = c1.pretty(pp).group();

                let d1 = if c1.is_compound() { d1.parens() } else { d1 };

                let d2 = c2.pretty(pp).group();
                let d2 = if c2.is_compound() { d2.parens() } else { d2 };

                d1.append(pp.space())
                    .append(pp.text("↝"))
                    .append(pp.line())
                    .append(d2)
                    .group()
            }
            Coercion::List(c) => pp.text("list").append(c.pretty(pp).parens()),
            Coercion::Seq(c1, c2) => {
                let d1 = c1.pretty(pp).group();

                let d1 = if c1.is_compound() { d1.parens() } else { d1 };

                let d2 = c2.pretty(pp).group();
                let d2 = if c2.is_compound() { d2.parens() } else { d2 };

                d1.append(pp.space())
                    .append(pp.text(";"))
                    .append(pp.line())
                    .append(d2)
                    .group()
            }
        }
    }
}

impl Display for Coercion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(DEFAULT_WIDTH, f)
    }
}

impl From<&Constant> for MigrationalType {
    fn from(c: &Constant) -> Self {
        c.ground_type().into()
    }
}

impl From<&Constant> for GroundType {
    fn from(c: &Constant) -> Self {
        c.ground_type()
    }
}

impl From<GroundType> for MigrationalType {
    fn from(g: GroundType) -> Self {
        match g {
            GroundType::Base(b) => MigrationalType::Base(b),
            GroundType::List => MigrationalType::List(Box::new(MigrationalType::Dyn())),
            GroundType::Fun => MigrationalType::fun(MigrationalType::Dyn(), MigrationalType::Dyn()),
        }
    }
}

impl From<GroundType> for GradualType {
    fn from(g: GroundType) -> Self {
        match g {
            GroundType::Base(b) => GradualType::Base(b),
            GroundType::List => GradualType::List(Box::new(GradualType::Dyn())),
            GroundType::Fun => GradualType::fun(GradualType::Dyn(), GradualType::Dyn()),
        }
    }
}

impl From<Constant> for GradualType {
    fn from(c: Constant) -> Self {
        match c {
            Constant::Bool(_) => GradualType::Base(BaseType::Bool),
            Constant::Int(_) => GradualType::Base(BaseType::Int),
            Constant::String(_) => GradualType::Base(BaseType::String),
        }
    }
}

impl Default for Side {
    fn default() -> Self {
        Side::Right
    }
}

impl Variation {
    pub fn new(d: usize) -> Self {
        Variation(d, None)
    }

    pub fn bias(&self) -> Option<Side> {
        self.1
    }

    pub fn biased(self, side: Side) -> Self {
        Variation(self.0, Some(side))
    }
}

impl Display for Variation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut res = write!(f, "d{}", self.0)?;

        if let Some(side) = self.1 {
            res = write!(f, "{}", side)?;
        }

        Ok(res)
    }
}

impl Display for Side {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Side::Left => write!(f, "L"),
            Side::Right => write!(f, "R"),
        }
    }
}

impl Display for SourceUOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourceUOp::Not => write!(f, "!"),
            SourceUOp::Negate => write!(f, "-"),
            SourceUOp::Is(g) => write!(f, "{}?", g),
        }
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

impl Display for ExplicitUOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExplicitUOp::Not => write!(f, "!"),
            ExplicitUOp::Negate => write!(f, "-"),
            ExplicitUOp::Is(g) => write!(f, "{}?", g),
        }
    }
}

impl Display for ExplicitBOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ExplicitBOp::PlusInt => "+i",
            ExplicitBOp::PlusString => "+s",
            ExplicitBOp::PlusDyn => "+?",
            ExplicitBOp::Minus => "-",
            ExplicitBOp::Times => "*",
            ExplicitBOp::Divide => "/",
            ExplicitBOp::And => "&&",
            ExplicitBOp::Or => "||",
            ExplicitBOp::EqualBool => "==b",
            ExplicitBOp::EqualInt => "==i",
            ExplicitBOp::EqualString => "==s",
            ExplicitBOp::EqualDyn => "==?",
            ExplicitBOp::LessThan => "<",
            ExplicitBOp::LessThanEqual => "<=",
            ExplicitBOp::Choice(d, op1, op2) => return write!(f, "{}<{}, {}>", d, op1, op2),
        };
        write!(f, "{}", s)
    }
}

impl Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::Bool(true) => write!(f, "true"),
            Constant::Bool(false) => write!(f, "false"),
            Constant::Int(n) => write!(f, "{}", n),
            Constant::String(s) => write!(f, "\"{}\"", s),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn expr_id() {
        assert_eq!(
            SourceExpr::parse("\\x. x").unwrap(),
            GradualExpr::lam("x".into(), None, GradualExpr::Var("x".into()))
        );

        assert_eq!(
            SourceExpr::parse("\\x:?. x").unwrap(),
            GradualExpr::lam(
                "x".into(),
                Some(GradualType::Dyn()),
                GradualExpr::Var("x".into())
            )
        );

        assert_eq!(
            SourceExpr::parse("\\x:bool. x").unwrap(),
            GradualExpr::lam(
                "x".into(),
                Some(BaseType::Bool.into()),
                GradualExpr::Var("x".into())
            )
        );
    }

    #[test]
    fn expr_app() {
        assert_eq!(
            SourceExpr::parse("true false 5").unwrap(),
            GradualExpr::app(
                GradualExpr::app(
                    GradualExpr::Const(Constant::Bool(true)),
                    GradualExpr::Const(Constant::Bool(false))
                ),
                GradualExpr::Const(Constant::Int(5))
            )
        );

        assert_eq!(
            SourceExpr::parse("true (false 5)").unwrap(),
            GradualExpr::app(
                GradualExpr::Const(Constant::Bool(true)),
                GradualExpr::app(
                    GradualExpr::Const(Constant::Bool(false)),
                    GradualExpr::Const(Constant::Int(5))
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
            SourceExpr::parse("\\b:bool. if b then false else true").unwrap(),
            GradualExpr::lam(
                "b".into(),
                Some(BaseType::Bool.into()),
                GradualExpr::if_(
                    GradualExpr::Var("b".into()),
                    GradualExpr::Const(Constant::Bool(false)),
                    GradualExpr::Const(Constant::Bool(true))
                )
            )
        );
    }

    #[test]
    fn expr_list() {
        assert!(SourceExpr::parse("[]").is_ok());
        assert!(SourceExpr::parse("[ ]").is_ok());
        assert!(SourceExpr::parse("1::[]").is_ok());
        assert!(SourceExpr::parse("1::2::[]").is_ok());
        assert!(SourceExpr::parse("1::(2::[])").is_ok());
        assert!(SourceExpr::parse("x::y::z").is_ok());

        assert!(SourceExpr::parse("[1;2]").is_ok());
        assert_eq!(
            SourceExpr::parse("[true;1]").unwrap(),
            SourceExpr::cons(
                SourceExpr::bool(true),
                SourceExpr::cons(SourceExpr::int(1), SourceExpr::Nil(None))
            )
        );

        assert!(SourceExpr::parse("x::y::").is_err());
        assert!(SourceExpr::parse("::x::y").is_err());
    }

    #[test]
    fn const_int() {
        assert!(SourceExpr::parse("22").is_ok());
        assert_eq!(
            SourceExpr::parse("47").unwrap(),
            GradualExpr::Const(Constant::Int(47))
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
            GradualExpr::Const(Constant::Bool(true))
        );
        assert_eq!(
            SourceExpr::parse("false").unwrap(),
            GradualExpr::Const(Constant::Bool(false))
        );
        assert_eq!(
            SourceExpr::parse("FALSE").unwrap(),
            GradualExpr::Var("FALSE".to_string())
        );
    }

    #[test]
    fn types_atomic() {
        assert_eq!(GradualType::parse("bool").unwrap(), BaseType::Bool.into());
        assert_eq!(GradualType::parse("int").unwrap(), BaseType::Int.into());
        assert_eq!(GradualType::parse("?").unwrap(), GradualType::Dyn());

        assert_eq!(
            GradualType::parse("string").unwrap(),
            BaseType::String.into()
        );
    }

    #[test]
    fn types_list() {
        assert_eq!(
            GradualType::parse("[bool]").unwrap(),
            GradualType::list(GradualType::bool())
        );
        assert_eq!(
            GradualType::parse("[?]").unwrap(),
            GradualType::list(GradualType::Dyn())
        );
        assert_eq!(
            GradualType::parse("[\t[\nbool] ]").unwrap(),
            GradualType::list(GradualType::list(GradualType::bool()))
        );
        assert_eq!(
            GradualType::parse("[?->[bool]]").unwrap(),
            GradualType::list(GradualType::fun(
                GradualType::Dyn(),
                GradualType::list(GradualType::bool())
            ))
        );

        assert!(GradualType::parse("[bool").is_err());
    }

    #[test]
    fn types() {
        assert_eq!(
            GradualType::parse("bool->bool").unwrap(),
            GradualType::fun(BaseType::Bool.into(), BaseType::Bool.into())
        );
        assert_eq!(
            GradualType::parse("bool->bool->bool").unwrap(),
            GradualType::fun(
                BaseType::Bool.into(),
                GradualType::fun(BaseType::Bool.into(), BaseType::Bool.into())
            )
        );

        assert_eq!(
            GradualType::parse("(bool->bool)->bool").unwrap(),
            GradualType::fun(
                GradualType::fun(BaseType::Bool.into(), BaseType::Bool.into()),
                BaseType::Bool.into()
            )
        );

        assert_eq!(
            GradualType::parse("(bool -> ?) -> bool").unwrap(),
            GradualType::fun(
                GradualType::fun(BaseType::Bool.into(), GradualType::Dyn()),
                BaseType::Bool.into()
            )
        );

        assert_eq!(
            GradualType::parse("(bool -> string) -> int -> ?").unwrap(),
            GradualType::fun(
                GradualType::fun(BaseType::Bool.into(), BaseType::String.into()),
                GradualType::fun(BaseType::Int.into(), GradualType::Dyn()),
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

    fn eq_up_to_ws(s1: &str, s2: &str) {
        let v1: Vec<&str> = s1.split_whitespace().collect();
        let v2: Vec<&str> = s2.split_whitespace().collect();

        assert_eq!(v1, v2);
    }

    fn se_round_trip_up_to_ws(s: &str, pp: &str) {
        let e = SourceExpr::parse(s).unwrap();
        let e_pp = format!("{}", e);

        eq_up_to_ws(pp, &e_pp);

        let e2 = SourceExpr::parse(&e_pp).unwrap();
        // may not be equal due to empty annotations... but shouldn't come up
        assert_eq!(e, e2);
        eq_up_to_ws(&format!("{}", e2), &e_pp);
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

    #[test]
    fn pretty_multi_lambda() {
        se_round_trip("\\x y. x", "\\x. \\y. x");
        se_round_trip("\\x y z. x", "\\x. \\y. \\z. x");
        se_round_trip("\\x (y:bool) z. x", "\\x. \\y : bool. \\z. x");
        se_round_trip("\\x y. x", "\\x. \\y. x");
        se_round_trip("\\x y z. x", "\\x. \\y. \\z. x");
        se_round_trip("\\x (y:bool) z. x", "\\x. \\y : bool. \\z. x");
    }

    #[test]
    fn pretty_let_fun() {
        se_round_trip(
            "let f x = if x then false else true in f false",
            "let f = \\x. if x then false else true in f false",
        );
        se_round_trip(
            "let f (x:bool) = if x then false else true in f false",
            "let f = \\x : bool. if x then false else true in f false",
        );
        se_round_trip(
            "let f (x:?) (y:bool) = if x && y then false else true in f false",
            "let f = \\x : ?. \\y : bool. if x && y then false else true in f false",
        );

        se_round_trip_up_to_ws(
            "let rec f x = g x and g y = f y in f 0",
            "let rec f = \\x. g x and g = \\y. f y in f 0",
        );

        se_round_trip_up_to_ws(
            "let rec f (x:bool) = g x and g (y:int) = f y in f 0",
            "let rec f = \\x : bool. g x and g = \\y : int. f y in f 0",
        )
    }
    #[test]
    fn parse_match() {
        match SourceExpr::parse("match [] with | [] -> 0 | hd::tl -> 1").unwrap() {
            GradualExpr::Match(e_scrutinee, e_nil, hd, tl, e_cons) => {
                assert_eq!(e_scrutinee.to_string(), "[]");
                assert_eq!(e_nil.to_string(), "0");
                assert_eq!(hd, "hd");
                assert_eq!(tl, "tl");
                assert_eq!(e_cons.to_string(), "1");
            }
            _ => panic!("expected match"),
        }
    }

    #[test]
    fn holes() {
        se_round_trip("__", "__");
        se_round_trip("__x", "__x");

        match SourceExpr::parse("__").unwrap() {
            GradualExpr::Hole(name, None) => assert_eq!(name, "__"),
            e => panic!("expected hole, got {}", e),
        };

        match SourceExpr::parse("__x").unwrap() {
            GradualExpr::Hole(name, None) => assert_eq!(name, "__x"),
            e => panic!("expected hole, got {}", e),
        };

        match SourceExpr::parse("a__x").unwrap() {
            GradualExpr::Var(name) => assert_eq!(name, "a__x"),
            e => panic!("expected var, got {}", e),
        };

        match SourceExpr::parse("_x").unwrap() {
            GradualExpr::Var(name) => assert_eq!(name, "_x"),
            e => panic!("expected var, got {}", e),
        };
    }

    #[test]
    fn strings() {
        se_round_trip(r#""hello there""#, r#""hello there""#);
        se_round_trip(r#"\x. "hello there""#, r#"\x. "hello there""#);
        se_round_trip(
            r#"\x:string. "hello there""#,
            r#"\x : string. "hello there""#,
        );
    }
}
