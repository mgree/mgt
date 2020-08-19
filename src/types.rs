use std::cmp::PartialEq;
use std::fmt::Display;
use std::hash::Hash;

use im_rc::HashSet;

use crate::options::DEFAULT_WIDTH;

/// gamma
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BaseType {
    Bool,
    Int,
    String,
}

/// alpha
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct TypeVariable(pub(super) usize);

/// G
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GradualType {
    Base(BaseType),
    Var(TypeVariable),
    Fun(Box<GradualType>, Box<GradualType>),
    List(Box<GradualType>),
    Dyn(),
}

/// d
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Variation(pub(crate) usize, pub(crate) Option<Side>);

/// .1 or .2
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}

/// V
#[derive(Clone, Debug, PartialEq)]
pub enum VariationalType {
    Base(BaseType),
    Var(TypeVariable),
    Fun(Box<VariationalType>, Box<VariationalType>),
    List(Box<VariationalType>),
    Choice(Variation, Box<VariationalType>, Box<VariationalType>),
}

/// M
#[derive(Clone, Debug, PartialEq)]
pub enum MigrationalType {
    Base(BaseType),
    Var(TypeVariable),
    Fun(Box<MigrationalType>, Box<MigrationalType>),
    List(Box<MigrationalType>),
    Dyn(),
    Choice(Variation, Box<MigrationalType>, Box<MigrationalType>),
}

impl GradualType {
    pub fn bool() -> Self {
        GradualType::Base(BaseType::Bool)
    }

    pub fn int() -> Self {
        GradualType::Base(BaseType::Int)
    }

    pub fn string() -> Self {
        GradualType::Base(BaseType::String)
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            GradualType::Dyn() => pp.text("?"),
            GradualType::Base(b) => pp.as_string(b),
            GradualType::Var(a) => pp.as_string(a),
            GradualType::List(g) => g.pretty(pp).brackets(),
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

    pub fn list(g: GradualType) -> GradualType {
        GradualType::List(Box::new(g))
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
            (GradualType::List(g1), GradualType::List(g2)) => g1.consistent(g2),
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

    pub fn join(&self, other: &GradualType) -> GradualType {
        match (self, other) {
            (g1, g2) if g1 == g2 => g1.clone(),
            (GradualType::Fun(g11, g12), GradualType::Fun(g21, g22)) => {
                GradualType::fun(g11.join(g21), g12.join(g22))
            }
            (GradualType::Base(b1), GradualType::Base(b2)) => {
                if b1 == b2 {
                    GradualType::Base(*b1)
                } else {
                    GradualType::Dyn()
                }
            }
            (_g1, _g2) => GradualType::Dyn(),
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
            GradualType::List(g) => g.has_dyn(),
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

    pub fn is_compound(&self) -> bool {
        match self {
            GradualType::Fun(_, _) | GradualType::List(_) => true,
            _ => false,
        }
    }
}

impl From<BaseType> for GradualType {
    fn from(b: BaseType) -> Self {
        GradualType::Base(b)
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
            VariationalType::Base(b) => pp.as_string(b),
            VariationalType::Var(a) => pp.as_string(a),
            VariationalType::List(g) => g.pretty(pp).brackets(),
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
            VariationalType::Choice(d, v1, v2) => pp
                .as_string(d)
                .append(
                    v1.pretty(pp)
                        .append(pp.text(","))
                        .append(v2.pretty(pp))
                        .angles(),
                )
                .group(),
        }
    }

    pub fn list(v: VariationalType) -> VariationalType {
        VariationalType::List(Box::new(v))
    }

    pub fn fun(v1: VariationalType, v2: VariationalType) -> VariationalType {
        VariationalType::Fun(Box::new(v1), Box::new(v2))
    }

    pub fn choice(d: Variation, v1: VariationalType, v2: VariationalType) -> VariationalType {
        // reduced smart constructor, since case (b) of unification needs to generate choices with identical branches!
        // we _do_ project the inner types to the appropriate side of that variation, though
        VariationalType::Choice(
            d,
            Box::new(v1.select(d, Side::Left)),
            Box::new(v2.select(d, Side::Right)),
        )
    }

    pub fn select(&self, d: Variation, side: Side) -> VariationalType {
        match self {
            VariationalType::Base(b) => VariationalType::Base(b.clone()),
            VariationalType::Var(a) => VariationalType::Var(*a),
            VariationalType::List(g) => VariationalType::list(g.select(d, side)),
            VariationalType::Fun(v1, v2) => {
                VariationalType::fun(v1.select(d, side), v2.select(d, side))
            }
            VariationalType::Choice(d2, v1, v2) => {
                if d == *d2 {
                    match side {
                        Side::Left => v1.select(d, side),
                        Side::Right => v2.select(d, side),
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

    pub fn string() -> Self {
        MigrationalType::Base(BaseType::String)
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            MigrationalType::Dyn() => pp.text("?"),
            MigrationalType::Base(b) => pp.as_string(b),
            MigrationalType::Var(a) => pp.as_string(a),
            MigrationalType::List(g) => g.pretty(pp).brackets(),
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
            MigrationalType::Choice(d, m1, m2) => pp
                .as_string(d)
                .append(
                    m1.pretty(pp)
                        .append(pp.text(","))
                        .append(m2.pretty(pp))
                        .angles(),
                )
                .group(),
        }
    }

    pub fn list(m: MigrationalType) -> MigrationalType {
        MigrationalType::List(Box::new(m))
    }

    pub fn fun(m1: MigrationalType, m2: MigrationalType) -> MigrationalType {
        MigrationalType::Fun(Box::new(m1), Box::new(m2))
    }

    pub fn choice(d: Variation, m1: MigrationalType, m2: MigrationalType) -> MigrationalType {
        // reduced smart constructor, since case (b) of unification needs to generate choices with identical branches!
        // we _do_ project the inner types to the appropriate side of that variation, though
        MigrationalType::Choice(
            d,
            Box::new(m1.select(d, Side::Left)),
            Box::new(m2.select(d, Side::Right)),
        )
    }

    pub fn select(&self, d: Variation, side: Side) -> MigrationalType {
        match self {
            MigrationalType::Dyn() => MigrationalType::Dyn(),
            MigrationalType::Base(b) => MigrationalType::Base(b.clone()),
            MigrationalType::Var(a) => MigrationalType::Var(*a),
            MigrationalType::List(m) => MigrationalType::list(m.select(d, side)),
            MigrationalType::Fun(m1, m2) => {
                MigrationalType::fun(m1.select(d, side), m2.select(d, side))
            }
            MigrationalType::Choice(d2, m1, m2) => {
                if d == *d2 {
                    match side {
                        Side::Left => m1.select(d, side),
                        Side::Right => m2.select(d, side),
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
            MigrationalType::Fun(m1, m2) | MigrationalType::Choice(_, m1, m2) => {
                m1.has_dyn() || m2.has_dyn()
            }
            MigrationalType::List(m) => m.has_dyn(),
            MigrationalType::Base(_) => false,
            MigrationalType::Var(_) => false,
        }
    }

    pub fn vars(&self) -> HashSet<&TypeVariable> {
        match self {
            MigrationalType::Dyn() | MigrationalType::Base(_) => HashSet::new(),
            MigrationalType::Var(alpha) => HashSet::unit(alpha),
            MigrationalType::List(m) => m.vars(),
            MigrationalType::Fun(m1, m2) | MigrationalType::Choice(_, m1, m2) => {
                m1.vars().union(m2.vars())
            }
        }
    }

    pub fn choices(&self) -> HashSet<&Variation> {
        match self {
            MigrationalType::Dyn() | MigrationalType::Base(_) | MigrationalType::Var(_) => {
                HashSet::new()
            }
            MigrationalType::List(m) => m.choices(),
            MigrationalType::Fun(m1, m2) => m1.choices().union(m2.choices()),
            MigrationalType::Choice(d, m1, m2) => m1.choices().union(m2.choices()).update(d),
        }
    }

    pub fn try_variational(&self) -> Option<VariationalType> {
        match self {
            MigrationalType::Dyn() => None,
            MigrationalType::Base(b) => Some(VariationalType::Base(b.clone())),
            MigrationalType::Var(a) => Some(VariationalType::Var(*a)),
            MigrationalType::List(m) => Some(VariationalType::list(m.try_variational()?)),
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

    pub fn try_gradual(&self) -> Option<GradualType> {
        match self {
            MigrationalType::Choice(_, _, _) => None,
            MigrationalType::Base(b) => Some(GradualType::Base(b.clone())),
            MigrationalType::Var(a) => Some(GradualType::Var(*a)),
            MigrationalType::List(m) => Some(GradualType::list(m.try_gradual()?)),
            MigrationalType::Dyn() => Some(GradualType::Dyn()),
            MigrationalType::Fun(m1, m2) => {
                let g1 = m1.try_gradual()?;
                let g2 = m2.try_gradual()?;

                Some(GradualType::fun(g1, g2))
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

impl From<BaseType> for MigrationalType {
    fn from(b: BaseType) -> Self {
        MigrationalType::Base(b)
    }
}

impl From<GradualType> for MigrationalType {
    fn from(g: GradualType) -> Self {
        match g {
            GradualType::Base(b) => MigrationalType::Base(b),
            GradualType::Var(a) => MigrationalType::Var(a),
            GradualType::Dyn() => MigrationalType::Dyn(),
            GradualType::List(g) => MigrationalType::list(MigrationalType::from(*g)),
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
            VariationalType::List(g) => MigrationalType::list(MigrationalType::from(*g)),
            VariationalType::Fun(t1, t2) => {
                MigrationalType::fun(MigrationalType::from(*t1), MigrationalType::from(*t2))
            }
            VariationalType::Choice(d, t1, t2) => {
                MigrationalType::choice(d, MigrationalType::from(*t1), MigrationalType::from(*t2))
            }
        }
    }
}
