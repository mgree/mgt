use std::cmp::PartialEq;

/// gamma
#[derive(Clone, Debug, PartialEq)]
pub enum BaseType {
    Bool,
    Int,
}

/// alpha
pub type TypeVariable = usize;

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

pub type Variation = usize;

/// M
#[derive(Clone, Debug, PartialEq)]
pub enum MigrationalType {
    Base(BaseType),
    Var(TypeVariable),
    Fun(Box<MigrationalType>, Box<MigrationalType>),
    Dyn(),
    Choice(Variation, Box<MigrationalType>, Box<MigrationalType>), // TODO first one is really always Dyn()...
}

/// pi
#[derive(Clone, Debug)]
pub enum Pattern {
    Bot(),
    Top(),
    Choice(Variation, Box<Pattern>, Box<Pattern>),
}

/// C
///
/// we treat /\ and epsilon by just using vectors
#[derive(Clone, Debug)]
pub enum Constraint {
    Consistent(Pattern, MigrationalType, MigrationalType),
    Choice(Variation, Constraints, Constraints),
}

#[derive(Clone, Debug)]
pub struct Constraints(Vec<Constraint>);

/// c
#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    Bool(bool),
    Int(usize),
}

/// x
pub type Variable = String;

/// e (ITGL)
#[derive(Clone, Debug)]
pub enum Expr {
    Const(Constant),
    Var(Variable),
    Lam(Variable, Box<Expr>),
    LamDyn(Variable, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    // TODO operations on constants
    // TODO explicitly typed lambdas
    // TODO ascriptions
}

impl Expr {
    pub fn lam(v: Variable, e: Expr) -> Expr {
        Expr::Lam(v, Box::new(e))
    }

    pub fn lam_dyn(v: Variable, e: Expr) -> Expr {
        Expr::LamDyn(v, Box::new(e))
    }
    pub fn app(e1: Expr, e2: Expr) -> Expr {
        Expr::App(Box::new(e1), Box::new(e2))
    }

    pub fn if_(e1: Expr, e2: Expr, e3: Expr) -> Expr {
        Expr::If(Box::new(e1), Box::new(e2), Box::new(e3))
    }
}

impl GradualType {
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

impl MigrationalType {
    pub fn fun(m1: MigrationalType, m2: MigrationalType) -> MigrationalType {
        MigrationalType::Fun(Box::new(m1), Box::new(m2))
    }

    pub fn choice(d: Variation, m1: MigrationalType, m2: MigrationalType) -> MigrationalType {
        MigrationalType::Choice(d, Box::new(m1), Box::new(m2))
    }
}

impl From<&StaticType> for MigrationalType {
    fn from(t: &StaticType) -> Self {
        match t {
            StaticType::Base(b) => MigrationalType::Base(b.clone()),
            StaticType::Var(a) => MigrationalType::Var(a.clone()),
            StaticType::Fun(t1, t2) => MigrationalType::fun(
                MigrationalType::from(t1.as_ref()),
                MigrationalType::from(t2.as_ref()),
            ),
        }
    }
}

impl From<&GradualType> for MigrationalType {
    fn from(t: &GradualType) -> Self {
        match t {
            GradualType::Base(b) => MigrationalType::Base(b.clone()),
            GradualType::Var(a) => MigrationalType::Var(a.clone()),
            GradualType::Dyn() => MigrationalType::Dyn(),
            GradualType::Fun(t1, t2) => MigrationalType::fun(
                MigrationalType::from(t1.as_ref()),
                MigrationalType::from(t2.as_ref()),
            ),
        }
    }
}

impl Pattern {
    pub fn choice(d: Variation, pat1: Pattern, pat2: Pattern) -> Pattern {
        Pattern::Choice(d, Box::new(pat1), Box::new(pat2))
    }
}

impl Constraint {
    pub fn and(self, other: Constraint) -> Constraints {
        Constraints(vec![self, other])
    }
}

impl Constraints {
    pub fn epsilon() -> Constraints {
        Constraints(Vec::new())
    }

    pub fn and(&mut self, c: Constraint) {
        self.0.push(c);
    }
}

impl From<Constraint> for Constraints {
    fn from(c: Constraint) -> Self {
        Constraints(vec![c])
    }
}

pub struct ConstraintGenerator {
    next_variable: TypeVariable,
    next_variation: Variation,
}

// TODO all this can be made imperative, I think
impl ConstraintGenerator {
    pub fn new() -> ConstraintGenerator {
        ConstraintGenerator {
            next_variable: 0,
            next_variation: 0,
        }
    }

    pub fn fresh_variable(&mut self) -> TypeVariable {
        let next = self.next_variable;
        self.next_variable += 1;

        next
    }

    pub fn fresh_variation(&mut self) -> Variation {
        let next = self.next_variation;
        self.next_variation += 1;

        next
    }

    // PICK UP HERE: cod, from(expr), pattern meet

    pub fn dom(
        &mut self,
        m_fun: &MigrationalType,
        m_arg: &MigrationalType,
    ) -> (Constraints, Pattern) {
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
                            m_arg.clone(),
                        )),
                    Pattern::Top(),
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

    pub fn cod(&mut self, m_fun: &MigrationalType) -> (MigrationalType, Constraints, Pattern) {
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
                    Pattern::Top(), // ??? paper just says pi
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
}
