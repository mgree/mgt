use im_rc::HashMap;

use std::cmp::PartialEq;

/// gamma
#[derive(Clone, Debug, PartialEq)]
pub enum BaseType {
    Bool,
    Int,
}

/// alpha
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TypeVariable(usize);

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

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Variation(usize);

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
    pub fn bool(b: bool) -> Expr {
        Expr::Const(Constant::Bool(b))
    }

    pub fn int(n: usize) -> Expr {
        Expr::Const(Constant::Int(n))
    }

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

impl From<&Constant> for MigrationalType {
    fn from(c: &Constant) -> Self {
        match c {
            Constant::Bool(_) => MigrationalType::Base(BaseType::Bool),
            Constant::Int(_) => MigrationalType::Base(BaseType::Bool),
        }
    }
}

impl Pattern {
    pub fn choice(d: Variation, pat1: Pattern, pat2: Pattern) -> Pattern {
        Pattern::Choice(d, Box::new(pat1), Box::new(pat2))
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

    pub fn and_many(&mut self, mut other: Constraints) {
        self.0.append(&mut other.0);
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

pub struct ConstraintGenerator {
    next_variable: usize,
    next_variation: usize,
    pub pattern: Pattern,
    pub constraints: Constraints,
}

impl ConstraintGenerator {
    pub fn new() -> ConstraintGenerator {
        /* TODO really, we need to associate these inferred types with bindings
           in the term... which means that fresh variables might need to start
           later (or we expand our variables have a notion of name)

           one nice approach: allow type annotations on lambdas, but `infer` 
           mutates the expression as it goes, setting the annotations to fresh 
           type variables on unannotated binders
        */
        ConstraintGenerator {
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

    pub fn infer(&mut self, ctx: Ctx, e: &Expr) -> Option<MigrationalType> {
        match e {
            Expr::Const(c) => Some(c.into()),
            Expr::Var(x) => ctx.lookup(x).cloned(),
            Expr::Lam(x, e) => {
                let m_dom = MigrationalType::Var(self.fresh_variable());
                let m_cod = self.infer(ctx.extend(x.clone(), m_dom.clone()), e)?;

                Some(MigrationalType::fun(m_dom, m_cod))
            }
            Expr::LamDyn(x, e) => {
                let d = self.fresh_variation();
                let m_dom = MigrationalType::choice(
                    d,
                    MigrationalType::Dyn(),
                    MigrationalType::Var(self.fresh_variable()),
                );
                let m_cod = self.infer(ctx.extend(x.clone(), m_dom.clone()), e)?;

                Some(MigrationalType::fun(m_dom, m_cod))
            }
            Expr::App(e_fun, e_arg) => {
                let m_fun = self.infer(ctx.clone(), e_fun)?;
                let m_arg = self.infer(ctx, e_arg)?;

                let (m_res, cs_res, pat_res) = self.cod(&m_fun);
                self.add_constraints(cs_res);
                self.add_pattern(pat_res);
                let (cs_arg, pat_arg) = self.dom(&m_fun, &m_arg);
                self.add_constraints(cs_arg);
                self.add_pattern(pat_arg);

                Some(m_res)
            }
            Expr::If(e_cond, e_then, e_else) => {
                // ??? MMG this rule isn't in the paper... but annotations are? :(
                let m_cond = self.infer(ctx.clone(), e_cond)?;
                let m_then = self.infer(ctx.clone(), e_then)?;
                let m_else = self.infer(ctx.clone(), e_else)?;

                self.add_constraint(Constraint::Consistent(
                    Pattern::Top(),
                    m_cond,
                    MigrationalType::Base(BaseType::Bool),
                ));

                self.add_constraint(Constraint::Consistent(
                    Pattern::Top(),
                    m_then.clone(),
                    m_else,
                ));

                Some(m_then)
            }
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
                            m_arg.clone(),
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
}
