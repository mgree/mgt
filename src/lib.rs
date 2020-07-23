#[macro_use]
extern crate lalrpop_util;

use im_rc::HashMap;
use im_rc::HashSet;
use std::iter::FromIterator;

use log::{debug, error, trace};

pub mod syntax;
use syntax::*;

pub struct TypeInference {
    next_variable: usize,
    next_variation: usize,
    pattern: Pattern,
    constraints: Constraints,
}

impl TypeInference {
    fn new() -> TypeInference {
        TypeInference {
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
                let m = ctx.lookup(x).cloned()?;
                Some((Expr::Var(x.clone()), m))
            }
            Expr::Lam(x, t, e) => match t {
                Some(GradualType::Dyn()) => {
                    let d = self.fresh_variation();
                    let m_dom = MigrationalType::choice(
                        d,
                        MigrationalType::Dyn(),
                        MigrationalType::Var(self.fresh_variable()),
                    );
                    let (e, m_cod) =
                        self.generate_constraints(ctx.extend(x.clone(), m_dom.clone()), e)?;

                    Some((
                        Expr::lam(x.clone(), m_dom.clone(), e),
                        MigrationalType::fun(m_dom, m_cod),
                    ))
                }
                Some(m_dom) => {
                    let (e, m_cod) =
                        self.generate_constraints(ctx.extend(x.clone(), m_dom.clone().into()), e)?;

                    let m_dom: MigrationalType = m_dom.clone().into();
                    Some((
                        Expr::lam(x.clone(), m_dom.clone(), e),
                        MigrationalType::fun(m_dom, m_cod),
                    ))
                }
                None => {
                    let m_dom = MigrationalType::Var(self.fresh_variable());
                    let (e, m_cod) =
                        self.generate_constraints(ctx.extend(x.clone(), m_dom.clone()), e)?;

                    Some((
                        Expr::lam(x.clone(), m_dom.clone(), e),
                        MigrationalType::fun(m_dom, m_cod),
                    ))
                }
            },
            Expr::Ann(e, t) => {
                let (e, m) = self.generate_constraints(ctx, e)?;

                match t {
                    Some(t) => {
                        let mut m_ann: MigrationalType = t.clone().into();

                        if m_ann.has_dyn() {
                            let d = self.fresh_variation();
                            let m_var = self.dyn_to_var(&m);

                            m_ann = MigrationalType::choice(d, m_ann, m_var);
                        }

                        self.add_constraint(Constraint::Consistent(
                            Pattern::Top(),
                            m.clone(),
                            m_ann.clone(),
                        ));

                        Some((Expr::ann(e, m), m_ann))
                    }
                    None => Some((e, m)),
                }
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
                    MigrationalType::Base(BaseType::Bool),
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
                        let m: MigrationalType = t.clone().into();
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
            _ => (
                // MMG could turn this into a join, will type more programs (but with lots of leftover dynamic)
                MigrationalType::Var(self.fresh_variable()),
                Constraints::epsilon(),
                Pattern::Bot(),
            ),
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
            map.insert(a.clone(), VariationalType::choice(d, v1, v2));
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
            Constraint::Choice(d, cs1, cs2) => {
                // (h)
                let (theta1, pi1) = self.unify(cs1);
                let (theta2, pi2) = self.unify(cs2);

                let theta = self.merge(d, theta1, theta2);
                (theta, Pattern::choice(d, pi1, pi2))
            }
        }
    }

    pub fn infer(e: &SourceExpr) -> Option<(TargetExpr, MigrationalType, HashSet<Eliminator>)> {
        let mut ti = TypeInference::new();

        let (e, m) = ti.generate_constraints(Ctx::empty(), e)?;

        debug!("Generated constraints:");
        debug!("  e = {}", e);
        debug!("  m = {}", m);
        debug!("  constraints = {}", ti.constraints);
        debug!("  pi = {}", ti.pattern);

        if ti.pattern == Pattern::Bot() {
            error!("constraint generation produced false pattern (i.e., statically untypable");
            return None;
        }

        let (theta, mut pi) = ti.unify(ti.constraints.clone());
        pi = pi.meet(ti.pattern);
        let e = e.apply(&theta);
        let m = m.clone().apply(&theta);
        debug!("Unified constraints:");
        debug!("  e = {}", e);
        debug!("  theta = {}", theta);
        debug!("  pi = {}", pi);
        debug!("  m = {}", m);

        let ds = m.choices().clone();
        let ves: HashSet<Eliminator> = pi
            .clone()
            .valid_eliminators()
            .into_iter()
            .map(move |ve| ve.expand(&ds))
            .collect();

        debug!("Maximal valid eliminators:");
        debug!("ves = [");
        for ve in ves.iter() {
            debug!("  {}", ve);
        }
        debug!("]");

        Some((e, m, ves))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use im_rc::HashSet;

    fn infer(s: &str) -> (TargetExpr, MigrationalType, HashSet<Eliminator>) {
        TypeInference::infer(&SourceExpr::parse(s).unwrap()).unwrap()
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
            MigrationalType::fun(
                MigrationalType::Base(BaseType::Bool),
                MigrationalType::Base(BaseType::Bool)
            )
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
            MigrationalType::fun(
                MigrationalType::Base(BaseType::Bool),
                MigrationalType::Base(BaseType::Bool)
            )
        );
    }

    #[test]
    fn infer_conditional() {
        let e = Expr::if_(Expr::bool(true), Expr::bool(false), Expr::bool(true));

        let (_e, m, ves) = TypeInference::infer(&e).unwrap();

        assert_eq!(m, MigrationalType::Base(BaseType::Bool));
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
            MigrationalType::fun(
                MigrationalType::Base(BaseType::Bool),
                MigrationalType::Base(BaseType::Bool)
            )
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
                MigrationalType::Base(BaseType::Bool),
                MigrationalType::fun(
                    MigrationalType::Dyn(),
                    MigrationalType::Base(BaseType::Bool)
                )
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
            MigrationalType::fun(
                MigrationalType::Base(BaseType::Bool),
                MigrationalType::Base(BaseType::Bool)
            )
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
    fn if_meet_not_join() {
        assert!(TypeInference::infer(
            &Expr::parse("\\x:?. if x then \\y:?. x else false").unwrap()
        )
        .is_none());
        assert!(
            TypeInference::infer(&Expr::parse("\\x:?. if x then \\y. x else false").unwrap())
                .is_none()
        );
        assert!(
            TypeInference::infer(&Expr::parse("\\x. if x then \\y:?. x else false").unwrap())
                .is_none()
        );
        assert!(
            TypeInference::infer(&Expr::parse("\\x. if x then \\y. x else false").unwrap())
                .is_none()
        );
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
            MigrationalType::fun(
                MigrationalType::Base(BaseType::Int),
                MigrationalType::Base(BaseType::Int)
            )
        );
    }

    #[test]
    fn let_plain() {
        let (_e, m, ves) = infer("let id = \\x. x in if id true then id true else id false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(m, MigrationalType::Base(BaseType::Bool));
    }

    #[test]
    fn let_dynfun() {
        let (_e, m, ves) = infer("let id = \\x:?. x in if id true then id true else id false");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(m, MigrationalType::Base(BaseType::Bool));
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
    fn let_const() {
        let (_e, m, ves) = infer("let x = 5 in x");

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        assert_eq!(m, MigrationalType::Base(BaseType::Int));
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
                MigrationalType::Base(BaseType::Bool),
                MigrationalType::fun(MigrationalType::Dyn(), MigrationalType::Dyn())
            )
        );
    }

    #[test]
    pub fn subst_merge() {
        let mut ti = TypeInference::new();
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
