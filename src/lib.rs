#[macro_use]
extern crate lalrpop_util;

use im_rc::HashMap;
use im_rc::HashSet;
use std::iter::FromIterator;

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

    fn generate_constraints(&mut self, ctx: Ctx, e: &SourceExpr) -> Option<(TargetExpr, MigrationalType)> {
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

                    Some((Expr::lam(x.clone(), m_dom.clone(), e), MigrationalType::fun(m_dom, m_cod)))
                }
                Some(m_dom) => {
                    let (e, m_cod) =
                        self.generate_constraints(ctx.extend(x.clone(), m_dom.clone().into()), e)?;

                    let m_dom: MigrationalType = m_dom.clone().into();
                    Some((Expr::lam(x.clone(), m_dom.clone(), e), MigrationalType::fun(m_dom, m_cod)))
                }
                None => {
                    let m_dom = MigrationalType::Var(self.fresh_variable());
                    let (e, m_cod) =
                        self.generate_constraints(ctx.extend(x.clone(), m_dom.clone()), e)?;

                    Some((Expr::lam(x.clone(), m_dom.clone(), e), MigrationalType::fun(m_dom, m_cod)))
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

                let (m_res, c_res, _pat_res) = self.meet(&m_then, &m_else);

                eprintln!(
                    "if constraints on {:?} and {:?}: {:?}",
                    m_then, m_else, c_res
                );
                self.add_constraints(c_res);

                Some((Expr::if_(e_cond, e_then, e_else), m_res))
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

    fn meet(
        &mut self,
        m1: &MigrationalType,
        m2: &MigrationalType,
    ) -> (MigrationalType, Constraints, Pattern) {
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
                let (theta2, pi2) = self.unify1(Constraint::Consistent(p, *m12, *m22));

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

        eprintln!("Generated constraints:");
        eprintln!("  e = {:?}", e);
        eprintln!("  m = {:?}", m);
        eprintln!("  constraints = {:?}", ti.constraints);

        if ti.pattern == Pattern::Bot() {
            eprintln!("ERROR: constraint generation produced false pattern");
            return None;
        }

        let (theta, pi) = ti.unify(ti.constraints.clone());
        let e = e.apply(&theta);
        let m = m.clone().apply(&theta);
        eprintln!("Unified constraints:");
        eprintln!("  e = {:?}", e);
        eprintln!("  theta = {:?}", theta);
        eprintln!("  pi = {:?}", pi);
        eprintln!("  m = {:?}", m);

        let ds = m.choices().clone();
        let ves = pi
            .clone()
            .valid_eliminators()
            .into_iter()
            .map(move |ve| expand(ve, &ds))
            .collect();

        eprintln!("Maximal valid eliminators:");
        eprintln!("  ves = {:?}", ves);

        Some((e, m, ves))
    }
}

#[cfg(test)]
mod test {
    use super::*;

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
                    _ => panic!("expected type variable, got {:?}", v2),
                }
            }
            v => panic!("expected variational choice, got {:?}", v),
        }

        match theta.lookup(&c).unwrap() {
            VariationalType::Choice(d2, v1, v2) => {
                assert_eq!(*d2, d);
                match **v1 {
                    VariationalType::Var(_) => (),
                    _ => panic!("expected type variable, got {:?}", v2),
                }
                assert_eq!(**v2, theta2.lookup(&c).unwrap().clone());
            }
            v => panic!("expected variational choice, got {:?}", v),
        }

        assert_eq!(theta.lookup(&e), None);
    }
}