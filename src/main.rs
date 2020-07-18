extern crate mgt;

use mgt::*;
use mgt::syntax::*;

fn main() {
    let x = Expr::Var(String::from("x"));
    let little_omega = Expr::lam(String::from("x"), Expr::app(x.clone(), x));
    let _big_omega = Expr::app(little_omega.clone(), little_omega.clone());

    debug_inferred_type(&little_omega);

    // debug_inferred_type(&big_omega);
}

fn debug_inferred_type(e: &Expr) {
    let (_m, _ves) = TypeInference::infer(e).expect("constraint generation failed");
    eprintln!("");
}

#[cfg(test)]
mod test {
    use super::*;
    use im_rc::HashSet;

    fn identity() -> Expr {
        let x = String::from("x");
        Expr::lam(x.clone(), Expr::Var(x))
    }

    fn dyn_identity() -> Expr {
        let x = String::from("x");
        Expr::lam_dyn(x.clone(), Expr::Var(x))
    }

    fn neg() -> Expr {
        let b = String::from("b");
        Expr::lam(
            b.clone(),
            Expr::if_(Expr::Var(b), Expr::bool(false), Expr::bool(true)),
        )
    }

    fn dyn_neg() -> Expr {
        let b = String::from("b");
        Expr::lam_dyn(
            b.clone(),
            Expr::if_(Expr::Var(b), Expr::bool(false), Expr::bool(true)),
        )
    }

    #[test]
    pub fn infer_identity() {
        let (m, ves) = TypeInference::infer(&identity()).unwrap();
        match m {
            MigrationalType::Fun(dom, cod) => match (*dom, *cod) {
                (MigrationalType::Var(a_dom), MigrationalType::Var(a_cod)) => {
                    assert_eq!(a_dom, a_cod)
                }
                _ => panic!("expected identical variables in domain and codomain"),
            },
            _ => panic!("expected function type"),
        }
        assert_eq!(ves, HashSet::unit(HashSet::new()));
    }

    #[test]
    pub fn infer_dyn_identity() {
        let (m, ves) = TypeInference::infer(&dyn_identity()).unwrap();

        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.into_iter().next().unwrap();
        let m = m.eliminate(ve);

        // should be given the true identity type
        match m {
            MigrationalType::Fun(dom, cod) => match (*dom, *cod) {
                (MigrationalType::Var(a_dom), MigrationalType::Var(a_cod)) => {
                    assert_eq!(a_dom, a_cod)
                }
                _ => panic!("expected identical variables in domain and codomain"),
            },
            _ => panic!("expected function type"),
        }
    }

    #[test]
    pub fn infer_dyn_const() {
        let x = String::from("x");
        let y = String::from("y");
        let k = Expr::lam_dyn(x.clone(), Expr::lam_dyn(y, Expr::Var(x)));

        let (m, ves) = TypeInference::infer(&k).unwrap();

        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.into_iter().next().unwrap();
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
    pub fn infer_boolean_negation() {
        let (m, ves) = TypeInference::infer(&neg()).unwrap();

        assert_eq!(
            m,
            MigrationalType::fun(
                MigrationalType::Base(BaseType::Bool),
                MigrationalType::Base(BaseType::Bool)
            )
        );
        assert_eq!(ves, HashSet::unit(HashSet::new()));
    }

    #[test]
    pub fn infer_dyn_boolean_negation() {
        let (m, ves) = TypeInference::infer(&dyn_neg()).unwrap();

        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.into_iter().next().unwrap();
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
    pub fn infer_conditional() {
        let e = Expr::if_(Expr::bool(true), Expr::bool(false), Expr::bool(true));

        let (m, ves) = TypeInference::infer(&e).unwrap();

        assert_eq!(m, MigrationalType::Base(BaseType::Bool));
        assert_eq!(ves, HashSet::unit(HashSet::new()));
    }

    #[test]
    pub fn infer_neg_or_id() {
        let e = Expr::if_(Expr::bool(true), dyn_neg(), dyn_identity());

        let (m, ves) = TypeInference::infer(&e).unwrap();
        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.into_iter().next().unwrap();
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
    pub fn infer_very_dynamic() {
        let x = String::from("x");
        let y = String::from("y");
        let e = Expr::lam_dyn(
            x.clone(),
            Expr::lam_dyn(
                y.clone(),
                Expr::if_(
                    Expr::Var(x.clone()),
                    Expr::app(Expr::Var(y.clone()), Expr::Var(x)),
                    Expr::app(neg(), Expr::Var(y)),
                ),
            ),
        );

        let (m, ves) = TypeInference::infer(&e).unwrap();

        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.into_iter().next().unwrap();
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
    pub fn infer_constants() {
        check_constant(Constant::Bool(true), BaseType::Bool);
        check_constant(Constant::Bool(false), BaseType::Bool);
        check_constant(Constant::Int(0), BaseType::Int);
        check_constant(Constant::Int(6), BaseType::Int);
        check_constant(Constant::Int(-47), BaseType::Int);
    }

    fn check_constant(c: Constant, b: BaseType) {
        let (m, ves) = TypeInference::infer(&Expr::Const(c)).unwrap();

        assert_eq!(ves.len(), 1);
        let ve = ves.into_iter().next().unwrap();
        assert!(ve.is_empty());

        assert_eq!(m, MigrationalType::Base(b));
    }

    #[test]
    pub fn infer_little_omega() {
        let x = Expr::Var(String::from("x"));
        let little_omega = Expr::lam(String::from("x"), Expr::app(x.clone(), x));

        let (m, ves) = TypeInference::infer(&little_omega).unwrap();

        assert!(m.is_fun());
        assert!(ves.is_empty());
    }

    #[test]
    pub fn infer_big_omega() {
        let x = Expr::Var(String::from("x"));
        let little_omega = Expr::lam(String::from("x"), Expr::app(x.clone(), x));
        let big_omega = Expr::app(little_omega.clone(), little_omega.clone());
        let (_m, ves) = TypeInference::infer(&big_omega).unwrap();

        // m will probably be a type variable, but who cares
        assert!(ves.is_empty());
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
