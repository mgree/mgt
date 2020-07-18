extern crate mgt;

use mgt::syntax::*;
use mgt::*;

fn main() {
    let x = Expr::Var(String::from("x"));
    let little_omega: SourceExpr = Expr::lam(String::from("x"), None, Expr::app(x.clone(), x));
    let _big_omega = Expr::app(little_omega.clone(), little_omega.clone());

    debug_inferred_type(&little_omega);

    // debug_inferred_type(&big_omega);
}

fn debug_inferred_type(e: &SourceExpr) {
    let (_e, _m, _ves) = TypeInference::infer(e).expect("constraint generation failed");
}

#[cfg(test)]
mod test {
    use super::*;
    use im_rc::HashSet;

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
    pub fn infer_identity() {
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
        assert_eq!(ves, HashSet::unit(HashSet::new()));
    }

    #[test]
    pub fn infer_dyn_identity() {
        let (_e, m, ves) = TypeInference::infer(&dyn_identity()).unwrap();

        // just one maximal eliminator
        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
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
    pub fn infer_boolean_negation() {
        let (_e, m, ves) = TypeInference::infer(&neg()).unwrap();

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
    pub fn infer_conditional() {
        let e = Expr::if_(Expr::bool(true), Expr::bool(false), Expr::bool(true));

        let (_e, m, ves) = TypeInference::infer(&e).unwrap();

        assert_eq!(m, MigrationalType::Base(BaseType::Bool));
        assert_eq!(ves, HashSet::unit(HashSet::new()));
    }

    #[test]
    pub fn infer_neg_or_id() {
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
    pub fn infer_very_dynamic() {
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
    pub fn infer_constants() {
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
    pub fn infer_little_omega() {
        let (_e, m, ves) = TypeInference::infer(&little_omega()).unwrap();

        assert!(m.is_fun());
        assert!(ves.is_empty());
    }

    #[test]
    pub fn infer_big_omega() {
        let big_omega = Expr::app(little_omega(), little_omega());
        let (_e, _m, ves) = TypeInference::infer(&big_omega).unwrap();

        // m will probably be a type variable, but who cares
        assert!(ves.is_empty());
    }

    #[test]
    pub fn infer_bool_id() {
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
    pub fn ill_typed_ann() {
        let (_e, _m, ves) = TypeInference::infer(&Expr::ann(
            Expr::Const(Constant::Int(5)),
            Some(GradualType::Base(BaseType::Bool)),
        ))
        .unwrap();

        assert_eq!(ves.len(), 0);
    }

    #[test]
    pub fn well_typed_ann() {
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
    pub fn infer_bad_constraints() {
        assert!(
            TypeInference::infer(&Expr::app(
                Expr::Const(Constant::Bool(true)),
                Expr::Const(Constant::Bool(false)),
            )).is_none(),
            "type inference should fail"
        );
    }

    #[test]
    pub fn eg_width() {
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
}
