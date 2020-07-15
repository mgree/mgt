extern crate mgt;

use mgt::*;

fn main() {
    let x = Expr::Var(String::from("x"));
    let little_omega = Expr::lam(String::from("x"), Expr::app(x.clone(), x));
    let big_omega = Expr::app(little_omega.clone(), little_omega.clone());
    println!("{:?}", big_omega);

    let mut ti = TypeInference::new();
    println!("{:?}", ti.generate_constraints(Ctx::empty(), &little_omega));
    println!("{:?}", ti.constraints);
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    pub fn infer_identity() {
        let x = String::from("x");
        let id = Expr::lam(x.clone(), Expr::Var(x));

        let mut ti = TypeInference::new();
        let m = ti.generate_constraints(Ctx::empty(), &id).unwrap();
        match m {
            MigrationalType::Fun(dom, cod) => assert_eq!(dom, cod),
            _ => panic!("expected function type"),
        }
    }

    #[test]
    pub fn infer_boolean_negation() {
        let b = String::from("b");
        let neg = Expr::lam(
            b.clone(),
            Expr::if_(Expr::Var(b), Expr::bool(false), Expr::bool(true)),
        );

        let mut ti = TypeInference::new();
        let m = ti.generate_constraints(Ctx::empty(), &neg).unwrap();
        match m {
            MigrationalType::Fun(dom, cod) => match (*dom, *cod) {
                (MigrationalType::Var(_alpha), MigrationalType::Var(_beta)) => (),
                (dom, cod) => panic!("expected variables, got {:?} and {:?}", dom, cod),
            },
            _ => panic!("expected function type, got {:?}", m),
        };
    }

    #[test]
    pub fn infer_conditional() {
        let e = Expr::if_(Expr::bool(true), Expr::bool(false), Expr::bool(true));

        let mut ti = TypeInference::new();
        let m = ti.generate_constraints(Ctx::empty(), &e).unwrap();

        match m {
            MigrationalType::Var(_alpha) => (),
            _ => panic!("expected a type variable, got {:?}", m),
        }
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
            v => panic!("expected variational choice, got {:?}", v)
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
            v => panic!("expected variational choice, got {:?}", v)
        }

        assert_eq!(theta.lookup(&e), None);
    }
}
