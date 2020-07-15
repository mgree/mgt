extern crate mgt;

use mgt::*;

fn main() {
    let x = Expr::Var(String::from("x"));
    let little_omega = Expr::lam(String::from("x"), Expr::app(x.clone(), x));
    let big_omega = Expr::app(little_omega.clone(), little_omega.clone());
    println!("{:?}", big_omega);

    let mut cg = ConstraintGenerator::new();
    println!("{:?}", cg.infer(Ctx::empty(), &little_omega));
    println!("{:?}", cg.constraints);
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    pub fn infer_identity() {
        let x = String::from("x");
        let id = Expr::lam(x.clone(), Expr::Var(x));

        let mut cg = ConstraintGenerator::new();
        let m = cg.infer(Ctx::empty(), &id).unwrap();
        match m {
            MigrationalType::Fun(dom, cod) => assert_eq!(dom, cod),
            _ => panic!("expected function type"),
        }
    }

    #[test]
    pub fn infer_boolean_negation() {
        let b = String::from("b");
        let neg = Expr::lam(b.clone(), Expr::if_(Expr::Var(b), Expr::bool(false), Expr::bool(true)));

        let mut cg = ConstraintGenerator::new();
        let m = cg.infer(Ctx::empty(), &neg).unwrap();
        match m {
            MigrationalType::Fun(dom, cod) => {
                match (*dom, *cod) {
                    (MigrationalType::Var(_alpha), MigrationalType::Var(_beta)) => (),
                    (dom, cod) => panic!("expected variables, got {:?} and {:?}", dom, cod),
                }
            }
            _ => panic!("expected function type, got {:?}", m),
        };
    }

    #[test]
    pub fn infer_conditional() {
        let e = Expr::if_(Expr::bool(true), Expr::bool(false), Expr::bool(true));

        let mut cg = ConstraintGenerator::new();
        let m = cg.infer(Ctx::empty(), &e).unwrap();

        match m {
            MigrationalType::Var(_alpha) => (),
            _ => panic!("expected a type variable, got {:?}", m),
        }
    }
}
