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
