extern crate mgt;

use mgt::*;

fn main() {
    let x = Expr::Var(String::from("x"));
    let little_omega = Expr::lam(String::from("x"), Expr::app(x.clone(), x));
    let big_omega = Expr::app(little_omega.clone(), little_omega.clone());
    println!("{:?}", big_omega);
}
