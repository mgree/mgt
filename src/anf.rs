use crate::coerce::Ctx;
use crate::syntax::*;

use log::debug;

pub const ANF_VARNAME: &str = "__mgt_var";

struct Anf {
    next_var: usize,
}

impl Anf {
    pub fn new() -> Self {
        Anf { next_var: 0 }
    }

    fn fresh(&mut self) -> String {
        let num = self.next_var;
        self.next_var += 1;

        format!("{}{}", ANF_VARNAME, num)
    }

    pub fn anf(&mut self, e: &mut ExplicitExpr, ctx: &Ctx) -> GradualType {
        use ExplicitExpr::*;
        match e {
            Const(c) => c.ground_type().into(),
            Var(x) => ctx.lookup(&x).unwrap().clone(),
            Hole(_, g) => g.clone(),
            Nil(g) => GradualType::list(g.clone()),
            Cons(e1, e2) => {
                let g1 = self.anf(e1, ctx);
                let g2 = self.anf(e2, ctx);

                assert_eq!(g1, g2.elt().unwrap());

                let x1 = self.fresh();
                let x2 = self.fresh();

                *e = ExplicitExpr::let_(
                    x1.clone(),
                    g1,
                    *e1.clone(),
                    ExplicitExpr::let_(
                        x2.clone(),
                        g2.clone(),
                        *e2.clone(),
                        ExplicitExpr::cons(ExplicitExpr::Var(x1), ExplicitExpr::Var(x2)),
                    ),
                );

                g2
            }
            Lam(x, g1, e_body) => {
                let g2 = self.anf(e_body, &ctx.extend(x.clone(), g1.clone()));
                GradualType::fun(g1.clone(), g2)
            }
            Coerce(e, c) => {
                let g1 = self.anf(e, ctx);
                let (g21, g22) = c.types().unwrap();
                debug!("{} : {} ~> {}", c, g21, g22);
                debug!("on {} : {}", e, g1);
                assert_eq!(g1, g21);
                g22
            }
            App(e1, e2) => {
                let g1 = self.anf(e1, ctx);
                let g2 = self.anf(e2, ctx);

                let x1 = self.fresh();
                let x2 = self.fresh();

                let g11 = g1.dom().unwrap();
                let g12 = g1.cod().unwrap();

                assert_eq!(g11, g2);
                *e = ExplicitExpr::let_(
                    x1.clone(),
                    g1,
                    *e1.clone(),
                    ExplicitExpr::let_(
                        x2.clone(),
                        g2,
                        *e2.clone(),
                        ExplicitExpr::app(ExplicitExpr::Var(x1), ExplicitExpr::Var(x2)),
                    ),
                );

                g12
            }
            UOp(op, e) => {
                let (g_dom, g_cod) = op.signature();

                let g = self.anf(e, ctx);

                assert_eq!(g_dom, g);

                g_cod
            }
            BOp(op, e1, e2) => {
                let (g_dom, g_cod) = op.signature();

                let g1 = self.anf(e1, ctx);
                let g2 = self.anf(e2, ctx);

                assert_eq!(g_dom, g1);
                assert_eq!(g_dom, g2);

                g_cod
            }
            If(e1, e2, e3) => {
                let g1 = self.anf(e1, ctx);
                let g2 = self.anf(e2, ctx);
                let g3 = self.anf(e3, ctx);

                assert_eq!(g1, GradualType::bool());
                assert_eq!(g2, g3);

                g2
            }
            Let(x, g, e1, e2) => {
                let g1 = self.anf(e1, ctx);
                assert_eq!(g, &g1);
                
                self.anf(e2, &ctx.extend(x.clone(), g1))
            }
            LetRec(bindings, e) => {
                let mut ctx = ctx.clone();
                for (xi, gi, _) in bindings.iter_mut() {
                    ctx = ctx.extend(xi.clone(), gi.clone());
                }

                for (_, gi, ei) in bindings.iter_mut() {
                    let got = self.anf(ei, &ctx);
                    assert_eq!(gi, &got);
                }

                self.anf(e, &ctx)
            }
            Match(e, e_nil, hd, tl, e_cons) => {
                let g = self.anf(e, ctx);

                let elt = g.elt().unwrap();

                let g1 = self.anf(e_nil, ctx);

                let g2 = self.anf(
                    e_cons,
                    &ctx.extend(hd.clone(), elt.clone())
                        .extend(tl.clone(), GradualType::list(elt)),
                );

                assert_eq!(g1, g2);

                g1
            }
        }
    }
}

impl ExplicitExpr {
    pub fn anf(&mut self) {
        let mut anf = Anf::new();
        anf.anf(self, &Ctx::empty());
    }
}
