use im_rc::HashMap;

use crate::syntax::*;

// Gamma
#[derive(Clone, Debug)]
pub struct Ctx(HashMap<Variable, GradualType>);

impl Ctx {
    pub fn empty() -> Self {
        Ctx(HashMap::new())
    }

    pub fn extend(&self, x: Variable, m: GradualType) -> Self {
        Ctx(self.0.update(x, m))
    }

    pub fn lookup(&self, x: &Variable) -> Option<&GradualType> {
        self.0.get(x)
    }
}

pub struct CoercionInsertion {}

impl CoercionInsertion {
    /// should only be called on an eliminated e
    fn make_explicit(&self, ctx: &Ctx, e: TargetExpr) -> (ExplicitExpr, GradualType) {
        assert!(e.choices().is_empty());

        match e {
            GradualExpr::Const(c) => (ExplicitExpr::Const(c.clone()), c.into()),
            GradualExpr::Var(x) => {
                let g = ctx.lookup(&x).expect("unbound variable").clone();
                (ExplicitExpr::Var(x), g)
            }
            GradualExpr::Lam(x, dom, e) => {
                let dom = dom.try_gradual().expect("malformed domain");
                let (e, cod) = self.make_explicit(&ctx.extend(x.clone(), dom.clone()), *e);

                (
                    ExplicitExpr::lam(x, dom.clone(), e),
                    GradualType::fun(dom, cod),
                )
            }
            GradualExpr::Ann(e, m) => {
                let g_ann = m.try_gradual().expect("malformed annotation");

                let (e, g) = self.make_explicit(ctx, *e);

                (ExplicitExpr::coerce(e, g, g_ann.clone()), g_ann)
            }
            GradualExpr::Hole(name) => (ExplicitExpr::Hole(name), GradualType::Dyn()),
            GradualExpr::App(e1, e2) => {
                let (e1, g1) = self.make_explicit(ctx, *e1);
                let (e2, g2) = self.make_explicit(ctx, *e2);

                let (g11, g12) = match g1.clone() {
                    GradualType::Fun(g11, g12) => (*g11, *g12),
                    GradualType::Dyn() => (GradualType::Dyn(), GradualType::Dyn()),
                    g => panic!("applied non-function: {} : {}", e1, g),
                };

                (
                    ExplicitExpr::app(
                        ExplicitExpr::coerce(e1, g1, GradualType::fun(g11.clone(), g12.clone())),
                        ExplicitExpr::coerce(e2, g2, g11),
                    ),
                    g12,
                )
            }
            GradualExpr::If(e1, e2, e3) => {
                let (e1, g1) = self.make_explicit(ctx, *e1);
                let (e2, g2) = self.make_explicit(ctx, *e2);
                let (e3, g3) = self.make_explicit(ctx, *e3);

                let g = g2.join(&g3);

                (
                    ExplicitExpr::if_(
                        ExplicitExpr::coerce(e1, g1, GradualType::bool()),
                        ExplicitExpr::coerce(e2, g2, g.clone()),
                        ExplicitExpr::coerce(e3, g3, g.clone()),
                    ),
                    g,
                )
            }
            GradualExpr::Let(x, m, e1, e2) => {
                let (e1, g1) = self.make_explicit(ctx, *e1);

                let g1_ann = m.try_gradual().expect("malformed let annotation");

                let (e2, g2) = self.make_explicit(&ctx.extend(x.clone(), g1_ann.clone()), *e2);

                (
                    ExplicitExpr::let_(x, g1_ann.clone(), ExplicitExpr::coerce(e1, g1, g1_ann), e2),
                    g2,
                )
            }
            GradualExpr::LetRec(defns, e2) => {
                let mut ctx = ctx.clone();
                for (x, m, _) in defns.iter() {
                    ctx = ctx.extend(
                        x.clone(),
                        m.try_gradual().expect("malformed let rec annotation"),
                    );
                }

                let defns: Vec<(Variable, GradualType, ExplicitExpr)> = defns
                    .into_iter()
                    .map(|(x, m, e1)| {
                        let (e1, g1) = self.make_explicit(&ctx, e1);

                        let g1_ann = m.try_gradual().expect("malformed letrec annotation");

                        (x, g1_ann.clone(), ExplicitExpr::coerce(e1, g1, g1_ann))
                    })
                    .collect();

                let (e2, g2) = self.make_explicit(&ctx, *e2);

                (ExplicitExpr::letrec(defns, e2), g2)
            }
            GradualExpr::UOp(op, e) => {
                let (e, g) = self.make_explicit(ctx, *e);

                let (g_dom, g_cod) = op.signature();

                (
                    ExplicitExpr::uop(op, ExplicitExpr::coerce(e, g, g_dom)),
                    g_cod,
                )
            }
            GradualExpr::BOp(op, e1, e2) => {
                let (e1, g1) = self.make_explicit(ctx, *e1);
                let (e2, g2) = self.make_explicit(ctx, *e2);

                let (g_dom, g_cod) = op.signature();

                (
                    ExplicitExpr::bop(
                        op,
                        ExplicitExpr::coerce(e1, g1, g_dom.clone()),
                        ExplicitExpr::coerce(e2, g2, g_dom),
                    ),
                    g_cod,
                )
            }
        }
    }

    pub fn run(e: TargetExpr) -> (ExplicitExpr, GradualType) {
        let ci = CoercionInsertion {};

        ci.make_explicit(&Ctx::empty(), e)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::infer::*;

    fn has_no_coercions(s: &str) {
        let (e, m, ves) = TypeInference::infer(&SourceExpr::parse(s).unwrap()).unwrap();

        for ve in ves.iter() {
            let e = e.clone().eliminate(ve);
            let m = m.clone().eliminate(ve);

            assert!(e.choices().is_empty());
            assert!(m.choices().is_empty());

            let (e, g) = CoercionInsertion::run(e);
            assert_eq!(m, g.into());

            assert!(e.coercions().is_empty());
        }
    }

    fn unique_coercion(s: &str) -> (ExplicitExpr, GradualType) {
        let (e, m, ves) = TypeInference::infer(&SourceExpr::parse(s).unwrap()).unwrap();

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        let (e, g) = CoercionInsertion::run(e.eliminate(ve));

        assert_eq!(m, g.clone().into());

        (e, g)
    }

    #[test]
    fn statically_typed_no_coercions() {
        has_no_coercions("2 + 2");
        has_no_coercions(r#""hi" + "sup""#);
        has_no_coercions("true == false");
        has_no_coercions("1 == 0");
        has_no_coercions(r#""a" == "b""#);

        has_no_coercions(r"\x. x");
        has_no_coercions(r"\x. x + 1");
        has_no_coercions(r#"\x. x + "hi""#);
        has_no_coercions(r"let id = \x. x in id 12");
        has_no_coercions(r"let id = \x. x in if true then false else id false");
    }

    #[test]
    fn overloaded_plus_coercions() {
        let (e, g) = unique_coercion("1 + true");

        assert_eq!(g, GradualType::Dyn());
        assert_eq!(
            e,
            ExplicitExpr::bop(
                ExplicitBOp::PlusDyn,
                ExplicitExpr::coerce(
                    ExplicitExpr::Const(Constant::Int(1)),
                    GradualType::int(),
                    GradualType::Dyn()
                ),
                ExplicitExpr::coerce(
                    ExplicitExpr::Const(Constant::Bool(true)),
                    GradualType::bool(),
                    GradualType::Dyn()
                ),
            )
        );
    }
}
