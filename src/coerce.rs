use crate::options::Options;
use im_rc::HashMap;

use log::{error, warn};

use crate::infer::BOpSignature;
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

pub struct CoercionInsertion {
    pub options: Options,
}

impl CoercionInsertion {
    pub fn new(options: Options) -> Self {
        CoercionInsertion { options }
    }

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

                (self.coerce(e, &g, &g_ann), g_ann)
            }
            GradualExpr::Hole(name, m) => {
                let g = m.try_gradual().expect("malformed annotation");

                (ExplicitExpr::Hole(name, g.clone()), g)
            }
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
                        self.coerce(e1, &g1, &GradualType::fun(g11.clone(), g12.clone())),
                        self.coerce(e2, &g2, &g11),
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
                        self.coerce(e1, &g1, &GradualType::bool()),
                        self.coerce(e2, &g2, &g),
                        self.coerce(e3, &g3, &g),
                    ),
                    g,
                )
            }
            GradualExpr::Let(x, m, e1, e2) => {
                let (e1, g1) = self.make_explicit(ctx, *e1);

                let g1_ann = m.try_gradual().expect("malformed let annotation");

                let (e2, g2) = self.make_explicit(&ctx.extend(x.clone(), g1_ann.clone()), *e2);

                (
                    ExplicitExpr::let_(x, g1_ann.clone(), self.coerce(e1, &g1, &g1_ann), e2),
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

                        (x, g1_ann.clone(), self.coerce(e1, &g1, &g1_ann))
                    })
                    .collect();

                let (e2, g2) = self.make_explicit(&ctx, *e2);

                (ExplicitExpr::letrec(defns, e2), g2)
            }
            GradualExpr::UOp(op, e) => {
                let (e, g) = self.make_explicit(ctx, *e);

                let (g_dom, g_cod) = op.signature();

                (ExplicitExpr::uop(op, self.coerce(e, &g, &g_dom)), g_cod)
            }
            GradualExpr::BOp(op, e1, e2) => {
                let (e1, g1) = self.make_explicit(ctx, *e1);
                let (e2, g2) = self.make_explicit(ctx, *e2);

                let (g_dom, g_cod) = op.signature();

                (
                    ExplicitExpr::bop(
                        op,
                        self.coerce(e1, &g1, &g_dom),
                        self.coerce(e2, &g2, &g_dom),
                    ),
                    g_cod,
                )
            }
        }
    }

    pub fn explicit(&self, e: TargetExpr) -> (ExplicitExpr, GradualType) {
        self.make_explicit(&Ctx::empty(), e)
    }

    fn dynamize(&self, ctx: &Ctx, e: SourceExpr) -> Option<(ExplicitExpr, GradualType)> {
        match e {
            GradualExpr::Const(c) => Some((ExplicitExpr::Const(c.clone()), c.into())),
            GradualExpr::Var(x) => {
                let g = ctx.lookup(&x)?.clone();
                Some((ExplicitExpr::Var(x), g))
            }
            GradualExpr::Lam(x, dom, e) => {
                let dom = dom.unwrap_or(GradualType::Dyn());
                let (e, cod) = self.dynamize(&ctx.extend(x.clone(), dom.clone()), *e)?;

                Some((
                    ExplicitExpr::lam(x, dom.clone(), e),
                    GradualType::fun(dom, cod),
                ))
            }
            GradualExpr::Ann(e, g) => {
                let g_ann = g.unwrap_or(GradualType::Dyn());

                let (e, g) = self.dynamize(ctx, *e)?;

                Some((self.coerce(e, &g, &g_ann), g_ann))
            }
            GradualExpr::Hole(name, g) => {
                let g = g.unwrap_or(GradualType::Dyn());

                Some((ExplicitExpr::Hole(name, g.clone()), g))
            }
            GradualExpr::App(e1, e2) => {
                let (e1, g1) = self.dynamize(ctx, *e1)?;
                let (e2, g2) = self.dynamize(ctx, *e2)?;

                let (g11, g12) = match g1.clone() {
                    GradualType::Fun(g11, g12) => (*g11, *g12),
                    GradualType::Dyn() => (GradualType::Dyn(), GradualType::Dyn()),
                    g => {
                        error!("applied non-function: {} : {}", e1, g);
                        return None;
                    }
                };

                Some((
                    ExplicitExpr::app(
                        self.coerce(e1, &g1, &GradualType::fun(g11.clone(), g12.clone())),
                        self.coerce(e2, &g2, &g11),
                    ),
                    g12,
                ))
            }
            GradualExpr::If(e1, e2, e3) => {
                let (e1, g1) = self.dynamize(ctx, *e1)?;
                let (e2, g2) = self.dynamize(ctx, *e2)?;
                let (e3, g3) = self.dynamize(ctx, *e3)?;

                let g = g2.join(&g3);

                if !g1.consistent(&GradualType::bool()) {
                    error!("condition on non-bool: {}", e1);
                    return None;
                }

                Some((
                    ExplicitExpr::if_(
                        self.coerce(e1, &g1, &GradualType::bool()),
                        self.coerce(e2, &g2, &g),
                        self.coerce(e3, &g3, &g),
                    ),
                    g,
                ))
            }
            GradualExpr::Let(x, g, e1, e2) => {
                let (e1, g1) = self.dynamize(ctx, *e1)?;

                let g1_ann = g.unwrap_or(GradualType::Dyn());

                if !g1.consistent(&g1_ann) {
                    error!(
                        "annotation {} inconsistent with inferred type {} of {}",
                        g1_ann, g1, e1
                    );
                    return None;
                }

                let (e2, g2) = self.dynamize(&ctx.extend(x.clone(), g1_ann.clone()), *e2)?;

                Some((
                    ExplicitExpr::let_(x, g1_ann.clone(), self.coerce(e1, &g1, &g1_ann), e2),
                    g2,
                ))
            }
            GradualExpr::LetRec(defns, e2) => {
                let mut ctx = ctx.clone();
                for (x, g, _) in defns.iter() {
                    ctx = ctx.extend(x.clone(), g.clone().unwrap_or(GradualType::Dyn()));
                }

                let defns = defns
                    .into_iter()
                    .map(|(x, g1_ann, e1)| {
                        let (e1, g1) = self.dynamize(&ctx, e1)?;

                        let g1_ann = g1_ann.unwrap_or(GradualType::Dyn());

                        if !g1.consistent(&g1_ann) {
                            error!(
                                "annotation {} inconsistent with inferred type {} of {}",
                                g1_ann, g1, e1
                            );
                            return None;
                        }

                        Some((x, g1_ann.clone(), self.coerce(e1, &g1, &g1_ann)))
                    })
                    .collect::<Option<Vec<_>>>()?;

                let (e2, g2) = self.dynamize(&ctx, *e2)?;

                Some((ExplicitExpr::letrec(defns, e2), g2))
            }
            GradualExpr::UOp(op, e) => {
                let (e, g) = self.dynamize(ctx, *e)?;

                let op = op.explicit();
                let (g_dom, g_cod) = op.signature();

                if !g_dom.consistent(&g) {
                    error!(
                        "operation {} expects {}, applied to {} : {}",
                        op, g_dom, g, e
                    );
                    return None;
                }

                Some((ExplicitExpr::uop(op, self.coerce(e, &g, &g_dom)), g_cod))
            }
            GradualExpr::BOp(op, e1, e2) => {
                let (e1, g1) = self.dynamize(ctx, *e1)?;
                let (e2, g2) = self.dynamize(ctx, *e2)?;

                let op = match op.explicit() {
                    BOpSignature::Simple(op) => op,
                    BOpSignature::Overloaded { dyn_op, .. } => dyn_op,
                };
                let (g_dom, g_cod) = op.signature();

                if !g_dom.consistent(&g1) {
                    error!(
                        "operation {} expects {}, first argument {} : {}",
                        op, g_dom, g1, e1
                    );
                    return None;
                }

                if !g_dom.consistent(&g2) {
                    error!(
                        "operation {} expects {}, second argument {} : {}",
                        op, g_dom, g2, e2
                    );
                    return None;
                }

                Some((
                    ExplicitExpr::bop(
                        op,
                        self.coerce(e1, &g1, &g_dom),
                        self.coerce(e2, &g2, &g_dom),
                    ),
                    g_cod,
                ))
            }
        }
    }

    pub fn dynamic(&self, e: SourceExpr) -> Option<(ExplicitExpr, GradualType)> {
        self.dynamize(&Ctx::empty(), e)
    }

    fn coerce(&self, e: ExplicitExpr, src: &GradualType, tgt: &GradualType) -> ExplicitExpr {
        let c = self.coercion(src, tgt);
        // TODO could check safety here
        ExplicitExpr::coerce(e, c)
    }

    fn coercion(&self, src: &GradualType, tgt: &GradualType) -> Coercion {
        let c = {
            if src == tgt {
                Coercion::Id(IdType::Trivial, src.clone())
            } else {
                match (src, tgt) {
                    (GradualType::Base(b), GradualType::Dyn()) => {
                        Coercion::Tag(GroundType::Base(*b))
                    }
                    (GradualType::Dyn(), GradualType::Base(b)) => {
                        Coercion::Check(GroundType::Base(*b))
                    }
                    (src @ GradualType::Fun(_, _), GradualType::Dyn()) => Coercion::seq(
                        self.coercion(
                            src,
                            &GradualType::fun(GradualType::Dyn(), GradualType::Dyn()),
                        ),
                        Coercion::Tag(GroundType::Fun),
                    ),
                    (GradualType::Dyn(), src @ GradualType::Fun(_, _)) => Coercion::seq(
                        Coercion::Check(GroundType::Fun),
                        self.coercion(
                            &GradualType::fun(GradualType::Dyn(), GradualType::Dyn()),
                            src,
                        ),
                    ),
                    (GradualType::Fun(g11, g12), GradualType::Fun(g21, g22)) => {
                        Coercion::fun(self.coercion(g21, g11), self.coercion(g12, g22))
                    }
                    (src, tgt) => {
                        assert!(!src.consistent(tgt));

                        if self.options.safe_only {
                            panic!("Coercion between inconsistent types {} and {} is guaranteed to fail; bailing. Set --allow-unsafe to continue.",
                            src, tgt);
                        } else {
                            warn!("Coercion between inconsistent types {} and {} will fail; going through ?", src, tgt);
                            Coercion::seq(
                                self.coercion(src, &GradualType::Dyn()),
                                self.coercion(&GradualType::Dyn(), tgt),
                            )
                        }
                    }
                }
            }
        };

        let (g_src, g_tgt) = c.types().expect("well typed coercion");
        assert_eq!(src, &g_src);
        assert_eq!(tgt, &g_tgt);

        c
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::infer::*;

    fn has_no_coercions(s: &str) {
        let (e, m, ves) = TypeInference::infer(&SourceExpr::parse(s).unwrap()).unwrap();

        let ci = CoercionInsertion::new(Options::default());

        for ve in ves.iter() {
            let e = e.clone().eliminate(ve);
            let m = m.clone().eliminate(ve);

            assert!(e.choices().is_empty());
            assert!(m.choices().is_empty());

            let (e, g) = ci.explicit(e);
            assert_eq!(m, g.into());

            assert!(e.coercions().is_empty());
        }
    }

    fn unique_coercion(s: &str) -> (ExplicitExpr, GradualType) {
        let (e, m, ves) = TypeInference::infer(&SourceExpr::parse(s).unwrap()).unwrap();

        assert_eq!(ves.len(), 1);
        let ve = ves.iter().next().unwrap();
        let m = m.eliminate(ve);

        let ci = CoercionInsertion::new(Options::default());
        let (e, g) = ci.explicit(e.eliminate(ve));

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

        has_no_coercions("__ + 1");
        has_no_coercions("__ + \"hi\"");
        has_no_coercions("(\\x. x * 1) __should_be_int");
    }

    #[test]
    fn exact_holes() {
        let (e, g) = unique_coercion("__num + 1");

        assert_eq!(g, GradualType::int());
        assert_eq!(
            e,
            ExplicitExpr::bop(
                ExplicitBOp::PlusInt,
                ExplicitExpr::Hole("__num".into(), GradualType::int()),
                ExplicitExpr::Const(Constant::Int(1))
            )
        );
    }

    #[test]
    fn overloaded_plus_coercions() {
        let (e, g) = unique_coercion("1 + true");
        let ci = CoercionInsertion::new(Options::default());

        assert_eq!(g, GradualType::Dyn());
        assert_eq!(
            e,
            ExplicitExpr::bop(
                ExplicitBOp::PlusDyn,
                ci.coerce(
                    ExplicitExpr::Const(Constant::Int(1)),
                    &GradualType::int(),
                    &GradualType::Dyn()
                ),
                ci.coerce(
                    ExplicitExpr::Const(Constant::Bool(true)),
                    &GradualType::bool(),
                    &GradualType::Dyn()
                ),
            )
        );
    }

    fn rejected(s: &str) {
        let e = SourceExpr::parse(s).unwrap();
        let ci = CoercionInsertion::new(Options::default());

        match ci.dynamic(e) {
            None => (),
            Some((e, g)) => panic!("expected failure, got {} : {}", e, g),
        }
    }

    #[test]
    fn statically_rejected() {
        rejected("true false");
        rejected("if 0 then 1 else true");
        rejected("if 0 then 1 else 1");
        rejected("(\\x.x) * 1");
    }

    fn accepted(s: &str) {
        let e = SourceExpr::parse(s).unwrap();
        let ci = CoercionInsertion::new(Options::default());

        match ci.dynamic(e.clone()) {
            None => panic!("expected success, but couldn't type {}", e),
            Some((_e, _g)) => (),
        }

        // TODO check that e : g
    }

    #[test]
    fn statically_accepted_surprisingly() {
        accepted("if 0 + 1 then 1 else true");
        accepted("(\\x.x) == (\\y. y)");
        accepted("(\\x.x) == \"hi\"");
        accepted("false && (if true then (true:?) else (0:?))");
    }

    fn coerce(s1: &str, s2: &str) -> Coercion {
        let ci = CoercionInsertion::new(Options::default());

        // has a number of nice asserts already
        ci.coercion(
            &GradualType::parse(s1).unwrap(),
            &GradualType::parse(s2).unwrap(),
        )
    }

    #[test]
    fn contravariant_function_coercions() {
        assert_eq!(
            coerce("int -> ?", "? -> int"),
            Coercion::fun(
                Coercion::Check(GroundType::Base(BaseType::Int)),
                Coercion::Check(GroundType::Base(BaseType::Int))
            )
        );

        assert_eq!(
            coerce("? -> int", "int -> ?"),
            Coercion::fun(
                Coercion::Tag(GroundType::Base(BaseType::Int)),
                Coercion::Tag(GroundType::Base(BaseType::Int))
            )
        );

        assert_eq!(
            coerce("? -> int", "?"),
            Coercion::seq(
                Coercion::fun(
                    Coercion::Id(IdType::Trivial, GradualType::Dyn()),
                    Coercion::Tag(GroundType::Base(BaseType::Int))
                ),
                Coercion::Tag(GroundType::Fun)
            )
        );

        let c = Coercion::seq(coerce("? -> int", "?"), coerce("?", "bool"));
        assert_eq!(
            c,
            Coercion::seq(
                Coercion::seq(
                    Coercion::fun(
                        Coercion::Id(IdType::Trivial, GradualType::Dyn()),
                        Coercion::Tag(GroundType::Base(BaseType::Int))
                    ),
                    Coercion::Tag(GroundType::Fun)
                ),
                Coercion::Check(GroundType::Base(BaseType::Bool))
            )
        );

        let (src, tgt) = c.types().expect("well typed");
        assert_eq!(src, GradualType::parse("? -> int").unwrap());
        assert_eq!(tgt, GradualType::bool());
    }
}
