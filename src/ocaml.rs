use std::io::Write;
use std::process::Command;

use log::{info, warn, error};

use crate::options::CompilationOptions;
use crate::syntax::*;

pub struct OCamlCompiler {
    pub options: CompilationOptions,
}

impl OCamlCompiler {
    pub fn new(options: CompilationOptions) -> Self {
        OCamlCompiler { options }
    }

    pub fn go(&self, variation: &str, e: ExplicitExpr, g: GradualType) {
        let exe = self.compile(variation, e, g);

        if self.options.run {
            let _ = self.run(exe);
        }
    }

    pub fn compile(&self, variation: &str, mut e: ExplicitExpr, g: GradualType) -> String {
        let pp = pretty::BoxAllocator;

        // eta expand any letrecs that might have coercions in there
        e.fix_letrecs();
        if self.options.enforce_ltr {
            e.anf();
        }

        let ocaml = e.ocaml::<_, ()>(&pp).indent(2);

        let src_file = self.options.file_ext(variation, ".ml");
        let mut src = std::fs::File::create(&src_file).expect("make source file");

        writeln!(src, "let v =").expect("write ocaml source (top-level let)");
        ocaml
            .1
            .render(80, &mut src)
            .expect("write ocaml source (actual code)");
        writeln!(src, ";;").expect("write ocaml source (double semi-colon)");
        writeln!(src, "print_endline ({} v)", g.printer()).expect("write ocaml source (printer)");

        info!("ocaml source is in {}", src_file);

        let ocamlfind = Command::new("which")
            .arg("ocamlfind")
            .output()
            .expect("located ocamlfind");

        let ocamlfind = std::str::from_utf8(&ocamlfind.stdout).expect("valid utf-8 path");
        info!("using ocamlfind in {}", &ocamlfind);

        let exe = self.options.file_ext(variation, ".exe");
        info!("writing executable in {}", exe);

        let res = Command::new("ocamlfind")
            .arg("ocamlopt")
            .arg("-package")
            .arg("mgt")
            .arg("-linkpkg")
            .arg(src_file)
            .arg("-o")
            .arg(&exe)
            .status()
            .expect("successful run of ocamlopt");

        if !res.success() {
            error!("Compiler failed!")
        }

        exe
    }

    pub fn run(&self, exe: String) -> bool {
        let res = Command::new(exe).status().expect("run compiled executable");

        res.success()
    }
}

impl GradualType {
    fn ocaml<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            GradualType::Dyn() => pp.text("Mgt.Runtime.dyn"),
            GradualType::Base(b) => pp.as_string(b),
            GradualType::Var(a) => pp.text(format!("'{}", a)),
            GradualType::List(g) if g.is_compound() => g
                .ocaml(pp)
                .parens()
                .append(pp.space())
                .append(pp.text("list")),
            GradualType::List(g) => g.ocaml(pp).append(pp.space()).append(pp.text("list")),
            GradualType::Fun(g1, g2) if g1.is_fun() => g1
                .ocaml(pp)
                .parens()
                .group()
                .append(pp.space())
                .append(pp.text("->"))
                .append(pp.line())
                .append(g2.ocaml(pp).group())
                .group(),
            GradualType::Fun(g1, g2) => g1
                .ocaml(pp)
                .group()
                .append(pp.space())
                .append(pp.text("->"))
                .append(pp.line())
                .append(g2.ocaml(pp).group())
                .group(),
        }
    }

    fn printer(&self) -> String {
        match self {
            GradualType::Dyn() => "Mgt.Runtime.string_of_dyn".to_string(),
            GradualType::Var(a) => {
                warn!(
                    "Program has polymorphic return type {}, printing will misbehave.",
                    a
                );
                "(fun _x -> \"polymorphic value\")".to_string()
            }
            GradualType::Base(BaseType::Bool) => "string_of_bool".to_string(),
            GradualType::Base(BaseType::Int) => "string_of_int".to_string(),
            GradualType::Base(BaseType::String) => "(fun s -> s)".to_string(),
            GradualType::List(g) => format!("Mgt.Runtime.string_of_list {}", g.printer()),
            GradualType::Fun(_, _) => "(fun _f -> \"<procedure>\")".to_string(),
        }
    }
}

impl ExplicitUOp {
    fn ocaml(&self) -> &'static str {
        match self {
            ExplicitUOp::Not => "not",
            ExplicitUOp::Negate => "-",
            ExplicitUOp::Is(GroundType::Base(BaseType::Bool)) => "Mgt.Runtime.is_bool",
            ExplicitUOp::Is(GroundType::Base(BaseType::Int)) => "Mgt.Runtime.is_int",
            ExplicitUOp::Is(GroundType::Base(BaseType::String)) => "Mgt.Runtime.is_string",
            ExplicitUOp::Is(GroundType::Fun) => "Mgt.Runtime.is_fun",
            ExplicitUOp::Is(GroundType::List) => "Mgt.Runtime.is_list",
        }
    }
}

enum BOpType {
    Prefix,
    Infix,
}

impl ExplicitBOp {
    fn ocaml(&self) -> (BOpType, &'static str) {
        match self {
            ExplicitBOp::PlusInt => (BOpType::Infix, "+"),
            ExplicitBOp::PlusString => (BOpType::Infix, "^"),
            ExplicitBOp::PlusDyn => (BOpType::Prefix, "Mgt.Runtime.bop_plusdyn"),
            ExplicitBOp::Minus => (BOpType::Infix, "-"),
            ExplicitBOp::Times => (BOpType::Infix, "*"),
            ExplicitBOp::Divide => (BOpType::Infix, "/"),
            ExplicitBOp::And => (BOpType::Infix, "&&"),
            ExplicitBOp::Or => (BOpType::Infix, "||"),
            ExplicitBOp::EqualBool => (BOpType::Infix, "="),
            ExplicitBOp::EqualInt => (BOpType::Infix, "="),
            ExplicitBOp::EqualString => (BOpType::Infix, "="),
            ExplicitBOp::EqualDyn => (BOpType::Prefix, "Mgt.Runtime.bop_equaldyn"),
            ExplicitBOp::LessThan => (BOpType::Infix, "<"),
            ExplicitBOp::LessThanEqual => (BOpType::Infix, "<="),
            ExplicitBOp::Choice(d, _op1, _op2) => panic!("unexpected choice {} in coerced term", d),
        }
    }
}

impl Coercion {
    fn ocaml<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Coercion::Id(_, _g) => pp.text("Mgt.Runtime.coerce_id"),
            Coercion::Check(g) => pp.text(format!("Mgt.Runtime.check_{}", g)),
            Coercion::Tag(g) => pp.text(format!("Mgt.Runtime.tag_{}", g)),
            Coercion::Fun(c1, c2) => pp.intersperse(
                vec![
                    pp.text("Mgt.Runtime.coerce_fun"),
                    c1.ocaml(pp).group().parens(),
                    c2.ocaml(pp).group().parens(),
                ],
                pp.line(),
            ),
            Coercion::List(c) => pp.intersperse(
                vec![
                    pp.text("Mgt.Runtime.coerce_list"),
                    c.ocaml(pp).group().parens(),
                ],
                pp.line(),
            ),
            Coercion::Seq(c1, c2) => pp.intersperse(
                vec![
                    pp.text("Mgt.Runtime.coerce_seq"),
                    c1.ocaml(pp).group().parens(),
                    c2.ocaml(pp).group().parens(),
                ],
                pp.line(),
            ),
        }
    }
}

impl ExplicitExpr {
    fn fix_letrecs(&mut self) {
        use ExplicitExpr::*;
        match self {
            Const(_) | Var(_) | Hole(_, _) | Nil(_) => (),
            Lam(_, _, e) | Coerce(e, _) | UOp(_, e) => e.fix_letrecs(),
            App(e1, e2) | Let(_, _, e1, e2) | BOp(_, e1, e2) | Cons(e1, e2) => {
                e1.fix_letrecs();
                e2.fix_letrecs();
            }
            If(e1, e2, e3) | Match(e1, e2, _, _, e3) => {
                e1.fix_letrecs();
                e2.fix_letrecs();
                e3.fix_letrecs();
            }
            LetRec(defns, e2) => {
                for (_, g, e1) in defns.iter_mut() {
                    e1.fix_letrecs();
                    *e1 = e1.eta_expand(g, 0);
                }
                e2.fix_letrecs();
            }
        }
    }

    fn eta_expand(&self, g: &GradualType, n: usize) -> Self {
        // no need to eta expand a function
        if let ExplicitExpr::Lam(_, _, _) = self {
            return self.clone();
        }

        match g {
            GradualType::Fun(g1, g2) => {
                let x = format!("mgt_eta{}", n);
                ExplicitExpr::lam(x, *g1.clone(), self.eta_expand(g2, n+1))
            }
            _ => {
                let mut e = self.clone();

                for i in 0..n {
                    let x = format!("mgt_eta{}", i);
                    e = ExplicitExpr::app(e, ExplicitExpr::Var(x));
                }

                e
            }
        }
    }

    fn ocaml<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            ExplicitExpr::Var(x) => pp.text(x),
            ExplicitExpr::Const(c) => pp.as_string(c),
            ExplicitExpr::Lam(x, t, e) => pp
                .text("fun ")
                .append(
                    pp.intersperse(vec![pp.text(x), pp.text(":"), t.ocaml(pp)], pp.space())
                        .parens(),
                )
                .append(pp.line())
                .append(pp.text("->"))
                .append(pp.line())
                .append(e.ocaml(pp).nest(2))
                .group(),
            ExplicitExpr::Hole(name, _t) => pp
                .text("Mgt.Runtime.hole")
                .append(pp.space())
                .append(pp.as_string(name).double_quotes())
                .group(),
            ExplicitExpr::Coerce(e, c) => c
                .ocaml(pp)
                .group()
                .append(pp.line())
                .append(e.ocaml(pp).nest(2).parens())
                .group(),
            ExplicitExpr::App(e1, e2) => {
                let mut d1 = e1.ocaml(pp);
                let mut d2 = e2.ocaml(pp);

                if e1.is_compound() && !e1.is_app() {
                    d1 = d1.parens();
                }

                if e2.is_compound() {
                    d2 = d2.parens();
                }

                d1.append(pp.line()).append(d2.nest(2)).group()
            }
            ExplicitExpr::If(e1, e2, e3) => {
                let d_cond = pp
                    .text("if")
                    .append(pp.space())
                    .append(e1.ocaml(pp).nest(2))
                    .append(pp.line());

                let d_then = pp
                    .text("then")
                    .append(pp.line())
                    .append(e2.ocaml(pp).nest(2))
                    .append(pp.line());

                let d_else = pp
                    .text("else")
                    .append(pp.line())
                    .append(e3.ocaml(pp).nest(2));

                pp.concat(vec![d_cond, d_then, d_else]).group()
            }
            ExplicitExpr::Let(x, t, e1, e2) => {
                let d_bind = pp
                    .intersperse(
                        vec![
                            pp.text("let"),
                            pp.text(x),
                            pp.text(":"),
                            t.ocaml(pp),
                            pp.text("="),
                        ],
                        pp.space(),
                    )
                    .group();

                pp.intersperse(vec![d_bind, e1.ocaml(pp).nest(2), pp.text("in")], pp.line())
                    .append(pp.hardline())
                    .append(e2.ocaml(pp))
            }
            ExplicitExpr::LetRec(defns, e2) => {
                let letrec = pp.text("let rec").append(pp.space());

                let bindings = pp.intersperse(
                    defns.iter().map(|(x, t, e1)| {
                        pp.intersperse(
                            vec![pp.text(x), pp.text(":"), t.ocaml(pp), pp.text("=")],
                            pp.space(),
                        )
                        .group()
                        .append(pp.line())
                        .append(e1.ocaml(pp).nest(2))
                    }),
                    pp.text("and").enclose(pp.hardline(), pp.hardline()),
                );

                letrec
                    .append(bindings)
                    .append(pp.hardline())
                    .append(pp.text("in"))
                    .append(pp.line())
                    .append(e2.ocaml(pp))
            }
            // TODO proper pretty printing with precedence
            ExplicitExpr::UOp(op, e) => {
                pp.text(op.ocaml())
                    .append(pp.space())
                    .append(if e.is_compound() {
                        e.ocaml(pp).parens()
                    } else {
                        e.ocaml(pp)
                    })
            }
            ExplicitExpr::BOp(op, e1, e2) => match op.ocaml() {
                (BOpType::Infix, op) => pp.intersperse(
                    vec![
                        if e1.is_compound() {
                            e1.ocaml(pp).parens()
                        } else {
                            e1.ocaml(pp)
                        },
                        pp.as_string(op),
                        if e2.is_compound() {
                            e2.ocaml(pp).parens()
                        } else {
                            e2.ocaml(pp)
                        },
                    ],
                    pp.space(),
                ),
                (BOpType::Prefix, op) => pp.intersperse(
                    vec![
                        pp.as_string(op),
                        if e1.is_compound() {
                            e1.ocaml(pp).parens()
                        } else {
                            e1.ocaml(pp)
                        },
                        if e2.is_compound() {
                            e2.ocaml(pp).parens()
                        } else {
                            e2.ocaml(pp)
                        },
                    ],
                    pp.space(),
                ),
            },
            ExplicitExpr::Nil(_t) => pp.text("[]"),
            // TODO identify concrete lists and pretty print accordingly
            ExplicitExpr::Cons(e1, e2) => pp.intersperse(
                vec![
                    if e1.is_compound() {
                        e1.ocaml(pp).parens()
                    } else {
                        e1.ocaml(pp)
                    },
                    pp.text("::"),
                    if e2.is_compound() {
                        e2.ocaml(pp).parens()
                    } else {
                        e2.ocaml(pp)
                    },
                ],
                pp.line(),
            ),
            ExplicitExpr::Match(e_scrutinee, e_nil, hd, tl, e_cons) => pp.intersperse(
                vec![
                    pp.intersperse(
                        vec![pp.text("match"), e_scrutinee.ocaml(pp), pp.text("with")],
                        pp.space(),
                    )
                    .group(),
                    pp.intersperse(
                        vec![
                            pp.text("|"),
                            pp.text("[]"),
                            pp.text("->"),
                            e_nil.ocaml(pp).indent(2),
                        ],
                        pp.space(),
                    )
                    .group(),
                    pp.intersperse(
                        vec![
                            pp.text("|"),
                            pp.as_string(hd),
                            pp.text("::"),
                            pp.as_string(tl),
                            pp.text("->"),
                            e_cons.ocaml(pp).indent(2),
                        ],
                        pp.space(),
                    )
                    .group(),
                ],
                pp.line(),
            ),
        }
    }
}
