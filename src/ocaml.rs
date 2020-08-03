use std::io::Write;
use std::process::Command;

use log::info;

use crate::options::Options;
use crate::syntax::*;

pub struct OCamlCompiler {
    pub options: Options,
    workdir: tempfile::TempDir,
}

impl OCamlCompiler {
    pub fn new(options: Options) -> Self {
        OCamlCompiler {
            options,
            workdir: tempfile::TempDir::new_in(".")
                .expect("allocating working directory for ocamlopt"),
        }
    }

    fn file_ext(&self, ext: &str) -> String {
        let path = self.workdir.path().to_owned();
        let path = path.join(self.options.file_ext(ext));
        path.to_str().expect("converting path to UTF-8").to_string()
    }

    pub fn compile(&self, e: ExplicitExpr) -> String {
        let pp = pretty::BoxAllocator;
        let ocaml = e.ocaml::<_, ()>(&pp);

        let src_file = self.file_ext(".ml");
        let mut src = std::fs::File::create(&src_file).expect("make source file");
        ocaml.1.render(80, &mut src).expect("write ocaml source");
        src.write("\n".as_bytes()).expect("write trailing newline");
        info!("ocaml source is in {}", src_file);

        let ocamlfind = Command::new("which")
            .arg("ocamlfind")
            .output()
            .expect("located ocamlfind");

        // debug path
        let _ = Command::new("sh").args(&["-c", "echo $PATH"]).status().expect("current path");

        let ocamlfind = std::str::from_utf8(&ocamlfind.stdout).expect("valid utf-8 path");
        info!("using ocamlfind in {}", &ocamlfind);

        let exe = self.file_ext(".exe");
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

        assert!(res.success());

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
}

impl ExplicitUOp {
    fn ocaml(&self) -> &'static str {
        match self {
            ExplicitUOp::Not => "not",
            ExplicitUOp::Negate => "-",
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
                    defns.into_iter().map(|(x, t, e1)| {
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
        }
    }
}
