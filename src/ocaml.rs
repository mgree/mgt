use crate::syntax::*;

impl GradualType {
    pub fn ocaml<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        todo!("ocaml-ized gradual types")
    }
}

impl ExplicitUOp {
    pub fn ocaml<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        todo!("ocaml-ized uop")
    }
}

impl ExplicitBOp {
    pub fn ocaml<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        todo!("ocaml-ized bop")
    }
}

impl ExplicitExpr {
    pub fn ocaml<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        todo!("ocaml-ized exprs")
    }
}