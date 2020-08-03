#[macro_use]
extern crate lalrpop_util;

pub mod options;

pub use options::{Options, CompilationMode};

pub mod syntax;

pub mod infer;

pub use infer::TypeInference;

pub mod coerce;

pub use coerce::CoercionInsertion;

pub mod ocaml;

pub use ocaml::OCamlCompiler;

