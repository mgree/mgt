#[macro_use]
extern crate lalrpop_util;

pub mod options;

pub use options::{CompilationMode, CompilationOptions, Options};

pub mod syntax;
pub mod types;

pub mod infer;

pub use infer::TypeInference;

pub mod coerce;

pub use coerce::CoercionInsertion;

pub mod anf;

pub mod ocaml;

pub use ocaml::OCamlCompiler;
