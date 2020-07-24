#[macro_use]
extern crate lalrpop_util;

pub mod syntax;

pub mod infer;

pub use infer::Ctx;
pub use infer::TypeInference;
