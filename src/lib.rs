#[macro_use]
extern crate lalrpop_util;

pub mod syntax;

pub mod infer;

pub use infer::{Ctx, Options, TypeInference};

pub mod coerce;

pub use coerce::CoercionInsertion;
