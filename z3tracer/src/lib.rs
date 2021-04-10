// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! This crate provides an experimental parser for Z3 tracing logs obtained by passing
//! `trace=true proof=true`.
//!
//! Currently, this library only supports Z3 v4.8.9
//!
//! ```
//! # use std::str::FromStr;
//! # use std::collections::BTreeMap;
//! use z3tracer::{Model, syntax::{Ident, Term}};
//! # fn main() -> z3tracer::error::RawResult<()> {
//! let mut model = Model::default();
//! let input = br#"
//! [mk-app] #0 a
//! [mk-app] #1 + #0 #0
//! [eof]
//! "#;
//! model.process(None, &input[1..])?;
//! assert_eq!(model.terms().len(), 2);
//! assert!(matches!(model.term(&Ident::from_str("#1")?)?, Term::App { .. }));
//! assert_eq!(model.id_to_sexp(&BTreeMap::new(), &Ident::from_str("#1").unwrap()).unwrap(), "(+ a a)");
//! # Ok(())
//! # }
//! ```
//!
//! See also in the [repository](https://github.com/facebookincubator/smt2utils/tree/master/z3tracer/notebooks) for more complex examples using Jupyter notebooks.
//!
//! More information about Z3 tracing logs can be found in the documentation of the
//! project [Axiom Profiler](https://github.com/viperproject/axiom-profiler).

#![forbid(unsafe_code)]

/// Error management.
pub mod error;
/// Tokenization of Z3 logs.
pub mod lexer;
/// Main analyzer module.
pub mod model;
/// Parsing of Z3 logs.
pub mod parser;
/// Terms and data structures found in Z3 logs.
pub mod syntax;

pub use error::{Error, Result};
pub use model::{Model, ModelConfig};
