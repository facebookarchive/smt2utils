// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! This crate provides an experimental parser for Z3 tracing logs obtained by passing
//! `trace=true proof=true`.
//!
//! More information about Z3 tracing logs can be found in the documentation of the
//! project [Axiom Profiler](https://github.com/viperproject/axiom-profiler).

#![forbid(unsafe_code)]

/// Error management.
pub mod error;
/// Tokenization of Z3 logs.
mod lexer;
/// Main analyzer module.
pub mod model;
/// Parsing of Z3 logs.
pub mod parser;
/// Terms and data structures found in Z3 logs.
pub mod syntax;

pub use error::{Error, Result};
pub use model::{Model, ModelConfig};
