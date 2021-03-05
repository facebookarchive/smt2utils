// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::syntax::{Equality, Ident};

/// Raw error cases.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum RawError {
    // Lexer
    InvalidUtf8String(std::string::FromUtf8Error),
    InvalidInteger(std::num::ParseIntError),
    InvalidHexadecimal(String),
    UnexpectedChar(Option<u8>, Vec<u8>),
    UnexpectedWord(String, Vec<&'static str>),
    // Parser
    MissingIdentifier,
    UndefinedIdent(Ident),
    UnexpectedProofTerm(Ident),
    MissingProof(Ident),
    CannotAttachMeaning(Ident),
    CannotAttachVarNames(Ident),
    UnknownCommand(String),
    InvalidEndOfInstance,
    InvalidInstanceKey,
    InvalidMatchKey,
    InvalidEnodeGeneration,
    CannotAttachEnode(usize, usize),
    CannotProcessEquality(Ident, Equality),
    CannotCheckEquality(Ident, Ident),
}

/// Record a position in the input stream.
#[derive(Clone, Eq, PartialEq)]
pub struct Position {
    /// Optional path name for the input stream.
    pub path_name: Option<String>,
    /// Line number in the input stream.
    pub line: usize,
    /// Column number in the line.
    pub column: usize,
}

/// An error together with a position where the error occurred.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Error {
    pub position: Position,
    pub error: RawError,
}

/// Result type based on `RawError`.
pub type RawResult<T> = std::result::Result<T, RawError>;

/// Result type based on `Error`.
pub type Result<T> = std::result::Result<T, Error>;

impl std::fmt::Debug for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let file = match &self.path_name {
            Some(p) => format!("{}:", p),
            None => String::new(),
        };
        write!(f, "{}{}:{}", file, self.line + 1, self.column + 1)
    }
}

impl From<Error> for RawError {
    fn from(value: Error) -> Self {
        value.error
    }
}
