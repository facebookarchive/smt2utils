// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::syntax::{Equality, Ident};

/// Raw error cases.
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum RawError {
    // Lexer
    #[error("Invalid UTF8 string {0}")]
    InvalidUtf8String(std::string::FromUtf8Error),
    #[error("Invalid integer {0}")]
    InvalidInteger(std::num::ParseIntError),
    #[error("Invalid hexadecimal string {0}")]
    InvalidHexadecimal(String),
    #[error("Unexpected char {0:?} {1:?}")]
    UnexpectedChar(Option<u8>, Vec<u8>),
    #[error("Unexpected word {0} {1:?}")]
    UnexpectedWord(String, Vec<&'static str>),
    // Parser
    #[error("Missing identifier")]
    MissingIdentifier,
    #[error("Undefined identifier {0:?}")]
    UndefinedIdent(Ident),
    #[error("Unexpected proof term {0:?}")]
    UnexpectedProofTerm(Ident),
    #[error("Missing proof {0:?}")]
    MissingProof(Ident),
    #[error("Cannot attach meaning {0:?}")]
    CannotAttachMeaning(Ident),
    #[error("Cannot attach var name {0:?}")]
    CannotAttachVarNames(Ident),
    #[error("Unknown command {0}")]
    UnknownCommand(String),
    #[error("Invalid end of instance")]
    InvalidEndOfInstance,
    #[error("Invalid instance key")]
    InvalidInstanceKey,
    #[error("Invalid match key")]
    InvalidMatchKey,
    #[error("Invalid enode generation")]
    InvalidEnodeGeneration,
    #[error("Cannot enode {0} {1}")]
    CannotAttachEnode(usize, usize),
    #[error("Cannot process equality {0:?} {1:?}")]
    CannotProcessEquality(Ident, Equality),
    #[error("Cannot check equality {0:?} {1:?}")]
    CannotCheckEquality(Ident, Ident),
}

/// Record a position in the input stream.
#[derive(Clone, Eq, PartialEq, thiserror::Error)]
#[error("{}{}:{}", match &.path_name { Some(p) => format!("{}:", p), None => String::new() }, .line + 1, .column + 1)]
pub struct Position {
    /// Optional path name for the input stream.
    pub path_name: Option<String>,
    /// Line number in the input stream.
    pub line: usize,
    /// Column number in the line.
    pub column: usize,
}

/// An error together with a position where the error occurred.
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
#[error("{position}: {error}")]
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
