// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::syntax::{Equality, Ident};

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum RawError {
    // Lexer
    InvalidUtf8String(std::string::FromUtf8Error),
    InvalidInteger(std::num::ParseIntError),
    InvalidHexadecimal(String),
    UnexpectedChar(Option<u8>, Vec<u8>),
    UnexpectedWord(String, Vec<&'static str>),
    // Parser
    UndefinedIdent(Ident),
    CannotAttachMeaning(Ident),
    CannotAttachVarNames(Ident),
    UnknownCommand(String),
    InvalidEndOfInstance,
    InvalidInstanceKey,
    InvalidMatchKey,
    MissingBody,
    InvalidEnodeGeneration,
    CannotAttachEnode(usize, usize),
    CannotProcessEquality(Ident, Equality),
    CannotCheckEquality(Ident, Ident),
}

/// Record a position in the input stream.
#[derive(Clone, Eq, PartialEq)]
pub struct Position {
    pub path_name: Option<String>,
    pub line: usize,
    pub column: usize,
}

/// Similar to `RawError` but includes a position where the error occurred.
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
