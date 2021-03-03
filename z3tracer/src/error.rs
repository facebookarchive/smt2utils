// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::syntax::{Equality, Ident};

#[derive(Debug)]
pub enum Error {
    EndOfInput,
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

pub type Result<T> = std::result::Result<T, Error>;

/// Record a position in the input stream.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

impl Position {
    pub fn new(line: usize, column: usize) -> Self {
        Self { line, column }
    }

    pub fn location_in_file(&self, path: &std::path::PathBuf) -> String {
        format!(
            "{}:{}:{}",
            path.to_string_lossy(),
            self.line + 1,
            self.column + 1
        )
    }
}
