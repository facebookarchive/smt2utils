// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::events::Ident;

#[derive(Debug)]
pub enum Error {
    // Tokens
    InvalidUtf8String,
    InvalidIdent(String),
    InvalidInteger(String),
    InvalidVarName,
    InvalidHexadecimal(String),
    UnexpectedToken(Option<u8>, u8),
    InvalidEquality(String),
    // Parsing
    UndefinedIdent(Ident),
    CannotOverrideIdent(Ident),
    CannotAttachMeaning(Ident),
    CannotAttachVarNames(Ident),
    UnknownCommand,
    UnexpectedInput,
    InvalidEndOfInstance,
    InvalidMatchKey,
    InvalidLiteral,
    MissingBody,
    InvalidEnodeGeneration,
    CannotAttachEnode(usize, usize),
}

pub type Result<T> = std::result::Result<T, Error>;
