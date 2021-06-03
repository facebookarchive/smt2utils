// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! This crate provides a generic parser for SMT2 commands, as specified by the
//! [SMT-LIB-2 standard](http://smtlib.cs.uiowa.edu/language.shtml).
//!
//! Commands are parsed and immediately visited by a user-provided
//! implementation of the trait [`visitors::Smt2Visitor`].
//!
//! To obtain concrete syntax values, use [`concrete::SyntaxBuilder`] as a
//! visitor:
//! ```
//! # use smt2parser::{CommandStream, concrete};
//! let input = b"(echo \"Hello world!\")(exit)";
//! let mut stream = CommandStream::new(
//!     &input[..],
//!     concrete::SyntaxBuilder,
//! );
//! let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
//! assert!(matches!(commands[..], [
//!     concrete::Command::Echo {..},
//!     concrete::Command::Exit,
//! ]));
//! assert_eq!(commands[0].to_string(), "(echo \"Hello world!\")");
//! ```

#![forbid(unsafe_code)]

#[macro_use]
extern crate pomelo;

pub mod concrete;
mod lexer;
mod parser;
pub mod renaming;
pub mod rewriter;
pub mod stats;
pub mod visitors;

/// SMT2 numeral values.
pub type Numeral = num::bigint::BigUint;
/// SMT2 decimal values.
pub type Decimal = num::rational::BigRational;
/// A base-16 digit.
pub type Nibble = u8;
/// SMT2 hexadecimal values.
pub type Hexadecimal = Vec<Nibble>;
/// SMT2 binary values.
pub type Binary = Vec<bool>;

/// A position in the input.
pub use lexer::Position;

/// Parse the input data and return a stream of interpreted SMT2 commands
pub struct CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::Smt2Visitor,
{
    lexer: lexer::Lexer<R>,
    visitor: T,
}

impl<R, T> CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::Smt2Visitor,
{
    pub fn new(reader: R, visitor: T) -> Self {
        Self {
            lexer: lexer::Lexer::new(reader),
            visitor,
        }
    }

    pub fn visitor(&self) -> &T {
        &self.visitor
    }

    pub fn visitor_mut(&mut self) -> &mut T {
        &mut self.visitor
    }

    pub fn into_visitor(self) -> T {
        self.visitor
    }
}

impl<R, T> Iterator for CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::Smt2Visitor,
{
    type Item = Result<T::Command, Position>;

    fn next(&mut self) -> Option<Result<T::Command, Position>> {
        let mut parser = parser::Parser::new(&mut self.visitor);
        let mut unmatched_paren = 0;
        while let Some(token) = self.lexer.next() {
            match &token {
                parser::Token::LeftParen => unmatched_paren += 1,
                parser::Token::RightParen => {
                    if unmatched_paren > 0 {
                        unmatched_paren -= 1;
                    }
                }
                _ => (),
            }
            if let Err(()) = parser.parse(token) {
                return Some(Err(self.lexer.current_position()));
            }
            if unmatched_paren == 0 {
                return match parser.end_of_input() {
                    Ok((command, _)) => Some(Ok(command)),
                    Err(()) => Some(Err(self.lexer.current_position())),
                };
            }
        }
        // TODO: lexing error.
        None
    }
}
