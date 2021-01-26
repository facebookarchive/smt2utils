// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

#[macro_use]
extern crate pomelo;

pub mod concrete;
mod lexer;
mod parser;
pub mod stats;
pub mod visitors;

pub type Numeral = num::bigint::BigUint;
pub type Decimal = num::rational::BigRational;
pub type Nibble = u8;
pub type Hexadecimal = Vec<Nibble>;
pub type Binary = Vec<bool>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Position {
    line: usize,
    column: usize,
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

pub struct CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::SMT2Visitor,
{
    lexer: lexer::Lexer<R>,
    visitor: T,
}

impl<R, T> CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::SMT2Visitor,
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
    T: visitors::SMT2Visitor,
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

use concrete::{Constant, SExpr, Symbol};

pub fn parse_simple_attribute_value(
    input: &str,
) -> Option<visitors::AttributeValue<Constant, Symbol, SExpr>> {
    let token = lexer::Lexer::new(input.as_bytes()).next()?;
    match token {
        parser::Token::Numeral(x) => Some(visitors::AttributeValue::Constant(Constant::Numeral(x))),
        parser::Token::Decimal(x) => Some(visitors::AttributeValue::Constant(Constant::Decimal(x))),
        parser::Token::String(x) => Some(visitors::AttributeValue::Constant(Constant::String(x))),
        parser::Token::Binary(x) => Some(visitors::AttributeValue::Constant(Constant::Binary(x))),
        parser::Token::Hexadecimal(x) => {
            Some(visitors::AttributeValue::Constant(Constant::Hexadecimal(x)))
        }
        parser::Token::Symbol(x) => Some(visitors::AttributeValue::Symbol(Symbol(x))),
        _ => None,
    }
}
