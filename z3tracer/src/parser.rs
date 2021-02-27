// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::error::{Error, Result};
use crate::syntax::{Equality, Ident, Literal, MatchedTerm, VarName};
use smt2parser::concrete::Symbol;

pub(crate) struct LineParser<'a> {
    content: &'a [u8],
}

impl<'a> LineParser<'a> {
    pub(crate) fn new(line: &'a [u8]) -> Self {
        Self { content: &line[..] }
    }

    #[inline]
    fn consume_byte(&mut self) {
        self.content = &self.content[1..];
    }

    fn read_byte(&mut self) -> Option<u8> {
        let c = *self.peek_byte()?;
        self.consume_byte();
        Some(c)
    }

    #[inline]
    fn peek_byte(&mut self) -> Option<&u8> {
        self.content.get(0)
    }

    fn skip_space(&mut self) -> bool {
        match self.peek_byte() {
            Some(b' ') => {
                self.consume_byte();
                true
            }
            _ => false,
        }
    }

    fn skip_spaces(&mut self) {
        while self.skip_space() {}
    }

    fn read_token(&mut self, token: u8) -> Result<()> {
        match self.read_byte() {
            Some(c) if c == token => {
                self.skip_spaces();
                Ok(())
            }
            x => Err(Error::UnexpectedToken(x, token)),
        }
    }

    pub(crate) fn check_end_of_line(&mut self) -> Result<()> {
        match self.peek_byte() {
            None => Ok(()),
            _ => Err(Error::UnexpectedInput),
        }
    }

    /// Read an SMT2 symbol.
    fn read_symbol(&mut self) -> Result<Symbol> {
        let mut bytes = Vec::new();
        if let Some(b'|') = self.peek_byte() {
            self.consume_byte();
            while let Some(c) = self.peek_byte() {
                if *c == b'|' {
                    self.consume_byte();
                    break;
                }
                bytes.push(*c);
                self.consume_byte();
            }
            self.skip_spaces();
            let s = String::from_utf8(bytes).map_err(|_| Error::InvalidUtf8String)?;
            return Ok(Symbol(s));
        }
        // Normal case
        while let Some(c) = self.peek_byte() {
            let c = *c;
            if c == b' ' {
                self.consume_byte();
                self.skip_spaces();
                break;
            }
            if c == b'#' || c == b';' || c == b'(' || c == b')' {
                break;
            }
            bytes.push(c);
            self.consume_byte();
        }
        let s = String::from_utf8(bytes).map_err(|_| Error::InvalidUtf8String)?;
        Ok(Symbol(s))
    }

    fn read_word(&mut self) -> Result<String> {
        let mut bytes = Vec::new();
        while let Some(c) = self.peek_byte() {
            let c = *c;
            if c == b' ' {
                self.consume_byte();
                self.skip_spaces();
                break;
            }
            if c == b'#' || c == b';' || c == b'(' || c == b')' {
                break;
            }
            bytes.push(c);
            self.consume_byte();
        }
        String::from_utf8(bytes).map_err(|_| Error::InvalidUtf8String)
    }

    pub(crate) fn read_string(&mut self) -> Result<String> {
        let mut bytes = Vec::new();
        while let Some(c) = self.peek_byte() {
            if *c == b' ' {
                self.consume_byte();
                self.skip_spaces();
                break;
            }
            bytes.push(*c);
            self.consume_byte();
        }
        String::from_utf8(bytes).map_err(|_| Error::InvalidUtf8String)
    }

    pub(crate) fn read_key(&mut self) -> Result<u64> {
        let word = self.read_word()?;
        u64::from_str_radix(word.trim_start_matches("0x"), 16)
            .map_err(|_| Error::InvalidHexadecimal(word))
    }

    pub(crate) fn read_integer(&mut self) -> Result<u64> {
        let word = self.read_word()?;
        word.parse().map_err(|_| Error::InvalidInteger(word))
    }

    pub(crate) fn read_optional_integer(&mut self) -> Result<Option<u64>> {
        match self.peek_byte() {
            Some(b';') => {
                self.consume_byte();
                self.skip_spaces();
                Ok(Some(self.read_integer()?))
            }
            _ => Ok(None),
        }
    }

    pub(crate) fn read_content(&mut self) -> Result<String> {
        Ok(String::from_utf8(self.content.to_vec()).map_err(|_| Error::InvalidUtf8String)?)
    }

    pub(crate) fn read_sequence<F, T>(&mut self, f: F) -> Result<Vec<T>>
    where
        F: Fn(&mut Self) -> Result<T>,
    {
        let mut items = Vec::new();
        while let Some(c) = self.peek_byte() {
            if *c == b';' {
                self.consume_byte();
                self.skip_spaces();
                break;
            }
            let item = f(self)?;
            items.push(item);
        }
        Ok(items)
    }

    pub(crate) fn read_ident(&mut self) -> Result<Ident> {
        let word1 = self.read_word()?;
        match self.peek_byte() {
            Some(b'#') => {
                self.consume_byte();
                let word2 = self.read_word()?;
                if word2.is_empty() {
                    Ok(Ident {
                        namespace: Some(word1),
                        id: None,
                    })
                } else {
                    let id = word2.parse().map_err(|_| Error::InvalidIdent(word2))?;
                    Ok(Ident {
                        namespace: Some(word1),
                        id: Some(id),
                    })
                }
            }
            _ => {
                let id = word1.parse().map_err(|_| Error::InvalidIdent(word1))?;
                Ok(Ident {
                    namespace: None,
                    id: Some(id),
                })
            }
        }
    }

    pub(crate) fn read_idents(&mut self) -> Result<Vec<Ident>> {
        self.read_sequence(Self::read_ident)
    }

    pub(crate) fn read_var_name(&mut self) -> Result<VarName> {
        self.read_token(b'(')?;
        let name = self.read_symbol()?;
        match self.peek_byte() {
            Some(b';') => {
                self.consume_byte();
                self.skip_spaces();
                let sort = self.read_symbol()?;
                self.read_token(b')')?;
                Ok(VarName { name, sort })
            }
            Some(b')') => {
                self.consume_byte();
                self.skip_spaces();
                let sort = Symbol("".to_string());
                Ok(VarName { name, sort })
            }
            _ => Err(Error::InvalidVarName),
        }
    }

    pub(crate) fn read_var_names(&mut self) -> Result<Vec<VarName>> {
        self.read_sequence(Self::read_var_name)
    }

    pub(crate) fn read_matched_term(&mut self) -> Result<MatchedTerm> {
        match self.peek_byte() {
            Some(b'(') => {
                self.consume_byte();
                self.skip_spaces();
                let t1 = self.read_ident()?;
                let t2 = self.read_ident()?;
                self.read_token(b')')?;
                Ok(MatchedTerm::SubPattern(t1, t2))
            }
            _ => Ok(MatchedTerm::RootPattern(self.read_ident()?)),
        }
    }

    pub(crate) fn read_matched_terms(&mut self) -> Result<Vec<MatchedTerm>> {
        self.read_sequence(Self::read_matched_term)
    }

    pub(crate) fn read_equality(&mut self) -> Result<Equality> {
        match self.read_string()?.as_ref() {
            "root" => Ok(Equality::Root),
            "lit" => {
                let t1 = self.read_ident()?;
                self.read_token(b';')?;
                let t2 = self.read_ident()?;
                Ok(Equality::Literal(t1, t2))
            }
            "cg" => {
                let terms = self.read_sequence(|line| {
                    line.read_token(b'(')?;
                    let t1 = line.read_ident()?;
                    let t2 = line.read_ident()?;
                    line.read_token(b')')?;
                    Ok((t1, t2))
                })?;
                let t = self.read_ident()?;
                Ok(Equality::Congruence(terms, t))
            }
            "th" => {
                let solver = self.read_string()?;
                self.read_token(b';')?;
                let t = self.read_ident()?;
                Ok(Equality::Theory(solver, t))
            }
            s => Err(Error::InvalidEquality(s.to_string())),
        }
    }

    pub(crate) fn read_literal(&mut self) -> Result<Literal> {
        match self.peek_byte() {
            Some(b'(') => {
                self.consume_byte();
                self.skip_spaces();
                match self.read_string()?.as_ref() {
                    "not" => {
                        let id = self.read_ident()?;
                        self.read_token(b')')?;
                        Ok(Literal { id, sign: false })
                    }
                    _ => Err(Error::InvalidLiteral),
                }
            }
            _ => {
                match self.read_ident() {
                    Ok(id) => Ok(Literal { id, sign: true }),
                    // Z3 sometimes output "true" and "false" literals
                    Err(Error::InvalidIdent(s)) if matches!(s.as_ref(), "true") => Ok(Literal {
                        id: Ident::default(),
                        sign: true,
                    }),
                    Err(Error::InvalidIdent(s)) if matches!(s.as_ref(), "false") => Ok(Literal {
                        id: Ident::default(),
                        sign: false,
                    }),
                    Err(e) => Err(e),
                }
            }
        }
    }

    pub(crate) fn read_literals(&mut self) -> Result<Vec<Literal>> {
        self.read_sequence(Self::read_literal)
    }
}

#[cfg(test)]
impl std::str::FromStr for Ident {
    type Err = Error;

    fn from_str(value: &str) -> Result<Self> {
        let mut line = LineParser::new(value.as_ref());
        line.read_ident()
    }
}

#[cfg(test)]
impl std::str::FromStr for VarName {
    type Err = Error;

    fn from_str(value: &str) -> Result<Self> {
        let mut line = LineParser::new(value.as_ref());
        line.read_var_name()
    }
}

#[test]
fn test_ident_from_str() {
    use std::str::FromStr;
    assert_eq!(
        Ident::from_str("123").unwrap(),
        Ident {
            namespace: None,
            id: Some(123)
        }
    );
    assert_eq!(
        Ident::from_str("foo#123").unwrap(),
        Ident {
            namespace: Some("foo".to_string()),
            id: Some(123)
        }
    );
    assert_eq!(
        Ident::from_str("foo#").unwrap(),
        Ident {
            namespace: Some("foo".to_string()),
            id: None
        }
    );
}

#[test]
fn test_var_name_from_str() {
    use std::str::FromStr;
    assert_eq!(
        VarName::from_str("(a;b)").unwrap(),
        VarName {
            name: Symbol("a".to_string()),
            sort: Symbol("b".to_string()),
        }
    );
    assert_eq!(
        VarName::from_str("(|a | ; b) ").unwrap(),
        VarName {
            name: Symbol("a ".to_string()),
            sort: Symbol("b".to_string()),
        }
    );
    assert_eq!(
        VarName::from_str("(|a| ; |b|)").unwrap(),
        VarName {
            name: Symbol("a".to_string()),
            sort: Symbol("b".to_string()),
        }
    );
}
