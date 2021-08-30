// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    error::{Error, Position, RawError, RawResult},
    syntax::{Equality, Ident, Literal, MatchedTerm, QiKey, VarName},
};
use smt2parser::concrete::Symbol;

use std::collections::BTreeMap;

pub struct Lexer<R> {
    reader: R,
    path_name: Option<String>,
    current_offset: usize,
    current_line: usize,
    current_column: usize,
    ident_versions: BTreeMap<(Option<String>, Option<u64>), usize>,
    key_versions: BTreeMap<u64, usize>,
}

impl<R> Lexer<R>
where
    R: std::io::BufRead,
{
    pub fn new(path_name: Option<String>, reader: R) -> Self {
        Self {
            path_name,
            reader,
            current_offset: 0,
            current_line: 0,
            current_column: 0,
            ident_versions: BTreeMap::new(),
            key_versions: BTreeMap::new(),
        }
    }

    fn current_position(&self) -> Position {
        Position {
            path_name: self.path_name.clone(),
            line: self.current_line,
            column: self.current_column,
        }
    }

    pub fn make_error(&self, error: RawError) -> Error {
        Error {
            position: self.current_position(),
            error,
        }
    }

    fn consume_byte(&mut self) {
        if let Some(c) = self.peek_byte() {
            if *c == b'\n' {
                self.current_line += 1;
                self.current_column = 0;
            } else {
                self.current_column += 1;
            }
            self.current_offset += 1;
            self.reader.consume(1)
        }
    }

    fn read_byte(&mut self) -> Option<u8> {
        let c = self.peek_byte().cloned();
        self.consume_byte();
        c
    }

    #[inline]
    fn peek_bytes(&mut self) -> &[u8] {
        self.reader
            .fill_buf()
            .expect("Error while reading input stream")
    }

    fn peek_byte(&mut self) -> Option<&u8> {
        self.peek_bytes().get(0)
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

    fn read_token(&mut self, token: u8) -> RawResult<()> {
        match self.read_byte() {
            Some(c) if c == token => {
                self.skip_spaces();
                Ok(())
            }
            x => Err(RawError::UnexpectedChar(
                x.map(char::from),
                vec![token as char],
            )),
        }
    }

    /// Read an SMT2 symbol.
    fn read_symbol(&mut self) -> RawResult<Symbol> {
        let mut bytes = Vec::new();
        if let Some(b'|') = self.peek_byte() {
            self.consume_byte();
            while let Some(c) = self.peek_byte() {
                if *c == b'|' {
                    self.consume_byte();
                    self.skip_spaces();
                    let s = String::from_utf8(bytes).map_err(RawError::InvalidUtf8String)?;
                    return Ok(Symbol(s));
                }
                if *c == b'\n' {
                    return Err(RawError::UnexpectedChar(Some(*c as char), vec!['|']));
                }
                bytes.push(*c);
                self.consume_byte();
            }
            return Err(RawError::UnexpectedChar(None, vec!['|']));
        }
        // Normal case
        while let Some(c) = self.peek_byte() {
            let c = *c;
            if c == b' ' {
                self.consume_byte();
                self.skip_spaces();
                break;
            }
            if c == b'\n' || c == b';' || c == b'(' || c == b')' {
                break;
            }
            bytes.push(c);
            self.consume_byte();
        }
        let s = String::from_utf8(bytes).map_err(RawError::InvalidUtf8String)?;
        Ok(Symbol(s))
    }

    fn read_word(&mut self) -> RawResult<String> {
        let mut bytes = Vec::new();
        while let Some(c) = self.peek_byte() {
            let c = *c;
            if c == b' ' {
                self.consume_byte();
                self.skip_spaces();
                break;
            }
            if c == b'\n' || c == b'#' || c == b';' || c == b'(' || c == b')' {
                break;
            }
            bytes.push(c);
            self.consume_byte();
        }
        String::from_utf8(bytes).map_err(RawError::InvalidUtf8String)
    }

    pub(crate) fn read_string(&mut self) -> RawResult<String> {
        let mut bytes = Vec::new();
        while let Some(c) = self.peek_byte() {
            if *c == b' ' {
                self.consume_byte();
                self.skip_spaces();
                break;
            }
            if *c == b'\n' {
                break;
            }
            bytes.push(*c);
            self.consume_byte();
        }
        String::from_utf8(bytes).map_err(RawError::InvalidUtf8String)
    }

    pub(crate) fn read_integer(&mut self) -> RawResult<u64> {
        let word = self.read_word()?;
        word.parse().map_err(RawError::InvalidInteger)
    }

    pub(crate) fn read_optional_integer(&mut self) -> RawResult<Option<u64>> {
        match self.peek_byte() {
            Some(b';') => {
                self.consume_byte();
                self.skip_spaces();
                Ok(Some(self.read_integer()?))
            }
            _ => Ok(None),
        }
    }

    pub(crate) fn read_optional_ident(&mut self) -> RawResult<Option<Ident>> {
        match self.peek_byte() {
            Some(b'#') => Ok(Some(self.read_ident()?)),
            _ => Ok(None),
        }
    }

    pub(crate) fn read_end_of_line(&mut self) -> RawResult<()> {
        match self.peek_byte() {
            Some(b'\n') => {
                self.consume_byte();
                self.skip_spaces();
                Ok(())
            }
            c => Err(RawError::UnexpectedChar(
                c.cloned().map(char::from),
                vec!['\n'],
            )),
        }
    }

    pub(crate) fn read_line(&mut self) -> RawResult<String> {
        let mut bytes = Vec::new();
        while let Some(c) = self.peek_byte() {
            if *c == b'\n' {
                break;
            }
            bytes.push(*c);
            self.consume_byte();
        }
        String::from_utf8(bytes).map_err(RawError::InvalidUtf8String)
    }

    pub(crate) fn read_sequence<F, T>(&mut self, f: F) -> RawResult<Vec<T>>
    where
        F: Fn(&mut Self) -> RawResult<T>,
    {
        let mut items = Vec::new();
        while let Some(c) = self.peek_byte() {
            if *c == b';' {
                self.consume_byte();
                self.skip_spaces();
                break;
            }
            if *c == b'\n' {
                break;
            }
            let item = f(self)?;
            items.push(item);
        }
        Ok(items)
    }

    fn make_ident(&mut self, namespace: Option<String>, id: Option<u64>, fresh: bool) -> Ident {
        let key = (namespace, id);
        let version = if fresh {
            let e = self
                .ident_versions
                .entry(key.clone())
                .and_modify(|e| *e += 1)
                .or_insert(0);
            *e
        } else {
            self.ident_versions.get(&key).cloned().unwrap_or(0)
        };
        Ident {
            namespace: key.0,
            id: key.1,
            version,
        }
    }

    fn make_key(&mut self, key: u64, fresh: bool) -> QiKey {
        let version = if fresh {
            let e = self
                .key_versions
                .entry(key)
                .and_modify(|e| *e += 1)
                .or_insert(0);
            *e
        } else {
            self.key_versions.get(&key).cloned().unwrap_or(0)
        };
        QiKey { key, version }
    }

    fn read_ident_internal(&mut self, fresh: bool) -> RawResult<Ident> {
        let word1 = self.read_word()?;
        match self.read_byte() {
            Some(b'#') => (),
            x => {
                return Err(RawError::UnexpectedChar(x.map(char::from), vec!['#']));
            }
        }
        let word2 = self.read_word()?;
        if word1.is_empty() {
            let id = word2.parse().map_err(RawError::InvalidInteger)?;
            Ok(self.make_ident(None, Some(id), fresh))
        } else if word2.is_empty() {
            Ok(self.make_ident(Some(word1), None, fresh))
        } else {
            let id = word2.parse().map_err(RawError::InvalidInteger)?;
            Ok(self.make_ident(Some(word1), Some(id), fresh))
        }
    }

    pub(crate) fn read_ident(&mut self) -> RawResult<Ident> {
        self.read_ident_internal(false)
    }

    pub(crate) fn read_fresh_ident(&mut self) -> RawResult<Ident> {
        self.read_ident_internal(true)
    }

    pub(crate) fn read_idents(&mut self) -> RawResult<Vec<Ident>> {
        self.read_sequence(Self::read_ident)
    }

    fn read_key_internal(&mut self, fresh: bool) -> RawResult<QiKey> {
        let word = self.read_word()?;
        let x = u64::from_str_radix(word.trim_start_matches("0x"), 16)
            .map_err(|_| RawError::InvalidHexadecimal(word))?;
        Ok(self.make_key(x, fresh))
    }

    pub(crate) fn read_key(&mut self) -> RawResult<QiKey> {
        self.read_key_internal(false)
    }

    pub(crate) fn read_fresh_key(&mut self) -> RawResult<QiKey> {
        self.read_key_internal(true)
    }

    pub(crate) fn read_var_name(&mut self) -> RawResult<VarName> {
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
            x => Err(RawError::UnexpectedChar(
                x.cloned().map(char::from),
                vec![';', ')'],
            )),
        }
    }

    pub(crate) fn read_var_names(&mut self) -> RawResult<Vec<VarName>> {
        self.read_sequence(Self::read_var_name)
    }

    pub(crate) fn read_matched_term(&mut self) -> RawResult<MatchedTerm> {
        match self.peek_byte() {
            Some(b'(') => {
                self.consume_byte();
                self.skip_spaces();
                let t1 = self.read_ident()?;
                let t2 = self.read_ident()?;
                self.read_token(b')')?;
                Ok(MatchedTerm::Equality(t1, t2))
            }
            _ => Ok(MatchedTerm::Trigger(self.read_ident()?)),
        }
    }

    pub(crate) fn read_matched_terms(&mut self) -> RawResult<Vec<MatchedTerm>> {
        self.read_sequence(Self::read_matched_term)
    }

    pub(crate) fn read_equality(&mut self) -> RawResult<Equality> {
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
            "ax" => {
                self.read_token(b';')?;
                let t = self.read_ident()?;
                Ok(Equality::Axiom(t))
            }
            "unknown" => {
                self.read_token(b';')?;
                let t = self.read_ident()?;
                Ok(Equality::Unknown(t))
            }
            s => Err(RawError::UnexpectedWord(
                s.to_string(),
                vec!["root", "lit", "cg", "th", "ax", "unknown"],
            )),
        }
    }

    pub(crate) fn read_literal(&mut self) -> RawResult<Literal> {
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
                    s => Err(RawError::UnexpectedWord(s.to_string(), vec!["not"])),
                }
            }
            Some(b'0'..=b'9') | Some(b'#') => {
                let id = self.read_ident()?;
                Ok(Literal { id, sign: true })
            }
            _ => match self.read_word()?.as_ref() {
                "true" => Ok(Literal {
                    id: Ident::default(),
                    sign: true,
                }),
                "false" => Ok(Literal {
                    id: Ident::default(),
                    sign: false,
                }),
                s => Err(RawError::UnexpectedWord(
                    s.to_string(),
                    vec!["true", "false"],
                )),
            },
        }
    }

    pub(crate) fn read_literals(&mut self) -> RawResult<Vec<Literal>> {
        self.read_sequence(Self::read_literal)
    }
}

#[test]
fn test_ident_from_str() {
    use std::str::FromStr;
    assert_eq!(
        Ident::from_str("#123").unwrap(),
        Ident {
            namespace: None,
            id: Some(123),
            version: 0,
        }
    );
    assert_eq!(
        Ident::from_str("foo#123").unwrap(),
        Ident {
            namespace: Some("foo".to_string()),
            id: Some(123),
            version: 0,
        }
    );
    assert_eq!(
        Ident::from_str("foo#").unwrap(),
        Ident {
            namespace: Some("foo".to_string()),
            id: None,
            version: 0,
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
