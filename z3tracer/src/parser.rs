// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use structopt::StructOpt;

use crate::{
    error::{RawError, RawResult, Result},
    lexer::Lexer,
    syntax::{Equality, Ident, Literal, Meaning, QiFrame, QiInstance, QiKey, Term, VarName},
};

// https://github.com/TeXitoi/structopt/issues/333
#[cfg_attr(not(doc), allow(missing_docs))]
#[cfg_attr(doc, doc = "Configuration for the parsing of Z3 traces.")]
#[derive(Debug, Default, Clone, StructOpt)]
pub struct ParserConfig {
    /// Whether to ignore lines which don't start with '['.
    #[structopt(long)]
    pub ignore_invalid_lines: bool,
    /// Whether to skip the check for unsupported Z3 version.
    #[structopt(long)]
    pub skip_z3_version_check: bool,
}

/// Parser for Z3 traces.
pub struct Parser<R, S> {
    config: ParserConfig,
    lexer: Lexer<R>,
    state: S,
}

/// Actions taken when visiting Z3 logs.
pub trait LogVisitor {
    fn add_term(&mut self, id: Ident, term: Term) -> RawResult<()>;

    fn add_instantiation(&mut self, key: QiKey, frame: QiFrame) -> RawResult<()>;

    fn start_instance(&mut self, key: QiKey, instance: QiInstance) -> RawResult<()>;

    fn end_instance(&mut self) -> RawResult<()>;

    fn add_equality(&mut self, id: Ident, eq: Equality) -> RawResult<()>;

    fn attach_meaning(&mut self, id: Ident, meaning: Meaning) -> RawResult<()>;

    fn attach_var_names(&mut self, id: Ident, names: Vec<VarName>) -> RawResult<()>;

    fn attach_enode(&mut self, id: Ident, generation: u64) -> RawResult<()>;

    fn tool_version(&mut self, s1: String, s2: String) -> RawResult<()>;

    fn begin_check(&mut self, i: u64) -> RawResult<()>;

    fn assign(&mut self, lit: Literal, s: String) -> RawResult<()>;

    fn conflict(&mut self, lits: Vec<Literal>, s: String) -> RawResult<()>;

    fn push(&mut self, i: u64) -> RawResult<()>;

    fn pop(&mut self, i: u64, j: u64) -> RawResult<()>;

    fn resolve_lit(&mut self, i: u64, lit: Literal) -> RawResult<()>;

    fn resolve_process(&mut self, lit: Literal) -> RawResult<()>;
}

impl<R, S> Parser<R, S> {
    pub fn new(config: ParserConfig, lexer: Lexer<R>, state: S) -> Self {
        Self {
            config,
            lexer,
            state,
        }
    }

    pub fn state(&self) -> &S {
        &self.state
    }

    pub fn into_state(self) -> S {
        self.state
    }
}

impl<R, S> Parser<R, S>
where
    R: std::io::BufRead,
    S: LogVisitor,
{
    /// Parse the input.
    pub fn parse(&mut self) -> Result<()> {
        while self.parse_line().map_err(|e| self.lexer.make_error(e))? {}
        Ok(())
    }

    /// Parse one line of the input.
    fn parse_line(&mut self) -> RawResult<bool> {
        let lexer = &mut self.lexer;
        let state = &mut self.state;
        match lexer.read_string().unwrap().as_ref() {
            "[mk-app]" => {
                let id = lexer.read_fresh_ident()?;
                let name = lexer.read_string()?;
                let args = lexer.read_idents()?;
                let term = Term::App {
                    name,
                    args,
                    meaning: None,
                };
                state.add_term(id, term)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[mk-var]" => {
                let id = lexer.read_fresh_ident()?;
                let index = lexer.read_integer()?;
                let term = Term::Var { index };
                state.add_term(id, term)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[mk-quant]" => {
                let id = lexer.read_fresh_ident()?;
                let name = lexer.read_string()?;
                let params = lexer.read_integer()? as usize;
                let mut triggers = lexer.read_idents()?;
                let body = triggers.pop().ok_or(RawError::MissingIdentifier)?;
                let term = Term::Quant {
                    name,
                    params,
                    triggers,
                    body,
                    var_names: None,
                };
                state.add_term(id, term)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[mk-lambda]" => {
                let id = lexer.read_fresh_ident()?;
                let name = lexer.read_string()?;
                let params = lexer.read_integer()?;
                let mut triggers = lexer.read_idents()?;
                let body = triggers.pop().ok_or(RawError::MissingIdentifier)?;
                let term = Term::Lambda {
                    name,
                    params,
                    triggers,
                    body,
                };
                state.add_term(id, term)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[mk-proof]" => {
                let id = lexer.read_fresh_ident()?;
                let name = lexer.read_string()?;
                let mut args = lexer.read_idents()?;
                let property = args.pop().ok_or(RawError::MissingIdentifier)?;
                let term = Term::Proof {
                    name,
                    args,
                    property,
                };
                state.add_term(id, term)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[attach-meaning]" => {
                let id = lexer.read_ident()?;
                let theory = lexer.read_string()?;
                let sexp = lexer.read_line()?;
                let meaning = Meaning { theory, sexp };
                state.attach_meaning(id, meaning)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[attach-var-names]" => {
                let id = lexer.read_ident()?;
                let names = lexer.read_var_names()?;
                state.attach_var_names(id, names)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[inst-discovered]" => {
                let method = lexer.read_string()?;
                let key = lexer.read_fresh_key()?;
                let quantifier = lexer.read_ident()?;
                let terms = lexer.read_idents()?;
                let blame = lexer.read_idents()?;
                let frame = QiFrame::Discovered {
                    method,
                    quantifier,
                    terms,
                    blame,
                };
                state.add_instantiation(key, frame)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[new-match]" => {
                let key = lexer.read_fresh_key()?;
                let quantifier = lexer.read_ident()?;
                let trigger = lexer.read_ident()?;
                let terms = lexer.read_idents()?;
                let used = lexer.read_matched_terms()?;
                let frame = QiFrame::NewMatch {
                    quantifier,
                    trigger,
                    terms,
                    used,
                };
                state.add_instantiation(key, frame)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[eq-expl]" => {
                let id = lexer.read_ident()?;
                let eq = lexer.read_equality()?;
                state.add_equality(id, eq)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[instance]" => {
                let key = lexer.read_key()?;
                let term = lexer.read_optional_ident()?;
                let generation = lexer.read_optional_integer()?;
                let instance = QiInstance {
                    generation,
                    term,
                    enodes: Vec::new(),
                };
                state.start_instance(key, instance)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[attach-enode]" => {
                let id = lexer.read_ident()?;
                let generation = lexer.read_integer()?;
                state.attach_enode(id, generation)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[end-of-instance]" => {
                state.end_instance()?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[tool-version]" => {
                let s1 = lexer.read_string()?;
                let s2 = lexer.read_string()?;
                if !self.config.skip_z3_version_check {
                    RawError::check_that_tool_version_is_supported(&s1, &s2)?;
                }
                state.tool_version(s1, s2)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[begin-check]" => {
                let i = lexer.read_integer()?;
                state.begin_check(i)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[assign]" => {
                let lit = lexer.read_literal()?;
                let s = lexer.read_line()?;
                state.assign(lit, s)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[conflict]" => {
                let lits = lexer.read_literals()?;
                let s = lexer.read_line()?;
                state.conflict(lits, s)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[push]" => {
                let i = lexer.read_integer()?;
                state.push(i)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[pop]" => {
                let i = lexer.read_integer()?;
                let j = lexer.read_integer()?;
                state.pop(i, j)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[resolve-lit]" => {
                let i = lexer.read_integer()?;
                let lit = lexer.read_literal()?;
                state.resolve_lit(i, lit)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[resolve-process]" => {
                let lit = lexer.read_literal()?;
                state.resolve_process(lit)?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            "[eof]" => {
                lexer.read_end_of_line()?;
                Ok(false)
            }
            s if self.config.ignore_invalid_lines && !s.starts_with('[') => {
                // Ignore lines not starting with '['
                lexer.read_line()?;
                lexer.read_end_of_line()?;
                Ok(true)
            }
            s => Err(RawError::UnknownCommand(s.to_string())),
        }
    }
}
