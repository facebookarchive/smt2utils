// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The `smt2patch` library provides the SMT2 "patching" functionalities and
//! configurations used by the binary tool `smt2patch`.

use smt2parser::{
    concrete::*,
    visitors::{CommandVisitor, TermVisitor},
};
use std::{
    collections::{HashMap, HashSet},
    io::Write,
    path::Path,
    str::FromStr,
};
use structopt::StructOpt;
use thiserror::Error;

/// Configuration for the SMT2 rewriting operations.
#[derive(Debug, Clone, StructOpt)]
pub struct RewriterConfig {
    #[structopt(long, parse(from_str = parse_clauses))]
    keep_only_clauses: Option<HashSet<String>>,

    #[structopt(long)]
    get_unsat_core: bool,

    #[structopt(long)]
    tag_quantifiers: bool,

    #[structopt(long, parse(try_from_str = try_parse_weights))]
    set_weights: Option<HashMap<String, usize>>,
}

fn parse_clauses(src: &str) -> HashSet<String> {
    let src = src.trim();
    let src = if src.starts_with('(') && src.ends_with(')') {
        &src[1..src.len() - 1].trim()
    } else {
        src
    };
    src.split(' ').map(String::from).collect()
}

fn try_parse_weights(src: &str) -> Result<HashMap<String, usize>, std::num::ParseIntError> {
    let src = src.trim();
    src.split(' ')
        .map(|s| {
            let mut items = s.splitn(2, '=');
            let key = items.next().unwrap();
            let value = items.next().unwrap_or("0").parse()?;
            Ok((key.to_string(), value))
        })
        .collect()
}

/// State of the SMT2 rewriter.
#[derive(Debug)]
pub struct Rewriter {
    config: RewriterConfig,
    discarded_options: HashSet<String>,
    builder: SyntaxBuilder,
    clause_count: usize,
    quantifier_count: usize,
}

const PRODUCE_UNSAT_CORES: &str = "produce-unsat-cores";
const CLAUSE: &str = "clause!";
const QUANT: &str = "quant!";

impl Rewriter {
    pub fn new(config: RewriterConfig, discarded_options: HashSet<String>) -> Self {
        Self {
            config,
            discarded_options,
            builder: SyntaxBuilder::default(),
            clause_count: 0,
            quantifier_count: 0,
        }
    }

    fn make_clause_name(&mut self, term: &Term) -> Symbol {
        let mut qid = String::new();
        if let Term::Forall { term, .. } = term {
            if let Some(s) = Self::get_quantifier_name(term) {
                qid = format!("!{}", s.0);
            }
        }
        let s = format!("{}{}{}", CLAUSE, self.clause_count, qid);
        self.clause_count += 1;
        Symbol(s)
    }

    fn make_quantifier_name(&mut self) -> Symbol {
        let s = format!("{}{}", QUANT, self.quantifier_count);
        self.quantifier_count += 1;
        Symbol(s)
    }

    fn get_clause_name(term: &Term) -> Option<&Symbol> {
        if let Some(AttributeValue::Symbol(s)) = Self::get_attribute(term, "named") {
            return Some(s);
        }
        None
    }

    fn get_quantifier_name(term: &Term) -> Option<&Symbol> {
        match Self::get_attribute(term, "qid") {
            Some(AttributeValue::Symbol(s)) => Some(s),
            _ => None,
        }
    }

    fn get_attribute<'a>(term: &'a Term, key: &str) -> Option<&'a AttributeValue> {
        match term {
            Term::Attributes { attributes, .. } => {
                for (k, v) in attributes {
                    if k.0 == key {
                        return Some(v);
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn set_attribute(mut term: Term, key: String, value: AttributeValue) -> Term {
        match &mut term {
            Term::Attributes { attributes, .. } => {
                for (k, v) in attributes.iter_mut() {
                    if k.0 == key {
                        *v = value;
                        return term;
                    }
                }
                attributes.push((Keyword(key), value));
                term
            }
            _ => Term::Attributes {
                term: Box::new(term),
                attributes: vec![(Keyword(key), value)],
            },
        }
    }
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("{0}")]
    Error(smt2parser::concrete::Error),
    #[error("Command was skipped")]
    SkipCommand,
}

impl std::convert::From<smt2parser::concrete::Error> for Error {
    fn from(e: smt2parser::concrete::Error) -> Self {
        Self::Error(e)
    }
}

impl smt2parser::rewriter::Rewriter for Rewriter {
    type V = SyntaxBuilder;
    type Error = Error;

    fn visitor(&mut self) -> &mut SyntaxBuilder {
        &mut self.builder
    }

    fn process_symbol(&mut self, symbol: Symbol) -> Result<Symbol, Error> {
        // Bump clause_count and quantifier_count when needed to avoid
        // clashes with user-provided symbols.
        if symbol.0.starts_with(CLAUSE) {
            if let Ok(i) = usize::from_str(&symbol.0[CLAUSE.len()..]) {
                self.clause_count = std::cmp::max(self.clause_count, i + 1);
            }
        } else if symbol.0.starts_with(QUANT) {
            if let Ok(i) = usize::from_str(&symbol.0[QUANT.len()..]) {
                self.clause_count = std::cmp::max(self.clause_count, i + 1);
            }
        }
        Ok(symbol)
    }

    fn visit_forall(&mut self, vars: Vec<(Symbol, Sort)>, term: Term) -> Result<Term, Error> {
        let name = Self::get_quantifier_name(&term)
            .cloned()
            .unwrap_or_else(|| self.make_quantifier_name());
        // Add name if needed.
        let term = if !self.config.tag_quantifiers {
            term
        } else {
            Self::set_attribute(
                term,
                "qid".to_string(),
                AttributeValue::Symbol(name.clone()),
            )
        };
        // Add weight if needed.
        let term = match &self.config.set_weights {
            None => term,
            Some(weights) => {
                let w = *weights.get(&name.0).unwrap_or(&0);
                Self::set_attribute(
                    term,
                    "weight".to_string(),
                    AttributeValue::Constant(Constant::Numeral(w.into())),
                )
            }
        };
        let value = self.visitor().visit_forall(vars, term)?;
        self.process_term(value)
    }

    fn visit_assert(&mut self, term: Term) -> Result<Command, Error> {
        let name = Self::get_clause_name(&term)
            .cloned()
            .unwrap_or_else(|| self.make_clause_name(&term));
        if let Some(list) = &self.config.keep_only_clauses {
            if !list.contains(&name.0) && !list.contains(&format!("|{}|", &name.0)) {
                // Discard clause.
                eprintln!("Discarding {}", name.0);
                return Err(Error::SkipCommand);
            }
        }
        let term = if self.config.get_unsat_core {
            Self::set_attribute(term, "named".to_string(), AttributeValue::Symbol(name))
        } else {
            term
        };
        let value = self.visitor().visit_assert(term)?;
        self.process_command(value)
    }

    fn visit_set_option(
        &mut self,
        keyword: Keyword,
        value: AttributeValue,
    ) -> Result<Command, Error> {
        if self.discarded_options.contains(&keyword.0) {
            return Err(Error::SkipCommand);
        }
        let value = self.visitor().visit_set_option(keyword, value)?;
        self.process_command(value)
    }

    fn visit_get_unsat_core(&mut self) -> Result<Command, Error> {
        if self.config.get_unsat_core {
            // Will be re-added in Patcher.
            return Err(Error::SkipCommand);
        }
        let value = self.visitor().visit_get_unsat_core()?;
        self.process_command(value)
    }
}

#[derive(Debug, Clone, StructOpt)]
pub struct PatcherConfig {
    #[structopt(flatten)]
    rewriter_config: RewriterConfig,
}

/// State of the SMT2 patcher.
#[derive(Debug)]
pub struct Patcher {
    config: PatcherConfig,
    script: Vec<Command>,
}

impl Patcher {
    pub fn new(config: PatcherConfig) -> Self {
        Self {
            config,
            script: Vec::new(),
        }
    }

    pub fn read(&mut self, path: &Path) -> std::io::Result<()> {
        let file = std::io::BufReader::new(std::fs::File::open(path)?);
        let mut discarded_options = HashSet::new();
        if self.config.rewriter_config.get_unsat_core {
            discarded_options.insert(PRODUCE_UNSAT_CORES.to_string());
        }
        let rewriter = Rewriter::new(self.config.rewriter_config.clone(), discarded_options);
        let mut stream =
            smt2parser::CommandStream::new(file, rewriter, path.to_str().map(String::from));
        for result in &mut stream {
            match result {
                Ok(command)
                    if self.config.rewriter_config.get_unsat_core
                        && command == Command::CheckSat =>
                {
                    self.script.push(command);
                    self.script.push(Command::GetUnsatCore);
                }
                Ok(command) => {
                    self.script.push(command);
                }
                Err(Error::SkipCommand) => {}
                Err(error) => {
                    panic!("{}", error);
                }
            }
        }
        Ok(())
    }

    pub fn write(&self, path: &Path) -> std::io::Result<()> {
        let mut file = std::fs::File::create(path)?;
        if self.config.rewriter_config.get_unsat_core {
            // TODO: repeat after resets
            writeln!(file, "(set-option :{} true)", PRODUCE_UNSAT_CORES)?;
        }
        for command in &self.script {
            writeln!(file, "{}", command)?;
        }
        Ok(())
    }
}
