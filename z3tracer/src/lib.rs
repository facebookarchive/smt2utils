// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! This crate provides an experimental parser for Z3 tracing logs obtained by passing
//! `trace=true proof=true`.
//!
//! More information about Z3 tracing logs can be found in the documentation of the
//! project [Axiom Profiler](https://github.com/viperproject/axiom-profiler).

#![forbid(unsafe_code)]

use smt2parser::concrete::Symbol;
use std::collections::{BTreeMap, BTreeSet};
use structopt::StructOpt;

pub mod error;
pub mod parser;
pub mod syntax;

use error::{Error, Result};
use parser::LineParser;
use syntax::{
    Equality, Ident, MatchedTerm, Meaning, QuantInstantiation, QuantInstantiationData,
    QuantInstantiationKind, Term, Visitor,
};

/// Configuration for the logging of quantifier instantiations.
#[derive(Debug, Clone, StructOpt)]
pub struct LogConfig {
    /// Whether to display variable instantiations.
    #[structopt(long)]
    with_variables: bool,

    /// Whether to display triggers.
    #[structopt(long)]
    with_triggers: bool,

    /// Whether to display 'used terms'
    #[structopt(long)]
    with_used_terms: bool,
}

#[derive(Default, Debug)]
pub struct Model {
    // Terms indexed by identifier.
    terms: BTreeMap<Ident, Term>,
    // Quantifier instantiations indexed by (hexadecimal) key.
    instantiations: BTreeMap<u64, QuantInstantiation>,
    // Equality reasoning indexed by target term identifier.
    equalities: BTreeMap<Ident, Equality>,
    // Track if a term depends on "enodes" produced by quantifier instantiations.
    qi_dependencies: BTreeMap<Ident, Vec<u64>>,
    // Stack of current quantifier instances.
    current_instances: Vec<(u64, QuantInstantiationData)>,
}

impl Model {
    /// All terms in the model.
    pub fn terms(&self) -> &BTreeMap<Ident, Term> {
        &self.terms
    }

    /// All instantiations in the model.
    pub fn instantiations(&self) -> &BTreeMap<u64, QuantInstantiation> {
        &self.instantiations
    }

    /// All equality steps in the model.
    pub fn equalities(&self) -> &BTreeMap<Ident, Equality> {
        &self.equalities
    }

    /// Parse the given input line.
    pub fn process_line(&mut self, bytes: &[u8]) -> Result<Option<u64>> {
        let mut line = LineParser::new(bytes);
        match line.read_string().unwrap().as_ref() {
            "[mk-app]" => {
                let id = line.read_ident()?;
                let name = line.read_string()?;
                let args = line.read_idents()?;
                line.check_end_of_line()?;
                let term = Term::App {
                    name,
                    args,
                    meaning: None,
                };
                self.set_term(id, term)?;
                Ok(None)
            }
            "[mk-var]" => {
                let id = line.read_ident()?;
                let index = line.read_integer()?;
                line.check_end_of_line()?;
                let term = Term::Var { index };
                self.set_term(id, term)?;
                Ok(None)
            }
            "[mk-quant]" => {
                let id = line.read_ident()?;
                let name = line.read_string()?;
                let params = line.read_integer()? as usize;
                let mut triggers = line.read_idents()?;
                line.check_end_of_line()?;
                let body = triggers.pop().ok_or(Error::MissingBody)?;
                let term = Term::Quant {
                    name,
                    params,
                    triggers,
                    body,
                    var_names: None,
                };
                self.set_term(id, term)?;
                Ok(None)
            }
            "[mk-lambda]" => {
                let id = line.read_ident()?;
                let name = line.read_string()?;
                let params = line.read_integer()?;
                let mut triggers = line.read_idents()?;
                line.check_end_of_line()?;
                let body = triggers.pop().ok_or(Error::MissingBody)?;
                let term = Term::Lambda {
                    name,
                    params,
                    triggers,
                    body, // NOTE: possibly a proof term
                };
                self.set_term(id, term)?;
                Ok(None)
            }
            "[mk-proof]" => {
                let id = line.read_ident()?;
                let name = line.read_string()?;
                let args = line.read_idents()?;
                line.check_end_of_line()?;
                let term = Term::Proof { name, args };
                // NOTE: proof terms are often overridden by terms later.
                self.set_term(id, term)?;
                Ok(None)
            }
            "[attach-meaning]" => {
                let id = line.read_ident()?;
                let theory = line.read_string()?;
                let sexp = line.read_content()?;
                match self.term_mut(&id)? {
                    Term::App { meaning, .. } => {
                        *meaning = Some(Meaning { theory, sexp });
                    }
                    _ => {
                        return Err(Error::CannotAttachMeaning(id));
                    }
                }
                Ok(None)
            }
            "[attach-var-names]" => {
                let id = line.read_ident()?;
                let names = line.read_var_names()?;
                line.check_end_of_line()?;
                match self.term_mut(&id)? {
                    Term::Quant {
                        var_names, params, ..
                    } if names.len() == *params => {
                        *var_names = Some(names);
                    }
                    _ => {
                        return Err(Error::CannotAttachVarNames(id));
                    }
                }
                Ok(None)
            }
            "[inst-discovered]" => {
                let method = line.read_string()?;
                let key = line.read_key()?;
                let quantifier = line.read_ident()?;
                let terms = line.read_idents()?;
                let blame = line.read_idents()?;
                line.check_end_of_line()?;
                let kind = QuantInstantiationKind::Discovered {
                    method,
                    quantifier,
                    terms,
                    blame,
                };
                let inst = QuantInstantiation { kind, data: None };
                // Ignore solver instances.
                if key != 0 {
                    inst.visit(&mut |id| self.check_ident(id))?;
                    self.instantiations.insert(key, inst);
                }
                Ok(None)
            }
            "[new-match]" => {
                let key = line.read_key()?;
                let quantifier = line.read_ident()?;
                let trigger = line.read_ident()?;
                let terms = line.read_idents()?;
                let used = line.read_matched_terms()?;
                line.check_end_of_line()?;
                let kind = QuantInstantiationKind::NewMatch {
                    quantifier,
                    trigger,
                    terms,
                    used,
                };
                let inst = QuantInstantiation { kind, data: None };
                // Ignore solver instances.
                if key != 0 {
                    inst.visit(&mut |id| self.check_ident(id))?;
                    self.instantiations.insert(key, inst);
                }
                Ok(None)
            }
            "[eq-expl]" => {
                let id = line.read_ident()?;
                let eq = line.read_equality()?;
                line.check_end_of_line()?;
                eq.visit(&mut |id| self.check_ident(id))?;
                self.equalities.insert(id, eq);
                Ok(None)
            }
            "[instance]" => {
                let key = line.read_key()?;
                let term = line.read_ident()?;
                let generation = line.read_optional_integer()?.unwrap_or_else(|| {
                    // Defaults to the same "generation" number as the outer instantiation, if any.
                    self.current_instances
                        .last()
                        .map(|(_, data)| data.generation)
                        .unwrap_or(0)
                });
                line.check_end_of_line()?;
                let data = QuantInstantiationData {
                    generation,
                    term,
                    enodes: Vec::new(),
                };
                self.current_instances.push((key, data));
                Ok(None)
            }
            "[attach-enode]" => {
                // Ignore commands outside of [instance]..[end-of-instance].
                if !self.current_instances.is_empty() {
                    let id = line.read_ident()?;
                    let generation = line.read_integer()?;
                    line.check_end_of_line()?;
                    let current_instance = self.current_instances.last_mut().unwrap();
                    let key = current_instance.0;
                    let data = &mut current_instance.1;
                    if generation != data.generation {
                        println!("{:?}", self.current_instances);
                        return Err(Error::InvalidEnodeGeneration);
                    }
                    data.enodes.push(id.clone());
                    self.qi_dependencies.insert(id, vec![key]);
                }
                Ok(None)
            }
            "[end-of-instance]" => {
                line.check_end_of_line()?;
                let (key, data) = self
                    .current_instances
                    .pop()
                    .ok_or(Error::InvalidEndOfInstance)?;
                // Ident check.
                data.visit(&mut |id| self.check_ident(id))?;
                // Ignore solver instances.
                if key != 0 {
                    let mut inst = self
                        .instantiations
                        .get_mut(&key)
                        .ok_or(Error::InvalidInstanceKey)?;
                    if inst.data.is_some() {
                        return Err(Error::InvalidEndOfInstance);
                    }
                    inst.data = Some(data);
                    Ok(Some(key))
                } else {
                    Ok(None)
                }
            }
            "[tool-version]" => {
                line.read_string()?;
                line.read_string()?;
                line.check_end_of_line()?;
                // ignored
                Ok(None)
            }
            "[begin-check]" => {
                line.read_integer()?;
                line.check_end_of_line()?;
                // ignored
                Ok(None)
            }
            "[assign]" => {
                line.read_literal()?.visit(&mut |id| self.check_ident(id))?;
                line.read_content()?;
                // ignored
                Ok(None)
            }
            "[conflict]" => {
                line.read_literals()?
                    .visit(&mut |id| self.check_ident(id))?;
                line.read_content()?;
                // ignored
                Ok(None)
            }
            "[push]" => {
                line.read_integer()?;
                line.check_end_of_line()?;
                // ignored
                Ok(None)
            }
            "[pop]" => {
                line.read_integer()?;
                line.read_integer()?;
                line.check_end_of_line()?;
                // ignored
                Ok(None)
            }
            "[resolve-lit]" => {
                line.read_integer()?;
                line.read_literal()?.visit(&mut |id| self.check_ident(id))?;
                line.check_end_of_line()?;
                // ignored
                Ok(None)
            }
            "[resolve-process]" => {
                line.read_literal()?.visit(&mut |id| self.check_ident(id))?;
                line.check_end_of_line()?;
                // ignored
                Ok(None)
            }
            "[eof]" => {
                line.check_end_of_line()?;
                // ignored
                Ok(None)
            }
            _ => Err(Error::UnknownCommand),
        }
    }

    /// Print debug information about a quantifier instantiation.
    pub fn log_instance(&self, config: &LogConfig, key: u64) -> Result<()> {
        let inst = self
            .instantiations
            .get(&key)
            .ok_or(Error::InvalidInstanceKey)?;
        match &inst.kind {
            QuantInstantiationKind::Discovered { .. } => (),
            QuantInstantiationKind::NewMatch {
                quantifier,
                terms,
                trigger,
                used,
            } => {
                let quantifier = self.term(quantifier)?;
                if let Term::Quant {
                    name,
                    var_names: Some(var_names),
                    ..
                } = quantifier
                {
                    // Bind variable names.
                    let mut venv = BTreeMap::new();
                    for (i, vn) in var_names.iter().enumerate() {
                        venv.insert(i as u64, vn.name.clone());
                    }
                    if config.with_triggers {
                        // Trim the outer "pattern" application.
                        let trigger = match self.term(trigger)? {
                            Term::App { name, args, .. }
                                if name == "pattern" && args.len() == 1 =>
                            {
                                &args[0]
                            }
                            _ => trigger,
                        };
                        println!("{} :: {{ {} }}", name, self.id_to_sexp(&venv, trigger)?);
                    } else {
                        println!("{}", name);
                    }
                    // Print instantiation terms.
                    let global_venv = BTreeMap::new();
                    if config.with_variables {
                        for (i, vn) in var_names.iter().enumerate() {
                            println!(
                                "  {} <-- {}",
                                vn.name.clone(),
                                self.id_to_sexp(&global_venv, &terms[i])?
                            );
                        }
                    }
                    if config.with_used_terms {
                        // Print 'used' terms.
                        for u in used {
                            use MatchedTerm::*;
                            match u {
                                RootPattern(id) => {
                                    println!("  ! {}", self.id_to_sexp(&global_venv, id)?);
                                }
                                SubPattern(id1, id2) => {
                                    println!(
                                        "  !! {} == {}",
                                        self.id_to_sexp(&global_venv, id1)?,
                                        self.id_to_sexp(&global_venv, id2)?
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn id_to_sexp(&self, venv: &BTreeMap<u64, Symbol>, id: &Ident) -> Result<String> {
        self.term_to_sexp(venv, self.term(id)?)
    }

    fn term_to_sexp(&self, venv: &BTreeMap<u64, Symbol>, term: &Term) -> Result<String> {
        use Term::*;
        match term {
            App {
                meaning: Some(meaning),
                ..
            } => Ok(meaning.sexp.clone()),
            App {
                name,
                args,
                meaning: None,
            } => {
                if args.is_empty() {
                    Ok(name.to_string())
                } else {
                    Ok(format!(
                        "({} {})",
                        name,
                        args.iter()
                            .map(|id| self.id_to_sexp(venv, id))
                            .collect::<Result<Vec<_>>>()?
                            .join(" ")
                    ))
                }
            }
            Var { index } => match venv.get(index) {
                Some(s) => Ok(format!("{}", s)),
                None => Ok(format!("_{}", index)),
            },
            Quant {
                name,
                params,
                triggers,
                body,
                var_names,
            } => {
                let mut venv = venv.clone();
                let vars = match var_names {
                    None => format!("{}", params),
                    Some(var_names) => {
                        for (i, vn) in var_names.iter().enumerate() {
                            venv.insert(i as u64, vn.name.clone());
                        }
                        var_names
                            .iter()
                            .map(|vn| format!("({} {})", vn.name, vn.sort))
                            .collect::<Vec<_>>()
                            .join(" ")
                    }
                };
                let patterns = triggers
                    .iter()
                    .map(|id| Ok(format!(":pattern {}", self.id_to_sexp(&venv, id)?)))
                    .collect::<Result<Vec<_>>>()?
                    .join(" ");
                Ok(format!(
                    "(QUANT ({}) (! {} :qid {} {}))",
                    vars,
                    self.id_to_sexp(&venv, body)?,
                    name,
                    patterns
                ))
            }
            Lambda {
                name,
                params,
                triggers,
                body,
            } => {
                let vars = format!("{}", params);
                let patterns = triggers
                    .iter()
                    .map(|id| Ok(format!(":pattern {}", self.id_to_sexp(venv, id)?)))
                    .collect::<Result<Vec<_>>>()?
                    .join(" ");
                Ok(format!(
                    "(LAMBDA ({}) (! {} :qid {} {}))",
                    vars,
                    self.id_to_sexp(venv, body)?,
                    name,
                    patterns
                ))
            }
            Proof { name, args } => Ok(format!(
                "(PROOF {} {})",
                name,
                args.iter()
                    .map(|id| self.id_to_sexp(venv, id))
                    .collect::<Result<Vec<_>>>()?
                    .join(" ")
            )),
        }
    }

    fn check_ident(&self, id: &Ident) -> Result<()> {
        if self.terms.contains_key(id) || id.is_empty() {
            Ok(())
        } else {
            Err(Error::UndefinedIdent(id.clone()))
        }
    }

    fn term(&self, id: &Ident) -> Result<&Term> {
        let t = self
            .terms
            .get(id)
            .ok_or_else(|| Error::UndefinedIdent(id.clone()))?;
        Ok(t)
    }

    fn term_mut(&mut self, id: &Ident) -> Result<&mut Term> {
        let t = self
            .terms
            .get_mut(id)
            .ok_or_else(|| Error::UndefinedIdent(id.clone()))?;
        Ok(t)
    }

    fn set_term(&mut self, ident: Ident, term: Term) -> Result<()> {
        let mut qi_deps = BTreeSet::new();
        term.visit(&mut |id| {
            self.check_ident(id)?;
            if let Some(deps) = self.qi_dependencies.get(id) {
                for dep in deps {
                    qi_deps.insert(*dep);
                }
            }
            Ok(())
        })?;
        self.terms.insert(ident.clone(), term);
        self.qi_dependencies
            .insert(ident, qi_deps.into_iter().collect());
        Ok(())
    }
}
