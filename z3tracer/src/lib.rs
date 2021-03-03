// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! This crate provides an experimental parser for Z3 tracing logs obtained by passing
//! `trace=true proof=true`.
//!
//! More information about Z3 tracing logs can be found in the documentation of the
//! project [Axiom Profiler](https://github.com/viperproject/axiom-profiler).

#![forbid(unsafe_code)]

use smt2parser::concrete::Symbol;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use structopt::StructOpt;

pub mod error;
mod lexer;
pub mod syntax;

use error::{RawError, RawResult, Result};
use lexer::Lexer;
use syntax::{
    Equality, Ident, MatchedTerm, Meaning, QuantInstantiation, QuantInstantiationData,
    QuantInstantiationKind, Term, Visitor,
};

/// The hexadecimal index of a quantifier instantiation (QI).
#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Clone, Copy)]
pub struct QIKey(u64);

/// Configuration for the analysis of Z3 traces.
#[derive(Debug, Default, Clone, StructOpt)]
pub struct ModelConfig {
    /// Whether to log quantifier instantiations (QIs).
    #[structopt(long)]
    qi_logs: bool,

    /// Whether to display variable instantiations in QIs
    #[structopt(long)]
    with_qi_variables: bool,

    /// Whether to display triggers in QIs.
    #[structopt(long)]
    with_qi_triggers: bool,

    /// Whether to display terms produced by QIs.
    #[structopt(long)]
    with_qi_produced_terms: bool,

    /// Whether to display terms used by QIs.
    #[structopt(long)]
    with_qi_used_terms: bool,
}

#[derive(Debug)]
pub struct TermData {
    term: Term,
    eq_class: Ident,
    qi_dependencies: BTreeSet<QIKey>,
    assignment: Option<bool>,
}

#[derive(Default, Debug)]
pub struct Model {
    // Configuration.
    config: ModelConfig,
    // Terms indexed by identifier.
    terms: BTreeMap<Ident, TermData>,
    // Quantifier instantiations indexed by (hexadecimal) key.
    instantiations: BTreeMap<QIKey, QuantInstantiation>,
    // Stack of current quantifier instances.
    current_instances: Vec<(QIKey, QuantInstantiationData)>,
}

impl Model {
    pub fn new(config: ModelConfig) -> Self {
        Self {
            config,
            terms: BTreeMap::new(),
            instantiations: BTreeMap::new(),
            current_instances: Vec::new(),
        }
    }

    /// All terms in the model.
    pub fn terms(&self) -> &BTreeMap<Ident, TermData> {
        &self.terms
    }

    /// All instantiations in the model.
    pub fn instantiations(&self) -> &BTreeMap<QIKey, QuantInstantiation> {
        &self.instantiations
    }

    /// Process the Z3 tracing logs in the given input.
    pub fn process<R>(&mut self, path_name: Option<String>, input: R) -> Result<()>
    where
        R: std::io::BufRead,
    {
        let mut lexer = Lexer::new(path_name, input);
        while self
            .process_line(&mut lexer)
            .map_err(|e| lexer.make_error(e))?
        {}
        Ok(())
    }

    /// Parse one line of the given input. Return the key of a QI that was produced, if any.
    fn process_line<R>(&mut self, lexer: &mut Lexer<R>) -> RawResult<bool>
    where
        R: std::io::BufRead,
    {
        match lexer.read_string().unwrap().as_ref() {
            "[mk-app]" => {
                let id = lexer.read_fresh_ident()?;
                let name = lexer.read_string()?;
                let args = lexer.read_idents()?;
                lexer.read_end_of_line()?;
                let term = Term::App {
                    name,
                    args,
                    meaning: None,
                };
                self.add_term(id, term)?;
                Ok(true)
            }
            "[mk-var]" => {
                let id = lexer.read_fresh_ident()?;
                let index = lexer.read_integer()?;
                lexer.read_end_of_line()?;
                let term = Term::Var { index };
                self.add_term(id, term)?;
                Ok(true)
            }
            "[mk-quant]" => {
                let id = lexer.read_fresh_ident()?;
                let name = lexer.read_string()?;
                let params = lexer.read_integer()? as usize;
                let mut triggers = lexer.read_idents()?;
                lexer.read_end_of_line()?;
                let body = triggers.pop().ok_or(RawError::MissingBody)?;
                let term = Term::Quant {
                    name,
                    params,
                    triggers,
                    body,
                    var_names: None,
                };
                self.add_term(id, term)?;
                Ok(true)
            }
            "[mk-lambda]" => {
                let id = lexer.read_fresh_ident()?;
                let name = lexer.read_string()?;
                let params = lexer.read_integer()?;
                let mut triggers = lexer.read_idents()?;
                lexer.read_end_of_line()?;
                let body = triggers.pop().ok_or(RawError::MissingBody)?;
                let term = Term::Lambda {
                    name,
                    params,
                    triggers,
                    body,
                };
                self.add_term(id, term)?;
                Ok(true)
            }
            "[mk-proof]" => {
                let id = lexer.read_fresh_ident()?;
                let name = lexer.read_string()?;
                let args = lexer.read_idents()?;
                lexer.read_end_of_line()?;
                // println!(
                //     "{} {:?}\n",
                //     name,
                //     args.iter().map(
                //         |id| format!("{}", self.id_to_sexp(&BTreeMap::new(), id).unwrap())
                //     ).collect::<Vec<_>>()
                // );
                let term = Term::Proof { name, args };
                self.add_term(id, term)?;
                Ok(true)
            }
            "[attach-meaning]" => {
                let id = lexer.read_ident()?;
                let theory = lexer.read_string()?;
                let sexp = lexer.read_line()?;
                match self.term_mut(&id)? {
                    Term::App { meaning, .. } => {
                        *meaning = Some(Meaning { theory, sexp });
                    }
                    _ => {
                        return Err(RawError::CannotAttachMeaning(id));
                    }
                }
                Ok(true)
            }
            "[attach-var-names]" => {
                let id = lexer.read_ident()?;
                let names = lexer.read_var_names()?;
                lexer.read_end_of_line()?;
                match self.term_mut(&id)? {
                    Term::Quant {
                        var_names, params, ..
                    } if names.len() == *params => {
                        *var_names = Some(names);
                    }
                    _ => {
                        return Err(RawError::CannotAttachVarNames(id));
                    }
                }
                Ok(true)
            }
            "[inst-discovered]" => {
                let method = lexer.read_string()?;
                let key = QIKey(lexer.read_key()?);
                let quantifier = lexer.read_ident()?;
                let terms = lexer.read_idents()?;
                let blame = lexer.read_idents()?;
                lexer.read_end_of_line()?;
                let kind = QuantInstantiationKind::Discovered {
                    method,
                    quantifier,
                    terms,
                    blame,
                };
                let inst = QuantInstantiation { kind, data: None };
                // Ignore solver instances.
                if !key.is_zero() {
                    inst.visit(&mut |id| self.check_ident(id))?;
                    self.instantiations.insert(key, inst);
                }
                Ok(true)
            }
            "[new-match]" => {
                let key = QIKey(lexer.read_key()?);
                let quantifier = lexer.read_ident()?;
                let trigger = lexer.read_ident()?;
                let terms = lexer.read_idents()?;
                let used = lexer.read_matched_terms()?;
                lexer.read_end_of_line()?;
                for u in &used {
                    if let MatchedTerm::Equality(id1, id2) = u {
                        self.check_equality(id1, id2)?;
                    }
                }
                let kind = QuantInstantiationKind::NewMatch {
                    quantifier,
                    trigger,
                    terms,
                    used,
                };
                let inst = QuantInstantiation { kind, data: None };
                // Ignore solver instances.
                if !key.is_zero() {
                    inst.visit(&mut |id| self.check_ident(id))?;
                    self.instantiations.insert(key, inst);
                }
                Ok(true)
            }
            "[eq-expl]" => {
                let id = lexer.read_ident()?;
                let eq = lexer.read_equality()?;
                lexer.read_end_of_line()?;
                eq.visit(&mut |id| self.check_ident(id))?;
                self.process_equality(&id, &eq)?;
                Ok(true)
            }
            "[instance]" => {
                let key = QIKey(lexer.read_key()?);
                let term = lexer.read_ident()?;
                let generation = lexer.read_optional_integer()?.unwrap_or_else(|| {
                    // Defaults to the same "generation" number as the outer instantiation, if any.
                    self.current_instances
                        .last()
                        .map(|(_, data)| data.generation)
                        .unwrap_or(0)
                });
                lexer.read_end_of_line()?;
                self.add_qi_dependency(&term, key)?;
                let data = QuantInstantiationData {
                    generation,
                    term,
                    enodes: Vec::new(),
                };
                self.current_instances.push((key, data));
                Ok(true)
            }
            "[attach-enode]" => {
                let id = lexer.read_ident()?;
                let generation = lexer.read_integer()?;
                lexer.read_end_of_line()?;
                // Ignore commands outside of [instance]..[end-of-instance].
                if !self.current_instances.is_empty() {
                    let current_instance = self.current_instances.last_mut().unwrap();
                    let key = current_instance.0;
                    let data = &mut current_instance.1;
                    if generation != data.generation {
                        return Err(RawError::InvalidEnodeGeneration);
                    }
                    data.enodes.push(id.clone());
                    self.add_qi_dependency(&id, key)?;
                }
                Ok(true)
            }
            "[end-of-instance]" => {
                lexer.read_end_of_line()?;
                let (key, data) = self
                    .current_instances
                    .pop()
                    .ok_or(RawError::InvalidEndOfInstance)?;
                // Ident check.
                data.visit(&mut |id| self.check_ident(id))?;
                // Ignore solver instances.
                if !key.is_zero() {
                    let mut inst = self
                        .instantiations
                        .get_mut(&key)
                        .ok_or(RawError::InvalidInstanceKey)?;
                    if inst.data.is_some() {
                        return Err(RawError::InvalidEndOfInstance);
                    }
                    inst.data = Some(data);
                    self.log_instance(key)?;
                    Ok(true)
                } else {
                    Ok(true)
                }
            }
            "[tool-version]" => {
                lexer.read_string()?;
                lexer.read_string()?;
                lexer.read_end_of_line()?;
                // ignored
                Ok(true)
            }
            "[begin-check]" => {
                lexer.read_integer()?;
                lexer.read_end_of_line()?;
                // ignored
                Ok(true)
            }
            "[assign]" => {
                let lit = lexer.read_literal()?;
                lexer.read_line()?;
                lit.visit(&mut |id| self.check_ident(id))?;
                self.term_data_mut(&lit.id)?.assignment = Some(lit.sign);
                // ignored
                Ok(true)
            }
            "[conflict]" => {
                lexer
                    .read_literals()?
                    .visit(&mut |id| self.check_ident(id))?;
                lexer.read_line()?;
                // ignored
                Ok(true)
            }
            "[push]" => {
                lexer.read_integer()?;
                lexer.read_end_of_line()?;
                // ignored
                Ok(true)
            }
            "[pop]" => {
                lexer.read_integer()?;
                lexer.read_integer()?;
                lexer.read_end_of_line()?;
                // ignored
                Ok(true)
            }
            "[resolve-lit]" => {
                lexer.read_integer()?;
                lexer
                    .read_literal()?
                    .visit(&mut |id| self.check_ident(id))?;
                lexer.read_end_of_line()?;
                // ignored
                Ok(true)
            }
            "[resolve-process]" => {
                lexer
                    .read_literal()?
                    .visit(&mut |id| self.check_ident(id))?;
                lexer.read_end_of_line()?;
                // ignored
                Ok(true)
            }
            "[eof]" => {
                lexer.read_end_of_line()?;
                // ignored
                Ok(false)
            }
            s => Err(RawError::UnknownCommand(s.to_string())),
        }
    }

    /// Print debug information about a quantifier instantiation.
    fn log_instance(&self, key: QIKey) -> RawResult<()> {
        let inst = self
            .instantiations
            .get(&key)
            .ok_or(RawError::InvalidInstanceKey)?;
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
                    if self.config.with_qi_triggers {
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
                    if self.config.with_qi_variables {
                        for (i, vn) in var_names.iter().enumerate() {
                            println!(
                                "  {} <-- {}",
                                vn.name.clone(),
                                self.id_to_sexp(&global_venv, &terms[i])?
                            );
                        }
                    }
                    if self.config.with_qi_used_terms {
                        // Print 'used' terms.
                        for u in used {
                            use MatchedTerm::*;
                            match u {
                                Trigger(id) => {
                                    println!("  ! {}", self.id_to_sexp(&global_venv, id)?);
                                }
                                Equality(id1, id2) => {
                                    println!(
                                        "  !! {} == {}",
                                        self.id_to_sexp(&global_venv, id1)?,
                                        self.id_to_sexp(&global_venv, id2)?
                                    );
                                }
                            }
                        }
                    }
                    if self.config.with_qi_produced_terms {
                        if let Some(data) = &inst.data {
                            // Print produced terms (aka attached enodes).
                            for e in &data.enodes {
                                println!("  --> {}", self.id_to_sexp(&global_venv, e)?);
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn id_to_sexp(&self, venv: &BTreeMap<u64, Symbol>, id: &Ident) -> RawResult<String> {
        self.term_to_sexp(venv, self.term(id)?)
    }

    fn term_to_sexp(&self, venv: &BTreeMap<u64, Symbol>, term: &Term) -> RawResult<String> {
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
                            .collect::<RawResult<Vec<_>>>()?
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
                    .collect::<RawResult<Vec<_>>>()?
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
                    .collect::<RawResult<Vec<_>>>()?
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
                    .collect::<RawResult<Vec<_>>>()?
                    .join(" ")
            )),
        }
    }

    fn check_ident(&self, id: &Ident) -> RawResult<()> {
        if self.terms.contains_key(id) || id.is_empty() {
            Ok(())
        } else {
            Err(RawError::UndefinedIdent(id.clone()))
        }
    }

    fn term(&self, id: &Ident) -> RawResult<&Term> {
        let t = &self
            .terms
            .get(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?
            .term;
        Ok(t)
    }

    fn term_mut(&mut self, id: &Ident) -> RawResult<&mut Term> {
        let t = &mut self
            .terms
            .get_mut(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?
            .term;
        Ok(t)
    }

    fn term_data(&self, id: &Ident) -> RawResult<&TermData> {
        let t = self
            .terms
            .get(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?;
        Ok(t)
    }

    fn term_data_mut(&mut self, id: &Ident) -> RawResult<&mut TermData> {
        let t = self
            .terms
            .get_mut(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?;
        Ok(t)
    }

    fn add_qi_dependency(&mut self, id: &Ident, key: QIKey) -> RawResult<()> {
        self.term_data_mut(id)?.qi_dependencies.insert(key);
        Ok(())
    }

    fn qi_dependencies(&mut self, id: &Ident) -> RawResult<Vec<QIKey>> {
        Ok(self
            .term_data(id)?
            .qi_dependencies
            .iter()
            .cloned()
            .collect())
    }

    fn add_term(&mut self, ident: Ident, term: Term) -> RawResult<()> {
        term.visit(&mut |id| self.check_ident(id))?;
        let data = TermData {
            term,
            eq_class: ident.clone(),
            qi_dependencies: BTreeSet::new(),
            assignment: None,
        };
        self.terms.insert(ident, data);
        Ok(())
    }

    fn get_equality_class(&mut self, id: &Ident) -> RawResult<Ident> {
        let cid = self.term_data(id)?.eq_class.clone();
        if cid == *id {
            return Ok(cid);
        }
        let new_cid = self.get_equality_class(&cid)?;
        if new_cid == cid {
            // No change since last time.
            return Ok(cid);
        }
        // Class was updated. We need to re-import dependencies from cid.
        let deps = self.qi_dependencies(&cid)?;
        let t = self.term_data_mut(id)?;
        t.eq_class = new_cid.clone();
        for d in deps {
            t.qi_dependencies.insert(d);
        }
        Ok(new_cid)
    }

    fn check_literal_equality(&self, eid: &Ident, id1: &Ident, id2: &Ident) -> RawResult<bool> {
        // Normal case.
        if let Term::App { name, args, .. } = self.term(eid)? {
            if name.as_str() == "=" && args.len() == 2 {
                if &args[0] == id1 && &args[1] == id2 || &args[0] == id2 && &args[1] == id1 {
                    return Ok(true);
                }
            }
        }
        // Assigned term.
        if eid == id1 {
            let t = self.term_data(eid)?;
            match (t.assignment, self.term(id2)?) {
                (Some(b), Term::App { name, args, .. })
                    if args.is_empty() && name.as_str() == if b { "true" } else { "false" } =>
                {
                    return Ok(true);
                }
                _ => (),
            }
        }
        Ok(false)
    }

    fn check_congruence_equality(
        &self,
        eqs: &[(Ident, Ident)],
        id1: &Ident,
        id2: &Ident,
    ) -> RawResult<bool> {
        let eqs = eqs.iter().cloned().collect::<HashSet<_>>();
        self.check_matching_ids(&eqs, id1, id2)
    }

    fn check_matching_ids(
        &self,
        eqs: &HashSet<(Ident, Ident)>,
        id1: &Ident,
        id2: &Ident,
    ) -> RawResult<bool> {
        if id1 == id2 {
            return Ok(true);
        }
        if eqs.contains(&(id1.clone(), id2.clone())) {
            return Ok(true);
        }
        let t1 = self.term(id1)?;
        let t2 = self.term(id2)?;
        self.check_matching_terms(eqs, t1, t2)
    }

    fn check_matching_terms(
        &self,
        eqs: &HashSet<(Ident, Ident)>,
        t1: &Term,
        t2: &Term,
    ) -> RawResult<bool> {
        use Term::*;
        match (t1, t2) {
            (
                App {
                    name: n1, args: a1, ..
                },
                App {
                    name: n2, args: a2, ..
                },
            ) if n1 == n2 && a1.len() == a2.len() => {
                for i in 0..a1.len() {
                    if !self.check_matching_ids(eqs, &a1[i], &a2[i])? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn process_equality(&mut self, id0: &Ident, eq: &Equality) -> RawResult<()> {
        use Equality::*;

        let id = self.get_equality_class(id0)?;
        let raw_cid = match eq {
            Root => {
                // id == *id0 is expected but not strictly guaranteed.
                return Ok(());
            }
            Literal(eid, cid) => {
                if !self.check_literal_equality(eid, id0, cid)? {
                    return Err(RawError::CannotProcessEquality(id0.clone(), eq.clone()));
                }
                // Import dependencies from the equation term.
                let deps = self.qi_dependencies(eid)?;
                let t = self.term_data_mut(&id)?;
                for d in deps {
                    t.qi_dependencies.insert(d);
                }
                cid
            }
            Congruence(eqs, cid) => {
                // Check congruence equalities.
                for (id1, id2) in eqs {
                    self.check_equality(id1, id2)?;
                }
                if !self.check_congruence_equality(eqs, id0, cid)? {
                    return Err(RawError::CannotProcessEquality(id0.clone(), eq.clone()));
                }
                cid
            }
            Theory(_, cid) => cid,
        };
        // Import class and dependencies from raw_cid.
        let cid = self.get_equality_class(raw_cid)?;
        let deps = self.qi_dependencies(raw_cid)?;

        let t = self.term_data_mut(&id)?;
        t.eq_class = cid;
        for d in deps {
            t.qi_dependencies.insert(d);
        }
        Ok(())
    }

    fn check_equality(&mut self, id1: &Ident, id2: &Ident) -> RawResult<()> {
        let c1 = self.get_equality_class(id1)?;
        let c2 = self.get_equality_class(id2)?;
        if c1 != c2 {
            return Err(RawError::CannotCheckEquality(id1.clone(), id2.clone()));
        }
        Ok(())
    }
}

impl QIKey {
    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}
