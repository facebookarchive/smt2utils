// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use smt2parser::concrete::Symbol;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashSet};
use structopt::StructOpt;

use crate::error::{RawError, RawResult, Result};
use crate::lexer::Lexer;
use crate::parser::{LogVisitor, Parser, ParserConfig};
use crate::syntax::{
    Equality, Ident, Literal, MatchedTerm, Meaning, QiKey, QuantInstantiation,
    QuantInstantiationData, QuantInstantiationKind, Term, VarName, Visitor,
};

// https://github.com/TeXitoi/structopt/issues/333
#[cfg_attr(not(doc), allow(missing_docs))]
#[cfg_attr(doc, doc = "Configuration for the analysis of Z3 traces.")]
#[derive(Debug, Default, Clone, StructOpt)]
pub struct ModelConfig {
    #[structopt(flatten)]
    pub parser_config: ParserConfig,

    /// Whether to log quantifier instantiations (QIs).
    #[structopt(long)]
    pub display_qi_logs: bool,

    /// Whether to display variable instantiations in QIs
    #[structopt(long)]
    pub with_qi_variables: bool,

    /// Whether to display triggers in QIs.
    #[structopt(long)]
    pub with_qi_triggers: bool,

    /// Whether to display terms produced by QIs.
    #[structopt(long)]
    pub with_qi_produced_terms: bool,

    /// Whether to display terms used by QIs.
    #[structopt(long)]
    pub with_qi_used_terms: bool,

    /// Whether to run consistency checks for identifiers, equations, etc.
    #[structopt(long)]
    pub skip_log_consistency_checks: bool,
}

/// Information on a term in the model.
#[derive(Debug, Clone)]
pub struct TermData {
    /// Term definition.
    pub term: Term,
    /// QIs that made this term an active "enode".
    pub enode_qi_dependencies: BTreeSet<QiKey>,
    /// Last truth assignment, if any.
    pub assignment: Option<bool>,
    /// Known instantiations (applicable when `term` is a quantified expression).
    pub instantiations: Vec<QiKey>,
    /// Timestamps (line numbers in Z3 logs) of instantiations.
    pub instantiation_timestamps: Vec<usize>,
    /// Known proofs of this term (applicable when `term` is a boolean formula).
    pub proofs: Vec<Ident>,
    /// Track the relative creation time of this term. Currently, this is the line
    /// number in the Z3 log.
    pub timestamp: usize,
}

/// Information on a quantifier instance.
#[derive(Debug, Clone)]
pub struct QuantInstanceData {
    /// Hexadecimal key of the instantiation.
    pub key: QiKey,
    /// Quantifier instantiation data including optional term and ident.
    pub data: QuantInstantiationData,
    /// Timestamp of the QI. Right now this is the line number in the Z3 logs where
    /// the instantiation occurs.
    pub timestamp: usize,
}

/// Main state of the Z3 tracer.
#[derive(Default, Debug)]
pub struct Model {
    // Configuration.
    config: ModelConfig,
    // Terms indexed by identifier.
    terms: BTreeMap<Ident, TermData>,
    // Quantifier instantiations indexed by (hexadecimal) key.
    instantiations: BTreeMap<QiKey, QuantInstantiation>,
    // Stack of current quantifier instances.
    current_instances: Vec<QuantInstanceData>,
    // Number of Z3 log callbacks already executed.
    processed_logs: usize,
}

impl Model {
    /// Build a new Z3 tracer.
    /// Experimental. Use `Model::default()` instead if possible.
    pub fn new(config: ModelConfig) -> Self {
        Self {
            config,
            terms: BTreeMap::new(),
            instantiations: BTreeMap::new(),
            current_instances: Vec::new(),
            processed_logs: 0,
        }
    }

    /// Process some input.
    pub fn process<R>(&mut self, path_name: Option<String>, input: R) -> Result<()>
    where
        R: std::io::BufRead,
    {
        let lexer = Lexer::new(path_name, input);
        let config = self.config.parser_config.clone();
        Parser::new(config, lexer, self).parse()
    }

    /// All terms in the model.
    pub fn terms(&self) -> &BTreeMap<Ident, TermData> {
        &self.terms
    }

    /// All instantiations in the model.
    pub fn instantiations(&self) -> &BTreeMap<QiKey, QuantInstantiation> {
        &self.instantiations
    }

    /// Number of Z3 logs that were processed.
    pub fn processed_logs(&self) -> usize {
        self.processed_logs
    }

    /// Construct a max-heap of the (most) instantiated quantified terms.
    pub fn most_instantiated_terms(&self) -> BinaryHeap<(usize, Ident)> {
        self.terms
            .iter()
            .filter_map(|(id, term)| {
                let c = term.instantiation_timestamps.len();
                if c > 0 {
                    Some((c, id.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Retrieve a particular term.
    pub fn term(&self, id: &Ident) -> RawResult<&Term> {
        let t = &self
            .terms
            .get(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?
            .term;
        Ok(t)
    }

    /// Retrieve a particular term, including metadata.
    pub fn term_data(&self, id: &Ident) -> RawResult<&TermData> {
        let t = self
            .terms
            .get(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?;
        Ok(t)
    }

    /// Display a term given by id.
    pub fn id_to_sexp(&self, venv: &BTreeMap<u64, Symbol>, id: &Ident) -> RawResult<String> {
        self.term_to_sexp(venv, self.term(id)?)
    }

    /// Display a term by id.
    pub fn term_to_sexp(&self, venv: &BTreeMap<u64, Symbol>, term: &Term) -> RawResult<String> {
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
            Proof {
                name,
                args,
                property,
            } => Ok(format!(
                "(PROOF {} {}{})",
                name,
                args.iter()
                    .map(|id| Ok(self.id_to_sexp(venv, id)? + " "))
                    .collect::<RawResult<Vec<_>>>()?
                    .join(""),
                self.id_to_sexp(venv, property)?,
            )),
            Builtin { name } => Ok(name.clone().unwrap_or_else(String::new)),
        }
    }

    fn append_id_subterms(&self, deps: &mut BTreeSet<Ident>, id: &Ident) -> RawResult<()> {
        deps.insert(id.clone());
        self.append_term_subterms(deps, self.term(id)?)
    }

    fn append_term_subterms(&self, deps: &mut BTreeSet<Ident>, term: &Term) -> RawResult<()> {
        term.visit(&mut |id| self.append_id_subterms(deps, id))
    }

    fn has_log_consistency_checks(&self) -> bool {
        !self.config.skip_log_consistency_checks
    }

    /// Print debug information about a quantifier instantiation.
    fn log_instance(&self, key: QiKey) -> RawResult<()> {
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
                        for data in &inst.data {
                            // Print maximal produced terms (aka attached enodes).
                            let mut subterms = BTreeSet::new();
                            for e in data.enodes.iter().rev() {
                                if !subterms.contains(e) {
                                    let t = self.term(e)?;
                                    self.append_term_subterms(&mut subterms, t)?;
                                    println!("  --> {}", self.term_to_sexp(&global_venv, t)?);
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn check_ident(&self, id: &Ident) -> RawResult<()> {
        if self.terms.contains_key(id) || id.is_builtin() {
            Ok(())
        } else {
            Err(RawError::UndefinedIdent(id.clone()))
        }
    }

    fn check_ident_is_not_a_proof(&self, id: &Ident) -> RawResult<()> {
        match self.term(id)? {
            Term::Proof { .. } => Err(RawError::UnexpectedProofTerm(id.clone())),
            Term::Lambda { body, .. } => self.check_ident_is_not_a_proof(body),
            _ => Ok(()),
        }
    }

    fn term_mut(&mut self, id: &Ident) -> RawResult<&mut Term> {
        let t = &mut self.term_data_mut(id)?.term;
        Ok(t)
    }

    fn term_data_mut(&mut self, id: &Ident) -> RawResult<&mut TermData> {
        if id.is_builtin() {
            // Builtins are added lazily
            let timestamp = self.processed_logs;
            let entry = self.terms.entry(id.clone()).or_insert_with(|| TermData {
                term: Term::Builtin {
                    name: id.namespace.clone(),
                },
                enode_qi_dependencies: BTreeSet::new(),
                assignment: None,
                instantiations: Vec::new(),
                instantiation_timestamps: Vec::new(),
                proofs: Vec::new(),
                timestamp,
            });
            return Ok(&mut *entry);
        }
        let t = self
            .terms
            .get_mut(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?;
        Ok(t)
    }

    fn check_literal_equality(&self, eid: &Ident, id1: &Ident, id2: &Ident) -> RawResult<bool> {
        let data = self.term_data(eid)?;
        // Normal case.
        if let Some([eid1, eid2]) = data.term.matches_equality() {
            if data.proofs.is_empty() && data.assignment.is_none() {
                return Err(RawError::MissingProof(eid.clone()));
            }
            if (&eid1 == id1 && &eid2 == id2) || (&eid1 == id2 && &eid2 == id1) {
                return Ok(true);
            }
        }
        // Assigned term.
        if eid == id1 {
            match (data.assignment, self.term(id2)?) {
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
}

impl LogVisitor for &mut Model {
    fn add_term(&mut self, ident: Ident, term: Term) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            term.visit(&mut |id| self.check_ident(id))?;
        }
        if let Term::Proof { property, .. } = &term {
            let data = self.term_data_mut(property)?;
            data.proofs.push(ident.clone());
        }
        if self.has_log_consistency_checks()
            && matches!(term, Term::App { .. } | Term::Quant { .. })
        {
            term.visit(&mut |id| self.check_ident_is_not_a_proof(id))?;
        }
        let data = TermData {
            term,
            enode_qi_dependencies: BTreeSet::new(),
            assignment: None,
            instantiations: Vec::new(),
            instantiation_timestamps: Vec::new(),
            proofs: Vec::new(),
            timestamp: self.processed_logs,
        };
        self.terms.insert(ident, data);
        Ok(())
    }

    fn add_instantiation(&mut self, key: QiKey, inst: QuantInstantiation) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            inst.visit(&mut |id| self.check_ident(id))?;
        }
        let quantifier = inst.kind.quantifier();
        self.term_data_mut(quantifier)?.instantiations.push(key);
        self.instantiations.insert(key, inst);
        Ok(())
    }

    fn start_instance(&mut self, key: QiKey, data: QuantInstantiationData) -> RawResult<()> {
        self.processed_logs += 1;
        // Ident check.
        if self.has_log_consistency_checks() {
            data.visit(&mut |id| self.check_ident(id))?;
        }
        self.current_instances.push(QuantInstanceData {
            key,
            data,
            timestamp: self.processed_logs,
        });
        Ok(())
    }

    fn end_instance(&mut self) -> RawResult<()> {
        self.processed_logs += 1;
        let QuantInstanceData {
            key,
            data,
            timestamp,
        } = self
            .current_instances
            .pop()
            .ok_or(RawError::InvalidEndOfInstance)?;
        let inst = self
            .instantiations
            .get_mut(&key)
            .ok_or(RawError::InvalidInstanceKey)?;
        inst.data.push(data);
        let quantifier = inst.kind.quantifier().clone();
        self.term_data_mut(&quantifier)?
            .instantiation_timestamps
            .push(timestamp);
        if self.config.display_qi_logs {
            self.log_instance(key)?;
        }
        Ok(())
    }

    fn add_equality(&mut self, id: Ident, eq: Equality) -> RawResult<()> {
        use Equality::*;

        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            eq.visit(&mut |id| self.check_ident(id))?;
        }
        match &eq {
            Root => (),
            Literal(eid, cid) => {
                if self.has_log_consistency_checks()
                    && !self.check_literal_equality(eid, &id, cid)?
                {
                    return Err(RawError::CannotProcessEquality(id, eq));
                }
            }
            Congruence(eqs, cid) => {
                if self.has_log_consistency_checks()
                    && !self.check_congruence_equality(eqs, &id, cid)?
                {
                    return Err(RawError::CannotProcessEquality(id, eq));
                }
            }
            Theory(_, _) => (),
            Axiom(_) => (),
            Unknown(_) => (),
        }
        Ok(())
    }

    fn attach_meaning(&mut self, id: Ident, m: Meaning) -> RawResult<()> {
        self.processed_logs += 1;
        match self.term_mut(&id)? {
            Term::App { meaning, .. } => {
                *meaning = Some(m);
                Ok(())
            }
            _ => Err(RawError::CannotAttachMeaning(id)),
        }
    }

    fn attach_var_names(&mut self, id: Ident, names: Vec<VarName>) -> RawResult<()> {
        self.processed_logs += 1;
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
        Ok(())
    }

    fn attach_enode(&mut self, id: Ident, _generation: u64) -> RawResult<()> {
        self.processed_logs += 1;
        // Ignore commands outside of [instance]..[end-of-instance].
        if !self.current_instances.is_empty() {
            let current_instance = self.current_instances.last_mut().unwrap();
            let key = current_instance.key;
            let data = &mut current_instance.data;
            data.enodes.push(id.clone());
            self.term_data_mut(&id)?.enode_qi_dependencies.insert(key);
        }
        Ok(())
    }

    fn tool_version(&mut self, _s1: String, _s2: String) -> RawResult<()> {
        self.processed_logs += 1;
        Ok(())
    }

    fn begin_check(&mut self, _i: u64) -> RawResult<()> {
        self.processed_logs += 1;
        Ok(())
    }

    fn assign(&mut self, lit: Literal, _s: String) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            lit.visit(&mut |id| self.check_ident(id))?;
        }
        self.term_data_mut(&lit.id)?.assignment = Some(lit.sign);
        Ok(())
    }

    fn conflict(&mut self, lits: Vec<Literal>, _s: String) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            lits.visit(&mut |id| self.check_ident(id))?;
        }
        Ok(())
    }

    fn push(&mut self, _i: u64) -> RawResult<()> {
        self.processed_logs += 1;
        Ok(())
    }

    fn pop(&mut self, _i: u64, _j: u64) -> RawResult<()> {
        self.processed_logs += 1;
        Ok(())
    }

    fn resolve_lit(&mut self, _i: u64, lit: Literal) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            lit.visit(&mut |id| self.check_ident(id))?;
        }
        Ok(())
    }

    fn resolve_process(&mut self, lit: Literal) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            lit.visit(&mut |id| self.check_ident(id))?;
        }
        Ok(())
    }
}
