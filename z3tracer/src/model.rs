// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use smt2parser::concrete::Symbol;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use structopt::StructOpt;

use crate::error::{RawError, RawResult, Result};
use crate::lexer::Lexer;
use crate::parser::{LogVisitor, Parser};
use crate::syntax::{
    Equality, Ident, Literal, MatchedTerm, Meaning, QIKey, QuantInstantiation,
    QuantInstantiationData, QuantInstantiationKind, Term, VarName, Visitor,
};

/// Configuration for the analysis of Z3 traces.
#[derive(Debug, Default, Clone, StructOpt)]
pub struct ModelConfig {
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
#[derive(Debug)]
pub struct TermData {
    pub term: Term,
    pub eq_class: Ident,
    pub qi_dependencies: BTreeSet<QIKey>,
    pub assignment: Option<bool>,
    pub instantiations: Vec<QIKey>,
}

/// Main state of the Z3 tracer.
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
    /// Build a new Z3 tracer.
    pub fn new(config: ModelConfig) -> Self {
        Self {
            config,
            terms: BTreeMap::new(),
            instantiations: BTreeMap::new(),
            current_instances: Vec::new(),
        }
    }

    /// Process some input.
    pub fn process<R>(&mut self, path_name: Option<String>, input: R) -> Result<()>
    where
        R: std::io::BufRead,
    {
        let lexer = Lexer::new(path_name, input);
        Parser::new(lexer, self).parse()
    }

    /// All terms in the model.
    pub fn terms(&self) -> &BTreeMap<Ident, TermData> {
        &self.terms
    }

    /// All instantiations in the model.
    pub fn instantiations(&self) -> &BTreeMap<QIKey, QuantInstantiation> {
        &self.instantiations
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
    fn id_to_sexp(&self, venv: &BTreeMap<u64, Symbol>, id: &Ident) -> RawResult<String> {
        self.term_to_sexp(venv, self.term(id)?)
    }

    /// Display a term by id.
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
        if self.terms.contains_key(id) || id.is_empty() {
            Ok(())
        } else {
            Err(RawError::UndefinedIdent(id.clone()))
        }
    }

    fn term_mut(&mut self, id: &Ident) -> RawResult<&mut Term> {
        let t = &mut self
            .terms
            .get_mut(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?
            .term;
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
            if name.as_str() == "=" && args.len() == 2 && &args[0] == id1 && &args[1] == id2
                || &args[0] == id2 && &args[1] == id1
            {
                return Ok(true);
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

    fn check_equality(&mut self, id1: &Ident, id2: &Ident) -> RawResult<()> {
        let c1 = self.get_equality_class(id1)?;
        let c2 = self.get_equality_class(id2)?;
        if c1 != c2 {
            return Err(RawError::CannotCheckEquality(id1.clone(), id2.clone()));
        }
        Ok(())
    }
}

impl LogVisitor for &mut Model {
    fn add_term(&mut self, ident: Ident, term: Term) -> RawResult<()> {
        if self.has_log_consistency_checks() {
            term.visit(&mut |id| self.check_ident(id))?;
        }
        let data = TermData {
            term,
            eq_class: ident.clone(),
            qi_dependencies: BTreeSet::new(),
            assignment: None,
            instantiations: Vec::new(),
        };
        self.terms.insert(ident, data);
        Ok(())
    }

    fn add_instantiation(&mut self, key: QIKey, inst: QuantInstantiation) -> RawResult<()> {
        if self.has_log_consistency_checks() {
            // Verify used equalities
            if let QuantInstantiationKind::NewMatch { used, .. } = &inst.kind {
                for u in used {
                    if let MatchedTerm::Equality(id1, id2) = u {
                        self.check_equality(id1, id2)?;
                    }
                }
            }
        }
        // Ignore solver instances.
        if !key.is_zero() {
            if self.has_log_consistency_checks() {
                inst.visit(&mut |id| self.check_ident(id))?;
            }
            let quantifier = inst.kind.quantifier();
            self.term_data_mut(quantifier)?.instantiations.push(key);
            self.instantiations.insert(key, inst);
        }
        Ok(())
    }

    fn start_instance(&mut self, key: QIKey, mut data: QuantInstantiationData) -> RawResult<()> {
        if data.generation.is_none() {
            // Set missing generation number.
            let gen = self
                .current_instances
                .last()
                .map(|(_, d)| d.generation)
                .unwrap_or(Some(0));
            data.generation = gen;
        }
        // Ident check.
        if self.has_log_consistency_checks() {
            data.visit(&mut |id| self.check_ident(id))?;
        }
        self.add_qi_dependency(&data.term, key)?;
        self.current_instances.push((key, data));
        Ok(())
    }

    fn end_instance(&mut self) -> RawResult<()> {
        let (key, data) = self
            .current_instances
            .pop()
            .ok_or(RawError::InvalidEndOfInstance)?;
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
            if self.config.display_qi_logs {
                self.log_instance(key)?;
            }
        }
        Ok(())
    }

    fn add_equality(&mut self, id0: Ident, eq: Equality) -> RawResult<()> {
        use Equality::*;

        if self.has_log_consistency_checks() {
            eq.visit(&mut |id| self.check_ident(id))?;
        }
        let id = self.get_equality_class(&id0)?;
        let raw_cid = match &eq {
            Root => {
                // id == *id0 is expected but not strictly guaranteed.
                return Ok(());
            }
            Literal(eid, cid) => {
                if self.has_log_consistency_checks()
                    && !self.check_literal_equality(eid, &id0, cid)?
                {
                    return Err(RawError::CannotProcessEquality(id0, eq));
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
                if self.has_log_consistency_checks() {
                    for (id1, id2) in eqs {
                        self.check_equality(id1, id2)?;
                    }
                    if !self.check_congruence_equality(eqs, &id0, cid)? {
                        return Err(RawError::CannotProcessEquality(id0, eq));
                    }
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

    fn attach_meaning(&mut self, id: Ident, m: Meaning) -> RawResult<()> {
        match self.term_mut(&id)? {
            Term::App { meaning, .. } => {
                *meaning = Some(m);
                Ok(())
            }
            _ => Err(RawError::CannotAttachMeaning(id)),
        }
    }

    fn attach_var_names(&mut self, id: Ident, names: Vec<VarName>) -> RawResult<()> {
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

    fn attach_enode(&mut self, id: Ident, generation: u64) -> RawResult<()> {
        // Ignore commands outside of [instance]..[end-of-instance].
        if !self.current_instances.is_empty() {
            let current_instance = self.current_instances.last_mut().unwrap();
            let key = current_instance.0;
            let data = &mut current_instance.1;
            if generation != data.generation.expect("Generation should be set") {
                return Err(RawError::InvalidEnodeGeneration);
            }
            data.enodes.push(id.clone());
            self.add_qi_dependency(&id, key)?;
        }
        Ok(())
    }

    fn tool_version(&mut self, _s1: String, _s2: String) -> RawResult<()> {
        Ok(())
    }

    fn begin_check(&mut self, _i: u64) -> RawResult<()> {
        Ok(())
    }

    fn assign(&mut self, lit: Literal, _s: String) -> RawResult<()> {
        if self.has_log_consistency_checks() {
            lit.visit(&mut |id| self.check_ident(id))?;
        }
        self.term_data_mut(&lit.id)?.assignment = Some(lit.sign);
        Ok(())
    }

    fn conflict(&mut self, lits: Vec<Literal>, _s: String) -> RawResult<()> {
        if self.has_log_consistency_checks() {
            lits.visit(&mut |id| self.check_ident(id))?;
        }
        Ok(())
    }

    fn push(&mut self, _i: u64) -> RawResult<()> {
        Ok(())
    }

    fn pop(&mut self, _i: u64, _j: u64) -> RawResult<()> {
        Ok(())
    }

    fn resolve_lit(&mut self, _i: u64, lit: Literal) -> RawResult<()> {
        if self.has_log_consistency_checks() {
            lit.visit(&mut |id| self.check_ident(id))?;
        }
        Ok(())
    }

    fn resolve_process(&mut self, lit: Literal) -> RawResult<()> {
        if self.has_log_consistency_checks() {
            lit.visit(&mut |id| self.check_ident(id))?;
        }
        Ok(())
    }
}
