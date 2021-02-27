// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::error::Result;
use smt2parser::concrete::Symbol;

/// An identifier such as `#45` or `foo#23`. Namespace-only identifiers such
/// as `foo#` are also allowed for Z3 primitive objects.
/// `#` is used for true and false literals.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Debug, Default)]
pub struct Ident {
    pub namespace: Option<String>,
    pub id: Option<u64>,
}

/// Concrete representation of a term.
#[derive(Debug, Clone)]
pub enum Term {
    App {
        name: String,
        args: Vec<Ident>,
        meaning: Option<Meaning>,
    },
    Var {
        index: u64,
    },
    Quant {
        name: String,
        params: usize,
        triggers: Vec<Ident>,
        body: Ident,
        var_names: Option<Vec<VarName>>,
    },
    Lambda {
        name: String,
        params: u64,
        triggers: Vec<Ident>,
        body: Ident,
    },
    Proof {
        name: String,
        args: Vec<Ident>,
    },
}

/// A literal (i.e. a signed identifier).
#[derive(Clone, Debug)]
pub struct Literal {
    pub id: Ident,
    pub sign: bool,
}

/// Additional data attached to a term (e.g. integer values).
#[derive(Clone, Debug)]
pub struct Meaning {
    pub theory: String,
    pub sexp: String,
}

/// A parameter declaration.
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct VarName {
    pub name: Symbol,
    pub sort: Symbol,
}

/// Quantifier instantiation (preambule).
#[derive(Clone, Debug)]
pub enum QuantInstantiationKind {
    Discovered {
        method: String,
        quantifier: Ident,
        terms: Vec<Ident>,
        blame: Vec<Ident>,
    },
    NewMatch {
        quantifier: Ident,
        trigger: Ident,
        terms: Vec<Ident>,
        used: Vec<MatchedTerm>,
    },
}

/// Quantifier instantiation (reminder).
#[derive(Clone, Debug)]
pub struct QuantInstantiationData {
    pub generation: u64,
    pub term: Ident,
    pub enodes: Vec<Ident>,
}

/// Quantifier instantiation (all parts).
#[derive(Clone, Debug)]
pub struct QuantInstantiation {
    pub kind: QuantInstantiationKind,
    pub data: Option<QuantInstantiationData>,
}

/// Description of a term matching a trigger in `NewMatch`.
#[derive(Eq, PartialEq, Clone, Debug)]
pub enum MatchedTerm {
    RootPattern(Ident),
    SubPattern(Ident, Ident),
}

/// Description of an E-matching step.
#[derive(Eq, PartialEq, Clone, Debug)]
pub enum Equality {
    Root,
    Literal(Ident, Ident),
    Congruence(Vec<(Ident, Ident)>, Ident),
    Theory(String, Ident),
}

impl Ident {
    /// Whether an identifier is the special empty value.
    pub fn is_empty(&self) -> bool {
        self.namespace.is_none() && self.id.is_none()
    }
}

/// Visitor trait for syntactic constructs.
pub trait Visitor<'a, F> {
    fn visit(&'a self, f: &mut F) -> Result<()>;
}

impl<'a, T, F> Visitor<'a, F> for Vec<T>
where
    T: Visitor<'a, F>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        for x in self {
            x.visit(f)?;
        }
        Ok(())
    }
}

impl<'a, T, F> Visitor<'a, F> for Option<T>
where
    T: Visitor<'a, F>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        if let Some(x) = self {
            x.visit(f)?;
        }
        Ok(())
    }
}

impl<'a, T1, T2, F> Visitor<'a, F> for (T1, T2)
where
    T1: Visitor<'a, F>,
    T2: Visitor<'a, F>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        self.0.visit(f)?;
        self.1.visit(f)
    }
}

impl<'a, F> Visitor<'a, F> for Ident
where
    F: FnMut(&'a Ident) -> Result<()>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        f(self)
    }
}

impl<'a, F> Visitor<'a, F> for Literal
where
    F: FnMut(&'a Ident) -> Result<()>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        f(&self.id)
    }
}

impl<'a, F> Visitor<'a, F> for Term
where
    F: FnMut(&'a Ident) -> Result<()>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        use Term::*;
        match self {
            App { args, .. } => args.visit(f),
            Var { .. } => Ok(()),
            Quant { triggers, body, .. } => {
                triggers.visit(f)?;
                f(body)
            }
            Lambda { triggers, body, .. } => {
                triggers.visit(f)?;
                f(body)
            }
            Proof { args, .. } => args.visit(f),
        }
    }
}

impl<'a, F> Visitor<'a, F> for QuantInstantiationKind
where
    F: FnMut(&'a Ident) -> Result<()>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        use QuantInstantiationKind::*;
        match self {
            Discovered { terms, blame, .. } => {
                terms.visit(f)?;
                blame.visit(f)
            }
            NewMatch { terms, used, .. } => {
                terms.visit(f)?;
                used.visit(f)
            }
        }
    }
}

impl<'a, F> Visitor<'a, F> for QuantInstantiation
where
    F: FnMut(&'a Ident) -> Result<()>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        self.kind.visit(f)?;
        self.data.visit(f)
    }
}

impl<'a, F> Visitor<'a, F> for MatchedTerm
where
    F: FnMut(&'a Ident) -> Result<()>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        use MatchedTerm::*;
        match self {
            RootPattern(id) => f(id),
            SubPattern(id1, id2) => {
                f(id1)?;
                f(id2)
            }
        }
    }
}

impl<'a, F> Visitor<'a, F> for Equality
where
    F: FnMut(&'a Ident) -> Result<()>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        use Equality::*;
        match self {
            Root => Ok(()),
            Literal(id1, id2) => {
                f(id1)?;
                f(id2)
            }
            Congruence(ids, id) => {
                ids.visit(f)?;
                f(id)
            }
            Theory(_, id) => f(id),
        }
    }
}

impl<'a, F> Visitor<'a, F> for QuantInstantiationData
where
    F: FnMut(&'a Ident) -> Result<()>,
{
    fn visit(&'a self, f: &mut F) -> Result<()> {
        self.term.visit(f)?;
        self.enodes.visit(f)
    }
}
