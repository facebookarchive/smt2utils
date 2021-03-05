// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::error::{Error, RawError};
use smt2parser::concrete::Symbol;

/// An identifier such as `#45` or `foo#23`.
/// * Namespace-only identifiers such
/// as `foo#` are also allowed for Z3 primitive objects.
/// * `#` is used for true and false literals.
/// * An implicit version number is added to disambiguate identifiers
/// re-used by Z3.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Default, Hash)]
pub struct Ident {
    pub namespace: Option<String>,
    pub id: Option<u64>,
    pub version: usize,
}

/// The hexadecimal index of a quantifier instantiation (QI).
#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Clone, Copy)]
pub struct QIKey(pub(crate) u64);

/// Concrete representation of a term.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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
        property: Ident,
    },
}

/// A literal (i.e. a signed identifier).
#[derive(Clone, Debug)]
pub struct Literal {
    pub id: Ident,
    pub sign: bool,
}

/// Additional data attached to a term (e.g. integer values).
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Meaning {
    pub theory: String,
    pub sexp: String,
}

/// A parameter declaration.
#[derive(Eq, PartialEq, Clone, Debug, Hash)]
pub struct VarName {
    pub name: Symbol,
    pub sort: Symbol,
}

/// Quantifier instantiation (case-specific data).
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

impl QuantInstantiationKind {
    /// Id of the quantifier term.
    pub fn quantifier(&self) -> &Ident {
        use QuantInstantiationKind::*;
        match self {
            Discovered { quantifier, .. } | NewMatch { quantifier, .. } => quantifier,
        }
    }
}

/// Quantifier instantiation (shared data).
#[derive(Clone, Debug)]
pub struct QuantInstantiationData {
    pub generation: Option<u64>,
    pub term: Ident,
    pub enodes: Vec<Ident>,
}

/// Quantifier instantiation.
#[derive(Clone, Debug)]
pub struct QuantInstantiation {
    pub kind: QuantInstantiationKind,
    pub data: Option<QuantInstantiationData>,
}

/// Description of a term matching a trigger in `NewMatch`.
#[derive(Eq, PartialEq, Clone, Debug)]
pub enum MatchedTerm {
    /// A term 'T' matching a QI trigger.
    Trigger(Ident),
    /// A subterm of such term 'T' equal to a subterm of the QI trigger.
    Equality(Ident, Ident),
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

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ns = match &self.namespace {
            Some(x) => x,
            None => "",
        };
        let id = match self.id {
            Some(id) => format!("{}", id),
            None => String::new(),
        };
        let version = match self.version {
            0 => String::new(),
            v => format!("!{}", v),
        };
        write!(f, "{}#{}{}", ns, id, version)
    }
}

impl QIKey {
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

/// Visitor trait for syntactic constructs.
pub trait Visitor<'a, F, E> {
    fn visit(&'a self, f: &mut F) -> Result<(), E>;
}

impl<'a, T, F, E> Visitor<'a, F, E> for Vec<T>
where
    T: Visitor<'a, F, E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
        for x in self {
            x.visit(f)?;
        }
        Ok(())
    }
}

impl<'a, T, F, E> Visitor<'a, F, E> for Option<T>
where
    T: Visitor<'a, F, E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
        if let Some(x) = self {
            x.visit(f)?;
        }
        Ok(())
    }
}

impl<'a, T1, T2, F, E> Visitor<'a, F, E> for (T1, T2)
where
    T1: Visitor<'a, F, E>,
    T2: Visitor<'a, F, E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
        self.0.visit(f)?;
        self.1.visit(f)
    }
}

impl<'a, F, E> Visitor<'a, F, E> for Ident
where
    F: FnMut(&'a Ident) -> Result<(), E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
        f(self)
    }
}

impl<'a, F, E> Visitor<'a, F, E> for Literal
where
    F: FnMut(&'a Ident) -> Result<(), E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
        f(&self.id)
    }
}

impl<'a, F, E> Visitor<'a, F, E> for Term
where
    F: FnMut(&'a Ident) -> Result<(), E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
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

impl<'a, F, E> Visitor<'a, F, E> for QuantInstantiationKind
where
    F: FnMut(&'a Ident) -> Result<(), E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
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

impl<'a, F, E> Visitor<'a, F, E> for QuantInstantiation
where
    F: FnMut(&'a Ident) -> Result<(), E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
        self.kind.visit(f)?;
        self.data.visit(f)
    }
}

impl<'a, F, E> Visitor<'a, F, E> for MatchedTerm
where
    F: FnMut(&'a Ident) -> Result<(), E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
        use MatchedTerm::*;
        match self {
            Trigger(id) => f(id),
            Equality(id1, id2) => {
                f(id1)?;
                f(id2)
            }
        }
    }
}

impl<'a, F, E> Visitor<'a, F, E> for Equality
where
    F: FnMut(&'a Ident) -> Result<(), E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
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

impl<'a, F, E> Visitor<'a, F, E> for QuantInstantiationData
where
    F: FnMut(&'a Ident) -> Result<(), E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
        self.term.visit(f)?;
        self.enodes.visit(f)
    }
}

impl std::str::FromStr for Ident {
    type Err = Error;

    fn from_str(value: &str) -> Result<Self, Error> {
        match value.find('!') {
            None => {
                let mut lexer = crate::lexer::Lexer::new(None, value.as_ref());
                lexer.read_ident().map_err(|e| lexer.make_error(e))
            }
            Some(pos) => {
                // The extended syntax `foo#4!7` is meant to be used for testing and debugging.
                let mut lexer = crate::lexer::Lexer::new(None, &value.as_bytes()[0..pos]);
                let mut id = lexer.read_ident().map_err(|e| lexer.make_error(e))?;
                id.version = value[pos + 1..]
                    .parse()
                    .map_err(|e| lexer.make_error(RawError::InvalidInteger(e)))?;
                Ok(id)
            }
        }
    }
}

impl std::str::FromStr for VarName {
    type Err = Error;

    fn from_str(value: &str) -> Result<Self, Error> {
        let mut lexer = crate::lexer::Lexer::new(None, value.as_ref());
        lexer.read_var_name().map_err(|e| lexer.make_error(e))
    }
}
