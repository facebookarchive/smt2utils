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
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Copy)]
pub struct QiKey {
    pub key: u64,
    pub version: usize,
}

/// Concrete representation of a term.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Term {
    /// Application of a symbol on top of other term(s).
    App {
        name: String,
        args: Vec<Ident>,
        meaning: Option<Meaning>,
    },
    /// Bound variable, used in the body a quantified expression or a lambda.
    Var { index: u64 },
    /// Quantified expression (either universal or existential).
    Quant {
        name: String,
        params: usize,
        triggers: Vec<Ident>,
        body: Ident,
        var_names: Option<Vec<VarName>>,
    },
    /// Lambda.
    Lambda {
        name: String,
        params: u64,
        triggers: Vec<Ident>,
        body: Ident,
    },
    /// Proof term.
    Proof {
        name: String,
        args: Vec<Ident>,
        property: Ident,
    },
    /// Builtin (typically used to refer to a theory or for true/false literals).
    Builtin { name: Option<String> },
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

/// A quantifier instantiation as declared by `[inst-discovered]` or `[new-match]`.
#[derive(Clone, Debug)]
pub enum QiFrame {
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

impl Term {
    pub fn name(&self) -> Option<&str> {
        use Term::*;
        match self {
            App { name, .. }
            | Quant { name, .. }
            | Lambda { name, .. }
            | Proof { name, .. }
            | Builtin { name: Some(name) } => Some(name.as_str()),
            Builtin { name: None } | Var { .. } => None,
        }
    }

    pub fn matches_equality(&self) -> Option<[Ident; 2]> {
        match self {
            Term::App { name, args, .. } if name.as_str() == "=" && args.len() == 2 => {
                Some([args[0].clone(), args[1].clone()])
            }
            _ => None,
        }
    }
}

impl QiFrame {
    /// Id of the quantifier term.
    pub fn quantifier(&self) -> &Ident {
        use QiFrame::*;
        match self {
            Discovered { quantifier, .. } | NewMatch { quantifier, .. } => quantifier,
        }
    }
}

/// Data specific to an instance of a quantifier instantiation (i.e. gathered
/// between `[instance]` and `[end-instance]`).
#[derive(Clone, Debug)]
pub struct QiInstance {
    pub generation: Option<u64>,
    pub term: Option<Ident>,
    pub enodes: Vec<Ident>,
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
    Axiom(Ident),
    Unknown(Ident),
}

impl Ident {
    /// Whether an identifier is the special builtin value.
    pub fn is_builtin(&self) -> bool {
        self.id.is_none()
    }

    pub fn previous_version(&self) -> Option<Self> {
        let mut id = self.clone();
        id.version = self.version.checked_sub(1)?;
        Some(id)
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

impl std::fmt::Debug for QiKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let version = match self.version {
            0 => String::new(),
            v => format!("!{}", v),
        };
        write!(f, "{:#x}{}", self.key, version)
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
            Builtin { .. } => Ok(()),
        }
    }
}

impl<'a, F, E> Visitor<'a, F, E> for QiFrame
where
    F: FnMut(&'a Ident) -> Result<(), E>,
{
    fn visit(&'a self, f: &mut F) -> Result<(), E> {
        use QiFrame::*;
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
            Theory(_, id) | Axiom(id) | Unknown(id) => f(id),
        }
    }
}

impl<'a, F, E> Visitor<'a, F, E> for QiInstance
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

impl std::str::FromStr for QiKey {
    type Err = std::num::ParseIntError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value.find('!') {
            None => {
                let key = u64::from_str_radix(value.trim_start_matches("0x"), 16)?;
                Ok(QiKey { key, version: 0 })
            }
            Some(pos) => {
                // The extended syntax `0x123!7` is meant to be used only for testing and debugging.
                let key = u64::from_str_radix(value.trim_start_matches("0x"), 16)?;
                let version = value[pos + 1..].parse()?;
                Ok(QiKey { key, version })
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
