// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Utilities for name resolution and renaming of bound symbols.

use crate::{
    concrete::*,
    rewriter::Rewriter,
    visitors::{Identifier, Index, Smt2Visitor},
};
use num::ToPrimitive;
use std::collections::{BTreeMap, BTreeSet};

/// A [`Rewriter`] implementation that converts old-style testers `is-Foo` into a proper indexed identifier `(_ is Foo)`.
#[derive(Debug, Default)]
pub struct TesterModernizer<V>(V);

impl<V> TesterModernizer<V> {
    pub fn new(visitor: V) -> Self {
        Self(visitor)
    }
}

impl<V, Error> Rewriter for TesterModernizer<V>
where
    V: Smt2Visitor<QualIdentifier = QualIdentifier, Symbol = Symbol, Error = Error>,
{
    type V = V;
    type Error = Error;

    fn visitor(&mut self) -> &mut V {
        &mut self.0
    }

    fn visit_simple_identifier(
        &mut self,
        value: Identifier<Symbol>,
    ) -> Result<QualIdentifier, Error> {
        let value = match value {
            Identifier::Simple { symbol } if symbol.0.starts_with("is-") => {
                let is = self.0.visit_bound_symbol("is".to_string())?;
                let name = self.0.visit_bound_symbol(symbol.0[3..].to_string())?;
                Identifier::Indexed {
                    symbol: is,
                    indices: vec![Index::Symbol(name)],
                }
            }
            v => v,
        };
        self.0.visit_simple_identifier(value)
    }
}

/// A [`Rewriter`] implementation that normalizes local symbols into `x0`, `x1`, etc.
/// * Normalization applies to all symbols disregarding their usage (datatype, sorts,
/// functions, variables, etc).
/// * "Global" symbols (those which don't resolve locally) are ignored.
#[derive(Debug, Default)]
pub struct SymbolNormalizer<V> {
    /// The underlying syntax visitor.
    visitor: V,
    /// Track the original name of local symbols.
    local_symbols: Vec<String>,
    /// Track symbols that were not resolved (thus ignored).
    global_symbols: BTreeSet<String>,
    /// Currently bound symbols.
    bound_symbols: BTreeMap<String, Vec<usize>>,
    /// Track (the size of) `local_symbols` and `bound_symbols` whenever a `(push)` command occurs.
    scopes: Vec<Scope>,
}

#[derive(Debug, Default)]
pub struct Scope {
    /// Number of local symbols.
    local: usize,
    /// Current number of bound symbols.
    bound: BTreeMap<String, usize>,
}

const SYMBOL_PREFIX: &str = "x";

impl<V> SymbolNormalizer<V> {
    pub fn new(visitor: V) -> Self {
        Self {
            visitor,
            local_symbols: Vec::new(),
            global_symbols: BTreeSet::new(),
            bound_symbols: BTreeMap::new(),
            scopes: Vec::new(),
        }
    }

    pub fn get_symbol(idx: usize) -> Symbol {
        Symbol(format!("{}{}", SYMBOL_PREFIX, idx))
    }

    fn parse_symbol(s: &Symbol) -> usize {
        str::parse(&s.0[SYMBOL_PREFIX.len()..]).expect("cannot parse symbol")
    }

    /// Initial names of all local symbols that were renamed.
    pub fn local_symbols(&self) -> impl IntoIterator<Item = &String> {
        &self.local_symbols
    }

    /// Symbols that failed to resolve locally (e.g. theory defined).
    pub fn global_symbols(&self) -> impl IntoIterator<Item = &String> {
        &self.global_symbols
    }

    fn push_scope(&mut self) {
        self.scopes.push(Scope {
            local: self.local_symbols.len(),
            bound: self
                .bound_symbols
                .iter()
                .map(|(k, v)| (k.to_string(), v.len()))
                .collect(),
        });
    }

    fn pop_scope(&mut self) {
        if let Some(scope) = self.scopes.pop() {
            self.local_symbols.truncate(scope.local);
            let symbols = std::mem::take(&mut self.bound_symbols);
            let symbols = symbols
                .into_iter()
                .filter_map(|(k, mut v)| match scope.bound.get(&k) {
                    Some(n) => {
                        v.truncate(*n);
                        Some((k, v))
                    }
                    None => None,
                })
                .collect();
            self.bound_symbols = symbols;
        }
    }
}

impl<V, Error> Rewriter for SymbolNormalizer<V>
where
    V: Smt2Visitor<Symbol = Symbol, Command = Command, Error = Error>,
{
    type V = V;
    type Error = Error;

    fn visitor(&mut self) -> &mut V {
        &mut self.visitor
    }

    fn visit_push(&mut self, level: crate::Numeral) -> Result<Command, Error> {
        for _ in 0..level.to_usize().expect("too many levels") {
            self.push_scope();
        }
        let value = self.visitor().visit_push(level)?;
        self.process_command(value)
    }

    fn visit_pop(&mut self, level: crate::Numeral) -> Result<Command, Error> {
        for _ in 0..level.to_usize().expect("too many levels") {
            self.pop_scope();
        }
        let value = self.visitor().visit_pop(level)?;
        self.process_command(value)
    }

    fn visit_reset(&mut self) -> Result<Command, Error> {
        self.local_symbols.clear();
        self.global_symbols.clear();
        self.bound_symbols.clear();
        self.scopes.clear();
        let value = self.visitor().visit_reset()?;
        self.process_command(value)
    }

    fn visit_bound_symbol(&mut self, value: String) -> Result<Symbol, Error> {
        let value = self
            .bound_symbols
            .get(&value)
            .map(|v| Self::get_symbol(*v.last().unwrap()))
            .unwrap_or_else(|| {
                self.global_symbols.insert(value.clone());
                Symbol(value)
            });
        self.process_symbol(value)
    }

    fn visit_fresh_symbol(&mut self, value: String) -> Result<Symbol, Error> {
        let s = Self::get_symbol(self.local_symbols.len());
        self.local_symbols.push(value);
        self.process_symbol(s)
    }

    fn bind_symbol(&mut self, symbol: &Symbol) {
        let i = Self::parse_symbol(symbol);
        let value = self.local_symbols[i].clone();
        self.bound_symbols.entry(value).or_default().push(i);
    }

    fn unbind_symbol(&mut self, symbol: &Symbol) {
        use std::collections::btree_map;
        let i = Self::parse_symbol(symbol);
        let value = self.local_symbols[i].clone();
        match self.bound_symbols.entry(value) {
            btree_map::Entry::Occupied(mut e) => {
                if let Some(scope) = self.scopes.last() {
                    if let Some(n) = scope.bound.get(&self.local_symbols[i]) {
                        // Never unbind names from the previous scope.
                        assert!(e.get().len() > *n);
                    }
                }
                // Check that we unbind the expected symbol.
                assert_eq!(e.get_mut().pop().unwrap(), i);
                if e.get().is_empty() {
                    e.remove_entry();
                }
            }
            _ => panic!("invalid entry"),
        }
    }
}

#[test]
fn test_testers() {
    use crate::{concrete, lexer::Lexer, parser::tests::parse_tokens};

    let value = parse_tokens(Lexer::new(&b"(assert (is-Foo 3))"[..])).unwrap();
    assert!(matches!(
        value,
        Command::Assert {
            term: Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple { .. }
                },
                ..
            }
        }
    ));
    let mut builder = concrete::SyntaxBuilder::default();
    assert_eq!(value, value.clone().accept(&mut builder).unwrap());
    // Visit with the TesterModernizer this time.
    let mut builder = TesterModernizer::<SyntaxBuilder>::default();
    assert!(matches!(
        value.accept(&mut builder).unwrap(),
        Command::Assert {
            term: Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Indexed { .. }
                },
                ..
            }
        }
    ));
}

#[test]
fn test_declare_datatypes_renaming() {
    use crate::{lexer::Lexer, parser::tests::parse_tokens};

    let value = parse_tokens(Lexer::new(&b"
(declare-datatypes (
    (Type 0)
    (TypeArray 0)
)(
    ((IntType) (VectorType (typeOfVectorType Type)) (StructType (nameOfStructType Name) (typesOfStructType TypeArray)))
    ((TypeArray (valueOfTypeArray (Array Int Type)) (lengthOfTypeArray Int)))
))"[..])).unwrap();
    assert!(matches!(value, Command::DeclareDatatypes { .. }));

    let value2 = parse_tokens(Lexer::new(
        &b"
(declare-datatypes (
    (x0 0)
    (x1 0)
)(
    ((x2) (x3 (x4 x0)) (x5 (x6 Name) (x7 x1)))
    ((x8 (x9 (Array Int x0)) (x10 Int)))
))"[..],
    ))
    .unwrap();
    assert!(matches!(value2, Command::DeclareDatatypes { .. }));
    let mut builder = SyntaxBuilder::default();
    assert_eq!(value, value.clone().accept(&mut builder).unwrap());

    let mut builder = SymbolNormalizer::<SyntaxBuilder>::default();
    assert_eq!(value2, value.accept(&mut builder).unwrap());
}

#[test]
fn test_symbol_renaming() {
    use crate::concrete::*;

    // (assert (let ((x (f x 2))) (= x 3)))
    let command = Command::Assert {
        term: Term::Let {
            var_bindings: vec![(
                Symbol("x".into()),
                Term::Application {
                    qual_identifier: QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("f".into()),
                        },
                    },
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("x".into()),
                            },
                        }),
                        Term::Constant(Constant::Numeral(num::BigUint::from(2u32))),
                    ],
                },
            )],
            term: Box::new(Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("=".into()),
                    },
                },
                arguments: vec![
                    Term::QualIdentifier(QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("x".into()),
                        },
                    }),
                    Term::Constant(Constant::Numeral(num::BigUint::from(3u32))),
                ],
            }),
        },
    };

    let mut builder = SymbolNormalizer::<SyntaxBuilder>::default();

    let command2 = command.accept(&mut builder).unwrap();
    let command3 = Command::Assert {
        term: Term::Let {
            var_bindings: vec![(
                Symbol("x0".into()),
                Term::Application {
                    qual_identifier: QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("f".into()),
                        },
                    },
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("x".into()),
                            },
                        }),
                        Term::Constant(Constant::Numeral(num::BigUint::from(2u32))),
                    ],
                },
            )],
            term: Box::new(Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("=".into()),
                    },
                },
                arguments: vec![
                    Term::QualIdentifier(QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("x0".into()),
                        },
                    }),
                    Term::Constant(Constant::Numeral(num::BigUint::from(3u32))),
                ],
            }),
        },
    };

    assert_eq!(command2, command3);
    assert_eq!(
        builder.local_symbols().into_iter().collect::<Vec<_>>(),
        vec!["x"]
    );
    assert_eq!(
        builder.global_symbols().into_iter().collect::<Vec<_>>(),
        vec!["=", "f", "x"]
    );
}
