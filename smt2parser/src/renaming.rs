// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Utilities for name resolution and renaming of bound symbols.

use crate::{
    concrete::*,
    rewriter::Rewriter,
    visitors::{Identifier, Index, Smt2Visitor, SymbolKind},
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
/// * Normalization applies to all locally resolved symbols.
/// * A different prefix is applied depending on the symbol kind (datatype, sorts,
/// functions, variables, etc).
/// * "Global" symbols (those which don't resolve locally) are ignored.
/// * Symbol names may be re-used after a `reset` or a `pop` command, but are otherwise
/// unique (disregarding the more limited lexical scoping of variables).
#[derive(Debug, Default)]
pub struct SymbolNormalizer<V> {
    /// The underlying syntax visitor.
    visitor: V,
    /// Original names of current local symbols, indexed by kind.
    current_local_symbols: BTreeMap<SymbolKind, Vec<String>>,
    /// Currently bound symbols.
    current_bound_symbols: BTreeMap<String, Vec<LocalSymbolRef>>,
    /// Support the scoping of symbols with `push` and `pop` commands.
    scopes: Vec<Scope>,
    /// Accumulate symbols that were not resolved (thus ignored).
    global_symbols: BTreeSet<String>,
    /// Track the maximal number of local variables simultaneously used, indexed per kind.
    max_local_symbols: BTreeMap<SymbolKind, usize>,
}

/// Reference to a local symbol.
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
struct LocalSymbolRef {
    kind: SymbolKind,
    index: usize,
}

/// Track the size of `current_local_symbols` and `current_bound_symbols` so that we can
/// backtrack later.
#[derive(Debug, Default)]
struct Scope {
    /// Number of local symbols index by kind.
    local: BTreeMap<SymbolKind, usize>,
    /// Current number of bound symbols.
    bound: BTreeMap<String, usize>,
}

impl<V> SymbolNormalizer<V> {
    pub fn new(visitor: V) -> Self {
        Self {
            visitor,
            current_local_symbols: BTreeMap::new(),
            current_bound_symbols: BTreeMap::new(),
            global_symbols: BTreeSet::new(),
            scopes: Vec::new(),
            max_local_symbols: BTreeMap::new(),
        }
    }

    fn get_symbol(r: LocalSymbolRef) -> Symbol {
        use SymbolKind::*;
        let prefix = match r.kind {
            Unknown => "?",
            Variable => "x",
            Constant => "k",
            Function => "f",
            Sort => "S",
            Datatype => "T",
            TypeVar => "X",
            Constructor => "c",
            Selector => "s",
        };
        Symbol(format!("{}{}", prefix, r.index))
    }

    fn parse_symbol(s: &Symbol) -> LocalSymbolRef {
        use SymbolKind::*;
        let kind = match &s.0[0..1] {
            "?" => Unknown,
            "x" => Variable,
            "k" => Constant,
            "f" => Function,
            "S" => Sort,
            "T" => Datatype,
            "X" => TypeVar,
            "c" => Constructor,
            "s" => Selector,
            _ => panic!("cannot parse symbol kind"),
        };
        let index = str::parse(&s.0[1..]).expect("cannot parse symbol index");
        LocalSymbolRef { kind, index }
    }

    /// Original names of the current local symbols.
    pub fn current_local_symbols(&self) -> &BTreeMap<SymbolKind, Vec<String>> {
        &self.current_local_symbols
    }

    /// Max number of the local symbols simulatenously used.
    pub fn max_local_symbols(&self) -> &BTreeMap<SymbolKind, usize> {
        &self.max_local_symbols
    }

    fn local_symbol_name(&self, r: LocalSymbolRef) -> String {
        self.current_local_symbols.get(&r.kind).unwrap()[r.index].to_string()
    }

    /// All symbol names that failed to be resolved locally at least once (e.g. theory defined symbols).
    pub fn global_symbols(&self) -> &BTreeSet<String> {
        &self.global_symbols
    }

    fn push_scope(&mut self) {
        self.scopes.push(Scope {
            local: self
                .current_local_symbols
                .iter()
                .map(|(k, v)| (*k, v.len()))
                .collect(),
            bound: self
                .current_bound_symbols
                .iter()
                .map(|(k, v)| (k.clone(), v.len()))
                .collect(),
        });
    }

    fn truncate_vectors<T: Ord, S>(sizes: &BTreeMap<T, usize>, vectors: &mut BTreeMap<T, Vec<S>>) {
        let vs = std::mem::take(vectors);
        let vs = vs
            .into_iter()
            .filter_map(|(k, mut v)| match sizes.get(&k) {
                Some(n) => {
                    v.truncate(*n);
                    Some((k, v))
                }
                None => None,
            })
            .collect();
        *vectors = vs;
    }

    fn pop_scope(&mut self) {
        if let Some(scope) = self.scopes.pop() {
            Self::truncate_vectors(&scope.local, &mut self.current_local_symbols);
            Self::truncate_vectors(&scope.bound, &mut self.current_bound_symbols);
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
        self.current_local_symbols.clear();
        self.current_bound_symbols.clear();
        self.scopes.clear();
        let value = self.visitor().visit_reset()?;
        self.process_command(value)
    }

    fn visit_bound_symbol(&mut self, value: String) -> Result<Symbol, Error> {
        let value = self
            .current_bound_symbols
            .get(&value)
            .map(|v| Self::get_symbol(*v.last().unwrap()))
            .unwrap_or_else(|| {
                self.global_symbols.insert(value.clone());
                Symbol(value)
            });
        self.process_symbol(value)
    }

    fn visit_fresh_symbol(&mut self, value: String, kind: SymbolKind) -> Result<Symbol, Error> {
        let r = LocalSymbolRef {
            kind,
            index: match self.current_local_symbols.get(&kind) {
                Some(v) => v.len(),
                None => 0,
            },
        };
        self.current_local_symbols
            .entry(kind)
            .or_default()
            .push(value);
        let n = self.max_local_symbols.entry(kind).or_default();
        *n = std::cmp::max(*n, r.index + 1);
        self.process_symbol(Self::get_symbol(r))
    }

    fn bind_symbol(&mut self, symbol: &Symbol) {
        let r = Self::parse_symbol(symbol);
        let name = self.local_symbol_name(r);
        self.current_bound_symbols.entry(name).or_default().push(r);
    }

    fn unbind_symbol(&mut self, symbol: &Symbol) {
        use std::collections::btree_map;
        let r = Self::parse_symbol(symbol);
        let name = self.local_symbol_name(r);
        match self.current_bound_symbols.entry(name.clone()) {
            btree_map::Entry::Occupied(mut e) => {
                if let Some(scope) = self.scopes.last() {
                    if let Some(n) = scope.bound.get(&name) {
                        // Never unbind names from the previous scope.
                        assert!(e.get().len() > *n);
                    }
                }
                // Check that we unbind the expected symbol.
                assert_eq!(e.get_mut().pop().unwrap(), r);
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
    (T0 0)
    (T1 0)
)(
    ((c0) (c1 (s0 T0)) (c2 (s1 Name) (s2 T1)))
    ((c3 (s3 (Array Int T0)) (s4 Int)))
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
        builder
            .current_local_symbols()
            .into_iter()
            .collect::<Vec<_>>(),
        vec![(&SymbolKind::Variable, &vec!["x".to_string()])]
    );
    assert_eq!(
        builder.global_symbols().into_iter().collect::<Vec<_>>(),
        vec!["=", "f", "x"]
    );
}
