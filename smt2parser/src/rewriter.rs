// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Rewriting of a concrete syntax trees

use crate::{
    visitors::{
        AttributeValue, CommandVisitor, ConstantVisitor, DatatypeDec, FunctionDec, Identifier,
        KeywordVisitor, QualIdentifierVisitor, SExprVisitor, Smt2Visitor, SortVisitor,
        SymbolVisitor, TermVisitor,
    },
    Binary, Decimal, Hexadecimal, Numeral,
};

/// Combine an SMT2 visitor with functions to rewrite intermediate values
/// of a given type.
pub struct Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8> {
    visitor: V,
    f_constant: F1,
    f_symbol: F2,
    f_keyword: F3,
    f_s_expr: F4,
    f_sort: F5,
    f_qual_identifier: F6,
    f_term: F7,
    f_command: F8,
}

impl<V, F1, F2, F3, F4, F5, F6, F7, F8> ConstantVisitor
    for Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8>
where
    V: ConstantVisitor,
    F1: FnMut(V::T) -> V::T,
{
    type T = V::T;

    fn visit_numeral_constant(&mut self, value: Numeral) -> Self::T {
        let value = self.visitor.visit_numeral_constant(value);
        (self.f_constant)(value)
    }
    fn visit_decimal_constant(&mut self, value: Decimal) -> Self::T {
        let value = self.visitor.visit_decimal_constant(value);
        (self.f_constant)(value)
    }
    fn visit_hexadecimal_constant(&mut self, value: Hexadecimal) -> Self::T {
        let value = self.visitor.visit_hexadecimal_constant(value);
        (self.f_constant)(value)
    }
    fn visit_binary_constant(&mut self, value: Binary) -> Self::T {
        let value = self.visitor.visit_binary_constant(value);
        (self.f_constant)(value)
    }
    fn visit_string_constant(&mut self, value: String) -> Self::T {
        let value = self.visitor.visit_string_constant(value);
        (self.f_constant)(value)
    }
}

impl<V, F1, F2, F3, F4, F5, F6, F7, F8> SymbolVisitor
    for Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8>
where
    V: SymbolVisitor,
    F2: FnMut(V::T) -> V::T,
{
    type T = V::T;

    fn visit_symbol(&mut self, value: String) -> Self::T {
        let value = self.visitor.visit_symbol(value);
        (self.f_symbol)(value)
    }
}

impl<V, F1, F2, F3, F4, F5, F6, F7, F8> KeywordVisitor
    for Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8>
where
    V: KeywordVisitor,
    F3: FnMut(V::T) -> V::T,
{
    type T = V::T;

    fn visit_keyword(&mut self, value: String) -> Self::T {
        let value = self.visitor.visit_keyword(value);
        (self.f_keyword)(value)
    }
}

impl<V, Constant, Symbol, Keyword, F1, F2, F3, F4, F5, F6, F7, F8>
    SExprVisitor<Constant, Symbol, Keyword> for Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8>
where
    V: SExprVisitor<Constant, Symbol, Keyword>,
    F4: FnMut(V::T) -> V::T,
{
    type T = V::T;

    fn visit_constant_s_expr(&mut self, value: Constant) -> Self::T {
        let value = self.visitor.visit_constant_s_expr(value);
        (self.f_s_expr)(value)
    }

    fn visit_symbol_s_expr(&mut self, value: Symbol) -> Self::T {
        let value = self.visitor.visit_symbol_s_expr(value);
        (self.f_s_expr)(value)
    }

    fn visit_keyword_s_expr(&mut self, value: Keyword) -> Self::T {
        let value = self.visitor.visit_keyword_s_expr(value);
        (self.f_s_expr)(value)
    }

    fn visit_application_s_expr(&mut self, values: Vec<Self::T>) -> Self::T {
        let value = self.visitor.visit_application_s_expr(values);
        (self.f_s_expr)(value)
    }
}

impl<V, Symbol, F1, F2, F3, F4, F5, F6, F7, F8> SortVisitor<Symbol>
    for Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8>
where
    V: SortVisitor<Symbol>,
    F5: FnMut(V::T) -> V::T,
{
    type T = V::T;

    fn visit_simple_sort(&mut self, identifier: Identifier<Symbol>) -> Self::T {
        let value = self.visitor.visit_simple_sort(identifier);
        (self.f_sort)(value)
    }

    fn visit_parameterized_sort(
        &mut self,
        identifier: Identifier<Symbol>,
        parameters: Vec<Self::T>,
    ) -> Self::T {
        let value = self
            .visitor
            .visit_parameterized_sort(identifier, parameters);
        (self.f_sort)(value)
    }
}

impl<V, Identifier, Sort, F1, F2, F3, F4, F5, F6, F7, F8> QualIdentifierVisitor<Identifier, Sort>
    for Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8>
where
    V: QualIdentifierVisitor<Identifier, Sort>,
    F6: FnMut(V::T) -> V::T,
{
    type T = V::T;

    fn visit_simple_identifier(&mut self, identifier: Identifier) -> Self::T {
        let value = self.visitor.visit_simple_identifier(identifier);
        (self.f_qual_identifier)(value)
    }

    fn visit_sorted_identifier(&mut self, identifier: Identifier, sort: Sort) -> Self::T {
        let value = self.visitor.visit_sorted_identifier(identifier, sort);
        (self.f_qual_identifier)(value)
    }
}

impl<V, Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort, F1, F2, F3, F4, F5, F6, F7, F8>
    TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort>
    for Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8>
where
    V: TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort>,
    F7: FnMut(V::T) -> V::T,
{
    type T = V::T;

    fn visit_constant(&mut self, constant: Constant) -> Self::T {
        let value = self.visitor.visit_constant(constant);
        (self.f_term)(value)
    }

    fn visit_qual_identifier(&mut self, qual_identifier: QualIdentifier) -> Self::T {
        let value = self.visitor.visit_qual_identifier(qual_identifier);
        (self.f_term)(value)
    }

    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Self::T {
        let value = self.visitor.visit_application(qual_identifier, arguments);
        (self.f_term)(value)
    }

    fn visit_let(&mut self, var_bindings: Vec<(Symbol, Self::T)>, term: Self::T) -> Self::T {
        let value = self.visitor.visit_let(var_bindings, term);
        (self.f_term)(value)
    }

    fn visit_forall(&mut self, vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T {
        let value = self.visitor.visit_forall(vars, term);
        (self.f_term)(value)
    }

    fn visit_exists(&mut self, vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T {
        let value = self.visitor.visit_exists(vars, term);
        (self.f_term)(value)
    }

    fn visit_match(&mut self, term: Self::T, cases: Vec<(Vec<Symbol>, Self::T)>) -> Self::T {
        let value = self.visitor.visit_match(term, cases);
        (self.f_term)(value)
    }

    fn visit_attributes(
        &mut self,
        term: Self::T,
        attributes: Vec<(Keyword, AttributeValue<Constant, Symbol, SExpr>)>,
    ) -> Self::T {
        let value = self.visitor.visit_attributes(term, attributes);
        (self.f_term)(value)
    }
}

impl<V, Term, Symbol, Sort, Keyword, Constant, SExpr, F1, F2, F3, F4, F5, F6, F7, F8>
    CommandVisitor<Term, Symbol, Sort, Keyword, Constant, SExpr>
    for Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8>
where
    V: CommandVisitor<Term, Symbol, Sort, Keyword, Constant, SExpr>,
    F8: FnMut(V::T) -> V::T,
{
    type T = V::T;

    fn visit_assert(&mut self, term: Term) -> Self::T {
        let value = self.visitor.visit_assert(term);
        (self.f_command)(value)
    }

    fn visit_check_sat(&mut self) -> Self::T {
        let value = self.visitor.visit_check_sat();
        (self.f_command)(value)
    }

    fn visit_check_sat_assuming(&mut self, literals: Vec<(Symbol, bool)>) -> Self::T {
        let value = self.visitor.visit_check_sat_assuming(literals);
        (self.f_command)(value)
    }

    fn visit_declare_const(&mut self, symbol: Symbol, sort: Sort) -> Self::T {
        let value = self.visitor.visit_declare_const(symbol, sort);
        (self.f_command)(value)
    }

    fn visit_declare_datatype(
        &mut self,
        symbol: Symbol,
        datatype: DatatypeDec<Symbol, Sort>,
    ) -> Self::T {
        let value = self.visitor.visit_declare_datatype(symbol, datatype);
        (self.f_command)(value)
    }

    fn visit_declare_datatypes(
        &mut self,
        datatypes: Vec<(Symbol, Numeral, DatatypeDec<Symbol, Sort>)>,
    ) -> Self::T {
        let value = self.visitor.visit_declare_datatypes(datatypes);
        (self.f_command)(value)
    }

    fn visit_declare_fun(&mut self, symbol: Symbol, parameters: Vec<Sort>, sort: Sort) -> Self::T {
        let value = self.visitor.visit_declare_fun(symbol, parameters, sort);
        (self.f_command)(value)
    }

    fn visit_declare_sort(&mut self, symbol: Symbol, arity: Numeral) -> Self::T {
        let value = self.visitor.visit_declare_sort(symbol, arity);
        (self.f_command)(value)
    }

    fn visit_define_fun(&mut self, sig: FunctionDec<Symbol, Sort>, term: Term) -> Self::T {
        let value = self.visitor.visit_define_fun(sig, term);
        (self.f_command)(value)
    }

    fn visit_define_fun_rec(&mut self, sig: FunctionDec<Symbol, Sort>, term: Term) -> Self::T {
        let value = self.visitor.visit_define_fun_rec(sig, term);
        (self.f_command)(value)
    }

    fn visit_define_funs_rec(&mut self, funs: Vec<(FunctionDec<Symbol, Sort>, Term)>) -> Self::T {
        let value = self.visitor.visit_define_funs_rec(funs);
        (self.f_command)(value)
    }

    fn visit_define_sort(
        &mut self,
        symbol: Symbol,
        parameters: Vec<Symbol>,
        sort: Sort,
    ) -> Self::T {
        let value = self.visitor.visit_define_sort(symbol, parameters, sort);
        (self.f_command)(value)
    }

    fn visit_echo(&mut self, message: String) -> Self::T {
        let value = self.visitor.visit_echo(message);
        (self.f_command)(value)
    }

    fn visit_exit(&mut self) -> Self::T {
        let value = self.visitor.visit_exit();
        (self.f_command)(value)
    }

    fn visit_get_assertions(&mut self) -> Self::T {
        let value = self.visitor.visit_get_assertions();
        (self.f_command)(value)
    }

    fn visit_get_assignment(&mut self) -> Self::T {
        let value = self.visitor.visit_get_assignment();
        (self.f_command)(value)
    }

    fn visit_get_info(&mut self, flag: Keyword) -> Self::T {
        let value = self.visitor.visit_get_info(flag);
        (self.f_command)(value)
    }

    fn visit_get_model(&mut self) -> Self::T {
        let value = self.visitor.visit_get_model();
        (self.f_command)(value)
    }

    fn visit_get_option(&mut self, keyword: Keyword) -> Self::T {
        let value = self.visitor.visit_get_option(keyword);
        (self.f_command)(value)
    }

    fn visit_get_proof(&mut self) -> Self::T {
        let value = self.visitor.visit_get_proof();
        (self.f_command)(value)
    }

    fn visit_get_unsat_assumptions(&mut self) -> Self::T {
        let value = self.visitor.visit_get_unsat_assumptions();
        (self.f_command)(value)
    }

    fn visit_get_unsat_core(&mut self) -> Self::T {
        let value = self.visitor.visit_get_unsat_core();
        (self.f_command)(value)
    }

    fn visit_get_value(&mut self, terms: Vec<Term>) -> Self::T {
        let value = self.visitor.visit_get_value(terms);
        (self.f_command)(value)
    }

    fn visit_pop(&mut self, level: Numeral) -> Self::T {
        let value = self.visitor.visit_pop(level);
        (self.f_command)(value)
    }

    fn visit_push(&mut self, level: Numeral) -> Self::T {
        let value = self.visitor.visit_push(level);
        (self.f_command)(value)
    }

    fn visit_reset(&mut self) -> Self::T {
        let value = self.visitor.visit_reset();
        (self.f_command)(value)
    }

    fn visit_reset_assertions(&mut self) -> Self::T {
        let value = self.visitor.visit_reset_assertions();
        (self.f_command)(value)
    }

    fn visit_set_info(
        &mut self,
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    ) -> Self::T {
        let value = self.visitor.visit_set_info(keyword, value);
        (self.f_command)(value)
    }

    fn visit_set_logic(&mut self, symbol: Symbol) -> Self::T {
        let value = self.visitor.visit_set_logic(symbol);
        (self.f_command)(value)
    }

    fn visit_set_option(
        &mut self,
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    ) -> Self::T {
        let value = self.visitor.visit_set_option(keyword, value);
        (self.f_command)(value)
    }
}

impl<V, F1, F2, F3, F4, F5, F6, F7, F8> Smt2Visitor for Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8>
where
    V: Smt2Visitor,
    F1: FnMut(V::Constant) -> V::Constant,
    F2: FnMut(V::Symbol) -> V::Symbol,
    F3: FnMut(V::Keyword) -> V::Keyword,
    F4: FnMut(V::SExpr) -> V::SExpr,
    F5: FnMut(V::Sort) -> V::Sort,
    F6: FnMut(V::QualIdentifier) -> V::QualIdentifier,
    F7: FnMut(V::Term) -> V::Term,
    F8: FnMut(V::Command) -> V::Command,
{
    type Constant = V::Constant;
    type QualIdentifier = V::QualIdentifier;
    type Keyword = V::Keyword;
    type Sort = V::Sort;
    type SExpr = V::SExpr;
    type Symbol = V::Symbol;
    type Term = V::Term;
    type Command = V::Command;
}

impl<V, F1, F2, F3, F4, F5, F6, F7, F8> Rewriter<V, F1, F2, F3, F4, F5, F6, F7, F8> {
    pub fn into_inner(self) -> V {
        self.visitor
    }
}

fn identity<T>(x: T) -> T {
    x
}

type Id<T> = fn(T) -> T;

/// Extend visitors with methods to create a `Rewriter`.
pub trait Smt2VisitorExt: Smt2Visitor + Sized {
    fn fix_constants_with<F>(
        self,
        f_constant: F,
    ) -> Rewriter<
        Self,
        F,
        Id<Self::Symbol>,
        Id<Self::Keyword>,
        Id<Self::SExpr>,
        Id<Self::Sort>,
        Id<Self::QualIdentifier>,
        Id<Self::Term>,
        Id<Self::Command>,
    > {
        Rewriter {
            visitor: self,
            f_constant,
            f_symbol: identity,
            f_keyword: identity,
            f_s_expr: identity,
            f_sort: identity,
            f_qual_identifier: identity,
            f_term: identity,
            f_command: identity,
        }
    }

    fn fix_symbols_with<F>(
        self,
        f_symbol: F,
    ) -> Rewriter<
        Self,
        Id<Self::Constant>,
        F,
        Id<Self::Keyword>,
        Id<Self::SExpr>,
        Id<Self::Sort>,
        Id<Self::QualIdentifier>,
        Id<Self::Term>,
        Id<Self::Command>,
    > {
        Rewriter {
            visitor: self,
            f_constant: identity,
            f_symbol,
            f_keyword: identity,
            f_s_expr: identity,
            f_sort: identity,
            f_qual_identifier: identity,
            f_term: identity,
            f_command: identity,
        }
    }

    fn fix_keywords_with<F>(
        self,
        f_keyword: F,
    ) -> Rewriter<
        Self,
        Id<Self::Constant>,
        Id<Self::Symbol>,
        F,
        Id<Self::SExpr>,
        Id<Self::Sort>,
        Id<Self::QualIdentifier>,
        Id<Self::Term>,
        Id<Self::Command>,
    > {
        Rewriter {
            visitor: self,
            f_constant: identity,
            f_symbol: identity,
            f_keyword,
            f_s_expr: identity,
            f_sort: identity,
            f_qual_identifier: identity,
            f_term: identity,
            f_command: identity,
        }
    }

    fn fix_s_exprs_with<F>(
        self,
        f_s_expr: F,
    ) -> Rewriter<
        Self,
        Id<Self::Constant>,
        Id<Self::Symbol>,
        Id<Self::Keyword>,
        F,
        Id<Self::Sort>,
        Id<Self::QualIdentifier>,
        Id<Self::Term>,
        Id<Self::Command>,
    > {
        Rewriter {
            visitor: self,
            f_constant: identity,
            f_symbol: identity,
            f_keyword: identity,
            f_s_expr,
            f_sort: identity,
            f_qual_identifier: identity,
            f_term: identity,
            f_command: identity,
        }
    }

    fn fix_sorts_with<F>(
        self,
        f_sort: F,
    ) -> Rewriter<
        Self,
        Id<Self::Constant>,
        Id<Self::Symbol>,
        Id<Self::Keyword>,
        Id<Self::SExpr>,
        F,
        Id<Self::QualIdentifier>,
        Id<Self::Term>,
        Id<Self::Command>,
    > {
        Rewriter {
            visitor: self,
            f_constant: identity,
            f_symbol: identity,
            f_keyword: identity,
            f_s_expr: identity,
            f_sort,
            f_qual_identifier: identity,
            f_term: identity,
            f_command: identity,
        }
    }

    fn fix_qual_identifiers_with<F>(
        self,
        f_qual_identifier: F,
    ) -> Rewriter<
        Self,
        Id<Self::Constant>,
        Id<Self::Symbol>,
        Id<Self::Keyword>,
        Id<Self::SExpr>,
        Id<Self::Sort>,
        F,
        Id<Self::Term>,
        Id<Self::Command>,
    > {
        Rewriter {
            visitor: self,
            f_constant: identity,
            f_symbol: identity,
            f_keyword: identity,
            f_s_expr: identity,
            f_sort: identity,
            f_qual_identifier,
            f_term: identity,
            f_command: identity,
        }
    }

    fn fix_terms_with<F>(
        self,
        f_term: F,
    ) -> Rewriter<
        Self,
        Id<Self::Constant>,
        Id<Self::Symbol>,
        Id<Self::Keyword>,
        Id<Self::SExpr>,
        Id<Self::Sort>,
        Id<Self::QualIdentifier>,
        F,
        Id<Self::Command>,
    > {
        Rewriter {
            visitor: self,
            f_constant: identity,
            f_symbol: identity,
            f_keyword: identity,
            f_s_expr: identity,
            f_sort: identity,
            f_qual_identifier: identity,
            f_term,
            f_command: identity,
        }
    }

    fn fix_commands_with<F>(
        self,
        f_command: F,
    ) -> Rewriter<
        Self,
        Id<Self::Constant>,
        Id<Self::Symbol>,
        Id<Self::Keyword>,
        Id<Self::SExpr>,
        Id<Self::Sort>,
        Id<Self::QualIdentifier>,
        Id<Self::Term>,
        F,
    > {
        Rewriter {
            visitor: self,
            f_constant: identity,
            f_symbol: identity,
            f_keyword: identity,
            f_s_expr: identity,
            f_sort: identity,
            f_qual_identifier: identity,
            f_term: identity,
            f_command,
        }
    }
}

impl<V> Smt2VisitorExt for V where V: Smt2Visitor + Sized {}

#[test]
fn test_term_rewriter() {
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

    let mut rewrite =
        crate::concrete::SyntaxBuilder.fix_symbols_with(|x: Symbol| Symbol(x.0 + "__"));

    let command2 = command.clone().accept(&mut rewrite);
    let command3 = Command::Assert {
        term: Term::Let {
            var_bindings: vec![(
                Symbol("x__".into()),
                Term::Application {
                    qual_identifier: QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("f__".into()),
                        },
                    },
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("x__".into()),
                            },
                        }),
                        Term::Constant(Constant::Numeral(num::BigUint::from(2u32))),
                    ],
                },
            )],
            term: Box::new(Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("=__".into()),
                    },
                },
                arguments: vec![
                    Term::QualIdentifier(QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("x__".into()),
                        },
                    }),
                    Term::Constant(Constant::Numeral(num::BigUint::from(3u32))),
                ],
            }),
        },
    };

    assert_eq!(command2, command3);

    let mut rewrite = crate::concrete::SyntaxBuilder.fix_commands_with(|_: Command| Command::Exit);
    let command2 = command.clone().accept(&mut rewrite);
    let command3 = Command::Exit;
    assert_eq!(command2, command3);
}
