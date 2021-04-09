// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A demo implementation of visiting traits that counts things.

use crate::{
    visitors::{
        CommandVisitor, ConstantVisitor, KeywordVisitor, QualIdentifierVisitor, SExprVisitor,
        Smt2Visitor, SortVisitor, SymbolVisitor, TermVisitor,
    },
    Binary, Decimal, Hexadecimal, Numeral,
};

/// An implementation of [`SMT2Visitor`] that returns simple
/// statistics on the SMT2 inputs.
#[derive(Clone, Eq, PartialEq, Default, Debug)]
pub struct StatsHolder {
    pub term_count: usize,
    pub term_max_depth: usize,
    pub term_max_size: usize,
}

/// Statistics about a term.
#[derive(Clone, Eq, PartialEq, Default, Debug)]
pub struct Term {
    pub tree_depth: usize,
    pub tree_size: usize,
}

impl Term {
    fn node<I>(iter: I) -> Self
    where
        I: Iterator<Item = Term>,
    {
        let mut result = Term::default();
        for t in iter {
            result.tree_depth = std::cmp::max(result.tree_depth, t.tree_depth);
            result.tree_size += t.tree_size;
        }
        result.tree_depth += 1;
        result.tree_size += 1;
        result
    }
}

impl ConstantVisitor for StatsHolder {
    type T = ();

    fn visit_numeral_constant(&mut self, _value: Numeral) -> Self::T {}
    fn visit_decimal_constant(&mut self, _value: Decimal) -> Self::T {}
    fn visit_hexadecimal_constant(&mut self, _value: Hexadecimal) -> Self::T {}
    fn visit_binary_constant(&mut self, _value: Binary) -> Self::T {}
    fn visit_string_constant(&mut self, _value: String) -> Self::T {}
}

impl SymbolVisitor for StatsHolder {
    type T = ();

    fn visit_symbol(&mut self, _value: String) -> Self::T {}
}

impl KeywordVisitor for StatsHolder {
    type T = ();

    fn visit_keyword(&mut self, _value: String) -> Self::T {}
}

type Constant = ();
type Symbol = ();
type Keyword = ();
type Sort = ();
type QualIdentifier = ();
type SExpr = ();

type Identifier = crate::visitors::Identifier<Symbol>;
type AttributeValue = crate::visitors::AttributeValue<Constant, Symbol, SExpr>;
type DatatypeDec = crate::visitors::DatatypeDec<Symbol, Sort>;
type FunctionDec = crate::visitors::FunctionDec<Symbol, Sort>;

impl SExprVisitor<Constant, Symbol, Keyword> for StatsHolder {
    type T = ();

    fn visit_constant_s_expr(&mut self, _value: Constant) -> Self::T {}

    fn visit_symbol_s_expr(&mut self, _value: Symbol) -> Self::T {}

    fn visit_keyword_s_expr(&mut self, _value: Keyword) -> Self::T {}

    fn visit_application_s_expr(&mut self, _values: Vec<Self::T>) -> Self::T {}
}

impl SortVisitor<Symbol> for StatsHolder {
    type T = ();

    fn visit_simple_sort(&mut self, _identifier: Identifier) -> Self::T {}

    fn visit_parameterized_sort(
        &mut self,
        _identifier: Identifier,
        _parameters: Vec<Self::T>,
    ) -> Self::T {
    }
}

impl QualIdentifierVisitor<Identifier, Sort> for StatsHolder {
    type T = ();

    fn visit_simple_identifier(&mut self, _identifier: Identifier) -> Self::T {}

    fn visit_sorted_identifier(&mut self, _identifier: Identifier, _sort: Sort) -> Self::T {}
}

impl TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> for StatsHolder {
    type T = Term;

    fn visit_constant(&mut self, _constant: Constant) -> Self::T {
        Term::default()
    }

    fn visit_qual_identifier(&mut self, _qual_identifier: QualIdentifier) -> Self::T {
        Term::default()
    }

    fn visit_application(
        &mut self,
        _qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Self::T {
        Term::node(arguments.into_iter())
    }

    fn visit_let(&mut self, var_bindings: Vec<(Symbol, Self::T)>, term: Self::T) -> Self::T {
        Term::node(std::iter::once(term).chain(var_bindings.into_iter().map(|(_, t)| t)))
    }

    fn visit_forall(&mut self, _vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T {
        Term::node(std::iter::once(term))
    }

    fn visit_exists(&mut self, _vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T {
        Term::node(std::iter::once(term))
    }

    fn visit_match(&mut self, term: Self::T, cases: Vec<(Vec<Symbol>, Self::T)>) -> Self::T {
        Term::node(std::iter::once(term).chain(cases.into_iter().map(|(_, t)| t)))
    }

    fn visit_attributes(
        &mut self,
        term: Self::T,
        _attributes: Vec<(Keyword, AttributeValue)>,
    ) -> Self::T {
        Term::node(std::iter::once(term))
    }
}

impl StatsHolder {
    fn visit_term(&mut self, term: Term) {
        self.term_count += 1;
        self.term_max_depth = std::cmp::max(term.tree_depth, self.term_max_depth);
        self.term_max_size = std::cmp::max(term.tree_size, self.term_max_size);
    }
}

impl CommandVisitor<Term, Symbol, Sort, Keyword, Constant, SExpr> for StatsHolder {
    type T = ();

    fn visit_assert(&mut self, term: Term) -> Self::T {
        self.visit_term(term)
    }

    fn visit_check_sat(&mut self) -> Self::T {}

    fn visit_check_sat_assuming(&mut self, _literals: Vec<(Symbol, bool)>) -> Self::T {}

    fn visit_declare_const(&mut self, _symbol: Symbol, _sort: Sort) -> Self::T {}

    fn visit_declare_datatype(&mut self, _symbol: Symbol, _datatype: DatatypeDec) -> Self::T {}

    fn visit_declare_datatypes(
        &mut self,
        _datatypes: Vec<(Symbol, Numeral, DatatypeDec)>,
    ) -> Self::T {
    }

    fn visit_declare_fun(
        &mut self,
        _symbol: Symbol,
        _parameters: Vec<Sort>,
        _sort: Sort,
    ) -> Self::T {
    }

    fn visit_declare_sort(&mut self, _symbol: Symbol, _arity: Numeral) -> Self::T {}

    fn visit_define_fun(&mut self, _sig: FunctionDec, term: Term) -> Self::T {
        self.visit_term(term)
    }

    fn visit_define_fun_rec(&mut self, _sig: FunctionDec, term: Term) -> Self::T {
        self.visit_term(term)
    }

    fn visit_define_funs_rec(&mut self, funs: Vec<(FunctionDec, Term)>) -> Self::T {
        for (_, term) in funs {
            self.visit_term(term);
        }
    }

    fn visit_define_sort(
        &mut self,
        _symbol: Symbol,
        _parameters: Vec<Symbol>,
        _sort: Sort,
    ) -> Self::T {
    }

    fn visit_echo(&mut self, _message: String) -> Self::T {}

    fn visit_exit(&mut self) -> Self::T {}

    fn visit_get_assertions(&mut self) -> Self::T {}

    fn visit_get_assignment(&mut self) -> Self::T {}

    fn visit_get_info(&mut self, _flag: Keyword) -> Self::T {}

    fn visit_get_model(&mut self) -> Self::T {}

    fn visit_get_option(&mut self, _keyword: Keyword) -> Self::T {}

    fn visit_get_proof(&mut self) -> Self::T {}

    fn visit_get_unsat_assumptions(&mut self) -> Self::T {}

    fn visit_get_unsat_core(&mut self) -> Self::T {}

    fn visit_get_value(&mut self, terms: Vec<Term>) -> Self::T {
        for term in terms {
            self.visit_term(term);
        }
    }

    fn visit_pop(&mut self, _level: Numeral) -> Self::T {}

    fn visit_push(&mut self, _level: Numeral) -> Self::T {}

    fn visit_reset(&mut self) -> Self::T {}

    fn visit_reset_assertions(&mut self) -> Self::T {}

    fn visit_set_info(&mut self, _keyword: Keyword, _value: AttributeValue) -> Self::T {}

    fn visit_set_logic(&mut self, _symbol: Symbol) -> Self::T {}

    fn visit_set_option(&mut self, _keyword: Keyword, _value: AttributeValue) -> Self::T {}
}

impl Smt2Visitor for StatsHolder {
    type Constant = ();
    type QualIdentifier = ();
    type Keyword = ();
    type Sort = ();
    type SExpr = ();
    type Symbol = ();
    type Term = Term;
    type Command = ();
}
