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

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// An implementation of [`Smt2Visitor`] that returns simple
/// statistics on the SMT2 inputs.
#[derive(Clone, Eq, PartialEq, Default, Debug, Serialize, Deserialize)]
pub struct Smt2Counters {
    pub numeral_constant_count: usize,
    pub decimal_constant_count: usize,
    pub hexadecimal_constant_count: usize,
    pub binary_constant_count: usize,
    pub string_constant_count: usize,
    pub fresh_symbol_count: usize,
    pub bound_symbol_count: usize,
    pub any_symbol_count: usize,
    pub keyword_count: usize,
    pub constant_s_expr_count: usize,
    pub symbol_s_expr_count: usize,
    pub keyword_s_expr_count: usize,
    pub application_s_expr_count: usize,
    pub simple_sort_count: usize,
    pub parameterized_sort_count: usize,
    pub simple_identifier_count: usize,
    pub sorted_identifier_count: usize,
    pub constant_count: usize,
    pub qual_identifier_count: usize,
    pub application_count: usize,
    pub let_count: usize,
    pub forall_count: usize,
    pub exists_count: usize,
    pub match_count: usize,
    pub attributes_count: usize,
    pub assert_count: usize,
    pub check_sat_count: usize,
    pub check_sat_assuming_count: usize,
    pub declare_const_count: usize,
    pub declare_datatype_count: usize,
    pub declare_datatypes_count: usize,
    pub declare_fun_count: usize,
    pub declare_sort_count: usize,
    pub define_fun_count: usize,
    pub define_fun_rec_count: usize,
    pub define_funs_rec_count: usize,
    pub define_sort_count: usize,
    pub echo_count: usize,
    pub exit_count: usize,
    pub get_assertions_count: usize,
    pub get_assignment_count: usize,
    pub get_info_count: usize,
    pub get_model_count: usize,
    pub get_option_count: usize,
    pub get_proof_count: usize,
    pub get_unsat_assumptions_count: usize,
    pub get_unsat_core_count: usize,
    pub get_value_count: usize,
    pub pop_count: usize,
    pub push_count: usize,
    pub reset_count: usize,
    pub reset_assertions_count: usize,
    pub set_info_count: usize,
    pub set_logic_count: usize,
    pub set_option_count: usize,

    pub term_count: usize,
    pub term_max_depth: usize,
    pub term_max_size: usize,
    pub term_sum_depth: usize,
    pub term_sum_size: usize,

    pub keyword_counts: BTreeMap<String, usize>,
    pub symbol_counts: BTreeMap<String, usize>,
}

impl Smt2Counters {
    /// Build a Smt2Visitor that holds statistics, including some
    /// interesting keywords and symbols.
    pub fn new(keywords: Vec<String>, symbols: Vec<String>) -> Self {
        let mut state = Self::default();
        for keyword in keywords {
            state.keyword_counts.insert(keyword, 0);
        }
        for symbol in symbols {
            state.symbol_counts.insert(symbol, 0);
        }
        state
    }

    fn visit_keyword(&mut self, keyword: &str) {
        if let Some(entry) = self.keyword_counts.get_mut(keyword) {
            *entry += 1;
        }
    }

    fn visit_symbol(&mut self, symbol: &str) {
        if let Some(entry) = self.symbol_counts.get_mut(symbol) {
            *entry += 1;
        }
    }
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

impl ConstantVisitor for Smt2Counters {
    type T = ();

    fn visit_numeral_constant(&mut self, _value: Numeral) -> Self::T {
        self.numeral_constant_count += 1;
    }
    fn visit_decimal_constant(&mut self, _value: Decimal) -> Self::T {
        self.decimal_constant_count += 1;
    }
    fn visit_hexadecimal_constant(&mut self, _value: Hexadecimal) -> Self::T {
        self.hexadecimal_constant_count += 1;
    }
    fn visit_binary_constant(&mut self, _value: Binary) -> Self::T {
        self.binary_constant_count += 1;
    }
    fn visit_string_constant(&mut self, _value: String) -> Self::T {
        self.string_constant_count += 1;
    }
}

impl SymbolVisitor for Smt2Counters {
    type T = ();

    fn visit_fresh_symbol(&mut self, _value: String) -> Self::T {
        self.fresh_symbol_count += 1;
    }

    fn visit_bound_symbol(&mut self, value: String) -> Result<Self::T, String> {
        self.bound_symbol_count += 1;
        self.visit_symbol(&value);
        Ok(())
    }

    fn visit_any_symbol(&mut self, _value: String) -> Self::T {
        self.any_symbol_count += 1;
    }
}

impl KeywordVisitor for Smt2Counters {
    type T = ();

    fn visit_keyword(&mut self, value: String) -> Self::T {
        self.keyword_count += 1;
        self.visit_keyword(&value);
    }
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

impl SExprVisitor<Constant, Symbol, Keyword> for Smt2Counters {
    type T = ();

    fn visit_constant_s_expr(&mut self, _value: Constant) -> Self::T {
        self.constant_s_expr_count += 1;
    }

    fn visit_symbol_s_expr(&mut self, _value: Symbol) -> Self::T {
        self.symbol_s_expr_count += 1;
    }

    fn visit_keyword_s_expr(&mut self, _value: Keyword) -> Self::T {
        self.keyword_s_expr_count += 1;
    }

    fn visit_application_s_expr(&mut self, _values: Vec<Self::T>) -> Self::T {
        self.application_s_expr_count += 1;
    }
}

impl SortVisitor<Symbol> for Smt2Counters {
    type T = ();

    fn visit_simple_sort(&mut self, _identifier: Identifier) -> Self::T {
        self.simple_sort_count += 1;
    }

    fn visit_parameterized_sort(
        &mut self,
        _identifier: Identifier,
        _parameters: Vec<Self::T>,
    ) -> Self::T {
        self.parameterized_sort_count += 1;
    }
}

impl QualIdentifierVisitor<Identifier, Sort> for Smt2Counters {
    type T = ();

    fn visit_simple_identifier(&mut self, _identifier: Identifier) -> Self::T {
        self.simple_identifier_count += 1;
    }

    fn visit_sorted_identifier(&mut self, _identifier: Identifier, _sort: Sort) -> Self::T {
        self.sorted_identifier_count += 1;
    }
}

impl TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> for Smt2Counters {
    type T = Term;

    fn visit_constant(&mut self, _constant: Constant) -> Self::T {
        self.constant_count += 1;
        Term::default()
    }

    fn visit_qual_identifier(&mut self, _qual_identifier: QualIdentifier) -> Self::T {
        self.qual_identifier_count += 1;
        Term::default()
    }

    fn visit_application(
        &mut self,
        _qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Self::T {
        self.application_count += 1;
        Term::node(arguments.into_iter())
    }

    fn visit_let(&mut self, var_bindings: Vec<(Symbol, Self::T)>, term: Self::T) -> Self::T {
        self.let_count += 1;
        Term::node(std::iter::once(term).chain(var_bindings.into_iter().map(|(_, t)| t)))
    }

    fn visit_forall(&mut self, _vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T {
        self.forall_count += 1;
        Term::node(std::iter::once(term))
    }

    fn visit_exists(&mut self, _vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T {
        self.exists_count += 1;
        Term::node(std::iter::once(term))
    }

    fn visit_match(&mut self, term: Self::T, cases: Vec<(Vec<Symbol>, Self::T)>) -> Self::T {
        self.match_count += 1;
        Term::node(std::iter::once(term).chain(cases.into_iter().map(|(_, t)| t)))
    }

    fn visit_attributes(
        &mut self,
        term: Self::T,
        _attributes: Vec<(Keyword, AttributeValue)>,
    ) -> Self::T {
        self.attributes_count += 1;
        Term::node(std::iter::once(term))
    }
}

impl Smt2Counters {
    fn visit_term(&mut self, term: Term) {
        self.term_count += 1;
        self.term_max_depth = std::cmp::max(term.tree_depth, self.term_max_depth);
        self.term_max_size = std::cmp::max(term.tree_size, self.term_max_size);
        self.term_sum_depth += term.tree_depth;
        self.term_sum_size += term.tree_size;
    }
}

impl CommandVisitor<Term, Symbol, Sort, Keyword, Constant, SExpr> for Smt2Counters {
    type T = ();

    fn visit_assert(&mut self, term: Term) -> Self::T {
        self.assert_count += 1;
        self.visit_term(term)
    }

    fn visit_check_sat(&mut self) -> Self::T {
        self.check_sat_count += 1;
    }

    fn visit_check_sat_assuming(&mut self, _literals: Vec<(Symbol, bool)>) -> Self::T {
        self.check_sat_assuming_count += 1;
    }

    fn visit_declare_const(&mut self, _symbol: Symbol, _sort: Sort) -> Self::T {
        self.declare_const_count += 1;
    }

    fn visit_declare_datatype(&mut self, _symbol: Symbol, _datatype: DatatypeDec) -> Self::T {
        self.declare_datatype_count += 1;
    }

    fn visit_declare_datatypes(
        &mut self,
        _datatypes: Vec<(Symbol, Numeral, DatatypeDec)>,
    ) -> Self::T {
        self.declare_datatypes_count += 1;
    }

    fn visit_declare_fun(
        &mut self,
        _symbol: Symbol,
        _parameters: Vec<Sort>,
        _sort: Sort,
    ) -> Self::T {
        self.declare_fun_count += 1;
    }

    fn visit_declare_sort(&mut self, _symbol: Symbol, _arity: Numeral) -> Self::T {
        self.declare_sort_count += 1;
    }

    fn visit_define_fun(&mut self, _sig: FunctionDec, term: Term) -> Self::T {
        self.define_fun_count += 1;
        self.visit_term(term)
    }

    fn visit_define_fun_rec(&mut self, _sig: FunctionDec, term: Term) -> Self::T {
        self.define_fun_rec_count += 1;
        self.visit_term(term)
    }

    fn visit_define_funs_rec(&mut self, funs: Vec<(FunctionDec, Term)>) -> Self::T {
        self.define_funs_rec_count += 1;
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
        self.define_sort_count += 1;
    }

    fn visit_echo(&mut self, _message: String) -> Self::T {
        self.echo_count += 1;
    }

    fn visit_exit(&mut self) -> Self::T {
        self.exit_count += 1;
    }

    fn visit_get_assertions(&mut self) -> Self::T {
        self.get_assertions_count += 1;
    }

    fn visit_get_assignment(&mut self) -> Self::T {
        self.get_assignment_count += 1;
    }

    fn visit_get_info(&mut self, _flag: Keyword) -> Self::T {
        self.get_info_count += 1;
    }

    fn visit_get_model(&mut self) -> Self::T {
        self.get_model_count += 1;
    }

    fn visit_get_option(&mut self, _keyword: Keyword) -> Self::T {
        self.get_option_count += 1;
    }

    fn visit_get_proof(&mut self) -> Self::T {
        self.get_proof_count += 1;
    }

    fn visit_get_unsat_assumptions(&mut self) -> Self::T {
        self.get_unsat_assumptions_count += 1;
    }

    fn visit_get_unsat_core(&mut self) -> Self::T {
        self.get_unsat_core_count += 1;
    }

    fn visit_get_value(&mut self, terms: Vec<Term>) -> Self::T {
        self.get_value_count += 1;
        for term in terms {
            self.visit_term(term);
        }
    }

    fn visit_pop(&mut self, _level: Numeral) -> Self::T {
        self.pop_count += 1;
    }

    fn visit_push(&mut self, _level: Numeral) -> Self::T {
        self.push_count += 1;
    }

    fn visit_reset(&mut self) -> Self::T {
        self.reset_count += 1;
    }

    fn visit_reset_assertions(&mut self) -> Self::T {
        self.reset_assertions_count += 1;
    }

    fn visit_set_info(&mut self, _keyword: Keyword, _value: AttributeValue) -> Self::T {
        self.set_info_count += 1;
    }

    fn visit_set_logic(&mut self, _symbol: Symbol) -> Self::T {
        self.set_logic_count += 1;
    }

    fn visit_set_option(&mut self, _keyword: Keyword, _value: AttributeValue) -> Self::T {
        self.set_option_count += 1;
    }
}

impl Smt2Visitor for Smt2Counters {
    type Constant = ();
    type QualIdentifier = ();
    type Keyword = ();
    type Sort = ();
    type SExpr = ();
    type Symbol = ();
    type Term = Term;
    type Command = ();
}
