// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A concrete syntax tree together with building functions (aka parser visitors) and SEXP-printing functions.

use crate::{
    lexer,
    visitors::{
        CommandVisitor, ConstantVisitor, KeywordVisitor, QualIdentifierVisitor, SExprVisitor,
        SMT2Visitor, SortVisitor, SymbolVisitor, TermVisitor,
    },
    Binary, Decimal, Hexadecimal, Numeral,
};

/// Concrete syntax for a constant.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Constant {
    Numeral(Numeral),
    Decimal(Decimal),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    String(String),
}

/// Concrete symbol.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Ord, PartialOrd)]
pub struct Symbol(pub String);

/// Concrete keyword.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Ord, PartialOrd)]
pub struct Keyword(pub String);

/// Concrete identifier.
pub type Identifier = crate::visitors::Identifier<Symbol>;

/// Concrete syntax for an S-expression.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum SExpr {
    Constant(Constant),
    Symbol(Symbol),
    Keyword(Keyword),
    Application(Vec<SExpr>),
}

/// Concrete [`crate::visitors::AttributeValue`].
pub type AttributeValue = crate::visitors::AttributeValue<Constant, Symbol, SExpr>;
/// Concrete [`crate::visitors::DatatypeDec`].
pub type DatatypeDec = crate::visitors::DatatypeDec<Symbol, Sort>;
/// Concrete [`crate::visitors::FunctionDec`].
pub type FunctionDec = crate::visitors::FunctionDec<Symbol, Sort>;

/// Concrete syntax for a sort.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Sort {
    Simple {
        identifier: Identifier,
    },
    Parameterized {
        identifier: Identifier,
        parameters: Vec<Sort>,
    },
}

/// Concrete syntax for a qualified-identifier.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum QualIdentifier {
    Simple { identifier: Identifier },
    Sorted { identifier: Identifier, sort: Sort },
}

/// Concrete syntax for a term.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Term {
    Constant(Constant),
    QualIdentifier(QualIdentifier),
    Application {
        qual_identifier: QualIdentifier,
        arguments: Vec<Term>,
    },
    Let {
        var_bindings: Vec<(Symbol, Term)>,
        term: Box<Term>,
    },
    Forall {
        vars: Vec<(Symbol, Sort)>,
        term: Box<Term>,
    },
    Exists {
        vars: Vec<(Symbol, Sort)>,
        term: Box<Term>,
    },
    Match {
        term: Box<Term>,
        cases: Vec<(Vec<Symbol>, Term)>,
    },
    Attributes {
        term: Box<Term>,
        attributes: Vec<(Keyword, AttributeValue)>,
    },
}

/// Concrete syntax for a command.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Command {
    Assert {
        term: Term,
    },
    CheckSat,
    CheckSatAssuming {
        literals: Vec<(Symbol, bool)>,
    },
    DeclareConst {
        symbol: Symbol,
        sort: Sort,
    },
    DeclareDatatype {
        symbol: Symbol,
        datatype: DatatypeDec,
    },
    DeclareDatatypes {
        datatypes: Vec<(Symbol, Numeral, DatatypeDec)>,
    },
    DeclareFun {
        symbol: Symbol,
        parameters: Vec<Sort>,
        sort: Sort,
    },
    DeclareSort {
        symbol: Symbol,
        arity: Numeral,
    },
    DefineFun {
        sig: FunctionDec,
        term: Term,
    },
    DefineFunRec {
        sig: FunctionDec,
        term: Term,
    },
    DefineFunsRec {
        funs: Vec<(FunctionDec, Term)>,
    },
    DefineSort {
        symbol: Symbol,
        parameters: Vec<Symbol>,
        sort: Sort,
    },
    Echo {
        message: String,
    },
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo {
        flag: Keyword,
    },
    GetModel,
    GetOption {
        keyword: Keyword,
    },
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue {
        terms: Vec<Term>,
    },
    Pop {
        level: Numeral,
    },
    Push {
        level: Numeral,
    },
    Reset,
    ResetAssertions,
    SetInfo {
        keyword: Keyword,
        value: AttributeValue,
    },
    SetLogic {
        symbol: Symbol,
    },
    SetOption {
        keyword: Keyword,
        value: AttributeValue,
    },
}

/// An implementation of [`SMT2Visitor`] that returns concrete syntax values.
#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub struct SyntaxBuilder;

impl ConstantVisitor for SyntaxBuilder {
    type T = Constant;

    fn visit_numeral_constant(&mut self, value: Numeral) -> Self::T {
        Constant::Numeral(value)
    }
    fn visit_decimal_constant(&mut self, value: Decimal) -> Self::T {
        Constant::Decimal(value)
    }
    fn visit_hexadecimal_constant(&mut self, value: Hexadecimal) -> Self::T {
        Constant::Hexadecimal(value)
    }
    fn visit_binary_constant(&mut self, value: Binary) -> Self::T {
        Constant::Binary(value)
    }
    fn visit_string_constant(&mut self, value: String) -> Self::T {
        Constant::String(value)
    }
}

impl SymbolVisitor for SyntaxBuilder {
    type T = Symbol;

    fn visit_symbol(&mut self, value: String) -> Self::T {
        Symbol(value)
    }
}

impl KeywordVisitor for SyntaxBuilder {
    type T = Keyword;

    fn visit_keyword(&mut self, value: String) -> Self::T {
        Keyword(value)
    }
}

impl SExprVisitor<Constant, Symbol, Keyword> for SyntaxBuilder {
    type T = SExpr;

    fn visit_constant_s_expr(&mut self, value: Constant) -> Self::T {
        SExpr::Constant(value)
    }

    fn visit_symbol_s_expr(&mut self, value: Symbol) -> Self::T {
        SExpr::Symbol(value)
    }

    fn visit_keyword_s_expr(&mut self, value: Keyword) -> Self::T {
        SExpr::Keyword(value)
    }

    fn visit_application_s_expr(&mut self, values: Vec<Self::T>) -> Self::T {
        SExpr::Application(values)
    }
}

impl SortVisitor<Symbol> for SyntaxBuilder {
    type T = Sort;

    fn visit_simple_sort(&mut self, identifier: Identifier) -> Self::T {
        Sort::Simple { identifier }
    }

    fn visit_parameterized_sort(
        &mut self,
        identifier: Identifier,
        parameters: Vec<Self::T>,
    ) -> Self::T {
        Sort::Parameterized {
            identifier,
            parameters,
        }
    }
}

impl QualIdentifierVisitor<Identifier, Sort> for SyntaxBuilder {
    type T = QualIdentifier;

    fn visit_simple_identifier(&mut self, identifier: Identifier) -> Self::T {
        QualIdentifier::Simple { identifier }
    }

    fn visit_sorted_identifier(&mut self, identifier: Identifier, sort: Sort) -> Self::T {
        QualIdentifier::Sorted { identifier, sort }
    }
}

impl TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> for SyntaxBuilder {
    type T = Term;

    fn visit_constant(&mut self, constant: Constant) -> Self::T {
        Term::Constant(constant)
    }

    fn visit_qual_identifier(&mut self, qual_identifier: QualIdentifier) -> Self::T {
        Term::QualIdentifier(qual_identifier)
    }

    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Self::T {
        Term::Application {
            qual_identifier,
            arguments,
        }
    }

    fn visit_let(&mut self, var_bindings: Vec<(Symbol, Self::T)>, term: Self::T) -> Self::T {
        let term = Box::new(term);
        Term::Let { var_bindings, term }
    }

    fn visit_forall(&mut self, vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T {
        let term = Box::new(term);
        Term::Forall { vars, term }
    }

    fn visit_exists(&mut self, vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T {
        let term = Box::new(term);
        Term::Exists { vars, term }
    }

    fn visit_match(&mut self, term: Self::T, cases: Vec<(Vec<Symbol>, Self::T)>) -> Self::T {
        let term = Box::new(term);
        Term::Match { term, cases }
    }

    fn visit_attributes(
        &mut self,
        term: Self::T,
        attributes: Vec<(Keyword, AttributeValue)>,
    ) -> Self::T {
        let term = Box::new(term);
        Term::Attributes { term, attributes }
    }
}

impl CommandVisitor<Term, Symbol, Sort, Keyword, Constant, SExpr> for SyntaxBuilder {
    type T = Command;

    fn visit_assert(&mut self, term: Term) -> Self::T {
        Command::Assert { term }
    }

    fn visit_check_sat(&mut self) -> Self::T {
        Command::CheckSat
    }

    fn visit_check_sat_assuming(&mut self, literals: Vec<(Symbol, bool)>) -> Self::T {
        Command::CheckSatAssuming { literals }
    }

    fn visit_declare_const(&mut self, symbol: Symbol, sort: Sort) -> Self::T {
        Command::DeclareConst { symbol, sort }
    }

    fn visit_declare_datatype(&mut self, symbol: Symbol, datatype: DatatypeDec) -> Self::T {
        Command::DeclareDatatype { symbol, datatype }
    }

    fn visit_declare_datatypes(
        &mut self,
        datatypes: Vec<(Symbol, Numeral, DatatypeDec)>,
    ) -> Self::T {
        Command::DeclareDatatypes { datatypes }
    }

    fn visit_declare_fun(&mut self, symbol: Symbol, parameters: Vec<Sort>, sort: Sort) -> Self::T {
        Command::DeclareFun {
            symbol,
            parameters,
            sort,
        }
    }

    fn visit_declare_sort(&mut self, symbol: Symbol, arity: Numeral) -> Self::T {
        Command::DeclareSort { symbol, arity }
    }

    fn visit_define_fun(&mut self, sig: FunctionDec, term: Term) -> Self::T {
        Command::DefineFun { sig, term }
    }

    fn visit_define_fun_rec(&mut self, sig: FunctionDec, term: Term) -> Self::T {
        Command::DefineFunRec { sig, term }
    }

    fn visit_define_funs_rec(&mut self, funs: Vec<(FunctionDec, Term)>) -> Self::T {
        Command::DefineFunsRec { funs }
    }

    fn visit_define_sort(
        &mut self,
        symbol: Symbol,
        parameters: Vec<Symbol>,
        sort: Sort,
    ) -> Self::T {
        Command::DefineSort {
            symbol,
            parameters,
            sort,
        }
    }

    fn visit_echo(&mut self, message: String) -> Self::T {
        Command::Echo { message }
    }

    fn visit_exit(&mut self) -> Self::T {
        Command::Exit
    }

    fn visit_get_assertions(&mut self) -> Self::T {
        Command::GetAssertions
    }

    fn visit_get_assignment(&mut self) -> Self::T {
        Command::GetAssignment
    }

    fn visit_get_info(&mut self, flag: Keyword) -> Self::T {
        Command::GetInfo { flag }
    }

    fn visit_get_model(&mut self) -> Self::T {
        Command::GetModel
    }

    fn visit_get_option(&mut self, keyword: Keyword) -> Self::T {
        Command::GetOption { keyword }
    }

    fn visit_get_proof(&mut self) -> Self::T {
        Command::GetProof
    }

    fn visit_get_unsat_assumptions(&mut self) -> Self::T {
        Command::GetUnsatAssumptions
    }

    fn visit_get_unsat_core(&mut self) -> Self::T {
        Command::GetUnsatCore
    }

    fn visit_get_value(&mut self, terms: Vec<Term>) -> Self::T {
        Command::GetValue { terms }
    }

    fn visit_pop(&mut self, level: Numeral) -> Self::T {
        Command::Pop { level }
    }

    fn visit_push(&mut self, level: Numeral) -> Self::T {
        Command::Push { level }
    }

    fn visit_reset(&mut self) -> Self::T {
        Command::Reset
    }

    fn visit_reset_assertions(&mut self) -> Self::T {
        Command::ResetAssertions
    }

    fn visit_set_info(&mut self, keyword: Keyword, value: AttributeValue) -> Self::T {
        Command::SetInfo { keyword, value }
    }

    fn visit_set_logic(&mut self, symbol: Symbol) -> Self::T {
        Command::SetLogic { symbol }
    }

    fn visit_set_option(&mut self, keyword: Keyword, value: AttributeValue) -> Self::T {
        Command::SetOption { keyword, value }
    }
}

impl SMT2Visitor for SyntaxBuilder {
    type Constant = Constant;
    type QualIdentifier = QualIdentifier;
    type Keyword = Keyword;
    type Sort = Sort;
    type SExpr = SExpr;
    type Symbol = Symbol;
    type Term = Term;
    type Command = Command;
}

impl std::fmt::Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨numeral⟩ | ⟨decimal⟩ | ⟨hexadecimal⟩ | ⟨binary⟩ | ⟨string⟩
        use Constant::*;
        match self {
            Numeral(num) => write!(f, "{}", num),
            Decimal(dec) => {
                let nom = dec.trunc();
                let mut denom = dec.fract();
                while !denom.is_integer() {
                    denom *= num::BigInt::from(10u32);
                }
                write!(f, "{}.{}", nom, denom)
            }
            Hexadecimal(hex) => {
                write!(f, "#x")?;
                for digit in hex {
                    write!(f, "{:x}", digit)?;
                }
                Ok(())
            }
            Binary(bin) => {
                write!(f, "#b")?;
                for digit in bin {
                    if *digit {
                        write!(f, "1")?;
                    } else {
                        write!(f, "0")?;
                    }
                }
                Ok(())
            }
            String(value) => {
                for s in value.split('"') {
                    write!(f, "\"{}\"", s)?;
                }
                Ok(())
            }
        }
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let c = self.0.as_bytes().get(0);
        if c.is_some()
            && lexer::is_non_digit_symbol_byte(*c.unwrap())
            && self.0.as_bytes().iter().all(|c| lexer::is_symbol_byte(*c))
        {
            write!(f, "{}", self.0)
        } else {
            write!(f, "|{}|", self.0)
        }
    }
}

impl std::fmt::Display for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, ":{}", self.0)
    }
}

impl std::fmt::Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨spec_constant⟩ | ⟨symbol⟩ | ⟨keyword⟩ | ( ⟨s_expr⟩∗ )
        use SExpr::*;
        match self {
            Constant(c) => write!(f, "{}", c),
            Symbol(s) => write!(f, "{}", s),
            Keyword(k) => write!(f, "{}", k),
            Application(values) => write!(
                f,
                "({})",
                values
                    .iter()
                    .map(|v| format!("{}", v))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

impl std::fmt::Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨identifier⟩ | ( ⟨identifier⟩ ⟨sort⟩+ )
        use Sort::*;
        match self {
            Simple { identifier } => write!(f, "{}", identifier),
            Parameterized {
                identifier,
                parameters,
            } => write!(
                f,
                "({} {})",
                identifier,
                parameters
                    .iter()
                    .map(|v| format!("{}", v))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

impl std::fmt::Display for QualIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨identifier⟩ | ( as ⟨identifier⟩ ⟨sort⟩ )
        use QualIdentifier::*;
        match self {
            Simple { identifier } => write!(f, "{}", identifier),
            Sorted { identifier, sort } => write!(f, "(as {} {})", identifier, sort),
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Term::*;
        match self {
            Constant(c) => {
                // ⟨spec_constant⟩
                write!(f, "{}", c)
            }
            QualIdentifier(id) => {
                // ⟨qual_identifier⟩
                write!(f, "{}", id)
            }
            Application {
                qual_identifier,
                arguments,
            } => {
                // ( ⟨qual_identifier ⟩ ⟨term⟩+ )
                write!(
                    f,
                    "({} {})",
                    qual_identifier,
                    arguments
                        .iter()
                        .map(|v| format!("{}", v))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            Let { var_bindings, term } => {
                // ( let ( ⟨var_binding⟩+ ) ⟨term⟩ )
                write!(
                    f,
                    "(let ({}) {})",
                    var_bindings
                        .iter()
                        .map(|(v, t)| format!("({} {})", v, t))
                        .collect::<Vec<_>>()
                        .join(" "),
                    term
                )
            }
            Forall { vars, term } => {
                // ( forall ( ⟨sorted_var⟩+ ) ⟨term⟩ )
                write!(
                    f,
                    "(forall ({}) {})",
                    vars.iter()
                        .map(|(v, s)| format!("({} {})", v, s))
                        .collect::<Vec<_>>()
                        .join(" "),
                    term
                )
            }
            Exists { vars, term } => {
                // ( exists ( ⟨sorted_var⟩+ ) ⟨term⟩ )
                write!(
                    f,
                    "(exists ({}) {})",
                    vars.iter()
                        .map(|(v, s)| format!("({} {})", v, s))
                        .collect::<Vec<_>>()
                        .join(" "),
                    term
                )
            }
            Match { term, cases } => {
                // ( match ⟨term⟩ ( ⟨match_case⟩+ ) )
                write!(
                    f,
                    "(match {} ({}))",
                    term,
                    cases
                        .iter()
                        .map(|(pattern, term)| {
                            let s = {
                                // ⟨symbol⟩ | ( ⟨symbol⟩ ⟨symbol⟩+ )
                                if pattern.len() == 1 {
                                    format!("{}", pattern[0])
                                } else {
                                    format!(
                                        "({})",
                                        pattern
                                            .iter()
                                            .map(|s| format!("{}", s))
                                            .collect::<Vec<_>>()
                                            .join(" ")
                                    )
                                }
                            };
                            format!("({} {})", s, term)
                        })
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            Attributes { term, attributes } => {
                // ( ! ⟨term⟩ ⟨attribute⟩+ )
                write!(
                    f,
                    "(! {} {})",
                    term,
                    attributes
                        .iter()
                        .map(|(key, value)| format!("{}{}", key, value))
                        .collect::<Vec<_>>()
                        .join(" "),
                )
            }
        }
    }
}

impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Command::*;
        match self {
            Assert { term } => write!(f, "(assert {})", term),
            CheckSat => write!(f, "(check-sat)"),
            CheckSatAssuming { literals } => {
                // ( check-sat-assuming ( ⟨prop_literal⟩∗ ) )
                write!(
                    f,
                    "(check-sat-assuming ({}))",
                    literals
                        .iter()
                        .map(|(s, b)| {
                            // ⟨symbol⟩ | ( not ⟨symbol⟩ )
                            if *b {
                                format!("{}", s)
                            } else {
                                format!("(not {})", s)
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            DeclareConst { symbol, sort } => write!(f, "(declare-const {} {})", symbol, sort),
            DeclareDatatype { symbol, datatype } => {
                write!(f, "(declare-datatype {} {})", symbol, datatype)
            }
            DeclareDatatypes { datatypes } => {
                // ( declare-datatypes ( ⟨sort_dec⟩n+1 ) ( ⟨datatype_dec⟩n+1 ) )
                let sorts = datatypes
                    .iter()
                    .map(|(sym, num, _)| format!("({} {})", sym, num))
                    .collect::<Vec<_>>()
                    .join(" ");
                let types = datatypes
                    .iter()
                    .map(|(_, _, ty)| format!("{}", ty))
                    .collect::<Vec<_>>()
                    .join(" ");
                write!(f, "(declare-datatypes ({}) ({}))", sorts, types)
            }
            DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                // ( declare-fun ⟨symbol⟩ ( ⟨sort⟩∗ ) ⟨sort⟩ )
                write!(
                    f,
                    "(declare-fun {} ({}) {})",
                    symbol,
                    parameters
                        .iter()
                        .map(|s| format!("{}", s))
                        .collect::<Vec<_>>()
                        .join(" "),
                    sort
                )
            }
            DeclareSort { symbol, arity } => write!(
                f,
                "(declare-sort {} {})",
                symbol,
                Constant::Numeral(arity.clone())
            ),
            DefineFun { sig, term } => {
                // ( define-fun ⟨function_dec⟩ ⟨term⟩ )
                write!(f, "(define-fun {} {})", sig, term)
            }
            DefineFunRec { sig, term } => {
                // ( define-fun-rec ⟨function_dec⟩ ⟨term⟩ )
                write!(f, "(define-fun {} {})", sig, term)
            }
            DefineFunsRec { funs } => {
                // ( define-funs-rec ( ( ⟨function_dec⟩ )n+1 ) ( ⟨term⟩n+1 ) )
                let sigs = funs
                    .iter()
                    .map(|(sig, _)| format!("({})", sig))
                    .collect::<Vec<_>>()
                    .join(" ");
                let terms = funs
                    .iter()
                    .map(|(_, t)| format!("{}", t))
                    .collect::<Vec<_>>()
                    .join(" ");
                write!(f, "(define-funs-rec ({}) ({}))", sigs, terms)
            }
            DefineSort {
                symbol,
                parameters,
                sort,
            } => {
                // ( define-sort ⟨symbol⟩ ( ⟨symbol⟩∗ ) ⟨sort⟩ )
                write!(
                    f,
                    "(define-sort {} ({}) {})",
                    symbol,
                    parameters
                        .iter()
                        .map(|s| format!("{}", s))
                        .collect::<Vec<_>>()
                        .join(" "),
                    sort
                )
            }
            Echo { message } => write!(f, "(echo {})", Constant::String(message.clone())),
            Exit => write!(f, "(exit)"),
            GetAssertions => write!(f, "(get-assertions)"),
            GetAssignment => write!(f, "(get-assignment)"),
            GetInfo { flag } => write!(f, "(get-info {})", flag),
            GetModel => write!(f, "(get-model)"),
            GetOption { keyword } => write!(f, "(get-info {})", keyword),
            GetProof => write!(f, "(get-proof)"),
            GetUnsatAssumptions => write!(f, "(get-unsat-assumptions)"),
            GetUnsatCore => write!(f, "(get-unsat-core)"),
            GetValue { terms } => {
                // ( get-value ( ⟨term⟩+ ) )
                write!(
                    f,
                    "(get-value ({}))",
                    terms
                        .iter()
                        .map(|t| format!("{}", t))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            Pop { level } => write!(f, "(pop {})", Constant::Numeral(level.clone())),
            Push { level } => write!(f, "(push {})", Constant::Numeral(level.clone())),
            Reset => write!(f, "(reset)"),
            ResetAssertions => write!(f, "(reset-assertions)"),
            SetInfo { keyword, value } => write!(f, "(set-info {} {})", keyword, value),
            SetLogic { symbol } => write!(f, "(set-logic {})", symbol),
            SetOption { keyword, value } => write!(f, "(set-option {} {})", keyword, value),
        }
    }
}

/// Parse a single-token attribute value.
pub fn parse_simple_attribute_value(input: &str) -> Option<AttributeValue> {
    use crate::parser::Token;
    let token = lexer::Lexer::new(input.as_bytes()).next()?;
    match token {
        Token::Numeral(x) => Some(AttributeValue::Constant(Constant::Numeral(x))),
        Token::Decimal(x) => Some(AttributeValue::Constant(Constant::Decimal(x))),
        Token::String(x) => Some(AttributeValue::Constant(Constant::String(x))),
        Token::Binary(x) => Some(AttributeValue::Constant(Constant::Binary(x))),
        Token::Hexadecimal(x) => Some(AttributeValue::Constant(Constant::Hexadecimal(x))),
        Token::Symbol(x) => Some(AttributeValue::Symbol(Symbol(x))),
        _ => None,
    }
}
