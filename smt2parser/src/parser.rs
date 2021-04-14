// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![allow(unused_braces)]
#![allow(clippy::type_complexity)]
#![allow(clippy::upper_case_acronyms)]

pub use internal::{Parser, Token};

pomelo! {
    %module internal;
    %include { use crate::visitors; }

    %stack_size 0;

    %parser pub struct Parser<'a, T: visitors::Smt2Visitor> {};
    %extra_argument &'a mut T;

    %token #[derive(Clone, Debug, PartialEq, Eq)] pub enum Token {};

    %type Keyword String;
    %type Symbol String;
    %type Numeral crate::Numeral;
    %type Decimal crate::Decimal;
    %type Hexadecimal crate::Hexadecimal;
    %type Binary crate::Binary;
    %type String String;

    %type command T::Command;

    %type term T::Term;
    %type terms Vec<T::Term>;

    %type constant T::Constant;
    %type qual_identifier T::QualIdentifier;
    %type identifier visitors::Identifier<T::Symbol>;

    %type symbol T::Symbol;
    %type symbols Vec<T::Symbol>;
    %type pattern Vec<T::Symbol>;

    %type keyword T::Keyword;

    %type sort T::Sort;
    %type sorts Vec<T::Sort>;

    %type attribute_value visitors::AttributeValue<T::Constant, T::Symbol, T::SExpr>;
    %type attributes Vec<(T::Keyword, visitors::AttributeValue<T::Constant, T::Symbol, T::SExpr>)>;

    %type s_expr T::SExpr;
    %type s_exprs Vec<T::SExpr>;

    %type index visitors::Index<T::Symbol>;
    %type indices Vec<visitors::Index<T::Symbol>>;

    %type var_binding (T::Symbol, T::Term);
    %type var_bindings Vec<(T::Symbol, T::Term)>;

    %type sorted_var (T::Symbol, T::Sort);
    %type sorted_vars Vec<(T::Symbol, T::Sort)>;

    %type match_case (Vec<T::Symbol>, T::Term);
    %type match_cases Vec<(Vec<T::Symbol>, T::Term)>;

    %type prop_literal (T::Symbol, bool);
    %type prop_literals Vec<(T::Symbol, bool)>;

    %type datatype_dec visitors::DatatypeDec<T::Symbol, T::Sort>;
    %type datatype_decs Vec<visitors::DatatypeDec<T::Symbol, T::Sort>>;

    %type selector_dec (T::Symbol, T::Sort);
    %type selector_decs Vec<(T::Symbol, T::Sort)>;

    %type constructor_dec visitors::ConstructorDec<T::Symbol, T::Sort>;
    %type constructor_decs Vec<visitors::ConstructorDec<T::Symbol, T::Sort>>;

    %type function_dec visitors::FunctionDec<T::Symbol, T::Sort>;
    %type function_decs Vec<visitors::FunctionDec<T::Symbol, T::Sort>>;

    %type sort_dec (T::Symbol, crate::Numeral);
    %type sort_decs Vec<(T::Symbol, crate::Numeral)>;

    %start_symbol command;

    symbol ::= Symbol(s) { extra.visit_symbol(s) }
    keyword ::= Keyword(s) { extra.visit_keyword(s) }

    symbols ::= symbol(x) { vec![x] }
    symbols ::= symbols(mut xs) symbol(x) { xs.push(x); xs }

    // attribute_value ::= ⟨spec_constant⟩ | ⟨symbol⟩ | ( ⟨s_expr⟩∗ ) |
    attribute_value ::= constant(x) { visitors::AttributeValue::Constant(x) }
    attribute_value ::= symbol(x) { visitors::AttributeValue::Symbol(x) }
    attribute_value ::= LeftParen s_exprs?(xs) RightParen { visitors::AttributeValue::SExpr(xs.unwrap_or_else(Vec::new)) }
    attribute_value ::= { visitors::AttributeValue::None }

    attributes ::= keyword(k) attribute_value(v) { vec![(k, v)] }
    attributes ::= attributes(mut xs) keyword(k) attribute_value(v) { xs.push((k, v)); xs }

    // s_expr ::= ⟨spec_constant⟩ | ⟨symbol⟩ | ⟨keyword⟩ | ( ⟨s_expr⟩∗ )
    s_expr ::= constant(x) { extra.visit_constant_s_expr(x) }
    s_expr ::= symbol(x) { extra.visit_symbol_s_expr(x) }
    s_expr ::= keyword(x) { extra.visit_keyword_s_expr(x) }
    s_expr ::= LeftParen s_exprs?(xs) RightParen { extra.visit_application_s_expr(xs.unwrap_or_else(Vec::new)) }

    s_exprs ::= s_expr(x) { vec![x] }
    s_exprs ::= s_exprs(mut xs) s_expr(x) { xs.push(x); xs }

    // index ::= ⟨numeral⟩ | ⟨symbol⟩
    index ::= Numeral(x) { visitors::Index::Numeral(x) }
    index ::= symbol(x) { visitors::Index::Symbol(x) }

    indices ::= index(x) { vec![x] }
    indices ::= indices(mut xs) index(x) { xs.push(x); xs }

    // identifier ::= ⟨symbol⟩ | ( _ ⟨symbol⟩ ⟨index⟩+ )
    identifier ::= symbol(symbol) { visitors::Identifier::Simple { symbol } }
    identifier ::= LeftParen Underscore symbol(symbol) indices(indices) RightParen { visitors::Identifier::Indexed { symbol, indices } }

    // sort ::= ⟨identifier⟩ | ( ⟨identifier⟩ ⟨sort⟩+ )
    sort ::= identifier(id) { extra.visit_simple_sort(id) }
    sort ::= LeftParen identifier(id) sorts(sorts) RightParen { extra.visit_parameterized_sort(id, sorts) }

    sorts ::= sort(x) { vec![x] }
    sorts ::= sorts(mut xs) sort(x) { xs.push(x); xs }

    // qual_identifier ::= ⟨identifier⟩ | ( as ⟨identifier⟩ ⟨sort⟩ )
    qual_identifier ::= identifier(x) { extra.visit_simple_identifier(x) }
    qual_identifier ::= LeftParen As identifier(id) sort(s) RightParen { extra.visit_sorted_identifier(id, s) }

    // constant ::= ⟨numeral⟩ | ⟨decimal⟩ | ⟨hexadecimal⟩ | ⟨binary⟩ | ⟨string⟩
    constant ::= Numeral(x) { extra.visit_numeral_constant(x) }
    constant ::= Decimal(x) { extra.visit_decimal_constant(x) }
    constant ::= Hexadecimal(x) { extra.visit_hexadecimal_constant(x) }
    constant ::= Binary(x) { extra.visit_binary_constant(x) }
    constant ::= String(x) { extra.visit_string_constant(x) }

    // ⟨var_binding⟩ ::= ( ⟨symbol⟩ ⟨term⟩ )
    var_binding ::= LeftParen symbol(s) term(t) RightParen { (s, t) }

    var_bindings ::= var_binding(x) { vec![x] }
    var_bindings ::= var_bindings(mut xs) var_binding(x) { xs.push(x); xs }

    // ⟨sorted_var⟩ ::= ( ⟨symbol⟩ ⟨sort⟩ )
    sorted_var ::= LeftParen symbol(s) sort(x) RightParen { (s, x) }

    sorted_vars ::= sorted_var(x) { vec![x] }
    sorted_vars ::= sorted_vars(mut xs) sorted_var(x) { xs.push(x); xs }

    // pattern ::= ⟨symbol⟩ | ( ⟨symbol⟩ ⟨symbol⟩+ )
    pattern ::= symbol(x) { vec![x] }
    pattern ::= LeftParen symbols(xs) RightParen { xs }

    // ⟨match_case⟩ ::= ( ⟨pattern⟩ ⟨term⟩ )
    match_case ::= LeftParen pattern(p) term(t) RightParen { (p, t) }

    match_cases ::= match_case(x) { vec![x] }
    match_cases ::= match_cases(mut xs) match_case(x) { xs.push(x); xs }

    // terms ::= ...
    //   ⟨spec_constant⟩
    term ::= constant(x) { extra.visit_constant(x) }
    //   ⟨qual_identifier⟩
    term ::= qual_identifier(x) { extra.visit_qual_identifier(x) }
    //   ( let ( ⟨var_binding⟩+ ) ⟨term⟩ )
    term ::= LeftParen Let LeftParen var_bindings(xs) RightParen term(t) RightParen { extra.visit_let(xs, t) }
    //   ( forall ( ⟨sorted_var⟩+ ) ⟨term⟩ )
    term ::= LeftParen Forall LeftParen sorted_vars(xs) RightParen term(t) RightParen { extra.visit_forall(xs, t) }
    //   ( exists ( ⟨sorted_var⟩+ ) ⟨term⟩ )
    term ::= LeftParen Exists LeftParen sorted_vars(xs) RightParen term(t) RightParen { extra.visit_exists(xs, t) }
    //   ( match ⟨term⟩ ( ⟨match_case⟩+ ) )
    term ::= LeftParen Match term(t) LeftParen match_cases(xs) RightParen RightParen { extra.visit_match(t, xs) }
    //   ( ! ⟨term⟩ ⟨attribute⟩+ )
    term ::= LeftParen Exclam term(t) attributes(xs) RightParen { extra.visit_attributes(t, xs) }
    //   ( ⟨qual_identifier ⟩ ⟨term⟩+ )
    term ::= LeftParen qual_identifier(id) terms(xs) RightParen { extra.visit_application(id, xs) }

    terms ::= term(x) { vec![x] }
    terms ::= terms(mut xs) term(x) { xs.push(x); xs }

    // prop_literal ::= ⟨symbol⟩ | ( not ⟨symbol⟩ )
    prop_literal ::= symbol(x) { (x, true) }
    prop_literal ::= LeftParen Symbol(s) symbol(x) RightParen {
        if s != "not" {
            return Err(());
        }
        (x, false)
    }

    prop_literals ::= prop_literal(x) { vec![x] }
    prop_literals ::= prop_literals(mut xs) prop_literal(x) { xs.push(x); xs }

    // ⟨selector_dec⟩ ::= ( ⟨symbol⟩ ⟨sort⟩ )
    selector_dec ::= LeftParen symbol(x) sort(s) RightParen { (x, s) }

    selector_decs ::= selector_dec(x) { vec![x] }
    selector_decs ::= selector_decs(mut xs) selector_dec(x) { xs.push(x); xs }

    // constructor_dec ::= ( ⟨symbol⟩ ⟨selector_dec⟩∗ )
    constructor_dec ::= LeftParen symbol(x) selector_decs?(xs) RightParen
    {
        visitors::ConstructorDec { symbol:x, selectors:xs.unwrap_or_else(Vec::new) }
    }

    constructor_decs ::= constructor_dec(x) { vec![x] }
    constructor_decs ::= constructor_decs(mut xs) constructor_dec(x) { xs.push(x); xs }

    // datatype_dec ::= ( ⟨constructor_dec⟩+ ) | ( par ( ⟨symbol⟩+ ) ( ⟨constructor_dec⟩+ ) )
    datatype_dec ::= LeftParen constructor_decs(xs) RightParen
    {
        visitors::DatatypeDec { parameters: Vec::new(), constructors: xs }
    }
    datatype_dec ::= LeftParen Par LeftParen symbols(ps) RightParen LeftParen constructor_decs(xs) RightParen RightParen
    {
        visitors::DatatypeDec { parameters: ps, constructors: xs }
    }

    datatype_decs ::= datatype_dec(x) { vec![x] }
    datatype_decs ::= datatype_decs(mut xs) datatype_dec(x) { xs.push(x); xs }

    // function_dec ::= ⟨symbol⟩ ( ⟨sorted_var⟩∗ ) ⟨sort⟩
    function_dec ::= symbol(x) LeftParen sorted_vars?(xs) RightParen sort(s)
    {
        visitors::FunctionDec {
            name: x,
            parameters: xs.unwrap_or_else(Vec::new),
            result: s,
        }
    }

    function_decs ::= function_dec(x) { vec![x] }
    function_decs ::= function_decs(mut xs) function_dec(x) { xs.push(x); xs }

    // sort_dec ::= ( ⟨symbol⟩ ⟨numeral⟩ )
    sort_dec ::= LeftParen symbol(x) Numeral(num) RightParen { (x, num) }

    sort_decs ::= sort_dec(x) { vec![x] }
    sort_decs ::= sort_decs(mut xs) sort_dec(x) { xs.push(x); xs }

    // command ::= ...
    //   ( assert ⟨term⟩ )
    command ::= LeftParen Assert term(t) RightParen { extra.visit_assert(t) }
    //   ( check-sat )
    command ::= LeftParen CheckSat RightParen { extra.visit_check_sat() }
    //   ( check-sat-assuming ( ⟨prop_literal⟩∗ ) )
    command ::= LeftParen CheckSatAssuming LeftParen prop_literals?(xs) RightParen RightParen
    {
        extra.visit_check_sat_assuming(xs.unwrap_or_else(Vec::new))
    }
    //   ( declare-const ⟨symbol⟩ ⟨sort⟩ )
    command ::= LeftParen DeclareConst symbol(x) sort(s) RightParen
    {
        extra.visit_declare_const(x, s)
    }
    //   ( declare-datatype ⟨symbol⟩ ⟨datatype_dec⟩)
    command ::= LeftParen DeclareDatatype symbol(s) datatype_dec(d) RightParen
    {
        extra.visit_declare_datatype(s, d)
    }
    //   ( declare-datatypes ( ⟨sort_dec⟩n+1 ) ( ⟨datatype_dec⟩n+1 ) )
    command ::= LeftParen DeclareDatatypes LeftParen sort_decs(sorts) RightParen LeftParen datatype_decs(datatypes) RightParen RightParen
    {
        if sorts.len() == datatypes.len() {
            let results = sorts
                .into_iter()
                .zip(datatypes.into_iter())
                .map(|((sort, arity), datatype)| (sort, arity, datatype))
                .collect::<Vec<_>>();
            extra.visit_declare_datatypes(results)
        } else {
            return Err(());
        }
    }
    //   ( declare-fun ⟨symbol⟩ ( ⟨sort⟩∗ ) ⟨sort⟩ )
    command ::= LeftParen DeclareFun symbol(x) LeftParen sorts?(xs) RightParen sort(r) RightParen
    {
        extra.visit_declare_fun(x, xs.unwrap_or_else(Vec::new), r)
    }
    //   ( declare-sort ⟨symbol⟩ ⟨numeral⟩ )
    command ::= LeftParen DeclareSort symbol(x) Numeral(num) RightParen
    {
        extra.visit_declare_sort(x, num)
    }
    //   ( define-fun ⟨function_dec⟩ ⟨term⟩ )
    command ::= LeftParen DefineFun function_dec(d) term(x) RightParen
    {
        extra.visit_define_fun(d, x)
    }
    //   ( define-fun-rec ⟨function_dec⟩ ⟨term⟩ )
    command ::= LeftParen DefineFunRec function_dec(d) term(x) RightParen
    {
        extra.visit_define_fun_rec(d, x)
    }
    //   ( define-funs-rec ( ( ⟨function_dec⟩ )n+1 ) ( ⟨term⟩n+1 ) )
    command ::= LeftParen DefineFunsRec LeftParen function_decs(sigs) RightParen LeftParen terms(xs) RightParen RightParen
    {
        if sigs.len() == xs.len() {
            let defs = sigs.into_iter().zip(xs.into_iter()).collect::<Vec<_>>();
            extra.visit_define_funs_rec(defs)
        } else {
            return Err(());
        }
    }
    //   ( define-sort ⟨symbol⟩ ( ⟨symbol⟩∗ ) ⟨sort⟩ )
    command ::= LeftParen DefineSort symbol(x) LeftParen symbols?(xs) RightParen sort(r) RightParen
    {
        extra.visit_define_sort(x, xs.unwrap_or_else(Vec::new), r)
    }
    //   ( echo ⟨string⟩ )
    command ::= LeftParen Echo String(x) RightParen { extra.visit_echo(x) }
    //   ( exit )
    command ::= LeftParen Exit RightParen { extra.visit_exit() }
    //   ( get-assertions )
    command ::= LeftParen GetAssertions RightParen { extra.visit_get_assertions() }
    //   ( get-assignment )
    command ::= LeftParen GetAssignments RightParen { extra.visit_get_assignment() }
    //   ( get-info ⟨info_flag⟩ )
    command ::= LeftParen GetInfo keyword(x) RightParen { extra.visit_get_info(x) }
    //   ( get-model )
    command ::= LeftParen GetModel RightParen { extra.visit_get_model() }
    //   ( get-option ⟨keyword⟩ )
    command ::= LeftParen GetOption keyword(x) RightParen { extra.visit_get_option(x) }
    //   ( get-proof )
    command ::= LeftParen GetProof RightParen { extra.visit_get_proof() }
    //   ( get-unsat-assumptions )
    command ::= LeftParen GetUnsatAssumptions RightParen { extra.visit_get_unsat_assumptions() }
    //   ( get-unsat-core )
    command ::= LeftParen GetUnsatCore RightParen { extra.visit_get_unsat_core() }
    //   ( get-value )
    command ::= LeftParen GetValue terms(xs) RightParen { extra.visit_get_value(xs) }
    //   ( pop ⟨numeral⟩ )
    command ::= LeftParen Pop Numeral(x) RightParen { extra.visit_pop(x) }
    //   ( push ⟨numeral⟩ )
    command ::= LeftParen Push Numeral(x) RightParen { extra.visit_push(x) }
    //   ( reset )
    command ::= LeftParen Reset RightParen { extra.visit_reset() }
    //   ( reset-assertions )
    command ::= LeftParen ResetAssertions RightParen { extra.visit_reset_assertions() }
    //   ( set-info ⟨attribute⟩ )
    command ::= LeftParen SetInfo keyword(k) attribute_value(v) RightParen { extra.visit_set_info(k, v) }
    //   ( set-logic ⟨symbol⟩ )
    command ::= LeftParen SetLogic symbol(x) RightParen { extra.visit_set_logic(x) }
    //   ( set-option ⟨attribute⟩ )
    command ::= LeftParen SetOption keyword(k) attribute_value(v) RightParen { extra.visit_set_option(k, v) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{concrete::*, lexer::Lexer};

    fn parse_tokens<I: IntoIterator<Item = Token>>(tokens: I) -> Result<Command, ()> {
        let mut builder = SyntaxBuilder;
        let mut p = Parser::new(&mut builder);
        for token in tokens.into_iter() {
            p.parse(token)?;
        }
        Ok(p.end_of_input()?.0)
    }

    #[test]
    fn test_echo() {
        let value = parse_tokens(vec![
            Token::LeftParen,
            Token::Echo,
            Token::String("foo".into()),
            Token::RightParen,
        ])
        .unwrap();
        assert_eq!(
            value,
            Command::Echo {
                message: "foo".into()
            }
        );
    }

    #[test]
    fn test_assert_term() {
        let value = parse_tokens(Lexer::new(&b"(assert 12)"[..])).unwrap();
        assert_eq!(
            value,
            Command::Assert {
                term: Term::Constant(Constant::Numeral(num::BigUint::from(12u32))),
            }
        );

        let value = parse_tokens(Lexer::new(&b"(assert (as A B))"[..])).unwrap();
        assert_eq!(
            value,
            Command::Assert {
                term: Term::QualIdentifier(QualIdentifier::Sorted {
                    identifier: Identifier::Simple {
                        symbol: Symbol("A".into())
                    },
                    sort: Sort::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("B".into())
                        }
                    },
                })
            },
        );

        let value = parse_tokens(Lexer::new(&b"(assert (let ((x (f x 2))) (= x 3)))"[..])).unwrap();
        assert_eq!(
            value,
            Command::Assert {
                term: Term::Let {
                    var_bindings: vec![(
                        Symbol("x".into()),
                        Term::Application {
                            qual_identifier: QualIdentifier::Simple {
                                identifier: Identifier::Simple {
                                    symbol: Symbol("f".into())
                                }
                            },
                            arguments: vec![
                                Term::QualIdentifier(QualIdentifier::Simple {
                                    identifier: Identifier::Simple {
                                        symbol: Symbol("x".into())
                                    }
                                }),
                                Term::Constant(Constant::Numeral(num::BigUint::from(2u32)))
                            ]
                        }
                    )],
                    term: Box::new(Term::Application {
                        qual_identifier: QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("=".into())
                            }
                        },
                        arguments: vec![
                            Term::QualIdentifier(QualIdentifier::Simple {
                                identifier: Identifier::Simple {
                                    symbol: Symbol("x".into())
                                }
                            }),
                            Term::Constant(Constant::Numeral(num::BigUint::from(3u32)))
                        ]
                    }),
                }
            }
        );

        let value = parse_tokens(Lexer::new(
            &b"(assert (forall ((x Bool) (y Int)) (f x y))\n ; dfg \n )"[..],
        ))
        .unwrap();
        assert!(matches!(
            value,
            Command::Assert {
                term: Term::Forall { .. }
            }
        ));

        let result = parse_tokens(Lexer::new(&b"(assert (forall () (f x y)))"[..]));
        assert!(result.is_err());

        let value = parse_tokens(Lexer::new(
            &b"(assert ( ;foo\n match 3 ( (x (+ x 2)) ) ))"[..],
        ))
        .unwrap();
        assert!(matches!(
            value,
            Command::Assert {
                term: Term::Match { .. }
            }
        ));

        let value = parse_tokens(Lexer::new(&b"(assert ( ! 3 :f 1 :g (a 3) ))"[..])).unwrap();
        assert!(matches!(
            value,
            Command::Assert {
                term: Term::Attributes { .. }
            }
        ));

        let value = parse_tokens(Lexer::new(&b"(assert ( f 1 2 3 ))"[..])).unwrap();
        assert!(matches!(
            value,
            Command::Assert {
                term: Term::Application { .. }
            }
        ));
    }

    #[test]
    fn test_declare_datatypes_with_comment() {
        let value = parse_tokens(Lexer::new(&b"(declare-datatypes ((T@$TypeValue 0)(T@$TypeValueArray 0)) ((($BooleanType ) ($IntegerType ) ($AddressType ) ($StrType ) ($VectorType (|t#$VectorType| T@$TypeValue) ) ($StructType (|name#$StructType| T@$TypeName) (|ts#$StructType| T@$TypeValueArray) ) ($TypeType ) ($ErrorType ) ) (($TypeValueArray (|v#$TypeValueArray| |T@[Int]$TypeValue|) (|l#$TypeValueArray| Int) ) ) ))"[..])).unwrap();

        assert!(matches!(value, Command::DeclareDatatypes { .. }));
        // Test syntax visiting while we're at it.
        assert_eq!(
            value,
            value.clone().accept(&mut crate::concrete::SyntaxBuilder)
        );
    }
}
