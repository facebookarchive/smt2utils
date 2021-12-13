// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use smt2parser::{
    concrete::{Constant, Symbol},
    visitors, Binary, Decimal, Error, Hexadecimal, Numeral, Position,
};
use std::collections::{BTreeSet, HashMap};
use structopt::StructOpt;

#[derive(Debug, Default, StructOpt, Clone)]
pub struct GraphBuilderConfig {
    /// Whether to add space around word tokens.
    #[structopt(long)]
    add_spaces: bool,
    /// Whether to keep the original symbol names in text outputs.
    #[structopt(long)]
    keep_symbols: bool,
    /// Whether to tag local symbol node with their names in graph outputs.
    #[structopt(long)]
    export_local_names: bool,
    /// Whether to normalize datatype declarations.
    #[structopt(long)]
    normalize_datatype_dec: bool,
    /// Whether to reuse generated symbol names (x0, x1, ..) when possible.
    #[structopt(long)]
    reuse_symbol_indices: bool,
}

/// State of the graph writer.
#[derive(Debug, Default)]
pub struct GraphBuilder {
    config: GraphBuilderConfig,
    nodes: Vec<Node>,
    commands: Vec<NodeRef>,
    bound_symbols: HashMap<String, Vec<NodeRef>>,
    // Used to generate fresh names for local symbols.
    next_symbol_index: usize,
    available_symbol_indices: BTreeSet<usize>,
    globals: HashMap<String, NodeRef>,
    constants: HashMap<Constant, NodeRef>,
    keywords: HashMap<String, NodeRef>,
    identifiers: HashMap<visitors::Identifier<NodeRef>, NodeRef>,
}

// This corresponds to syntactic tokens.
#[derive(Debug)]
pub enum Node {
    Constant(Constant),
    // Local symbols are considered anonymous in graph outputs unless --export-local-names
    // is passed.
    LocalSymbol(String, usize),
    GlobalSymbol(String),
    Keyword(String),
    Sequence(SeqKind, Vec<NodeRef>),
}

#[derive(Debug, Clone, Copy)]
pub enum SeqKind {
    // Anonymous sequences
    Script,
    AttributeValue,
    ConstructorDecSymbol,
    ConstructorDec,
    DatatypeDec,
    DatatypeDecParams,
    DatatypeDecConstr,
    FunctionDec,
    FunctionDecParams,
    SExpr,
    Sort,
    Application,
    VarBinding,
    VarBindings,
    Pattern,
    Case,
    Cases,
    // Primitive
    Not,
    // Reserved keywords
    Underscore,
    Exclam,
    As,
    Let,
    Exists,
    Forall,
    Match,
    Par,
    Assert,
    CheckSat,
    CheckSatAssuming,
    CheckSatAssumingLiterals,
    DeclareConst,
    DeclareDatatype,
    DeclareDatatypes,
    DeclareDatatypesArity,
    DeclareDatatypesSorts,
    DeclareDatatypesTypes,
    DeclareFun,
    DeclareFunParams,
    DeclareSort,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
    DefineFunsRecSig,
    DefineFunsRecSigs,
    DefineFunsRecTerms,
    DefineSort,
    DefineSortParams,
    Echo,
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo,
    GetModel,
    GetOption,
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue,
    GetValueTerms,
    Pop,
    Push,
    Reset,
    ResetAssertions,
    SetInfo,
    SetLogic,
    SetOption,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
pub struct NodeRef(usize);

impl GraphBuilder {
    pub fn new(config: GraphBuilderConfig) -> Self {
        GraphBuilder {
            config,
            ..Self::default()
        }
    }

    pub fn write_smt_ast<W: std::io::Write>(
        &self,
        f: &mut W,
        node: NodeRef,
    ) -> std::io::Result<()> {
        use Node::*;
        match &self.nodes[node.0] {
            Constant(c) => {
                write!(f, "{}", c)?;
            }
            LocalSymbol(name, _) if self.config.keep_symbols => {
                write!(f, "{}", Symbol(name.to_string()))?;
            }
            LocalSymbol(_, n) => {
                write!(f, "x{}", n)?;
            }
            GlobalSymbol(name) => {
                write!(f, "{}", Symbol(name.to_string()))?;
            }
            Keyword(name) => {
                write!(f, ":{}", name)?;
            }
            Sequence(kind, nodes) if self.config.add_spaces => {
                write!(f, "( ")?;
                if let Some(name) = kind.reserved_name() {
                    write!(f, "{} ", name)?;
                }
                for node in nodes {
                    self.write_smt_ast(f, *node)?;
                    write!(f, " ")?;
                }
                write!(f, ")")?;
            }
            Sequence(kind, nodes) => {
                write!(f, "(")?;
                let mut nodes = nodes.iter();
                match kind.reserved_name() {
                    Some(name) => {
                        write!(f, "{}", name)?;
                    }
                    None => {
                        if let Some(node) = nodes.next() {
                            self.write_smt_ast(f, *node)?;
                        }
                    }
                }
                for node in nodes {
                    write!(f, " ")?;
                    self.write_smt_ast(f, *node)?;
                }
                write!(f, ")")?;
            }
        }
        Ok(())
    }

    pub fn to_graph(&self) -> petgraph::graph::Graph<String, usize> {
        let mut pg_nodes = Vec::new();
        let mut graph = petgraph::graph::Graph::new();
        let mut edge_count = 0;
        for node in &self.nodes {
            use Node::*;
            let label = match node {
                Constant(c) => c.to_string(),
                LocalSymbol(name, _) if self.config.keep_symbols => {
                    format!("{}", Symbol(name.to_string()))
                }
                LocalSymbol(_, n) => format!("x{}", n),
                GlobalSymbol(name) => format!("{}", Symbol(name.to_string())),
                Keyword(name) => format!(":{}", name),
                Sequence(kind, _) => format!("{:?}", kind),
            };
            let n = graph.add_node(label);
            if let Sequence(_, nodes) = node {
                edge_count += nodes.len();
                for (i, node) in nodes.iter().enumerate() {
                    graph.add_edge(n, pg_nodes[node.0], i);
                }
            }
            pg_nodes.push(n);
        }
        let n = graph.add_node("SCRIPT".to_string());
        for (i, command) in self.commands.iter().enumerate() {
            edge_count += 1;
            graph.add_edge(n, pg_nodes[command.0], i);
        }
        eprintln!(
            "Done exporting graph with {} nodes and {} edges",
            self.nodes.len() + 1,
            edge_count
        );
        graph
    }
}

type AttributeValue = visitors::AttributeValue<NodeRef, NodeRef, NodeRef>;
type ConstructorDec = visitors::ConstructorDec<NodeRef, NodeRef>;
type DatatypeDec = visitors::DatatypeDec<NodeRef, NodeRef>;
type FunctionDec = visitors::FunctionDec<NodeRef, NodeRef>;

impl SeqKind {
    fn reserved_name(self) -> Option<&'static str> {
        use SeqKind::*;
        match self {
            Underscore => Some("_"),
            Exclam => Some("!"),
            As => Some("as"),
            Let => Some("let"),
            Exists => Some("exists"),
            Forall => Some("forall"),
            Match => Some("match"),
            Par => Some("par"),
            Assert => Some("assert"),
            CheckSat => Some("check-sat"),
            CheckSatAssuming => Some("check-sat-assuming"),
            DeclareConst => Some("declare-const"),
            DeclareDatatype => Some("declare-datatype"),
            DeclareDatatypes => Some("declare-datatypes"),
            DeclareFun => Some("declare-fun"),
            DeclareSort => Some("declare-sort"),
            DefineFun => Some("define-fun"),
            DefineFunRec => Some("define-fun-rec"),
            DefineFunsRec => Some("define-funs-rec"),
            DefineSort => Some("define-sort"),
            Echo => Some("echo"),
            Exit => Some("exit"),
            GetAssertions => Some("get-assertions"),
            GetAssignment => Some("get-assignment"),
            GetInfo => Some("get-info"),
            GetModel => Some("get-model"),
            GetOption => Some("get-option"),
            GetProof => Some("get-proof"),
            GetUnsatAssumptions => Some("get-unsat-assumptions"),
            GetUnsatCore => Some("get-unsat-core"),
            GetValue => Some("get-value"),
            Pop => Some("pop"),
            Push => Some("push"),
            Reset => Some("reset"),
            ResetAssertions => Some("reset-assertions"),
            SetInfo => Some("set-info"),
            SetLogic => Some("set-logic"),
            SetOption => Some("set-option"),
            _ => None,
        }
    }
}

impl GraphBuilder {
    fn make_node(&mut self, node: Node) -> NodeRef {
        let i = self.nodes.len();
        self.nodes.push(node);
        NodeRef(i)
    }

    fn make_sequence(&mut self, kind: SeqKind, children: Vec<NodeRef>) -> NodeRef {
        self.make_node(Node::Sequence(kind, children))
    }

    fn make_constant(&mut self, value: Constant) -> NodeRef {
        if let Some(n) = self.constants.get(&value) {
            return *n;
        }
        let n = self.make_node(Node::Constant(value.clone()));
        self.constants.insert(value, n);
        n
    }

    fn make_keyword(&mut self, value: String) -> NodeRef {
        if let Some(n) = self.keywords.get(&value) {
            return *n;
        }
        let n = self.make_node(Node::Keyword(value.clone()));
        self.keywords.insert(value, n);
        n
    }

    fn make_local_symbol(&mut self, name: String) -> NodeRef {
        if self.config.reuse_symbol_indices {
            if let Some(k) = self.available_symbol_indices.iter().next() {
                // Reuse symbol index of previously unbinded symbol.
                let k = *k;
                self.available_symbol_indices.remove(&k);
                return self.make_node(Node::LocalSymbol(name, k));
            }
        }
        let node = Node::LocalSymbol(name, self.next_symbol_index);
        self.next_symbol_index += 1;
        self.make_node(node)
    }

    fn make_global_symbol(&mut self, value: String) -> NodeRef {
        if let Some(n) = self.globals.get(&value) {
            return *n;
        }
        let n = self.make_node(Node::GlobalSymbol(value.clone()));
        self.globals.insert(value, n);
        n
    }

    fn make_attribute_value(&mut self, value: AttributeValue) -> Option<NodeRef> {
        use visitors::AttributeValue::*;
        match value {
            None => Option::None,
            Constant(c) => Some(c),
            Symbol(s) => Some(s),
            SExpr(exprs) => Some(self.make_sequence(SeqKind::AttributeValue, exprs)),
        }
    }

    fn make_constructor_dec(&mut self, value: ConstructorDec) -> NodeRef {
        let mut children = vec![value.symbol];
        for (symbol, sort) in value.selectors {
            children.push(self.make_sequence(SeqKind::ConstructorDecSymbol, vec![symbol, sort]))
        }
        self.make_sequence(SeqKind::ConstructorDecSymbol, children)
    }

    fn make_datatype_dec(&mut self, value: DatatypeDec) -> NodeRef {
        let constructors = value
            .constructors
            .into_iter()
            .map(|c| self.make_constructor_dec(c))
            .collect();
        if value.parameters.is_empty() && !self.config.normalize_datatype_dec {
            self.make_sequence(SeqKind::DatatypeDec, constructors)
        } else {
            let children = vec![
                self.make_sequence(SeqKind::DatatypeDecParams, value.parameters),
                self.make_sequence(SeqKind::DatatypeDecConstr, constructors),
            ];
            self.make_sequence(SeqKind::Par, children)
        }
    }

    fn make_function_dec(&mut self, value: FunctionDec) -> Vec<NodeRef> {
        let parameters = value
            .parameters
            .into_iter()
            .map(|(symbol, sort)| {
                self.make_sequence(SeqKind::FunctionDecParams, vec![symbol, sort])
            })
            .collect();
        vec![
            value.name,
            self.make_sequence(SeqKind::FunctionDec, parameters),
            value.result,
        ]
    }

    fn symbol_name(&self, s: NodeRef) -> Option<&str> {
        match &self.nodes[s.0] {
            Node::LocalSymbol(s, _) | Node::GlobalSymbol(s) => Some(s),
            _ => None,
        }
    }

    fn make_identifier(&mut self, value: visitors::Identifier<NodeRef>) -> NodeRef {
        match &value {
            visitors::Identifier::Simple { symbol } => *symbol,
            visitors::Identifier::Indexed { symbol, indices } => {
                if let Some(c) = self.identifiers.get(&value) {
                    return *c;
                }
                let mut children = vec![*symbol];
                for i in indices {
                    let m = match i {
                        visitors::Index::Numeral(n) => {
                            self.make_constant(Constant::Numeral(n.clone()))
                        }
                        visitors::Index::Symbol(s) => *s,
                    };
                    children.push(m);
                }
                let n = self.make_sequence(SeqKind::Underscore, children);
                self.identifiers.insert(value, n);
                n
            }
        }
    }
}

impl visitors::ConstantVisitor for GraphBuilder {
    type T = NodeRef;
    type E = Error;

    fn visit_numeral_constant(&mut self, value: Numeral) -> Result<Self::T, Self::E> {
        Ok(self.make_constant(Constant::Numeral(value)))
    }
    fn visit_decimal_constant(&mut self, value: Decimal) -> Result<Self::T, Self::E> {
        Ok(self.make_constant(Constant::Decimal(value)))
    }
    fn visit_hexadecimal_constant(&mut self, value: Hexadecimal) -> Result<Self::T, Self::E> {
        Ok(self.make_constant(Constant::Hexadecimal(value)))
    }
    fn visit_binary_constant(&mut self, value: Binary) -> Result<Self::T, Self::E> {
        Ok(self.make_constant(Constant::Binary(value)))
    }
    fn visit_string_constant(&mut self, value: String) -> Result<Self::T, Self::E> {
        Ok(self.make_constant(Constant::String(value)))
    }
}

impl visitors::SymbolVisitor for GraphBuilder {
    type T = NodeRef;
    type E = Error;

    fn visit_bound_symbol(&mut self, value: String) -> Result<Self::T, Self::E> {
        let s = self
            .bound_symbols
            .get(&value)
            .map(|v| *v.last().unwrap())
            .unwrap_or_else(|| self.make_global_symbol(value));
        Ok(s)
    }

    fn visit_fresh_symbol(
        &mut self,
        value: String,
        _: visitors::SymbolKind,
    ) -> Result<Self::T, Self::E> {
        Ok(self.make_local_symbol(value))
    }

    fn bind_symbol(&mut self, symbol: &NodeRef) {
        let name = self.symbol_name(*symbol).unwrap().to_string();
        self.bound_symbols.entry(name).or_default().push(*symbol);
    }

    fn unbind_symbol(&mut self, symbol: &NodeRef) {
        use std::collections::hash_map;

        let name = self.symbol_name(*symbol).unwrap().to_string();
        match self.bound_symbols.entry(name) {
            hash_map::Entry::Occupied(mut e) => {
                let node = e.get_mut().pop().unwrap();
                if self.config.reuse_symbol_indices {
                    if let Node::LocalSymbol(_, k) = &self.nodes[node.0] {
                        // Make symbol index available for the next call to make_local_symbol.
                        self.available_symbol_indices.insert(*k);
                    }
                }
                if e.get().is_empty() {
                    e.remove_entry();
                }
            }
            _ => panic!("invalid entry"),
        }
    }
}

impl visitors::KeywordVisitor for GraphBuilder {
    type T = NodeRef;
    type E = Error;

    fn visit_keyword(&mut self, value: String) -> Result<Self::T, Self::E> {
        Ok(self.make_keyword(value))
    }
}

impl visitors::SExprVisitor<NodeRef, NodeRef, NodeRef> for GraphBuilder {
    type T = NodeRef;
    type E = Error;

    fn visit_constant_s_expr(&mut self, value: NodeRef) -> Result<Self::T, Self::E> {
        Ok(value)
    }

    fn visit_symbol_s_expr(&mut self, value: NodeRef) -> Result<Self::T, Self::E> {
        Ok(value)
    }

    fn visit_keyword_s_expr(&mut self, value: NodeRef) -> Result<Self::T, Self::E> {
        Ok(value)
    }

    fn visit_application_s_expr(&mut self, values: Vec<Self::T>) -> Result<Self::T, Self::E> {
        Ok(self.make_sequence(SeqKind::SExpr, values))
    }
}

impl visitors::SortVisitor<NodeRef> for GraphBuilder {
    type T = NodeRef;
    type E = Error;

    fn visit_simple_sort(
        &mut self,
        identifier: visitors::Identifier<NodeRef>,
    ) -> Result<Self::T, Self::E> {
        Ok(self.make_identifier(identifier))
    }

    fn visit_parameterized_sort(
        &mut self,
        identifier: visitors::Identifier<NodeRef>,
        parameters: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        let mut children = vec![self.make_identifier(identifier)];
        children.extend(parameters);
        Ok(self.make_sequence(SeqKind::Sort, children))
    }
}

impl visitors::QualIdentifierVisitor<visitors::Identifier<NodeRef>, NodeRef> for GraphBuilder {
    type T = NodeRef;
    type E = Error;

    fn visit_simple_identifier(
        &mut self,
        identifier: visitors::Identifier<NodeRef>,
    ) -> Result<Self::T, Self::E> {
        Ok(self.make_identifier(identifier))
    }

    fn visit_sorted_identifier(
        &mut self,
        identifier: visitors::Identifier<NodeRef>,
        sort: NodeRef,
    ) -> Result<Self::T, Self::E> {
        let children = vec![self.make_identifier(identifier), sort];
        Ok(self.make_sequence(SeqKind::As, children))
    }
}

impl visitors::TermVisitor<NodeRef, NodeRef, NodeRef, NodeRef, NodeRef, NodeRef> for GraphBuilder {
    type T = NodeRef;
    type E = Error;

    fn visit_constant(&mut self, constant: NodeRef) -> Result<Self::T, Self::E> {
        Ok(constant)
    }

    fn visit_qual_identifier(&mut self, qual_identifier: NodeRef) -> Result<Self::T, Self::E> {
        Ok(qual_identifier)
    }

    fn visit_application(
        &mut self,
        qual_identifier: NodeRef,
        arguments: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        let mut children = vec![qual_identifier];
        children.extend(arguments);
        Ok(self.make_sequence(SeqKind::Application, children))
    }

    fn visit_let(
        &mut self,
        var_bindings: Vec<(NodeRef, Self::T)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        let var_bindings = var_bindings
            .into_iter()
            .map(|(x, t)| self.make_sequence(SeqKind::VarBinding, vec![x, t]))
            .collect();
        let children = vec![self.make_sequence(SeqKind::VarBindings, var_bindings), term];
        Ok(self.make_sequence(SeqKind::Let, children))
    }

    fn visit_forall(
        &mut self,
        vars: Vec<(NodeRef, NodeRef)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        let var_bindings = vars
            .into_iter()
            .map(|(x, t)| self.make_sequence(SeqKind::VarBinding, vec![x, t]))
            .collect();
        let children = vec![self.make_sequence(SeqKind::VarBindings, var_bindings), term];
        Ok(self.make_sequence(SeqKind::Forall, children))
    }

    fn visit_exists(
        &mut self,
        vars: Vec<(NodeRef, NodeRef)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        let var_bindings = vars
            .into_iter()
            .map(|(x, t)| self.make_sequence(SeqKind::VarBinding, vec![x, t]))
            .collect();
        let children = vec![self.make_sequence(SeqKind::VarBindings, var_bindings), term];
        Ok(self.make_sequence(SeqKind::Exists, children))
    }

    fn visit_match(
        &mut self,
        term: Self::T,
        cases: Vec<(Vec<NodeRef>, Self::T)>,
    ) -> Result<Self::T, Self::E> {
        let cases = cases
            .into_iter()
            .map(|(xs, t)| {
                let xs = self.make_sequence(SeqKind::Pattern, xs);
                self.make_sequence(SeqKind::Case, vec![xs, t])
            })
            .collect();
        let children = vec![term, self.make_sequence(SeqKind::Cases, cases)];
        Ok(self.make_sequence(SeqKind::Match, children))
    }

    fn visit_attributes(
        &mut self,
        term: Self::T,
        attributes: Vec<(NodeRef, AttributeValue)>,
    ) -> Result<Self::T, Self::E> {
        let mut children = vec![term];
        for (keyword, value) in attributes {
            children.push(keyword);
            if let Some(value) = self.make_attribute_value(value) {
                children.push(value);
            }
        }
        Ok(self.make_sequence(SeqKind::Exclam, children))
    }
}

impl visitors::CommandVisitor<NodeRef, NodeRef, NodeRef, NodeRef, NodeRef, NodeRef>
    for GraphBuilder
{
    type T = NodeRef;
    type E = Error;

    fn visit_assert(&mut self, term: NodeRef) -> Result<Self::T, Self::E> {
        let children = vec![term];
        let n = self.make_sequence(SeqKind::Assert, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_check_sat(&mut self) -> Result<Self::T, Self::E> {
        let children = Vec::new();
        let n = self.make_sequence(SeqKind::CheckSat, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_check_sat_assuming(
        &mut self,
        literals: Vec<(NodeRef, bool)>,
    ) -> Result<Self::T, Self::E> {
        let literals = literals
            .into_iter()
            .map(|(n, x)| {
                if x {
                    n
                } else {
                    let children = vec![n];
                    self.make_sequence(SeqKind::Not, children)
                }
            })
            .collect();
        let children = vec![self.make_sequence(SeqKind::CheckSatAssumingLiterals, literals)];
        let n = self.make_sequence(SeqKind::CheckSatAssuming, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_declare_const(&mut self, symbol: NodeRef, sort: NodeRef) -> Result<Self::T, Self::E> {
        let children = vec![symbol, sort];
        let n = self.make_sequence(SeqKind::DeclareConst, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_declare_datatype(
        &mut self,
        symbol: NodeRef,
        datatype: DatatypeDec,
    ) -> Result<Self::T, Self::E> {
        let children = vec![symbol, self.make_datatype_dec(datatype)];
        let n = self.make_sequence(SeqKind::DeclareDatatype, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_declare_datatypes(
        &mut self,
        datatypes: Vec<(NodeRef, Numeral, DatatypeDec)>,
    ) -> Result<Self::T, Self::E> {
        let sorts = datatypes
            .iter()
            .map(|(sym, num, _)| {
                let n = self.make_constant(Constant::Numeral(num.clone()));
                self.make_sequence(SeqKind::DeclareDatatypesArity, vec![*sym, n])
            })
            .collect();
        let types = datatypes
            .iter()
            .map(|(_, _, ty)| self.make_datatype_dec(ty.clone()))
            .collect();
        let children = vec![
            self.make_sequence(SeqKind::DeclareDatatypesSorts, sorts),
            self.make_sequence(SeqKind::DeclareDatatypesTypes, types),
        ];
        let n = self.make_sequence(SeqKind::DeclareDatatypes, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_declare_fun(
        &mut self,
        symbol: NodeRef,
        parameters: Vec<NodeRef>,
        sort: NodeRef,
    ) -> Result<Self::T, Self::E> {
        let children = vec![
            symbol,
            self.make_sequence(SeqKind::DeclareFunParams, parameters),
            sort,
        ];
        let n = self.make_sequence(SeqKind::DeclareFun, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_declare_sort(&mut self, symbol: NodeRef, arity: Numeral) -> Result<Self::T, Self::E> {
        let children = vec![symbol, self.make_constant(Constant::Numeral(arity))];
        let n = self.make_sequence(SeqKind::DeclareSort, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_define_fun(&mut self, sig: FunctionDec, term: NodeRef) -> Result<Self::T, Self::E> {
        let mut children = self.make_function_dec(sig);
        children.push(term);
        let n = self.make_sequence(SeqKind::DefineFun, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_define_fun_rec(
        &mut self,
        sig: FunctionDec,
        term: NodeRef,
    ) -> Result<Self::T, Self::E> {
        let mut children = self.make_function_dec(sig);
        children.push(term);
        let n = self.make_sequence(SeqKind::DefineFunRec, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_define_funs_rec(
        &mut self,
        funs: Vec<(FunctionDec, NodeRef)>,
    ) -> Result<Self::T, Self::E> {
        let sigs = funs
            .iter()
            .map(|(sig, _)| {
                let sig = self.make_function_dec(sig.clone());
                self.make_sequence(SeqKind::DefineFunsRecSig, sig)
            })
            .collect();
        let terms = funs.iter().map(|(_, t)| *t).collect();
        let children = vec![
            self.make_sequence(SeqKind::DefineFunsRecSigs, sigs),
            self.make_sequence(SeqKind::DefineFunsRecTerms, terms),
        ];
        let n = self.make_sequence(SeqKind::DefineFunsRec, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_define_sort(
        &mut self,
        symbol: NodeRef,
        parameters: Vec<NodeRef>,
        sort: NodeRef,
    ) -> Result<Self::T, Self::E> {
        let children = vec![
            symbol,
            self.make_sequence(SeqKind::DefineSortParams, parameters),
            sort,
        ];
        let n = self.make_sequence(SeqKind::DefineSort, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_echo(&mut self, message: String) -> Result<Self::T, Self::E> {
        let children = vec![self.make_constant(Constant::String(message))];
        let n = self.make_sequence(SeqKind::Echo, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_exit(&mut self) -> Result<Self::T, Self::E> {
        let n = self.make_sequence(SeqKind::Exit, Vec::new());
        self.commands.push(n);
        Ok(n)
    }

    fn visit_get_assertions(&mut self) -> Result<Self::T, Self::E> {
        let n = self.make_sequence(SeqKind::GetAssertions, Vec::new());
        self.commands.push(n);
        Ok(n)
    }

    fn visit_get_assignment(&mut self) -> Result<Self::T, Self::E> {
        let n = self.make_sequence(SeqKind::GetAssignment, Vec::new());
        self.commands.push(n);
        Ok(n)
    }

    fn visit_get_info(&mut self, flag: NodeRef) -> Result<Self::T, Self::E> {
        let children = vec![flag];
        let n = self.make_sequence(SeqKind::GetInfo, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_get_model(&mut self) -> Result<Self::T, Self::E> {
        let n = self.make_sequence(SeqKind::GetModel, Vec::new());
        self.commands.push(n);
        Ok(n)
    }

    fn visit_get_option(&mut self, keyword: NodeRef) -> Result<Self::T, Self::E> {
        let children = vec![keyword];
        let n = self.make_sequence(SeqKind::GetOption, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_get_proof(&mut self) -> Result<Self::T, Self::E> {
        let n = self.make_sequence(SeqKind::GetProof, Vec::new());
        self.commands.push(n);
        Ok(n)
    }

    fn visit_get_unsat_assumptions(&mut self) -> Result<Self::T, Self::E> {
        let n = self.make_sequence(SeqKind::GetUnsatAssumptions, Vec::new());
        self.commands.push(n);
        Ok(n)
    }

    fn visit_get_unsat_core(&mut self) -> Result<Self::T, Self::E> {
        let n = self.make_sequence(SeqKind::GetUnsatCore, Vec::new());
        self.commands.push(n);
        Ok(n)
    }

    fn visit_get_value(&mut self, terms: Vec<NodeRef>) -> Result<Self::T, Self::E> {
        let children = vec![self.make_sequence(SeqKind::GetValueTerms, terms)];
        let n = self.make_sequence(SeqKind::GetValue, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_pop(&mut self, level: Numeral) -> Result<Self::T, Self::E> {
        let children = vec![self.make_constant(Constant::Numeral(level))];
        let n = self.make_sequence(SeqKind::Pop, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_push(&mut self, level: Numeral) -> Result<Self::T, Self::E> {
        let children = vec![self.make_constant(Constant::Numeral(level))];
        let n = self.make_sequence(SeqKind::Push, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_reset(&mut self) -> Result<Self::T, Self::E> {
        let n = self.make_sequence(SeqKind::Reset, Vec::new());
        self.commands.push(n);
        Ok(n)
    }

    fn visit_reset_assertions(&mut self) -> Result<Self::T, Self::E> {
        let n = self.make_sequence(SeqKind::ResetAssertions, Vec::new());
        self.commands.push(n);
        Ok(n)
    }

    fn visit_set_info(
        &mut self,
        keyword: NodeRef,
        value: AttributeValue,
    ) -> Result<Self::T, Self::E> {
        let mut children = vec![keyword];
        if let Some(value) = self.make_attribute_value(value) {
            children.push(value);
        }
        let n = self.make_sequence(SeqKind::SetInfo, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_set_logic(&mut self, symbol: NodeRef) -> Result<Self::T, Self::E> {
        let children = vec![symbol];
        let n = self.make_sequence(SeqKind::SetLogic, children);
        self.commands.push(n);
        Ok(n)
    }

    fn visit_set_option(
        &mut self,
        keyword: NodeRef,
        value: AttributeValue,
    ) -> Result<Self::T, Self::E> {
        let mut children = vec![keyword];
        if let Some(value) = self.make_attribute_value(value) {
            children.push(value);
        }
        let n = self.make_sequence(SeqKind::SetOption, children);
        self.commands.push(n);
        Ok(n)
    }
}

impl visitors::Smt2Visitor for GraphBuilder {
    type Error = Error;
    type Constant = NodeRef;
    type QualIdentifier = NodeRef;
    type Keyword = NodeRef;
    type Sort = NodeRef;
    type SExpr = NodeRef;
    type Symbol = NodeRef;
    type Term = NodeRef;
    type Command = NodeRef;

    fn syntax_error(&mut self, pos: Position, s: String) -> Self::Error {
        Error::SyntaxError(pos, s)
    }

    fn parsing_error(&mut self, pos: Position, s: String) -> Self::Error {
        Error::ParsingError(pos, s)
    }
}
