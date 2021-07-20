// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The `smt2patch` library provides the SMT2 "patching" functionalities and
//! configurations used by the binary tool `smt2patch`.

use smt2parser::concrete::*;
use std::{io::Write, path::Path};
use structopt::StructOpt;

/// Configuration for the SMT2 rewriting operations.
#[derive(Debug, Default, Clone, StructOpt)]
pub struct RewriterConfig {}

/// State of the SMT2 rewriter.
#[derive(Debug)]
pub struct Rewriter {
    config: RewriterConfig,
    builder: SyntaxBuilder,
}

impl Rewriter {
    pub fn new(config: RewriterConfig) -> Self {
        Self {
            config,
            builder: SyntaxBuilder::default(),
        }
    }
}

fn get_slice3(v: Vec<Term>) -> [Term; 3] {
    assert_eq!(v.len(), 3);
    let mut it = v.into_iter();
    [it.next().unwrap(), it.next().unwrap(), it.next().unwrap()]
}

fn make_simple_qual_ident(name: String) -> QualIdentifier {
    QualIdentifier::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol(name),
        },
    }
}

impl smt2parser::rewriter::Rewriter for Rewriter {
    type V = SyntaxBuilder;
    type Error = smt2parser::concrete::Error;

    fn visitor(&mut self) -> &mut SyntaxBuilder {
        &mut self.builder
    }

    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Term>,
    ) -> Result<Term, Self::Error> {
        let value = match (qual_identifier, arguments) {
            (
                QualIdentifier::Simple {
                    identifier:
                        Identifier::Simple {
                            symbol: Symbol(name),
                        },
                },
                args,
            ) if name == "store" && args.len() == 3 => {
                let [a, i, q] = get_slice3(args);
                let seq_update = make_simple_qual_ident("seq.update".to_string());
                let seq_unit = make_simple_qual_ident("seq.unit".to_string());
                let s = Term::Application {
                    qual_identifier: seq_unit,
                    arguments: vec![q],
                };
                Term::Application {
                    qual_identifier: seq_update,
                    arguments: vec![a, i, s],
                }
            }
            (qual_identifier, arguments) => Term::Application {
                qual_identifier,
                arguments,
            },
        };
        self.process_term(value)
    }
}

#[derive(Debug, Clone, StructOpt)]
pub struct PatcherConfig {
    #[structopt(flatten)]
    rewriter_config: RewriterConfig,
}

/// State of the SMT2 patcher.
#[derive(Debug)]
pub struct Patcher {
    config: PatcherConfig,
    script: Vec<Command>,
}

impl Patcher {
    pub fn new(config: PatcherConfig) -> Self {
        Self {
            config,
            script: Vec::new(),
        }
    }

    pub fn read(&mut self, path: &Path) -> std::io::Result<()> {
        let file = std::io::BufReader::new(std::fs::File::open(path)?);
        let rewriter = Rewriter::new(self.config.rewriter_config.clone());
        let mut stream =
            smt2parser::CommandStream::new(file, rewriter, path.to_str().map(String::from));
        for result in &mut stream {
            match result {
                Ok(command) => {
                    self.script.push(command);
                }
                Err(error) => {
                    panic!("{}", error);
                }
            }
        }
        Ok(())
    }

    pub fn write(&self, path: &Path) -> std::io::Result<()> {
        let mut file = std::fs::File::create(path)?;
        for command in &self.script {
            writeln!(file, "{}", command)?;
        }
        Ok(())
    }
}
