// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use z3tracer::{error::Error, Lexer, LogConfig, Model};

use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "z3tracer", about = "Utility for Z3 tracing log files")]
struct Options {
    #[structopt(flatten)]
    config: LogConfig,

    /// Path to the Z3 log files.
    #[structopt(parse(from_os_str))]
    inputs: Vec<PathBuf>,
}

fn process_file(config: &LogConfig, path: PathBuf) -> std::io::Result<()> {
    let file = std::io::BufReader::new(std::fs::File::open(&path)?);
    let mut lexer = Lexer::new(file);

    let mut model = Model::default();
    loop {
        match model.process_line(&mut lexer) {
            Ok(Some(qi)) => {
                model.log_instance(config, qi).unwrap();
            }
            Ok(None) => {
                // Command was processed but it's not a QI.
                continue;
            }
            Err(Error::EndOfInput) => {
                break;
            }
            Err(e) => {
                panic!(
                    "Error at {:?}:{:?}: {:?}",
                    path,
                    lexer.current_position(),
                    e
                );
            }
        };
    }
    println!("Terms: {}", model.terms().len());
    println!("Instantiations: {}", model.instantiations().len());
    println!("Equalities: {}", model.equalities().len());
    Ok(())
}

fn main() {
    let options = Options::from_args();
    for input in options.inputs {
        process_file(&options.config, input).unwrap();
    }
}
