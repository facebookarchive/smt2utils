// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use z3tracer::{LogConfig, Model};

use std::io::BufRead;
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

    let mut model = Model::default();
    for line in file.lines() {
        let line = line?;
        match model.process_line(line.as_ref()) {
            Ok(Some(qi)) => {
                model.log_instance(config, qi).unwrap();
            }
            Ok(None) => {
                continue;
            }
            Err(e) => {
                panic!("Error:\n{}\n{:?}\n", line, e);
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
