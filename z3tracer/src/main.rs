// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use z3tracer::Model;

use std::io::BufRead;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "z3tracer", about = "Utility for Z3 tracing log files")]
struct Options {
    /// Path to the Z3 log files.
    #[structopt(parse(from_os_str))]
    inputs: Vec<PathBuf>,
}

fn process_file(path: PathBuf) -> std::io::Result<()> {
    let file = std::io::BufReader::new(std::fs::File::open(&path)?);

    let mut model = Model::default();
    for line in file.lines() {
        let line = line?;
        if let Err(e) = model.process_line(line.as_ref()) {
            panic!("Error:\n{}\n{:?}\n", line, e);
        }
    }
    println!("Terms: {}", model.terms().len());
    println!("Instantiations: {}", model.instantiations().len());
    println!("Equalities: {}", model.equalities().len());
    Ok(())
}

fn main() {
    let options = Options::from_args();
    for input in options.inputs {
        process_file(input).unwrap();
    }
}
