// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use z3tracer::{Model, ModelConfig};

use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "z3tracer", about = "Utility for Z3 tracing log files")]
struct Options {
    #[structopt(flatten)]
    config: ModelConfig,

    /// Path to the Z3 log files.
    #[structopt(parse(from_os_str))]
    inputs: Vec<PathBuf>,
}

fn process_file(config: ModelConfig, path: PathBuf) -> std::io::Result<()> {
    eprintln!("Processing {}", path.to_str().unwrap_or(""));
    let file = std::io::BufReader::new(std::fs::File::open(&path)?);
    let mut model = Model::new(config);
    if let Err(le) = model.process(path.to_str().map(String::from), file) {
        panic!("Error at {:?}: {:?}", le.position, le.error);
    }
    eprintln!("Done processing {}", path.to_str().unwrap_or(""));
    eprintln!("- Terms: {}", model.terms().len());
    eprintln!("- Instantiations: {}", model.instantiations().len());
    Ok(())
}

fn main() {
    let options = Options::from_args();
    for input in options.inputs {
        process_file(options.config.clone(), input).unwrap();
    }
}
