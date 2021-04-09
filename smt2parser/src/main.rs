// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use smt2parser::{concrete::SyntaxBuilder, stats::StatsHolder, CommandStream};
use std::path::PathBuf;
use structopt::{clap::arg_enum, StructOpt};

arg_enum! {
#[derive(Debug, StructOpt)]
enum Operation {
    Print,
    Count,
}
}

#[derive(Debug, StructOpt)]
#[structopt(name = "smt2bin", about = "Utility for SMT2 files")]
struct Options {
    /// Operation
    #[structopt(possible_values = &Operation::variants(), case_insensitive = true)]
    operation: Operation,

    /// Path to the SMT2 files.
    #[structopt(parse(from_os_str))]
    inputs: Vec<PathBuf>,
}

fn process_file<T, F>(state: T, file_path: PathBuf, f: F) -> T
where
    T: smt2parser::visitors::Smt2Visitor,
    F: Fn(T::Command),
{
    let file =
        std::io::BufReader::new(std::fs::File::open(&file_path).expect("Cannot read input file"));
    let mut stream = CommandStream::new(file, state);
    for result in &mut stream {
        match result {
            Ok(command) => f(command),
            Err(error) => {
                eprintln!("error:\n --> {}", error.location_in_file(&file_path));
                break;
            }
        }
    }
    stream.into_visitor()
}

fn main() {
    let options = Options::from_args();
    match options.operation {
        Operation::Print => {
            for input in options.inputs {
                process_file(SyntaxBuilder, input, |command| println!("{}", command));
            }
        }

        Operation::Count => {
            let mut state = StatsHolder::default();
            for input in options.inputs {
                state = process_file(state, input, |_| {});
            }
            println!("{:#?}", state)
        }
    }
}
