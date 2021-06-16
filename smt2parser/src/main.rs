// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use smt2parser::{concrete::SyntaxBuilder, stats::Smt2Counters, CommandStream};
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "smt2bin",
    about = "Demo tool for processing files with smt2parser"
)]
struct Options {
    /// Operation
    #[structopt(subcommand)]
    operation: Operation,
}

#[derive(Debug, StructOpt)]
enum Operation {
    Print {
        /// Path to the SMT2 files.
        #[structopt(parse(from_os_str))]
        inputs: Vec<PathBuf>,
    },
    Count {
        /// Optional path to keyword file. One keyword per line.
        #[structopt(long, parse(from_os_str))]
        keywords: Option<PathBuf>,

        /// Optional path to symbol file. One symbol per line.
        #[structopt(long, parse(from_os_str))]
        symbols: Option<PathBuf>,

        /// Path to the SMT2 files.
        #[structopt(parse(from_os_str))]
        inputs: Vec<PathBuf>,
    },
}

fn process_file<T, F>(state: T, file_path: PathBuf, f: F) -> std::io::Result<T>
where
    T: smt2parser::visitors::Smt2Visitor,
    F: Fn(T::Command),
    T::Error: std::fmt::Display,
{
    let file = std::io::BufReader::new(std::fs::File::open(&file_path)?);
    let mut stream = CommandStream::new(file, state, file_path.to_str().map(String::from));
    for result in &mut stream {
        match result {
            Ok(command) => f(command),
            Err(error) => {
                eprintln!("{}", error);
                break;
            }
        }
    }
    Ok(stream.into_visitor())
}

fn read_words(path: Option<PathBuf>) -> std::io::Result<Vec<String>> {
    match path {
        None => Ok(Vec::new()),
        Some(path) => {
            use std::io::BufRead;
            let file = std::io::BufReader::new(std::fs::File::open(&path)?);
            file.lines().collect()
        }
    }
}

fn main() -> std::io::Result<()> {
    let options = Options::from_args();
    match options.operation {
        Operation::Print { inputs } => {
            for input in inputs {
                process_file(SyntaxBuilder, input, |command| println!("{}", command))?;
            }
        }
        Operation::Count {
            keywords,
            symbols,
            inputs,
        } => {
            let keywords = read_words(keywords)?;
            let symbols = read_words(symbols)?;
            let mut state = Smt2Counters::new(keywords, symbols);
            for input in inputs {
                state = process_file(state, input, |_| {})?;
            }
            println!("{:#?}", state)
        }
    }
    Ok(())
}
