// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use structopt::StructOpt;

/// Patch for SMT2 commands. Compatible with the command-line syntax of Z3.
#[derive(Debug, StructOpt)]
struct Options {
    /// Output file
    #[structopt(long, default_value = "/dev/stdout")]
    output: std::path::PathBuf,

    #[structopt(flatten)]
    config: smt2patch::PatcherConfig,

    /// Input file
    input: std::path::PathBuf,
}

fn main() -> anyhow::Result<()> {
    let options = Options::from_args();

    eprintln!("Current options: {:#?}", options);

    let mut patcher = smt2patch::Patcher::new(options.config);
    patcher.read(&options.input)?;
    patcher.write(&options.output)?;
    Ok(())
}
