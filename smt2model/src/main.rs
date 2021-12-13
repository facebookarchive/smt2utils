// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use anyhow::Result;
use smt2model::{
    graph::{GraphBuilder, GraphBuilderConfig},
    rewriter::{Error, Rewriter, RewriterConfig},
};
use smt2parser::{concrete::SyntaxBuilder, renaming::TesterModernizer, CommandStream};
use std::{
    io::Write,
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};
use structopt::{clap::arg_enum, StructOpt};

arg_enum! {
#[derive(Debug, StructOpt, Clone, Copy)]
enum OutputFormat {
    Smt,
    Dot,
}
}

/// Compute simple features for SMT2 files (including Z3 execution time).
#[derive(Debug, StructOpt)]
struct Options {
    /// Output Format.
    #[structopt(long, possible_values = &OutputFormat::variants(), case_insensitive = true, default_value = "smt")]
    format: OutputFormat,
    #[structopt(flatten)]
    rewriter_config: RewriterConfig,
    #[structopt(flatten)]
    graph_builder_config: GraphBuilderConfig,
    /// Output directory.
    #[structopt(long)]
    output_dir: Option<PathBuf>,
    /// Whether to concatenate all outputs into a single file.
    #[structopt(long)]
    output_file: Option<PathBuf>,
    /// Whether to skip input files that seem to have been processed already.
    #[structopt(long)]
    incremental: bool,
    /// Discard input files whose bucket number is higher or equal than `sampling_offset + sampling_increment`.
    #[structopt(long, default_value = "1")]
    sampling_increment: u64,
    /// Discard input files whose bucket number is lower than `sampling_offset`.
    #[structopt(long, default_value = "0")]
    sampling_offset: u64,
    /// Set the number of buckets 0..=(N-1) used for sampling base paths. See --sampling-increment and --sampling-offset
    #[structopt(long, default_value = "1")]
    sampling_total: u64,
    /// Whether to reschedule a slurm job in case of interruptions.
    #[structopt(long)]
    slurm: bool,
    /// Path to the smt2 files.
    #[structopt(parse(from_os_str))]
    inputs: Vec<PathBuf>,
}

fn append_os_str(mut os_str: std::ffi::OsString, ext: &std::ffi::OsStr) -> std::ffi::OsString {
    os_str.push(ext);
    os_str
}

fn append_suffix(path: PathBuf, suffix: &str) -> PathBuf {
    append_os_str(path.into_os_string(), suffix.as_ref()).into()
}

fn parse_suffix<'a>(s: &'a str, suffix: &str) -> Option<&'a str> {
    if s.ends_with(suffix) {
        Some(&s[0..s.len() - suffix.len()])
    } else {
        None
    }
}

fn parse_tar_gz_base_path(path: &Path) -> Option<&str> {
    let s = path.to_str().unwrap_or("");
    parse_suffix(s, ".tar.gz").or_else(|| parse_suffix(s, ".tgz"))
}

fn parse_smt_base_path(path: &Path) -> Option<&str> {
    let s = path.to_str().unwrap_or("");
    parse_suffix(s, ".smt").or_else(|| parse_suffix(s, ".smt2"))
}

fn get_output_path(format: OutputFormat, output_dir: &Path, entry: &Path) -> PathBuf {
    let entry = if entry.is_relative() {
        PathBuf::from(&output_dir).join(entry)
    } else {
        entry.to_path_buf()
    };
    let s = match format {
        OutputFormat::Smt => ".out.smt2",
        OutputFormat::Dot => ".out.dot",
    };
    append_suffix(entry, s)
}

fn handle_input(
    rewriter_config: RewriterConfig,
    graph_builder_config: GraphBuilderConfig,
    format: OutputFormat,
    append: bool,
    output_path: &Path,
    input_path: &Path,
) -> Result<()> {
    if append {
        eprintln!(
            "Writing {} with data from {}",
            output_path.to_str().unwrap_or(""),
            input_path.to_str().unwrap_or("")
        );
    } else {
        eprintln!("Writing {}", output_path.to_str().unwrap_or(""));
    }
    let file = std::io::BufReader::new(std::fs::File::open(&input_path)?);
    let mut builder = GraphBuilder::new(graph_builder_config);
    let mut stream = CommandStream::new(
        file,
        Rewriter::new(rewriter_config, TesterModernizer::new(SyntaxBuilder)),
        input_path.to_str().map(String::from),
    );
    std::fs::create_dir_all(output_path.parent().unwrap_or_else(|| Path::new(".")))?;
    let mut output = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(append)
        .open(output_path)?;
    let mut need_space = false;
    for result in &mut stream {
        match result {
            Ok(command) => {
                // Visit the syntax again for name-binding-aware rewriting.
                let command = command.accept(&mut builder)?;
                // Print the command.
                if let OutputFormat::Smt = format {
                    if need_space {
                        write!(output, " ")?;
                    }
                    builder.write_smt_ast(&mut output, command)?;
                    if append {
                        need_space = true;
                    } else {
                        writeln!(output)?;
                    }
                }
            }
            Err(Error::SkipCommand) => {}
            Err(error) => {
                eprintln!("{}", error);
                break;
            }
        }
    }
    if let OutputFormat::Dot = format {
        use petgraph::{dot::*, visit::NodeRef};

        let graph = builder.to_graph();
        // let dot = petgraph::dot::Dot::new(&graph);
        let dot = Dot::with_attr_getters(
            &graph,
            &[Config::NodeNoLabel, Config::EdgeNoLabel],
            &|_, er| format!("label = \"{}\"", er.weight()),
            &|_, nr| {
                let w = nr.weight();
                // '"' '\\' '\n'
                format!("label = \"{}\"", w)
            },
        );
        writeln!(output, "{:?}", dot)?;
    }
    if append {
        writeln!(output)?;
    }
    Ok(())
}

fn is_selected(options: &Options, path: &Path) -> bool {
    use rand::{Rng, SeedableRng};
    use std::hash::{Hash, Hasher};

    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    path.hash(&mut hasher);
    let seed = hasher.finish();
    let mut rng = rand::rngs::SmallRng::seed_from_u64(seed);
    let s = rng.gen_range(0..options.sampling_total);
    s >= options.sampling_offset && s < options.sampling_offset + options.sampling_increment
}

fn process_input<F, G>(
    options: &Options,
    sigterm: &AtomicBool,
    sigusr: &AtomicBool,
    output_dir: &Path,
    input_path: &Path,
    mut pre_process: F,
    post_process: G,
) -> Result<()>
where
    F: FnMut(&Path) -> Result<Option<PathBuf>>,
    G: Fn(&Path) -> std::io::Result<()>,
{
    if sigterm.swap(false, Ordering::Relaxed) {
        eprintln!("Ignoring SIGTERM");
    }
    if sigusr.swap(false, Ordering::Relaxed) {
        eprintln!("Handling SIGUSR1");
        // TODO: to be future-proof, we must test that this is not a child process.
        if let Ok("0") = std::env::var("SLURM_PROCID").as_deref() {
            if let Ok(id) = std::env::var("SLURM_JOB_ID") {
                let status = std::process::Command::new("scontrol")
                    .args(&["requeue", &id])
                    .status()?;
                eprintln!("scontrol finished with: {}", status);
            }
        }
        anyhow::bail!("Interrupted by SIGUSR1");
    }
    if !is_selected(options, input_path) {
        // Entry is not selected.
        return Ok(());
    }
    if parse_smt_base_path(input_path).is_none() {
        eprintln!(
            "Skipping non-SMT entry {}",
            input_path.to_str().unwrap_or("")
        );
        return Ok(());
    }
    let output_path = match &options.output_file {
        Some(path) => {
            if options.sampling_total > 1 {
                append_suffix(path.clone(), &format!(".{}", options.sampling_offset))
            } else {
                path.clone()
            }
        }
        None => get_output_path(options.format, output_dir, input_path),
    };

    if options.incremental && output_path.exists() {
        eprintln!(
            "Skipping processed entry {}",
            input_path.to_str().unwrap_or("")
        );
        return Ok(());
    }

    let input = match pre_process(input_path)? {
        None => return Ok(()),
        Some(i) => i,
    };
    match handle_input(
        options.rewriter_config.clone(),
        options.graph_builder_config.clone(),
        options.format,
        options.output_file.is_some(),
        &output_path,
        &input,
    ) {
        Ok(()) => (),
        Err(e) => {
            eprintln!(
                "Error while sampling {}: {} (skipping entry)",
                input.to_str().unwrap_or(""),
                e
            );
        }
    };
    post_process(&input)?;
    Ok(())
}

fn main() -> Result<()> {
    let options = Options::from_args();
    if options.incremental && options.output_file.is_some() {
        panic!("--incremental and --output-file cannot be used at the same time.");
    }
    let sigterm = Arc::new(AtomicBool::new(false));
    let siguser = Arc::new(AtomicBool::new(false));
    if options.slurm {
        signal_hook::flag::register(signal_hook::consts::SIGTERM, Arc::clone(&sigterm))?;
        signal_hook::flag::register(signal_hook::consts::SIGUSR1, Arc::clone(&siguser))?;
    }
    let output_dir = options
        .output_dir
        .clone()
        .unwrap_or_else(|| PathBuf::from("."));
    std::fs::create_dir_all(&output_dir)?;
    for input in &options.inputs {
        if parse_tar_gz_base_path(&input).is_some() {
            // Tar-gz archive.
            let tmp_dir = tempfile::tempdir()?;
            let tgz_input = std::fs::File::open(&input)?;
            let tar_input = flate2::read::GzDecoder::new(tgz_input);
            let mut archive = tar::Archive::new(tar_input);
            for entry in archive.entries()? {
                let mut entry = entry?;
                let input_path = entry.path()?.to_path_buf();
                process_input(
                    &options,
                    &sigterm,
                    &siguser,
                    &output_dir,
                    &input_path,
                    |input_path| {
                        // Make input file ready.
                        let input = tmp_dir.path().join(input_path);
                        if !entry.unpack_in(tmp_dir.path())? {
                            // Entries outside `tmp_dir` are skipped.
                            eprintln!("Skipping incorrect path {}", input.to_str().unwrap_or(""));
                            Ok(None)
                        } else {
                            Ok(Some(input))
                        }
                    },
                    |input| std::fs::remove_file(&input),
                )?;
            }
        } else {
            // Plain SMT2 file.
            process_input(
                &options,
                &sigterm,
                &siguser,
                &output_dir,
                &input,
                |path| Ok(Some(path.to_path_buf())),
                |_| Ok(()),
            )?;
        }
    }
    Ok(())
}
