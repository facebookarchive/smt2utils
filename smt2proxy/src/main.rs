// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use std::{
    io::{BufRead, Write},
    sync::{Arc, Mutex},
};
use structopt::StructOpt;

/// Proxy for SMT2 commands. Compatible with the command-line syntax of Z3.
#[derive(Debug, StructOpt)]
struct Options {
    /// Use SMT2 input format (ignored, always true).
    #[structopt(long)]
    smt2: bool,

    /// Print Z3 version.
    #[structopt(long)]
    version: bool,

    /// Use stdin for Z3 input.
    #[structopt(long)]
    r#in: bool,

    /// Z3 soft query timeout in milliseconds.
    #[structopt(long)]
    t: Option<u32>,

    /// Z3 verbose level.
    #[structopt(long)]
    v: Option<u32>,

    /// Z3 virtual memory limit in MB.
    #[structopt(long)]
    memory: Option<u32>,

    /// Have Z3 display statistics.
    #[structopt(long)]
    st: bool,

    /// Have Z3 display a model for satisfiable queries.
    #[structopt(long)]
    model: bool,

    /// Input file
    #[structopt(long)]
    file: Option<std::path::PathBuf>,

    /// Extra arguments for Z3: `key=value` arguments and optional input file at the end.
    #[structopt(name = "EXTRA")]
    extra: Vec<String>,

    #[structopt(flatten)]
    smt2proxy_config: smt2proxy::CommandProcessorConfig,
}

// Z3 CLI compatibility: allow long args to start with a single `-` and short/long args to use `:` instead of `=`.
fn iter_args() -> impl Iterator<Item = std::ffi::OsString> {
    std::env::args().map(|arg| {
        if arg.starts_with('-') && arg.len() > 2 {
            match arg.find(':') {
                None => "-".to_string() + &arg,
                Some(n) if n > 2 => "-".to_string() + &arg.replace(':', "="),
                _ => arg.replace(':', "="),
            }
            .into()
        } else {
            arg.into()
        }
    })
}

fn make_z3_args(options: &Options) -> Vec<String> {
    let mut args = vec!["-smt2".to_string(), "-in".to_string()];
    if let Some(x) = &options.t {
        args.push(format!("-t:{}", x))
    }
    if let Some(x) = &options.v {
        args.push(format!("-v:{}", x))
    }
    if let Some(x) = &options.memory {
        args.push(format!("-memory:{}", x))
    }
    if options.st {
        args.push("-st".into());
    }
    if options.model {
        args.push("-model".into());
    }
    for arg in &options.extra {
        if arg.contains('=') {
            args.push(arg.to_string());
        }
    }
    args
}

#[derive(Debug)]
enum Event {
    Done,
    Query(Box<Result<smt2parser::concrete::Command, smt2parser::Error>>),
}

fn spawn_child_stream_logger<R>(
    logger: Option<Arc<Mutex<std::fs::File>>>,
    input: R,
    repeat: bool,
    error_msg: &'static str,
) -> std::thread::JoinHandle<()>
where
    R: std::io::Read + Send + 'static,
{
    let input = std::io::BufReader::new(input);
    std::thread::spawn(move || {
        for line in input.lines() {
            let line = line.expect(error_msg);
            if let Some(logger) = &logger {
                let mut f = logger.lock().unwrap();
                writeln!(f, ";; {}", line).expect("Failed to write to log file");
            }
            if repeat {
                println!("{}", line);
            }
        }
    })
}

fn process_events(
    receiver: std::sync::mpsc::Receiver<Event>,
    z3_args: Vec<String>,
    mut processor: smt2proxy::CommandProcessor,
) {
    if let Some(logger) = processor.logger() {
        let mut f = logger.lock().unwrap();
        writeln!(
            f,
            "; z3 {}",
            z3_args
                .iter()
                .map(|x| format!("\"{}\"", x))
                .collect::<Vec<_>>()
                .join(" ")
        )
        .unwrap();
    }

    let mut child = std::process::Command::new("z3")
        .args(&z3_args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();

    let handler_stdout = spawn_child_stream_logger(
        processor.logger().clone(),
        child.stdout.take().expect("Failed to open child stdout"),
        /* repeat */ true,
        "Failed to read child stdout",
    );

    let handler_stderr = spawn_child_stream_logger(
        processor.logger().clone(),
        child.stderr.take().expect("Failed to open child stderr"),
        /* repeat */ false,
        "Failed to read child stderr",
    );

    {
        let mut child_stdin = child.stdin.take().expect("Failed to open child stdin");

        while let Ok(event) = receiver.recv() {
            match event {
                Event::Query(value) => match *value {
                    Ok(in_command) => {
                        let out_commands = processor.process(in_command);
                        for command in out_commands {
                            writeln!(child_stdin, "{}", command)
                                .expect("Failed to write to child stdin");
                        }
                    }
                    Err(error) => {
                        if let Some(logger) = processor.logger() {
                            let mut f = logger.lock().unwrap();
                            writeln!(f, "; {}", error).expect("Failed to write to log file");
                        }
                        break;
                    }
                },
                Event::Done => {
                    break;
                }
            }
        }
        let out_commands = processor.stop();
        for command in out_commands {
            writeln!(child_stdin, "{}", command).expect("Failed to write to child stdin");
        }
    }
    // child_stdin is now closed.
    // Wait for z3 to read EOF and terminate normally.
    child.wait().unwrap();
    // Wait for the child stream loggers to read EOF and terminate.
    handler_stdout.join().unwrap();
    handler_stderr.join().unwrap();
}

fn main() {
    let options = Options::from_iter(iter_args());
    let smt2proxy_normalize_symbols = options.smt2proxy_config.smt2proxy_normalize_symbols;

    if options.version {
        std::process::Command::new("z3")
            .arg("-version")
            .status()
            .unwrap();
        return;
    }

    // Spawn the command processor in a separate thread.
    let (sender, receiver) = std::sync::mpsc::channel();
    let handler = {
        let z3_args = make_z3_args(&options);
        let processor = smt2proxy::CommandProcessor::from(options.smt2proxy_config);
        std::thread::spawn(move || {
            process_events(receiver, z3_args, processor);
        })
    };

    // Setup the input file.
    let stdin = std::io::stdin();
    let input: Box<dyn std::io::BufRead> = if options.r#in {
        Box::new(stdin.lock())
    } else {
        let path_opt = options
            .extra
            .last()
            .filter(|s| !s.contains('='))
            .map(std::path::PathBuf::from);
        let path = options
            .file
            .or(path_opt)
            .expect("Input file is required unless flags `-in` or `-version` are passed.");
        let f = std::fs::File::open(&path)
            .unwrap_or_else(|_| panic!("Failed to open input file {:?}", path));
        Box::new(std::io::BufReader::new(f))
    };

    // Send the input commands to the command processor.
    let stream: Box<dyn Iterator<Item = std::result::Result<_, _>>> = {
        if smt2proxy_normalize_symbols {
            let builder =
                smt2parser::renaming::TesterModernizer::new(smt2parser::concrete::SyntaxBuilder);
            Box::new(smt2parser::CommandStream::new(input, builder, None))
        } else {
            let builder = smt2parser::concrete::SyntaxBuilder;
            Box::new(smt2parser::CommandStream::new(input, builder, None))
        }
    };
    for result in stream {
        sender.send(Event::Query(Box::new(result))).unwrap();
    }

    // Send EOF to z3.
    sender.send(Event::Done).unwrap();

    // Wait for the command processor to terminate.
    handler.join().unwrap();
}
