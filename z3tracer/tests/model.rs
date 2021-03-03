// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use z3tracer::{error::Error, Lexer, Model};

fn process_file(path: &str) -> std::io::Result<Model> {
    let file = std::io::BufReader::new(std::fs::File::open(path)?);
    let mut lexer = Lexer::new(file);
    let mut model = Model::default();
    loop {
        match model.process_line(&mut lexer) {
            Ok(_) => (),
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
    Ok(model)
}

#[test]
fn test_file1() -> std::io::Result<()> {
    let model = process_file("tests/data/file1.log")?;
    assert_eq!(model.terms().len(), 273318);
    assert_eq!(model.instantiations().len(), 3023);
    Ok(())
}
