// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use z3tracer::Model;

fn process_file(path: &str) -> std::io::Result<Model> {
    let file = std::io::BufReader::new(std::fs::File::open(path)?);
    let mut model = Model::default();
    if let Err(le) = model.process(Some(path.to_string()), file) {
        panic!("Error at {:?}: {:?}", le.position, le.error);
    }
    Ok(model)
}

#[test]
fn test_file1() -> std::io::Result<()> {
    let model = process_file("tests/data/file1.log")?;
    assert_eq!(model.count_terms(), 273318);
    assert_eq!(model.count_instantiations(), 3023);
    Ok(())
}
